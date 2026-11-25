"""Comprehensive test & 46-attack adversarial red-team suite for Paper 10.

Author: Lluis Eriksson
"""

from __future__ import annotations

import copy
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

import pytest

from src import (
    BELL_JOINT_LHS_UB_Q,
    bell_conditional_ppt_eigs_exact,
    canonical_linear_witness_exact,
    polytope_measurement_families_exact,
    two_copy_superactivation_margin_exact,
    universal_finite_m_bound_exact,
    verify_steering_certificate_exact,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "results" / "certificates"


def test_exact_algebra_identities() -> None:
    """Verify universal finite-m gap, cuboctahedron supremacy, PPT eigenvalues, and 2-copy superactivation."""
    assert universal_finite_m_bound_exact(1) == Fraction(1, 1)
    assert universal_finite_m_bound_exact(2) == Fraction(2, 3)
    assert universal_finite_m_bound_exact(3) == Fraction(4, 7)
    assert universal_finite_m_bound_exact(6) == Fraction(16, 31)

    fams = polytope_measurement_families_exact()
    u6, w6 = fams["m6_cuboctahedron"]
    _, _, vc6_sq = canonical_linear_witness_exact(w6, w6, u6, Fraction(1, 1))
    assert vc6_sq == Fraction(5, 18)

    # Exact PPT eigenvalues at v = 1/2, t = 1 (full Bell)
    eigs = bell_conditional_ppt_eigs_exact(Fraction(1, 2), Fraction(1, 1))
    assert min(eigs) == Fraction(1, 16)

    # Exact 2-copy superactivation at v = 1/2 AND strictly below at v = 49999/100000
    _, _, m_half = two_copy_superactivation_margin_exact(Fraction(1, 2), Fraction(114, 1))
    assert m_half == Fraction(1199, 134064) and m_half > 0
    _, _, m_below = two_copy_superactivation_margin_exact(Fraction(49999, 100000), Fraction(114, 1))
    assert m_below > 0


def test_all_14_shipped_certificates_verify() -> None:
    certs = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(certs) == 14
    modes = set()
    for cp in certs:
        data = json.loads(cp.read_text(encoding="utf-8"))
        res = verify_steering_certificate_exact(data)
        assert res["verified"] is True
        modes.add(res["mode"])
    assert modes == {
        "finite_m_steering_witness",
        "finite_m_lhs_model",
        "universal_finite_m_gap",
        "two_copy_superactivation",
    }


def test_46_live_adversarial_red_team_attacks_rejected() -> None:
    """Every adversarial corruption across all 4 modes MUST raise ValueError."""
    c_wit = json.loads((CERT_DIR / "witness_m6_cuboctahedron_v53.cert.json").read_text(encoding="utf-8"))
    c_lhs = json.loads((CERT_DIR / "lhs_m6_cuboctahedron_v525.cert.json").read_text(encoding="utf-8"))
    c_unv = json.loads((CERT_DIR / "univ_gap_m6_v16_31.cert.json").read_text(encoding="utf-8"))
    c_sup = json.loads((CERT_DIR / "superact_two_copy_v_half.cert.json").read_text(encoding="utf-8"))

    attacks = []

    def add(name, fn, base=c_wit):
        cand = copy.deepcopy(base)
        fn(cand)
        attacks.append((name, cand))

    # 1-12: Schema, type, and identifier hygiene attacks
    add("01_bad_schema", lambda c: c.__setitem__("schema_version", "FAKE-1.0"))
    add("02_missing_key", lambda c: c.pop("lhs_bound_sq"))
    add("03_extra_key", lambda c: c.__setitem__("rogue", 1))
    add("04_blank_cert_id", lambda c: c.__setitem__("cert_id", "   "))
    add("05_newline_cert_id", lambda c: c.__setitem__("cert_id", "bad\nid"))
    add("06_bool_m_settings", lambda c: c.__setitem__("m_settings", True))
    add("07_float_visibility", lambda c: c.__setitem__("visibility_v", 0.53))
    add("08_decimal_visibility", lambda c: c.__setitem__("visibility_v", Decimal("0.53")))
    add("09_tuple_vectors", lambda c: c.__setitem__("w_vectors", tuple(c["w_vectors"])))
    add("10_non_str_key", lambda c: c.__setitem__(42, "bad"))
    add("11_bad_mode", lambda c: c.__setitem__("mode", "bogus_mode"))
    add("12_wrong_verdict", lambda c: c.__setitem__("verdict", "CERTIFIED_UNSTEERABLE_LHS"))

    # 13-20: Canonical rational parser attacks
    add("13_unreduced_frac", lambda c: c.__setitem__("visibility_v", "106/200"))
    add("14_denom_one", lambda c: c.__setitem__("u_norm_sq", "2/1"))
    add("15_neg_zero", lambda c: c["w_vectors"][0].__setitem__(2, "-0"))
    add("16_leading_plus", lambda c: c.__setitem__("u_norm_sq", "+2"))
    add("17_leading_zero", lambda c: c.__setitem__("u_norm_sq", "02"))
    add("18_trailing_newline", lambda c: c.__setitem__("visibility_v", "53/100\n"))
    add("19_unicode_digit", lambda c: c.__setitem__("u_norm_sq", "\u0662"))
    add("20_zero_visibility", lambda c: c.__setitem__("visibility_v", "0"))

    # 21-28: Mode 1 (finite_m_steering_witness) algebraic attacks
    add("21_unviolated_witness_v52", lambda c: (
        c.__setitem__("visibility_v", "13/25"),
        c.__setitem__("quantum_score_sq", "12168/625"),
    ))
    add("22_forged_lhs_bound", lambda c: c.__setitem__("lhs_bound_sq", "19"))
    add("23_forged_quantum_sq", lambda c: c.__setitem__("quantum_score_sq", "999"))
    add("24_forged_crit_v_sq", lambda c: c.__setitem__("critical_v_sq", "1/4"))
    add("25_wrong_w_norm", lambda c: c["w_vectors"][0].__setitem__(0, "2"))
    add("26_duplicate_axis", lambda c: c["w_vectors"].__setitem__(1, copy.deepcopy(c["w_vectors"][0])))
    add("27_antipodal_axis", lambda c: c["w_vectors"].__setitem__(1, ["-1", "-1", "0"]))
    add("28_m_out_of_range", lambda c: c.__setitem__("m_settings", 1))

    # 29-36: Mode 2 (finite_m_lhs_model) physical & quantum-state attacks
    add("29_lhs_bloch_outside_ball", lambda c: c["lhs_states"][0].__setitem__("bloch_b", ["2", "0", "0"]), base=c_lhs)
    add("30_lhs_weights_ne_1", lambda c: c["lhs_states"][0].__setitem__("weight_p", "1/12"), base=c_lhs)
    add("31_lhs_zero_weight", lambda c: c["lhs_states"][0].__setitem__("weight_p", "0"), base=c_lhs)
    add("32_lhs_non_binary_sign", lambda c: c["lhs_states"][0]["signs_a"].__setitem__(0, 0), base=c_lhs)
    add("33_lhs_bool_sign", lambda c: c["lhs_states"][0]["signs_a"].__setitem__(0, True), base=c_lhs)
    add("34_lhs_non_isotropic_marginal", lambda c: c["lhs_states"][0].__setitem__("bloch_b", ["0", "0", "0"]), base=c_lhs)
    add("35_lhs_forged_high_v", lambda c: c.__setitem__("visibility_v", "53/100"), base=c_lhs)
    add("36_lhs_empty_states", lambda c: c.__setitem__("lhs_states", []), base=c_lhs)

    # 37-40: Mode 3 (universal_finite_m_gap) attacks
    add("37_univ_exceeds_bound", lambda c: c.__setitem__("visibility_v", "17/31"), base=c_unv)
    add("38_univ_wrong_regions", lambda c: c.__setitem__("max_regions", 30), base=c_unv)
    add("39_univ_wrong_bound", lambda c: c.__setitem__("universal_bound_v", "17/31"), base=c_unv)
    add("40_univ_m_zero", lambda c: c.__setitem__("m_settings", 0), base=c_unv)

    # 41-44: Mode 4 (two_copy_superactivation) attacks
    add("41_super_forged_bell_ub", lambda c: c.__setitem__("bell_joint_lhs_ub", "1/2"), base=c_sup)
    add("42_super_no_violation_v499", lambda c: (
        c.__setitem__("visibility_v", "499/1000"),
        c.__setitem__("quantum_score_q", "5726067/50000"),
        c.__setitem__("superactivation_margin", "-48723647/176400000"),
    ), base=c_sup)
    add("43_super_non_ppt_v60", lambda c: (
        c.__setitem__("visibility_v", "3/5"),
        c.__setitem__("quantum_score_q", "3447/25"),
        c.__setitem__("superactivation_margin", "7673153/335160"),
        c.__setitem__("ppt_min_eig_at_full_bell", "-1/50"),
        c.__setitem__("single_copy_pvm_unsteerable", 0),
    ), base=c_sup)
    add("44_super_wrong_single_copy_flag", lambda c: c.__setitem__("single_copy_pvm_unsteerable", 0), base=c_sup)

    # 45-46: Hostile audit regression tests (Blocker 2: nonzero Alice marginal; Blocker 3: v > 1/2 superactivation)
    attacks.append(("45_lhs_nonzero_alice_marginal", {
        "schema_version": "EPR-STEER-CERT-1.0",
        "cert_id": "forged_lhs_alice_marginal",
        "mode": "finite_m_lhs_model",
        "verdict": "CERTIFIED_UNSTEERABLE_LHS",
        "m_settings": 1,
        "visibility_v": "1/4",
        "u_norm_sq": "1",
        "w_vectors": [["1", "0", "0"]],
        "lhs_states": [
            {"weight_p": "1/2", "signs_a": [1], "bloch_b": ["1/2", "0", "0"]},
            {"weight_p": "1/4", "signs_a": [1], "bloch_b": ["-1/2", "0", "0"]},
            {"weight_p": "1/4", "signs_a": [-1], "bloch_b": ["-1/2", "0", "0"]},
        ],
    }))
    attacks.append(("46_superact_already_single_copy_steerable_v55", {
        "schema_version": "EPR-STEER-CERT-1.0",
        "cert_id": "forged_superact_v55",
        "mode": "two_copy_superactivation",
        "verdict": "CERTIFIED_TWO_COPY_SUPERACTIVATED_SEPARABLE_CONDITIONALS",
        "visibility_v": "11/20",
        "rigidity_gamma": "114",
        "bell_joint_lhs_ub": "5167/7056",
        "quantum_score_q": "50523/400",
        "lhs_upper_bound": "15382627/134064",
        "superactivation_margin": "193933723/16758000",
        "ppt_min_eig_at_full_bell": "37/1600",
        "single_copy_pvm_unsteerable": 0,
    }))

    assert len(attacks) == 46
    for name, cand in attacks:
        with pytest.raises(ValueError, match="."):
            verify_steering_certificate_exact(cand)
