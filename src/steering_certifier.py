"""Zero-floating-point-trust exact-Q certificate builder and verifier for Paper 10.

Schema: EPR-STEER-CERT-1.0
Author: Lluis Eriksson

Pure Python stdlib ONLY (`fractions.Fraction`, `math`, `re`).
Supports 4 sound, mutually exclusive exact-Q modes:
  1. `finite_m_steering_witness`  -> CERTIFIED_STEERABLE
  2. `finite_m_lhs_model`         -> CERTIFIED_UNSTEERABLE_LHS
  3. `universal_finite_m_gap`     -> CERTIFIED_UNIVERSAL_FINITE_M_UNSTEERABLE
  4. `two_copy_superactivation`   -> CERTIFIED_TWO_COPY_SUPERACTIVATED_SEPARABLE_CONDITIONALS
"""

from __future__ import annotations

import math
import re
from fractions import Fraction
from typing import Any, Dict, List, Sequence, Tuple

from .steering_exact import (
    BELL_JOINT_LHS_UB_Q,
    bell_conditional_ppt_eigs_exact,
    canonical_linear_witness_exact,
    dot3,
    great_circle_max_regions,
    norm_sq3,
    two_copy_superactivation_margin_exact,
    universal_finite_m_bound_exact,
)

SCHEMA_VERSION = "EPR-STEER-CERT-1.0"
_CERT_ID_RE = re.compile(r"\A[A-Za-z0-9._-]{1,120}\Z", re.ASCII)
_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z", re.ASCII)
_FRAC_RE = re.compile(r"\A(?P<num>-?[1-9][0-9]*)/(?P<den>[1-9][0-9]*)\Z", re.ASCII)

_VALID_MODES = frozenset({
    "finite_m_steering_witness",
    "finite_m_lhs_model",
    "universal_finite_m_gap",
    "two_copy_superactivation",
})

_MODE_VERDICT = {
    "finite_m_steering_witness": "CERTIFIED_STEERABLE",
    "finite_m_lhs_model": "CERTIFIED_UNSTEERABLE_LHS",
    "universal_finite_m_gap": "CERTIFIED_UNIVERSAL_FINITE_M_UNSTEERABLE",
    "two_copy_superactivation": "CERTIFIED_TWO_COPY_SUPERACTIVATED_SEPARABLE_CONDITIONALS",
}

_WITNESS_KEYS = frozenset({
    "schema_version", "cert_id", "mode", "verdict", "m_settings",
    "visibility_v", "u_norm_sq", "w_vectors", "f_vectors",
    "quantum_score_sq", "lhs_bound_sq", "critical_v_sq",
})

_LHS_KEYS = frozenset({
    "schema_version", "cert_id", "mode", "verdict", "m_settings",
    "visibility_v", "u_norm_sq", "w_vectors", "lhs_states",
})

_LHS_STATE_KEYS = frozenset({"weight_p", "signs_a", "bloch_b"})

_UNIV_KEYS = frozenset({
    "schema_version", "cert_id", "mode", "verdict", "m_settings",
    "visibility_v", "max_regions", "universal_bound_v",
})

_SUPER_KEYS = frozenset({
    "schema_version", "cert_id", "mode", "verdict",
    "visibility_v", "rigidity_gamma", "bell_joint_lhs_ub",
    "quantum_score_q", "lhs_upper_bound", "superactivation_margin",
    "ppt_min_eig_at_full_bell", "single_copy_pvm_unsteerable",
})


def _assert_strict_json_types(obj: Any, path: str = "$") -> None:
    if obj is None:
        return
    if type(obj) is bool:
        raise ValueError(f"Forbidden bool at {path}: {obj!r}")
    if type(obj) is int:
        return
    if type(obj) is str:
        return
    if type(obj) is list:
        for idx, item in enumerate(obj):
            _assert_strict_json_types(item, f"{path}[{idx}]")
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise ValueError(f"Non-string dict key at {path}: {k!r}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    raise ValueError(f"Forbidden type {type(obj).__name__} at {path}: {obj!r}")


def canonical_fraction_str(x: Fraction) -> str:
    if not isinstance(x, Fraction):
        raise TypeError(f"Expected Fraction, got {type(x).__name__}")
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def parse_canonical_fraction(s: Any, field_name: str = "rational") -> Fraction:
    if type(s) is not str:
        raise ValueError(f"{field_name} must be canonical str, got {type(s).__name__}")
    if _INT_RE.match(s):
        return Fraction(int(s), 1)
    m = _FRAC_RE.match(s)
    if not m:
        raise ValueError(f"Non-canonical rational string for {field_name}: {s!r}")
    num = int(m.group("num"))
    den = int(m.group("den"))
    if den < 2:
        raise ValueError(f"Denominator must be >= 2 for {field_name}: {s!r}")
    if math.gcd(abs(num), den) != 1:
        raise ValueError(f"Unreduced rational string for {field_name}: {s!r}")
    return Fraction(num, den)


def _parse_vec3(raw: Any, field: str) -> Tuple[Fraction, Fraction, Fraction]:
    if type(raw) is not list or len(raw) != 3:
        raise ValueError(f"{field} must be a 3-element list")
    return (
        parse_canonical_fraction(raw[0], f"{field}[0]"),
        parse_canonical_fraction(raw[1], f"{field}[1]"),
        parse_canonical_fraction(raw[2], f"{field}[2]"),
    )


def _check_distinct_projective_axes(vecs: Sequence[Tuple[Fraction, Fraction, Fraction]]) -> None:
    seen = set()
    for idx, w in enumerate(vecs):
        # Canonicalize projective sign (+w ~ -w)
        neg = (-w[0], -w[1], -w[2])
        key = w if w >= neg else neg
        if key in seen:
            raise ValueError(f"Duplicate/antipodal measurement axis at index {idx}: {w}")
        seen.add(key)


def build_finite_m_witness_certificate(
    cert_id: str,
    v: Fraction,
    u_norm_sq: Fraction,
    w_vectors: Sequence[Sequence[Fraction]],
    f_vectors: Sequence[Sequence[Fraction]],
) -> Dict[str, Any]:
    if type(cert_id) is not str or not _CERT_ID_RE.match(cert_id):
        raise ValueError(f"Invalid cert_id: {cert_id!r}")
    s_q_sq, lhs_sq, v_crit_sq = canonical_linear_witness_exact(w_vectors, f_vectors, u_norm_sq, v)
    if s_q_sq <= lhs_sq:
        raise ValueError(f"Witness does not violate LHS bound: S_Q^2={s_q_sq} <= L^2={lhs_sq}")
    cert = {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "finite_m_steering_witness",
        "verdict": _MODE_VERDICT["finite_m_steering_witness"],
        "m_settings": len(w_vectors),
        "visibility_v": canonical_fraction_str(v),
        "u_norm_sq": canonical_fraction_str(u_norm_sq),
        "w_vectors": [[canonical_fraction_str(c) for c in w] for w in w_vectors],
        "f_vectors": [[canonical_fraction_str(c) for c in f] for f in f_vectors],
        "quantum_score_sq": canonical_fraction_str(s_q_sq),
        "lhs_bound_sq": canonical_fraction_str(lhs_sq),
        "critical_v_sq": canonical_fraction_str(v_crit_sq),
    }
    verify_steering_certificate_exact(cert)
    return cert


def build_finite_m_lhs_certificate(
    cert_id: str,
    v: Fraction,
    u_norm_sq: Fraction,
    w_vectors: Sequence[Sequence[Fraction]],
    lhs_states: Sequence[Tuple[Fraction, Sequence[int], Sequence[Fraction]]],
) -> Dict[str, Any]:
    if type(cert_id) is not str or not _CERT_ID_RE.match(cert_id):
        raise ValueError(f"Invalid cert_id: {cert_id!r}")
    cert = {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "finite_m_lhs_model",
        "verdict": _MODE_VERDICT["finite_m_lhs_model"],
        "m_settings": len(w_vectors),
        "visibility_v": canonical_fraction_str(v),
        "u_norm_sq": canonical_fraction_str(u_norm_sq),
        "w_vectors": [[canonical_fraction_str(c) for c in w] for w in w_vectors],
        "lhs_states": [
            {
                "weight_p": canonical_fraction_str(p),
                "signs_a": [int(a) for a in signs],
                "bloch_b": [canonical_fraction_str(c) for c in b],
            }
            for p, signs, b in lhs_states
        ],
    }
    verify_steering_certificate_exact(cert)
    return cert


def build_universal_gap_certificate(cert_id: str, m: int, v: Fraction) -> Dict[str, Any]:
    if type(cert_id) is not str or not _CERT_ID_RE.match(cert_id):
        raise ValueError(f"Invalid cert_id: {cert_id!r}")
    r_max = great_circle_max_regions(m)
    v_ub = universal_finite_m_bound_exact(m)
    if v <= 0 or v > v_ub:
        raise ValueError(f"v={v} exceeds universal finite-m bound {v_ub}")
    cert = {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "universal_finite_m_gap",
        "verdict": _MODE_VERDICT["universal_finite_m_gap"],
        "m_settings": m,
        "visibility_v": canonical_fraction_str(v),
        "max_regions": r_max,
        "universal_bound_v": canonical_fraction_str(v_ub),
    }
    verify_steering_certificate_exact(cert)
    return cert


def build_two_copy_superactivation_certificate(
    cert_id: str,
    v: Fraction,
    gamma: Fraction,
) -> Dict[str, Any]:
    if type(cert_id) is not str or not _CERT_ID_RE.match(cert_id):
        raise ValueError(f"Invalid cert_id: {cert_id!r}")
    if v > Fraction(1, 2):
        raise ValueError(
            f"Two-copy superactivation requires a single-copy PVM-unsteerable state (v <= 1/2); got v={v}"
        )
    q_val, l_ub, margin = two_copy_superactivation_margin_exact(v, gamma)
    eigs = bell_conditional_ppt_eigs_exact(v, Fraction(1, 1))
    min_ppt = min(eigs)
    if margin <= 0:
        raise ValueError(f"No superactivation: margin={margin} <= 0")
    if min_ppt < 0:
        raise ValueError(f"Conditional state is not separable (PPT): min_eig={min_ppt} < 0")
    cert = {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "two_copy_superactivation",
        "verdict": _MODE_VERDICT["two_copy_superactivation"],
        "visibility_v": canonical_fraction_str(v),
        "rigidity_gamma": canonical_fraction_str(gamma),
        "bell_joint_lhs_ub": canonical_fraction_str(BELL_JOINT_LHS_UB_Q),
        "quantum_score_q": canonical_fraction_str(q_val),
        "lhs_upper_bound": canonical_fraction_str(l_ub),
        "superactivation_margin": canonical_fraction_str(margin),
        "ppt_min_eig_at_full_bell": canonical_fraction_str(min_ppt),
        "single_copy_pvm_unsteerable": 1,
    }
    verify_steering_certificate_exact(cert)
    return cert


def verify_steering_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Independently verify an EPR-STEER-CERT-1.0 certificate with ZERO floating-point trust."""
    if type(cert) is not dict:
        raise ValueError("Certificate must be a strict dict")
    _assert_strict_json_types(cert)

    if cert.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"Unsupported schema_version: {cert.get('schema_version')!r}")
    cert_id = cert.get("cert_id")
    if type(cert_id) is not str or not _CERT_ID_RE.match(cert_id):
        raise ValueError(f"Invalid cert_id: {cert_id!r}")

    mode = cert.get("mode")
    if mode not in _VALID_MODES:
        raise ValueError(f"Unsupported mode: {mode!r}")
    if cert.get("verdict") != _MODE_VERDICT[mode]:
        raise ValueError(f"Verdict mismatch for mode {mode}: got {cert.get('verdict')!r}")

    if mode == "finite_m_steering_witness":
        if set(cert.keys()) != _WITNESS_KEYS:
            raise ValueError("Key set mismatch for finite_m_steering_witness")
        m = cert["m_settings"]
        if type(m) is not int or not (2 <= m <= 16):
            raise ValueError(f"m_settings must be int in [2, 16], got {m!r}")
        v = parse_canonical_fraction(cert["visibility_v"], "visibility_v")
        u_nsq = parse_canonical_fraction(cert["u_norm_sq"], "u_norm_sq")
        if v <= 0 or v > 1 or u_nsq <= 0:
            raise ValueError("Invalid visibility_v or u_norm_sq")
        w_raw = cert["w_vectors"]
        f_raw = cert["f_vectors"]
        if type(w_raw) is not list or type(f_raw) is not list or len(w_raw) != m or len(f_raw) != m:
            raise ValueError("w_vectors and f_vectors must be lists of length m_settings")
        w_vecs = [_parse_vec3(w_raw[i], f"w_vectors[{i}]") for i in range(m)]
        f_vecs = [_parse_vec3(f_raw[i], f"f_vectors[{i}]") for i in range(m)]
        _check_distinct_projective_axes(w_vecs)
        s_q_sq, lhs_sq, v_crit_sq = canonical_linear_witness_exact(w_vecs, f_vecs, u_nsq, v)
        if parse_canonical_fraction(cert["quantum_score_sq"], "quantum_score_sq") != s_q_sq:
            raise ValueError("quantum_score_sq mismatch")
        if parse_canonical_fraction(cert["lhs_bound_sq"], "lhs_bound_sq") != lhs_sq:
            raise ValueError("lhs_bound_sq mismatch")
        if parse_canonical_fraction(cert["critical_v_sq"], "critical_v_sq") != v_crit_sq:
            raise ValueError("critical_v_sq mismatch")
        if s_q_sq <= lhs_sq:
            raise ValueError(f"Steering inequality NOT violated: S_Q^2={s_q_sq} <= L^2={lhs_sq}")
        return {
            "verified": True, "cert_id": cert_id, "mode": mode, "verdict": cert["verdict"],
            "m_settings": m, "visibility_v": str(v), "critical_v_sq": str(v_crit_sq),
        }

    if mode == "finite_m_lhs_model":
        if set(cert.keys()) != _LHS_KEYS:
            raise ValueError("Key set mismatch for finite_m_lhs_model")
        m = cert["m_settings"]
        if type(m) is not int or not (1 <= m <= 32):
            raise ValueError(f"m_settings must be int in [1, 32], got {m!r}")
        v = parse_canonical_fraction(cert["visibility_v"], "visibility_v")
        u_nsq = parse_canonical_fraction(cert["u_norm_sq"], "u_norm_sq")
        if v <= 0 or v > 1 or u_nsq <= 0:
            raise ValueError("Invalid visibility_v or u_norm_sq")
        w_raw = cert["w_vectors"]
        if type(w_raw) is not list or len(w_raw) != m:
            raise ValueError("w_vectors must have length m_settings")
        w_vecs = [_parse_vec3(w_raw[i], f"w_vectors[{i}]") for i in range(m)]
        for i, w in enumerate(w_vecs):
            if norm_sq3(w) != u_nsq:
                raise ValueError(f"w_vectors[{i}] norm_sq != u_norm_sq")
        _check_distinct_projective_axes(w_vecs)

        states = cert["lhs_states"]
        if type(states) is not list or len(states) == 0:
            raise ValueError("lhs_states must be non-empty list")
        sum_p = Fraction(0, 1)
        marg = [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)]
        alice_marg = [Fraction(0, 1) for _ in range(m)]
        corr = [[Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)] for _ in range(m)]
        for idx, st in enumerate(states):
            if type(st) is not dict or set(st.keys()) != _LHS_STATE_KEYS:
                raise ValueError(f"lhs_states[{idx}] key mismatch")
            p = parse_canonical_fraction(st["weight_p"], f"lhs_states[{idx}].weight_p")
            if p <= 0:
                raise ValueError(f"lhs_states[{idx}].weight_p must be > 0")
            signs = st["signs_a"]
            if type(signs) is not list or len(signs) != m:
                raise ValueError(f"lhs_states[{idx}].signs_a length mismatch")
            for a in signs:
                if type(a) is not int or a not in (-1, 1):
                    raise ValueError(f"lhs_states[{idx}].signs_a must contain only int -1 or +1")
            b = _parse_vec3(st["bloch_b"], f"lhs_states[{idx}].bloch_b")
            # Valid quantum Bloch ball constraint: ||n||^2 <= 1  <==>  ||b||^2 <= u_norm_sq
            if norm_sq3(b) > u_nsq:
                raise ValueError(f"lhs_states[{idx}] violates quantum Bloch ball: ||b||^2={norm_sq3(b)} > {u_nsq}")
            sum_p += p
            for d in range(3):
                marg[d] += p * b[d]
            for x in range(m):
                ax = signs[x]
                alice_marg[x] += p * ax
                for d in range(3):
                    corr[x][d] += p * ax * b[d]
        if sum_p != Fraction(1, 1):
            raise ValueError(f"LHS probability weights do not sum to 1: {sum_p}")
        if marg != [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)]:
            raise ValueError(f"LHS Bob marginal is not isotropic I/2: {marg}")
        for x in range(m):
            if alice_marg[x] != Fraction(0, 1):
                raise ValueError(f"LHS Alice marginal Tr(sigma_{{+|{x}}}) != 1/2: sum(p*a_x) = {alice_marg[x]}")
            target = [v * w_vecs[x][d] for d in range(3)]
            if corr[x] != target:
                raise ValueError(f"LHS correlation mismatch at setting x={x}: {corr[x]} != {target}")
        return {
            "verified": True, "cert_id": cert_id, "mode": mode, "verdict": cert["verdict"],
            "m_settings": m, "visibility_v": str(v), "num_hidden_states": len(states),
        }

    if mode == "universal_finite_m_gap":
        if set(cert.keys()) != _UNIV_KEYS:
            raise ValueError("Key set mismatch for universal_finite_m_gap")
        m = cert["m_settings"]
        if type(m) is not int or not (1 <= m <= 100000):
            raise ValueError(f"m_settings must be int in [1, 100000], got {m!r}")
        v = parse_canonical_fraction(cert["visibility_v"], "visibility_v")
        if v <= 0 or v > 1:
            raise ValueError("visibility_v must be in (0, 1]")
        r_act = great_circle_max_regions(m)
        v_ub_act = universal_finite_m_bound_exact(m)
        if cert["max_regions"] != r_act:
            raise ValueError("max_regions mismatch")
        if parse_canonical_fraction(cert["universal_bound_v"], "universal_bound_v") != v_ub_act:
            raise ValueError("universal_bound_v mismatch")
        if v > v_ub_act:
            raise ValueError(f"visibility_v={v} exceeds universal bound {v_ub_act}")
        return {
            "verified": True, "cert_id": cert_id, "mode": mode, "verdict": cert["verdict"],
            "m_settings": m, "visibility_v": str(v), "universal_bound_v": str(v_ub_act),
        }

    # mode == "two_copy_superactivation"
    if set(cert.keys()) != _SUPER_KEYS:
        raise ValueError("Key set mismatch for two_copy_superactivation")
    v = parse_canonical_fraction(cert["visibility_v"], "visibility_v")
    gamma = parse_canonical_fraction(cert["rigidity_gamma"], "rigidity_gamma")
    if v <= 0 or v > Fraction(1, 2) or gamma <= 0:
        raise ValueError(
            "two_copy_superactivation requires single-copy PVM-unsteerable v in (0, 1/2] and gamma > 0"
        )
    if parse_canonical_fraction(cert["bell_joint_lhs_ub"], "bell_joint_lhs_ub") != BELL_JOINT_LHS_UB_Q:
        raise ValueError("bell_joint_lhs_ub must equal exact 5167/7056")
    q_act, l_act, m_act = two_copy_superactivation_margin_exact(v, gamma)
    min_ppt_act = min(bell_conditional_ppt_eigs_exact(v, Fraction(1, 1)))
    if parse_canonical_fraction(cert["quantum_score_q"], "quantum_score_q") != q_act:
        raise ValueError("quantum_score_q mismatch")
    if parse_canonical_fraction(cert["lhs_upper_bound"], "lhs_upper_bound") != l_act:
        raise ValueError("lhs_upper_bound mismatch")
    if parse_canonical_fraction(cert["superactivation_margin"], "superactivation_margin") != m_act:
        raise ValueError("superactivation_margin mismatch")
    if parse_canonical_fraction(cert["ppt_min_eig_at_full_bell"], "ppt_min_eig_at_full_bell") != min_ppt_act:
        raise ValueError("ppt_min_eig_at_full_bell mismatch")
    if cert["single_copy_pvm_unsteerable"] != 1:
        raise ValueError("single_copy_pvm_unsteerable flag must be strict int 1 (v <= 1/2)")
    if m_act <= 0:
        raise ValueError(f"Superactivation margin not strictly positive: {m_act}")
    if min_ppt_act < 0:
        raise ValueError(f"Conditional states violate PPT separability: {min_ppt_act}")
    return {
        "verified": True, "cert_id": cert_id, "mode": mode, "verdict": cert["verdict"],
        "visibility_v": str(v), "rigidity_gamma": str(gamma), "margin": str(m_act),
        "ppt_min_eig": str(min_ppt_act),
    }
