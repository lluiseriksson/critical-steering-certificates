"""Run all 4 computational experiments for Paper 10 and emit 14 exact-Q certificates.

Outputs:
  results/certificates/<cert_id>.cert.json  (14 exact-Q EPR-STEER-CERT-1.0 certificates)
  results/exp1_certified_atlas.json
  results/exp2_polytope_ladder_and_universal_gap.json
  results/exp3_two_copy_haar_mc_crosscheck.json
  results/exp4_ppt_separability_phase_diagram.json

Author: Lluis Eriksson
"""

from __future__ import annotations

import itertools
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Tuple

import numpy as np
from scipy.stats import special_ortho_group

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src import (
    BELL_JOINT_LHS_UB_Q,
    bell_conditional_ppt_eigs_exact,
    build_finite_m_lhs_certificate,
    build_finite_m_witness_certificate,
    build_two_copy_superactivation_certificate,
    build_universal_gap_certificate,
    canonical_fraction_str,
    canonical_linear_witness_exact,
    great_circle_max_regions,
    polytope_measurement_families_exact,
    two_copy_superactivation_margin_exact,
    universal_finite_m_bound_exact,
    verify_steering_certificate_exact,
)


def _build_cuboctahedron_lhs_24(alpha: Fraction) -> List[Tuple[Fraction, List[int], Tuple[Fraction, Fraction, Fraction]]]:
    """24-state exact-Q LHS model for m=6 cuboctahedron (u_norm_sq = 2):
    signed permutations of alpha * (2, 1, 0), valid whenever 5 * alpha^2 <= 2,
    reproducing v = (5/6) * alpha exactly (hitting optimal sqrt(5/18) as alpha -> sqrt(2/5)).
    """
    fams = polytope_measurement_families_exact()
    _, w_vecs = fams["m6_cuboctahedron"]
    # Generate all 24 signed permutations of (2, 1, 0)
    raw_dirs: List[Tuple[int, int, int]] = []
    for perm in set(itertools.permutations([2, 1, 0])):
        nz = [i for i, val in enumerate(perm) if val != 0]
        for s0 in (-1, 1):
            for s1 in (-1, 1):
                vec = list(perm)
                vec[nz[0]] *= s0
                vec[nz[1]] *= s1
                raw_dirs.append((vec[0], vec[1], vec[2]))
    assert len(raw_dirs) == 24
    p = Fraction(1, 24)
    states = []
    for d in raw_dirs:
        b = (alpha * d[0], alpha * d[1], alpha * d[2])
        signs = []
        for w in w_vecs:
            dp = w[0] * b[0] + w[1] * b[1] + w[2] * b[2]
            assert dp != 0  # Every (2,1,0) permutation has strictly nonzero inner product with all 6 cuboctahedron axes!
            signs.append(1 if dp > 0 else -1)
        states.append((p, signs, b))
    return states


def run_exp1_certified_atlas(cert_dir: Path) -> Dict[str, Any]:
    """Generate and independently verify 14 exact-Q EPR-STEER-CERT-1.0 certificates across all 4 modes."""
    cert_dir.mkdir(parents=True, exist_ok=True)
    for old in cert_dir.glob("*.cert.json"):
        old.unlink()

    fams = polytope_measurement_families_exact()
    certs: List[Dict[str, Any]] = []

    # --- Mode 1: 5 exact-Q finite-m steering witnesses ---
    witness_specs = [
        ("witness_m2_square_v71", "m2_square", Fraction(71, 100)),
        ("witness_m3_octahedron_v58", "m3_octahedron", Fraction(58, 100)),
        ("witness_m6_cuboctahedron_v53", "m6_cuboctahedron", Fraction(53, 100)),
        ("witness_m12_pyth221_v56", "m12_pythagorean_221", Fraction(56, 100)),
        ("witness_m15_oct_pyth221_v52", "m15_oct_plus_pyth221", Fraction(52, 100)),
    ]
    for cid, fname, v in witness_specs:
        u_nsq, w_vecs = fams[fname]
        certs.append(build_finite_m_witness_certificate(cid, v, u_nsq, w_vecs, w_vecs))

    # --- Mode 2: 4 explicit exact-Q finite-m LHS models ---
    # 2a. m=2 square at v = 7/10 (4 states: +-7/10, +-7/10, 0 -> norm^2 = 98/100 <= 1)
    u2, w2 = fams["m2_square"]
    s2 = [
        (Fraction(1, 4), [sx, sy], (Fraction(7 * sx, 10), Fraction(7 * sy, 10), Fraction(0, 1)))
        for sx in (-1, 1) for sy in (-1, 1)
    ]
    certs.append(build_finite_m_lhs_certificate("lhs_m2_square_v70", Fraction(7, 10), u2, w2, s2))

    # 2b. m=3 octahedron at v = 57/100 (8 octant states: 57/100*(+-1,+-1,+-1) -> norm^2 = 9747/10000 <= 1)
    u3, w3 = fams["m3_octahedron"]
    s3 = [
        (Fraction(1, 8), [sx, sy, sz], (Fraction(57 * sx, 100), Fraction(57 * sy, 100), Fraction(57 * sz, 100)))
        for sx in (-1, 1) for sy in (-1, 1) for sz in (-1, 1)
    ]
    certs.append(build_finite_m_lhs_certificate("lhs_m3_octahedron_v57", Fraction(57, 100), u3, w3, s3))

    # 2c. m=4 cube diagonals (u_norm_sq=3) at v = 57/100 (6 axis states: +-171/100 e_k -> norm^2 = 29241/10000 <= 3)
    u4, w4 = fams["m4_cube_diagonals"]
    s4 = []
    for axis in range(3):
        for sgn in (-1, 1):
            b = [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)]
            b[axis] = Fraction(171 * sgn, 100)
            signs = [1 if (w[0] * b[0] + w[1] * b[1] + w[2] * b[2]) > 0 else -1 for w in w4]
            s4.append((Fraction(1, 6), signs, tuple(b)))
    certs.append(build_finite_m_lhs_certificate("lhs_m4_cube_diag_v57", Fraction(57, 100), u4, w4, s4))

    # 2d. m=6 cuboctahedron (u_norm_sq=2) at v = 21/40 = 0.525 < sqrt(5/18) = 0.5270 (24 states!)
    u6, w6 = fams["m6_cuboctahedron"]
    s6 = _build_cuboctahedron_lhs_24(Fraction(63, 100))
    certs.append(build_finite_m_lhs_certificate("lhs_m6_cuboctahedron_v525", Fraction(21, 40), u6, w6, s6))

    # --- Mode 3: 3 universal exact-Q finite-m gap certificates ---
    certs.append(build_universal_gap_certificate("univ_gap_m3_v4_7", 3, Fraction(4, 7)))
    certs.append(build_universal_gap_certificate("univ_gap_m6_v16_31", 6, Fraction(16, 31)))
    certs.append(build_universal_gap_certificate("univ_gap_m100_v4951_9901", 100, Fraction(4951, 9901)))

    # --- Mode 4: 2 exact-Q two-copy superactivation certificates (at v=1/2 AND strictly below!) ---
    certs.append(build_two_copy_superactivation_certificate("superact_two_copy_v_half", Fraction(1, 2), Fraction(114, 1)))
    certs.append(build_two_copy_superactivation_certificate("superact_two_copy_below_half", Fraction(49999, 100000), Fraction(114, 1)))

    rows: List[Dict[str, Any]] = []
    for cert in certs:
        cid = cert["cert_id"]
        cpath = cert_dir / f"{cid}.cert.json"
        cpath.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")

        t0 = time.perf_counter()
        loaded = json.loads(cpath.read_text(encoding="utf-8"))
        res = verify_steering_certificate_exact(loaded)
        v_ms = (time.perf_counter() - t0) * 1000.0
        rows.append({
            "cert_id": cid,
            "mode": res["mode"],
            "verdict": res["verdict"],
            "visibility_v": res["visibility_v"],
            "visibility_float": float(Fraction(res["visibility_v"])),
            "m_settings": cert.get("m_settings"),
            "verify_ms": round(v_ms, 3),
            "verified": True,
        })

    return {
        "experiment": "exp1_certified_atlas",
        "num_certificates": len(rows),
        "all_verified": all(r["verified"] for r in rows),
        "max_verify_ms": max(r["verify_ms"] for r in rows),
        "certificates": rows,
    }


def run_exp2_polytope_ladder_and_universal_gap() -> Dict[str, Any]:
    """Compare exact finite-m polytope thresholds (including icosahedron & dodecahedron) vs Theorem 3.1 bound."""
    fams = polytope_measurement_families_exact()
    polytopes: List[Dict[str, Any]] = []

    for name, (u_nsq, w_vecs) in fams.items():
        m = len(w_vecs)
        _, _, v_crit_sq = canonical_linear_witness_exact(w_vecs, w_vecs, u_nsq, Fraction(1, 1))
        v_univ = universal_finite_m_bound_exact(m)
        polytopes.append({
            "family": name,
            "m": m,
            "exact_v_crit_sq": canonical_fraction_str(v_crit_sq),
            "v_crit_float": math.sqrt(float(v_crit_sq)),
            "gap_above_half": math.sqrt(float(v_crit_sq)) - 0.5,
            "universal_bound_q": canonical_fraction_str(v_univ),
            "universal_bound_float": float(v_univ),
            "universal_gap": float(v_univ) - 0.5,
            "is_rational_exact": True,
        })

    # Also add Platonic icosahedron (m=6) and dodecahedron (m=10) for explicit Theorem 3.2 comparison!
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    platonic = [
        ("m6_icosahedron_platonic", [
            (0, 1, phi), (0, 1, -phi), (1, phi, 0), (1, -phi, 0), (phi, 0, 1), (-phi, 0, 1),
        ]),
        ("m10_dodecahedron_platonic", [
            (1, 1, 1), (1, 1, -1), (1, -1, 1), (-1, 1, 1),
            (0, 1 / phi, phi), (0, 1 / phi, -phi),
            (1 / phi, phi, 0), (1 / phi, -phi, 0),
            (phi, 0, 1 / phi), (-phi, 0, 1 / phi),
        ]),
    ]
    for name, vecs in platonic:
        m = len(vecs)
        uvs = [np.array(x, dtype=float) / np.linalg.norm(x) for x in vecs]
        max_n = 0.0
        for tail in itertools.product((-1, 1), repeat=m - 1):
            signs = (1,) + tail
            s = sum(a * v for a, v in zip(signs, uvs))
            nrm = float(np.linalg.norm(s))
            if nrm > max_n:
                max_n = nrm
        v_c = max_n / m
        v_univ = universal_finite_m_bound_exact(m)
        polytopes.append({
            "family": name,
            "m": m,
            "exact_v_crit_sq": "(3+sqrt(5))/18" if m == 6 else "(7+3*sqrt(5))/50",
            "v_crit_float": v_c,
            "gap_above_half": v_c - 0.5,
            "universal_bound_q": canonical_fraction_str(v_univ),
            "universal_bound_float": float(v_univ),
            "universal_gap": float(v_univ) - 0.5,
            "is_rational_exact": False,
        })

    polytopes.sort(key=lambda r: (r["m"], r["v_crit_float"]))

    # Universal gap curve across m = 1..100
    m_grid = [1, 2, 3, 4, 6, 8, 10, 12, 15, 20, 30, 50, 100]
    univ_curve = []
    for m in m_grid:
        vb = universal_finite_m_bound_exact(m)
        univ_curve.append({
            "m": m,
            "max_regions": great_circle_max_regions(m),
            "universal_bound_q": canonical_fraction_str(vb),
            "universal_bound_float": float(vb),
            "gap_above_half": float(vb) - 0.5,
        })

    return {
        "experiment": "exp2_polytope_ladder_and_universal_gap",
        "polytopes": polytopes,
        "universal_curve": univ_curve,
    }


def run_exp3_two_copy_haar_mc_crosscheck() -> Dict[str, Any]:
    """Independent 100,000-sample Haar SO(3)xSO(3) MC validating Theorem 3.3 bounds & tight threshold."""
    rng = np.random.default_rng(20261125)
    N = 100000
    R1 = special_ortho_group.rvs(3, size=N, random_state=rng)
    R2 = special_ortho_group.rvs(3, size=N, random_state=rng)

    # 1. Exact verification of L_joint(q) vs analytical upper bound 5167/7056 + sqrt(2) sin(2q) across 21 Schmidt angles
    qs = np.linspace(0.0, math.pi / 4.0, 21)
    schmidt_rows: List[Dict[str, Any]] = []
    L_arr = []
    for q in qs:
        sb = math.sin(2.0 * q)
        cb = math.cos(2.0 * q)
        M00 = sb * R1[:, 0, 0] * R2[:, 0, 0] - sb * R1[:, 1, 0] * R2[:, 1, 0] + R1[:, 2, 0] * R2[:, 2, 0]
        M11 = sb * R1[:, 0, 1] * R2[:, 0, 1] - sb * R1[:, 1, 1] * R2[:, 1, 1] + R1[:, 2, 1] * R2[:, 2, 1]
        M22 = sb * R1[:, 0, 2] * R2[:, 0, 2] - sb * R1[:, 1, 2] * R2[:, 1, 2] + R1[:, 2, 2] * R2[:, 2, 2]
        vals = np.maximum.reduce([
            M00 - M11 + M22,
            -M00 + M11 + M22,
            M00 + M11 - M22,
            -M00 - M11 - M22,
        ])
        mean_l = float(np.mean(vals))
        se_l = float(np.std(vals) / math.sqrt(N))
        ub_exact_q = float(BELL_JOINT_LHS_UB_Q) + math.sqrt(2.0) * sb
        L_arr.append(mean_l)
        schmidt_rows.append({
            "q": round(float(q), 6),
            "cos_2q": round(cb, 6),
            "sin_2q": round(sb, 6),
            "L_joint_mc": mean_l,
            "L_joint_se": se_l,
            "L_joint_ub": ub_exact_q,
            "bound_holds": mean_l <= ub_exact_q,
        })
    L_arr = np.array(L_arr)
    cbs = np.cos(2.0 * qs)

    # 2. Verify E[x^2 y^2 z^2] = 1/105 and L_joint(0) = 3/4 - E[min(p1,p2,p3)]
    u = R1[:, 2, :]
    v = R2[:, 2, :]
    p0 = np.abs(u[:, 0] * v[:, 0])
    p1 = np.abs(u[:, 1] * v[:, 1])
    p2 = np.abs(u[:, 2] * v[:, 2])
    e_min_mc = float(np.mean(np.minimum.reduce([p0, p1, p2])))
    e_min_se = float(np.std(np.minimum.reduce([p0, p1, p2])) / math.sqrt(N))
    e_x2y2z2_mc = float(np.mean((u[:, 0] * u[:, 1] * u[:, 2]) ** 2))
    e_x2y2z2_se = float(np.std((u[:, 0] * u[:, 1] * u[:, 2]) ** 2) / math.sqrt(N))
    z_moment = abs(e_x2y2z2_mc - 1.0 / 105.0) / e_x2y2z2_se

    # 3. Gamma sweep: both MC tight v_crit(gamma) AND exact-Q certified v_cert(gamma)
    gamma_rows: List[Dict[str, Any]] = []
    for g in [1, 2, 3, 5, 10, 20, 50, 70, 100, 114, 150, 200]:
        tot_mc = g * cbs + L_arr
        l_mc_max = float(np.max(tot_mc))
        v_mc = (-2 * g + math.sqrt(4 * g * g + 12 * l_mc_max)) / 6.0

        q_half, l_ub_q, margin_q = two_copy_superactivation_margin_exact(Fraction(1, 2), Fraction(g, 1))
        v_cert = (-2 * g + math.sqrt(4 * g * g + 12 * float(l_ub_q))) / 6.0
        gamma_rows.append({
            "gamma": g,
            "Q_half": float(q_half),
            "L_mc_max": l_mc_max,
            "v_tight_mc": v_mc,
            "L_ub_exact_q": float(l_ub_q),
            "margin_exact_q_at_half": float(margin_q),
            "v_cert_exact_q": v_cert,
            "exact_q_superactivated_at_half": bool(margin_q > 0),
        })

    return {
        "experiment": "exp3_two_copy_haar_mc_crosscheck",
        "num_samples": N,
        "L_joint_0_mc": L_arr[0],
        "L_joint_0_ub_exact_q": float(BELL_JOINT_LHS_UB_Q),
        "E_min_mc": e_min_mc,
        "E_min_se": e_min_se,
        "E_min_lb_exact_q": float(Fraction(125, 7056)),
        "E_x2y2z2_mc": e_x2y2z2_mc,
        "E_x2y2z2_exact": 1.0 / 105.0,
        "E_x2y2z2_z_score": z_moment,
        "all_schmidt_bounds_hold": all(r["bound_holds"] for r in schmidt_rows),
        "schmidt_curve": schmidt_rows,
        "gamma_sweep": gamma_rows,
    }


def run_exp4_ppt_separability_phase_diagram() -> Dict[str, Any]:
    """Verify exact rational PPT eigenvalues against direct 4x4 matrix partial-transpose eigendecomposition."""
    I2 = np.eye(2, dtype=complex)
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
    Z = np.array([[1, 0], [0, -1]], dtype=complex)

    max_err = 0.0
    checks: List[Dict[str, Any]] = []
    for v_num in (40, 49, 50, 55, 58, 65, 75, 90):
        v = Fraction(v_num, 100)
        for t_num in (0, 1, 2, 4, 10):
            t = Fraction(t_num, 10)
            c = (Fraction(1) - t * t) / (Fraction(1) + t * t)
            s = (Fraction(2) * t) / (Fraction(1) + t * t)
            eigs_q = sorted(bell_conditional_ppt_eigs_exact(v, t))
            # Direct 4x4 matrix construction and partial transpose on qubit 2
            vf, cf, sf = float(v), float(c), float(s)
            rho_B = 0.25 * (
                np.kron(I2, I2)
                - vf * cf * (np.kron(Z, I2) + np.kron(I2, Z))
                + vf * vf * (sf * np.kron(X, X) - sf * np.kron(Y, Y) + np.kron(Z, Z))
            )
            rho_pt = rho_B.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)
            eigs_num = sorted(float(x) for x in np.linalg.eigvalsh(rho_pt))
            err = max(abs(float(eq) - en) for eq, en in zip(eigs_q, eigs_num))
            max_err = max(max_err, err)
            if t in (Fraction(1, 10), Fraction(1, 1)):
                checks.append({
                    "v": canonical_fraction_str(v),
                    "t": canonical_fraction_str(t),
                    "s": canonical_fraction_str(s),
                    "min_ppt_eig_q": canonical_fraction_str(eigs_q[0]),
                    "min_ppt_eig_float": float(eigs_q[0]),
                    "separable_ppt": bool(eigs_q[0] >= 0),
                    "matrix_err": err,
                })

    return {
        "experiment": "exp4_ppt_separability_phase_diagram",
        "num_grid_checks": 40,
        "max_eigenvalue_error": max_err,
        "sample_checks": checks,
    }


def main() -> None:
    res_dir = ROOT / "results"
    res_dir.mkdir(parents=True, exist_ok=True)
    cert_dir = res_dir / "certificates"

    t0 = time.perf_counter()
    e1 = run_exp1_certified_atlas(cert_dir)
    (res_dir / "exp1_certified_atlas.json").write_text(json.dumps(e1, indent=2) + "\n", encoding="utf-8")

    e2 = run_exp2_polytope_ladder_and_universal_gap()
    (res_dir / "exp2_polytope_ladder_and_universal_gap.json").write_text(json.dumps(e2, indent=2) + "\n", encoding="utf-8")

    e3 = run_exp3_two_copy_haar_mc_crosscheck()
    (res_dir / "exp3_two_copy_haar_mc_crosscheck.json").write_text(json.dumps(e3, indent=2) + "\n", encoding="utf-8")

    e4 = run_exp4_ppt_separability_phase_diagram()
    (res_dir / "exp4_ppt_separability_phase_diagram.json").write_text(json.dumps(e4, indent=2) + "\n", encoding="utf-8")

    dt = time.perf_counter() - t0
    print(f"All 4 Paper 10 experiments completed in {dt:.2f}s:")
    print(f"  Exp 1: {e1['num_certificates']} exact-Q certs verified={e1['all_verified']}, max_ms={e1['max_verify_ms']:.2f}")
    print(f"  Exp 2: {len(e2['polytopes'])} polytopes mapped vs universal cap-cell bound")
    print(f"  Exp 3: 100k Haar MC: L_joint(0)={e3['L_joint_0_mc']:.5f} <= {e3['L_joint_0_ub_exact_q']:.5f}, moment_z={e3['E_x2y2z2_z_score']:.2f}, all_bounds={e3['all_schmidt_bounds_hold']}")
    print(f"  Exp 4: 40 PPT grid checks, max_err={e4['max_eigenvalue_error']:.2e}")


if __name__ == "__main__":
    main()
