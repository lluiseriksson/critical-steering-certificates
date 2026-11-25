"""Pure-stdlib exact-Q mathematical engine for Paper 10:
  - Universal finite-m great-circle steering gap bound (Theorem 3.1)
  - Exact rational polytope measurement families & linear witness solver (Theorem 3.2)
  - Exact two-copy superactivation witness & conditional-state PPT spectrum (Theorem 3.3)

ZERO third-party imports, ZERO floating-point arithmetic.
Author: Lluis Eriksson
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

# Exact rational upper bound on L_joint(q=0) = 3/4 - E[min(|x1x2|,|y1y2|,|z1z2|)]:
#   E[min] >= (3125/16) * (1/105)^2 = 125/7056  ==>  L_joint(0) <= 3/4 - 125/7056 = 5167/7056
BELL_JOINT_LHS_UB_Q = Fraction(5167, 7056)


def great_circle_max_regions(m: int) -> int:
    """Maximum number of open regions on S^2 carved by m great circles: R(m) = m(m-1) + 2."""
    if type(m) is not int or m < 1:
        raise ValueError(f"m must be int >= 1, got {m!r}")
    return m * (m - 1) + 2


def universal_finite_m_bound_exact(m: int) -> Fraction:
    """Theorem 3.1 universal exact-Q unsteerability bound:
        v_m^* >= R(m) / (2 * (R(m) - 1)) = 1/2 + 1 / (2 * (m^2 - m + 1)).
    """
    r = great_circle_max_regions(m)
    return Fraction(r, 2 * (r - 1))


def dot3(a: Sequence[Fraction], b: Sequence[Fraction]) -> Fraction:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def norm_sq3(a: Sequence[Fraction]) -> Fraction:
    return a[0] * a[0] + a[1] * a[1] + a[2] * a[2]


def canonical_linear_witness_exact(
    w_vectors: Sequence[Sequence[Fraction]],
    f_vectors: Sequence[Sequence[Fraction]],
    u_norm_sq: Fraction,
    v: Fraction,
) -> Tuple[Fraction, Fraction, Fraction]:
    """Compute exact rational (S_Q^2, L_LHS^2, v_crit^2) for a linear steering witness.

    Alice measures u_x = w_x / sqrt(u_norm_sq) with ||w_x||_2^2 = u_norm_sq > 0.
    Quantum score: S_Q(v) = v * sum_x (w_x . f_x) / sqrt(u_norm_sq), so
      S_Q^2 = (v^2 / u_norm_sq) * (sum_x w_x . f_x)^2.
    LHS bound squared: L_LHS^2 = max_{a in {+-1}^m} ||sum_x a_x f_x||_2^2.
    Critical threshold squared: v_crit^2 = u_norm_sq * L_LHS^2 / (sum_x w_x . f_x)^2.
    """
    m = len(w_vectors)
    if m < 1 or m != len(f_vectors):
        raise ValueError("w_vectors and f_vectors must be non-empty and equal length")
    if u_norm_sq <= 0:
        raise ValueError("u_norm_sq must be strictly positive")
    if v <= 0 or v > 1:
        raise ValueError("visibility v must lie in (0, 1]")
    for idx, w in enumerate(w_vectors):
        if len(w) != 3 or norm_sq3(w) != u_norm_sq:
            raise ValueError(f"w_vectors[{idx}] does not satisfy ||w||^2 == {u_norm_sq}")
    for idx, f in enumerate(f_vectors):
        if len(f) != 3:
            raise ValueError(f"f_vectors[{idx}] must have length 3")

    inner_sum = sum((dot3(w, f) for w, f in zip(w_vectors, f_vectors)), Fraction(0, 1))
    if inner_sum <= 0:
        raise ValueError(f"Witness alignment sum(w_x . f_x) must be > 0, got {inner_sum}")

    # Exhaustive exact search over all 2^{m-1} sign patterns (a_0 = +1 by symmetry)
    max_lhs_sq = Fraction(0, 1)
    for tail in itertools.product((-1, 1), repeat=m - 1):
        signs = (1,) + tail
        sx = sum((f[0] if s == 1 else -f[0] for s, f in zip(signs, f_vectors)), Fraction(0, 1))
        sy = sum((f[1] if s == 1 else -f[1] for s, f in zip(signs, f_vectors)), Fraction(0, 1))
        sz = sum((f[2] if s == 1 else -f[2] for s, f in zip(signs, f_vectors)), Fraction(0, 1))
        n2 = sx * sx + sy * sy + sz * sz
        if n2 > max_lhs_sq:
            max_lhs_sq = n2

    s_q_sq = (v * v * inner_sum * inner_sum) / u_norm_sq
    v_crit_sq = (u_norm_sq * max_lhs_sq) / (inner_sum * inner_sum)
    return s_q_sq, max_lhs_sq, v_crit_sq


def polytope_measurement_families_exact() -> Dict[str, Tuple[Fraction, List[Tuple[Fraction, Fraction, Fraction]]]]:
    """Canonical exact-Q measurement polytopes on S^2 (scaled so ||w_x||^2 = u_norm_sq in Q)."""
    F = Fraction
    return {
        "m2_square": (
            F(1),
            [(F(1), F(0), F(0)), (F(0), F(1), F(0))],
        ),
        "m3_octahedron": (
            F(1),
            [(F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1))],
        ),
        "m4_cube_diagonals": (
            F(3),
            [(F(1), F(1), F(1)), (F(1), F(1), F(-1)), (F(1), F(-1), F(1)), (F(-1), F(1), F(1))],
        ),
        "m6_cuboctahedron": (
            F(2),
            [
                (F(1), F(1), F(0)), (F(1), F(-1), F(0)),
                (F(1), F(0), F(1)), (F(1), F(0), F(-1)),
                (F(0), F(1), F(1)), (F(0), F(1), F(-1)),
            ],
        ),
        # Pure rational unit vectors on S^2 (norm_sq = 1, Pythagorean triple (2,2,1)/3 and axes (1,0,0)): m = 15!
        "m7_oct_plus_cube_pyth": (
            F(9),
            [
                (F(3), F(0), F(0)), (F(0), F(3), F(0)), (F(0), F(0), F(3)),
                (F(2), F(2), F(1)), (F(2), F(-2), F(1)), (F(-2), F(2), F(1)), (F(-2), F(-2), F(1)),
            ],
        ),
        "m12_pythagorean_221": (
            F(9),
            [
                (F(2), F(2), F(1)), (F(2), F(2), F(-1)), (F(2), F(-2), F(1)), (F(-2), F(2), F(1)),
                (F(2), F(1), F(2)), (F(2), F(-1), F(2)), (F(2), F(1), F(-2)), (F(-2), F(1), F(2)),
                (F(1), F(2), F(2)), (F(-1), F(2), F(2)), (F(1), F(-2), F(2)), (F(1), F(2), F(-2)),
            ],
        ),
        "m15_oct_plus_pyth221": (
            F(9),
            [
                (F(3), F(0), F(0)), (F(0), F(3), F(0)), (F(0), F(0), F(3)),
                (F(2), F(2), F(1)), (F(2), F(2), F(-1)), (F(2), F(-2), F(1)), (F(-2), F(2), F(1)),
                (F(2), F(1), F(2)), (F(2), F(-1), F(2)), (F(2), F(1), F(-2)), (F(-2), F(1), F(2)),
                (F(1), F(2), F(2)), (F(-1), F(2), F(2)), (F(1), F(-2), F(2)), (F(1), F(2), F(-2)),
            ],
        ),
    }


def bell_conditional_ppt_eigs_exact(v: Fraction, t: Fraction) -> Tuple[Fraction, Fraction, Fraction, Fraction]:
    """Exact rational eigenvalues of Bob's partial-transposed conditional state rho_B^{T_2}(v, t)
    under partially entangled Bell measurement |psi_j(t)> = (|00> + t|11>)/sqrt(1+t^2):
      c = (1 - t^2) / (1 + t^2),   s = 2t / (1 + t^2),
      lam_1 = (1 - 2vc + v^2)/4,   lam_2 = (1 + 2vc + v^2)/4,
      lam_3 = (1 - v^2 + 2 v^2 s)/4, lam_4 = (1 - v^2 - 2 v^2 s)/4.
    """
    if v < 0 or v > 1:
        raise ValueError("v must be in [0, 1]")
    if t < 0 or t > 1:
        raise ValueError("t must be in [0, 1]")
    c = (Fraction(1) - t * t) / (Fraction(1) + t * t)
    s = (Fraction(2) * t) / (Fraction(1) + t * t)
    l1 = (Fraction(1) - 2 * v * c + v * v) / 4
    l2 = (Fraction(1) + 2 * v * c + v * v) / 4
    l3 = (Fraction(1) - v * v + 2 * v * v * s) / 4
    l4 = (Fraction(1) - v * v - 2 * v * v * s) / 4
    return (l1, l2, l3, l4)


def two_copy_superactivation_margin_exact(v: Fraction, gamma: Fraction) -> Tuple[Fraction, Fraction, Fraction]:
    """Theorem 3.3 exact-Q two-copy superactivation certificate computation:
      Q_gamma(v) = 2 * gamma * v + 3 * v^2,
      L_gamma_ub = 5167/7056 + gamma + 1/gamma,
      margin     = Q_gamma(v) - L_gamma_ub.
    """
    if v <= 0 or v > 1:
        raise ValueError("v must lie in (0, 1]")
    if gamma <= 0:
        raise ValueError("gamma must be strictly positive")
    q_val = 2 * gamma * v + 3 * v * v
    l_ub = BELL_JOINT_LHS_UB_Q + gamma + Fraction(1, 1) / gamma
    return q_val, l_ub, q_val - l_ub
