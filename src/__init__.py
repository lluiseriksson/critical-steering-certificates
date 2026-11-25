"""Exact-Q finite-setting steering gap laws, polytope certificates, and two-copy superactivation.

Author: Lluis Eriksson
"""

from .steering_exact import (
    BELL_JOINT_LHS_UB_Q,
    bell_conditional_ppt_eigs_exact,
    canonical_linear_witness_exact,
    great_circle_max_regions,
    polytope_measurement_families_exact,
    two_copy_superactivation_margin_exact,
    universal_finite_m_bound_exact,
)
from .steering_certifier import (
    SCHEMA_VERSION,
    build_finite_m_lhs_certificate,
    build_finite_m_witness_certificate,
    build_two_copy_superactivation_certificate,
    build_universal_gap_certificate,
    canonical_fraction_str,
    parse_canonical_fraction,
    verify_steering_certificate_exact,
)

__all__ = [
    "BELL_JOINT_LHS_UB_Q",
    "SCHEMA_VERSION",
    "bell_conditional_ppt_eigs_exact",
    "build_finite_m_lhs_certificate",
    "build_finite_m_witness_certificate",
    "build_two_copy_superactivation_certificate",
    "build_universal_gap_certificate",
    "canonical_fraction_str",
    "canonical_linear_witness_exact",
    "great_circle_max_regions",
    "parse_canonical_fraction",
    "polytope_measurement_families_exact",
    "two_copy_superactivation_margin_exact",
    "universal_finite_m_bound_exact",
    "verify_steering_certificate_exact",
]
