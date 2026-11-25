"""End-to-end Gate-2 verification script for Paper 10.

Checks:
  1. Lean 4 (`lake build` + `AuditAxioms.lean`): 18/18 theorems, 0 warnings, 0 sorry, 0 Classical.choice.
  2. All 14 exact-Q EPR-STEER-CERT-1.0 certificates independently verified (0 floats).
  3. Full pytest suite (including 46/46 live adversarial red-team attacks).
  4. SHA256SUMS.json manifest integrity (or writes manifest with `--write-manifest`).

Author: Lluis Eriksson
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src import verify_steering_certificate_exact

EXPECTED_LEAN_THEOREMS = [
    "CriticalSteering.great_circle_regions_closed_form",
    "CriticalSteering.cap_centroid_area_identity",
    "CriticalSteering.discrete_cauchy_schwarz_nonneg",
    "CriticalSteering.universal_finite_m_gap_bound",
    "CriticalSteering.finite_m_gap_strictly_above_half",
    "CriticalSteering.finite_m_gap_monotone",
    "CriticalSteering.finite_m_single_setting_exact_one",
    "CriticalSteering.cuboctahedron_beats_icosahedron",
    "CriticalSteering.bell_sign_parity_odd_neg",
    "CriticalSteering.bell_sign_parity_even_neg",
    "CriticalSteering.sos_poly_256_minus_3125_identity",
    "CriticalSteering.sos_cubic_factor_strictly_pos",
    "CriticalSteering.sos_min_lower_bound_cleared",
    "CriticalSteering.zero_sum_four_cauchy_schwarz",
    "CriticalSteering.bell_four_squares_identity",
    "CriticalSteering.rigidity_envelope_rational_upper",
    "CriticalSteering.two_copy_superactivation_at_and_below_half",
    "CriticalSteering.ppt_conditional_separability_and_witness_duality",
]

MANIFEST_PATHS = [
    "LICENSE",
    "README.md",
    "pyproject.toml",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/CriticalSteering.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/steering_exact.py",
    "src/steering_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "results/exp1_certified_atlas.json",
    "results/exp2_polytope_ladder_and_universal_gap.json",
    "results/exp3_two_copy_haar_mc_crosscheck.json",
    "results/exp4_ppt_separability_phase_diagram.json",
    "paper/references.bib",
    "paper/main.tex",
    "paper/figures/fig1_finite_m_gap_and_polytopes.png",
    "paper/figures/fig2_two_copy_superactivation.png",
    "paper/figures/fig3_ppt_separability_pocket.png",
]


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def check_lean() -> None:
    lean_dir = ROOT / "lean"
    p1 = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True)
    if p1.returncode != 0:
        raise RuntimeError(f"lake build failed:\n{p1.stdout}\n{p1.stderr}")
    if "warning:" in (p1.stdout + p1.stderr).lower():
        raise RuntimeError(f"Lean 4 build emitted warnings:\n{p1.stdout}\n{p1.stderr}")

    p2 = subprocess.run(["lake", "env", "lean", "AuditAxioms.lean"], cwd=lean_dir, capture_output=True, text=True)
    if p2.returncode != 0:
        raise RuntimeError(f"AuditAxioms.lean failed:\n{p2.stdout}\n{p2.stderr}")
    out = p2.stdout + p2.stderr
    for bad in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if bad in out:
            raise RuntimeError(f"Forbidden Lean axiom detected: {bad}\n{out}")
    for thm in EXPECTED_LEAN_THEOREMS:
        if thm not in out:
            raise RuntimeError(f"Missing Lean theorem in axiom audit: {thm}")
    print(f"[PASS] Lean 4 kernel: {len(EXPECTED_LEAN_THEOREMS)}/18 theorems, 0 warnings, 0 sorry, 0 Classical.choice")


def check_certs() -> None:
    cert_dir = ROOT / "results" / "certificates"
    paths = sorted(cert_dir.glob("*.cert.json"))
    if len(paths) != 14:
        raise RuntimeError(f"Expected 14 exact-Q certificates, found {len(paths)}")
    for cp in paths:
        data = json.loads(cp.read_text(encoding="utf-8"))
        res = verify_steering_certificate_exact(data)
        if not res["verified"]:
            raise RuntimeError(f"Certificate failed: {cp}")
    print(f"[PASS] Exact-Q certificates: {len(paths)}/14 independently verified (0 floats)")


def check_pytest() -> None:
    p = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"pytest failed:\n{p.stdout}\n{p.stderr}")
    print(f"[PASS] pytest: {p.stdout.strip().splitlines()[-1]}")


def collect_manifest_files() -> list[str]:
    files = list(MANIFEST_PATHS)
    cert_dir = ROOT / "results" / "certificates"
    for cp in sorted(cert_dir.glob("*.cert.json")):
        files.append(f"results/certificates/{cp.name}")
    return sorted(files)


def write_manifest() -> None:
    manifest = {}
    for rel in collect_manifest_files():
        fp = ROOT / rel
        if not fp.exists():
            raise FileNotFoundError(f"Missing manifest file: {rel}")
        manifest[rel] = sha256_file(fp)
    (ROOT / "SHA256SUMS.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"[PASS] Wrote SHA256SUMS.json ({len(manifest)} files)")


def check_manifest() -> None:
    mpath = ROOT / "SHA256SUMS.json"
    if not mpath.exists():
        raise FileNotFoundError("SHA256SUMS.json missing; run with --write-manifest first")
    manifest = json.loads(mpath.read_text(encoding="utf-8"))
    for rel, expected in manifest.items():
        fp = ROOT / rel
        if not fp.exists():
            raise RuntimeError(f"Manifest file missing: {rel}")
        actual = sha256_file(fp)
        if actual != expected:
            raise RuntimeError(f"SHA256 mismatch for {rel}: {actual} != {expected}")
    print(f"[PASS] SHA256SUMS.json: {len(manifest)}/{len(manifest)} hashes match")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    ap.add_argument("--skip-manifest", action="store_true")
    args = ap.parse_args()

    check_lean()
    check_certs()
    check_pytest()
    if args.write_manifest:
        write_manifest()
    elif not args.skip_manifest:
        check_manifest()
    print("=== ALL PAPER 10 GATE-2 VERIFICATION CHECKS PASSED ===")


if __name__ == "__main__":
    main()
