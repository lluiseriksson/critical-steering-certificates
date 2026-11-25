"""Generate 3 publication-quality figures for Paper 10 from exact JSON outputs.

Author: Lluis Eriksson
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"


def style_axes(ax: plt.Axes) -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.grid(True, linestyle="--", alpha=0.35, linewidth=0.7)


def make_fig1(exp2: dict) -> None:
    """Fig 1: Universal finite-m gap bound vs exact polytopes + cuboctahedron supremacy."""
    fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.5))

    # Panel (a): Visibility threshold v vs m (m = 2..15)
    ax = axes[0]
    style_axes(ax)
    ms_dense = np.arange(2, 16)
    v_univ_dense = 0.5 + 1.0 / (2.0 * (ms_dense * (ms_dense - 1) + 1))
    ax.plot(ms_dense, v_univ_dense, "o-", color="#1b7837", lw=2.1, ms=5.0,
            label=r"Universal cap-cell bound $\frac{1}{2}+\frac{1}{2(m^2-m+1)}$ (Thm 3.1)")
    ax.fill_between(ms_dense, 0.5, v_univ_dense, color="#1b7837", alpha=0.14,
                    label=r"Provably $m$-setting unsteerable gap")

    rat_polys = [p for p in exp2["polytopes"] if p["is_rational_exact"]]
    pla_polys = [p for p in exp2["polytopes"] if not p["is_rational_exact"]]
    ax.scatter([p["m"] for p in rat_polys], [p["v_crit_float"] for p in rat_polys],
               s=62, marker="s", color="#2166ac", edgecolor="#111111", zorder=5,
               label=r"Exact-$\mathbb{Q}$ polytope witnesses ($m=2,3,4,6,7,12,15$)")
    ax.scatter([p["m"] for p in pla_polys], [p["v_crit_float"] for p in pla_polys],
               s=76, marker="D", color="#d95f02", edgecolor="#111111", zorder=5,
               label=r"Platonic icosahedron ($m=6$) & dodecahedron ($m=10$)")
    ax.axhline(0.5, color="#b2182b", linestyle="--", lw=1.6, label=r"PVM-critical boundary $v_c = 1/2$")

    ax.annotate("Cuboctahedron (0.5270)\nbeats Icosahedron (0.5393)",
                xy=(6.0, 0.5270), xytext=(7.2, 0.61),
                fontsize=7.8, color="#2166ac", fontweight="bold",
                arrowprops=dict(arrowstyle="->", color="#2166ac", lw=1.0))

    ax.set_xlabel(r"Number of projective measurement settings $m$", fontsize=9.8)
    ax.set_ylabel(r"Werner visibility $v$", fontsize=9.8)
    ax.set_title(r"(a) Exact Finite-$m$ Steering Polytopes vs. Universal Gap", fontsize=10.1, fontweight="bold")
    ax.set_xlim(1.5, 15.8)
    ax.set_ylim(0.485, 0.74)
    ax.legend(loc="upper right", fontsize=7.2, frameon=True, framealpha=0.95)

    # Panel (b): Log-log gap above v_c = 1/2 across m = 2..100
    ax = axes[1]
    style_axes(ax)
    uc = [r for r in exp2["universal_curve"] if r["m"] >= 2]
    ax.loglog([r["m"] for r in uc], [r["gap_above_half"] for r in uc], "o-", color="#1b7837", lw=2.1, ms=5.0,
              label=r"Universal lower bound $\Delta_{\mathrm{univ}}(m) = \frac{1}{2(m^2-m+1)} = \Omega(m^{-2})$")
    ax.loglog([p["m"] for p in rat_polys], [p["gap_above_half"] for p in rat_polys], "s",
              color="#2166ac", ms=6.5, markeredgecolor="#111111",
              label=r"Exact-$\mathbb{Q}$ polytope gap $v_m^* - 1/2$")
    ax.loglog([p["m"] for p in pla_polys], [p["gap_above_half"] for p in pla_polys], "D",
              color="#d95f02", ms=6.5, markeredgecolor="#111111",
              label=r"Platonic icosahedron / dodecahedron gap")
    ax.set_xlabel(r"Number of measurement settings $m$ (log scale)", fontsize=9.8)
    ax.set_ylabel(r"Gap above criticality $v_m^* - 1/2$", fontsize=9.8)
    ax.set_title(r"(b) Asymptotic $\Omega(m^{-2})$ Unsteerable Neighborhood Law", fontsize=10.1, fontweight="bold")
    ax.legend(loc="lower left", fontsize=7.6, frameon=True, framealpha=0.95)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_finite_m_gap_and_polytopes.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def make_fig2(exp3: dict) -> None:
    """Fig 2: Exact-Q SOS upper bound vs Haar MC across Schmidt angles + 2-copy superactivation."""
    fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.4))

    # Panel (a): L_joint(q) vs exact-Q SOS bound across Schmidt angle q
    ax = axes[0]
    style_axes(ax)
    sc = exp3["schmidt_curve"]
    qs = [r["q"] for r in sc]
    ax.plot(qs, [r["L_joint_ub"] for r in sc], "--", color="#b2182b", lw=2.1,
            label=r"Exact-$\mathbb{Q}$ SOS + subadditivity bound $\frac{5167}{7056} + \sqrt{2}\sin(2q)$")
    ax.plot(qs, [r["L_joint_mc"] for r in sc], "o-", color="#2166ac", lw=2.0, ms=4.5,
            label=r"Independent Haar MC ($N=100{,}000$) $L_{\mathrm{joint}}(q)$")
    ax.axhline(0.75, color="#1b7837", linestyle=":", lw=1.8,
               label=r"Quantum Bell score at $v=1/2$: $Q_{\mathrm{joint}}(1/2) = 3/4$")
    ax.annotate(r"Exact-$\mathbb{Q}$ gap at $q=0$:" + "\n" + r"$3/4 - 5167/7056 = 125/7056$",
                xy=(0.01, 0.7323), xytext=(0.14, 0.56),
                fontsize=7.8, color="#b2182b", fontweight="bold",
                arrowprops=dict(arrowstyle="->", color="#b2182b", lw=1.0))
    ax.set_xlabel(r"Hidden-state Schmidt angle $q \in [0, \pi/4]$", fontsize=9.8)
    ax.set_ylabel(r"Joint Bell-witness LHS score $L_{\mathrm{joint}}(q)$", fontsize=9.8)
    ax.set_title(r"(a) Exact-$\mathbb{Q}$ SOS Bound vs. Haar MC Across Hidden States", fontsize=10.0, fontweight="bold")
    ax.set_ylim(0.50, 2.28)
    ax.legend(loc="upper left", fontsize=7.3, frameon=True, framealpha=0.95)

    # Panel (b): Two-copy critical visibility v_crit(gamma) vs gamma (crossing below v = 1/2!)
    ax = axes[1]
    style_axes(ax)
    gs = [r for r in exp3["gamma_sweep"] if r["gamma"] >= 2]
    gv = [r["gamma"] for r in gs]
    ax.semilogx(gv, [r["v_cert_exact_q"] for r in gs], "s-", color="#b2182b", lw=2.0, ms=5.2,
                label=r"Exact-$\mathbb{Q}$ certified threshold $v_{\mathrm{cert}}^{(2)}(\gamma)$ (zero floats)")
    ax.semilogx(gv, [r["v_tight_mc"] for r in gs], "o-", color="#2166ac", lw=2.0, ms=5.2,
                label=r"Tight Haar-MC threshold $v_{\mathrm{tight}}^{(2)}(\gamma)$ (min $0.4933$ at $\gamma=3$)")
    ax.axhline(0.5, color="#1b7837", linestyle="--", lw=1.7,
               label=r"Single-copy PVM-critical boundary $v_c = 1/2$")
    ax.axhspan(0.492, 0.500, color="#1b7837", alpha=0.10, label=r"Two-copy superactivation region ($v < 1/2$)")
    ax.set_xlabel(r"Local-rigidity penalty weight $\gamma$ (log scale)", fontsize=9.8)
    ax.set_ylabel(r"Two-copy steering threshold $v^{(2)}(\gamma)$", fontsize=9.8)
    ax.set_title(r"(b) Two-Copy Superactivation Below PVM Criticality ($v < 1/2$)", fontsize=10.0, fontweight="bold")
    ax.set_ylim(0.4920, 0.5048)
    ax.legend(loc="upper right", fontsize=7.1, frameon=True, framealpha=0.95)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_two_copy_superactivation.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def make_fig3(exp1: dict, exp4: dict) -> None:
    """Fig 3: Conditional-state PPT separability phase diagram + exact-Q verifier runtimes."""
    fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.4))

    # Panel (a): PPT separability boundary v^2(1 + 2s) = 1 in (v, s) plane
    ax = axes[0]
    style_axes(ax)
    vs = np.linspace(0.30, 0.99, 400)
    s_swap = np.clip((1.0 - vs * vs) / (2.0 * vs * vs), 0.0, 1.0)
    ax.plot(vs, s_swap, color="#b2182b", lw=2.2, label=r"Exact PPT boundary $s_{\mathrm{swap}}(v) = \frac{1-v^2}{2v^2}$")
    ax.fill_between(vs, 0.0, s_swap, color="#1b7837", alpha=0.15,
                    label=r"All conditional states on $B_1 B_2$ separable ($\lambda_{\min}^{\mathrm{PT}} \geq 0$)")
    ax.fill_between(vs, s_swap, 1.0, color="#b2182b", alpha=0.10,
                    label=r"Entanglement-swapped conditional states ($\lambda_{\min}^{\mathrm{PT}} < 0$)")
    ax.axvline(0.5, color="#2166ac", linestyle="--", lw=1.8,
               label=r"PVM-critical $v=1/2$ ($\lambda_{\min}^{\mathrm{PT}} \geq 1/16 > 0\ \forall s \in [0,1]$)")
    ax.axvline(1.0 / math.sqrt(3.0), color="#d95f02", linestyle=":", lw=1.6,
               label=r"Full-Bell PPT threshold $v = 1/\sqrt{3} \approx 0.5774$")
    ax.scatter([0.5], [1.0], s=80, color="#2166ac", edgecolor="#111111", zorder=6)
    ax.set_xlabel(r"Werner visibility $v$", fontsize=9.8)
    ax.set_ylabel(r"Measurement entanglement $s = 2t/(1+t^2)$", fontsize=9.8)
    ax.set_title(r"(a) Conditional-State PPT Phase Diagram on $B_1 B_2$", fontsize=10.1, fontweight="bold")
    ax.set_xlim(0.32, 0.98)
    ax.set_ylim(-0.02, 1.04)
    ax.legend(loc="lower left", fontsize=7.0, frameon=True, framealpha=0.95)

    # Panel (b): Exact-Q verifier runtime across all 14 certificates
    ax = axes[1]
    style_axes(ax)
    certs = exp1["certificates"]
    mode_colors = {
        "finite_m_steering_witness": "#2166ac",
        "finite_m_lhs_model": "#1b7837",
        "universal_finite_m_gap": "#d95f02",
        "two_copy_superactivation": "#b2182b",
    }
    xs = np.arange(len(certs))
    ms = [c["verify_ms"] for c in certs]
    cols = [mode_colors[c["mode"]] for c in certs]
    ax.bar(xs, ms, color=cols, edgecolor="#111111", linewidth=0.7, width=0.66)
    ax.set_yscale("log")
    ax.set_ylim(0.1, 2000.0)
    ax.set_xticks(xs)
    ax.set_xticklabels([f"C{i+1}" for i in range(len(certs))], fontsize=8.0)
    ax.set_xlabel(r"Exact-$\mathbb{Q}$ certificate index (C1–C14 across all 4 modes)", fontsize=9.6)
    ax.set_ylabel(r"Pure-stdlib verification time (ms, log scale)", fontsize=9.8)
    ax.set_title(r"(b) Zero-Float EPR-STEER-CERT-1.0 Verifier Runtime", fontsize=10.0, fontweight="bold")
    # Custom legend for modes
    from matplotlib.patches import Patch
    handles = [
        Patch(facecolor="#2166ac", edgecolor="#111", label="Finite-$m$ witness (C1–C5)"),
        Patch(facecolor="#1b7837", edgecolor="#111", label="Finite-$m$ LHS model (C6–C9)"),
        Patch(facecolor="#d95f02", edgecolor="#111", label="Universal gap (C10–C12)"),
        Patch(facecolor="#b2182b", edgecolor="#111", label="2-copy superact. (C13–C14)"),
    ]
    ax.legend(handles=handles, loc="upper right", fontsize=7.2, frameon=True, framealpha=0.95)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_ppt_separability_pocket.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    exp1 = json.loads((RES_DIR / "exp1_certified_atlas.json").read_text(encoding="utf-8"))
    exp2 = json.loads((RES_DIR / "exp2_polytope_ladder_and_universal_gap.json").read_text(encoding="utf-8"))
    exp3 = json.loads((RES_DIR / "exp3_two_copy_haar_mc_crosscheck.json").read_text(encoding="utf-8"))
    exp4 = json.loads((RES_DIR / "exp4_ppt_separability_phase_diagram.json").read_text(encoding="utf-8"))

    make_fig1(exp2)
    make_fig2(exp3)
    make_fig3(exp1, exp4)
    print(f"Generated 3 Paper 10 figures in {FIG_DIR}")


if __name__ == "__main__":
    main()
