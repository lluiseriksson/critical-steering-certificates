# Exact-Q Finite-Setting Steering Gap Laws and Machine-Checked Two-Copy Superactivation

Zero-dependency Lean 4 formalization, pure-stdlib exact-$\mathbb{Q}$ certificate verifier (`EPR-STEER-CERT-1.0`), and reproducible computational benchmarks for:

> **Exact-$\mathbb{Q}$ Finite-Setting Steering Gap Laws, Rational Polytope Certificates, and Machine-Checked Two-Copy Superactivation of PVM-Critical Two-Qubit States**
> — *Lluis Eriksson* (November 2026)

Advancing Zhang and Chen (`arXiv:2611.09321`, November 2026), Wiseman–Jones–Doherty (*PRL* 98, 140402, 2007), and Quintino–Brunner–Huber (*PRA* 94, 062123, 2016).

## Key Results

1. **Universal Exact-$\mathbb{Q}$ Finite-$m$ Steering Gap Law (Theorem 3.1):**
   Proves via great-circle cell counting ($R(m) \le m^2 - m + 2$), spherical-cap centroid rearrangement ($\|\mathbf{m}_r\|_2 \le \alpha_r(1-\alpha_r)$), and Cauchy–Schwarz that for **every** $m \ge 1$ and **every** $m$ projective measurements on $S^2$, the Werner state $\rho_v$ is provably unsteerable for all $v \le \frac{1}{2} + \frac{1}{2(m^2 - m + 1)}$ (exact $v_1^* = 1$ at $m=1$, within $1.0\%$ of optimal at $m=3$, and within $2.1\%$ at $m=6$).
2. **Exact-$\mathbb{Q}$ Polytope Steering Duality & Cuboctahedral Supremacy (Theorem 3.2):**
   Exact squared-rational primal–dual steering certificates across $m \in \{2, 3, 4, 6, 7, 12, 15\}$, proving that the rational cuboctahedron ($m=6$, exact threshold $v_6^{\mathrm{cub}} = \sqrt{5/18} \approx 0.5270$) strictly outperforms the Platonic icosahedron ($v_6^{\mathrm{ico}} = (1+\sqrt{5})/6 \approx 0.5393$, $(v_6^{\mathrm{ico}})^2 = (3+\sqrt{5})/18$) in exact $6$-setting steering threshold!
3. **Unconditional Exact-$\mathbb{Q}$ Two-Copy Superactivation with Strictly Separable Conditional States (Theorem 3.3):**
   Proves closed-form PPT eigenvalues $\lambda_{\min} = (1 - v^2(1+2s))/4 \ge 1/16 > 0$ at $v=1/2$ for all partially entangled Bell measurements, and certifies strict two-copy superactivation of $\rho_{1/2}^{\otimes 2}$ (and strictly below criticality at $v = 49999/100000 < 1/2$) purely over $\mathbb{Q}$ via our Bell sign-parity identity, SOS polynomial factorization $256 - 3125 p(1-p)^4$, and exact spherical moment $\mathbb{E}_{S^2}[x^2 y^2 z^2] = 1/105$.
4. **Zero-Float `EPR-STEER-CERT-1.0` Verifier & Lean 4 Kernel (Theorem 3.4):**
   18 machine-checked theorems in zero-dependency Lean 4 (`v4.35.0`, 0 `sorry`, 0 `Classical.choice`, 0 warnings), 14 independently verified exact-$\mathbb{Q}$ certificates across 4 mutually exclusive modes, and 46/46 live adversarial red-team attacks rejected.

## Reproduction

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

## License

MIT License (see `LICENSE`).
