# The Laguerre identity of `Ξ` as an inverse-square zero sum; a log-concave kernel violating Laguerre

- **ID:** ANC-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** survivors and no-go of `5-failed/anchor-law-inner-band.md`
- **Statement:** (i) off the divisor, `ΞC'(z)² − ΞC(z)ΞC''(z) = ΞC(z)² ∑_q (z − a_q)⁻²` over the
  multiplicity copies `q` of the zeros; (ii) at a real `γ` a conjugate pair `γ ∓ δ i` contributes
  exactly `−2/δ²`, so the first Laguerre inequality at `γ` with `Ξ(γ) ≠ 0` forces
  `2/δ² ≤ Re ∑_{others} (γ − a_q)⁻²`; (iii) the kernel `e^{−πu²}(cosh(ωu) + 6/5)`, `ω² = 2π/5`,
  is positive, even, log-concave, has Fourier transform `e^{−πt²}(e^{1/10}cos(ωt) + 6/5)`, and
  that transform violates the first Laguerre inequality at `t₀ = π/ω`.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity` | `xiMittagLefflerTerm`, `logDeriv_XiC_eq_tsum`, `hasSum_neg_inv_sq_deriv_logDeriv_XiC`, `summable_inv_sq_sub_xiSpectralPoint`, `laguerre_XiC_eq_tsum_inv_sq`, `tsum_inv_sq_sub_xiSpectralPoint_pair`, `laguerre_XiC_re_pair`, `two_div_sq_le_of_laguerre_nonneg` |
| `GaloisForLFunctions.HTGeometry.LaguerreKernelCounterexample` | `laguerreKernel`, `laguerreTransform`, `laguerreKernel_pos`, `laguerreKernel_even`, `laguerreKernel_logConcave`, `fourier_laguerreKernel`, `laguerreTransform_laguerre_neg` |

Inputs reused: `XiC_eq_constant_mul_canonicalProduct`, `logDeriv_canonicalProductE1Indexed`,
`xiSpectralPoint_inv_sq_summable`, `eventually_norm_ge_of_summable_inv_sq`,
mathlib `hasSum_deriv_of_summable_norm`, `fourier_gaussian_pi'`, `concaveOn_of_deriv2_nonpos`.
Axioms: `propext, Classical.choice, Quot.sound`.

## Log
- 2026-09-02 — created at stage 3 from the no-go closure of ULF-ANC-001.
