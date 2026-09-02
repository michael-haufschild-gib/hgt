# Möbius-series convergence forces a zero-free half-plane; pair parity; Eisenstein blindness

- **ID:** IND-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** survivors of `5-failed/zero-individuation-law-two-completion-producer.md`
- **Statement:** (i) if `∑ μ(n) n^{−s}` converges at `s₀` then `ζ(s) ≠ 0` for `Re s > Re s₀`,
  `s ≠ 1`, hence the abscissa of convergence of the Möbius series is at least `Re ρ` for every
  zero `ρ`; (ii) the sum of any `φ` over a reflected pair `½ ± δ + iγ` is even in `δ` and its
  derivative at `δ = 0` vanishes; (iii) the completed Eisenstein constant term
  `Λ(2s) y^s + Λ(2−2s) y^{1−s}` never vanishes at a half-zero of `Λ` with `Re s < ½`.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.MoebiusConvergenceZeroFree` | `moebiusShift`, `differentiable_dirichletPartialSum_moebiusShift`, `dirichletSum_moebiusShift_mul_riemannZeta`, `riemannZeta_ne_zero_of_moebius_convergesAt`, `re_le_abscissaOfConv_moebiusShift` |
| `GaloisForLFunctions.RHTower.ZeroLedgerPairParity` | `pairLedger`, `pairLedger_even`, `deriv_pairLedger_zero`, `eisensteinConstantTerm`, `eisensteinConstantTerm_one_sub`, `eisensteinConstantTerm_ne_zero_of_completedRiemannZeta_eq_zero`, `completedRiemannZeta_ne_zero_of_eisensteinConstantTerm_eq_zero` |

Inputs reused: `DirichletConvergesAt`, `dirichletSum`, `tendstoLocallyUniformlyOn_dirichletPartialSum`
(Cahen), `abscissaOfConv`, `zetaEntire`, `moebiusCoeffC`, `LSeries_moebiusCoeff_mul_riemannZeta`,
`convex_decayHalfPlane`, `completedRiemannZeta_ne_zero_of_one_le_re`. Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3 from the no-go closure of ULF-IND-001.
