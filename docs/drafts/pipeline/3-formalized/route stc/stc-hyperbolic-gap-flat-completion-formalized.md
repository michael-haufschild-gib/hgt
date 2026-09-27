# Hyperbolic-gap flat completion of the Gamma prime pair — Lean certificate

- **Paper card:** `stc-hyperbolic-gap-flat-completion.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.HyperbolicGapFlatCompletion`,
  `GaloisForLFunctions.RHTower.STCHyperbolicGapFlatCompletionSource`,
  shared layers `GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators`, `GaloisForLFunctions.RHTower.STCPrimeWindowPackets`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`S(t) = hyperbolicGapSinc t`; `b_u(p) = stcDepthZeroAmplitude u p`; matrices on `ℓ²(primes)` via `HasLpMatrix`.

| Card item | Lean theorem |
|-|-|
| (1) normalized literal pair `n(y-x)/2 · sinh(g(x+y)/2)` | `reflectionOddExterior_div_amplitudes` |
| (2) flat completion = coboundary of `cosh(g log p)` | `flatGap_reflectionOddExterior_coboundary`, `flatGapEdge_eq_cosh_sub`, `flatGapEdge_triangle` |
| (3)–(4) continuous rigidity (`F = S(g·/2)`, `Φ = cosh(g·)/g + C`) | `flatGap_continuous_rigidity` |
| (4a)–(4b) prime-only rigidity via PNT prime triples and the exponential cocycle | `flatGap_prime_rigidity`, `exists_prime_triples_logGap`, `exponentialGapCocycle_rigidity` |
| (5) `u_p(ρ) = -2 p^{-1/2+iτ} ∂_g cosh(g log p)` | `orbitwiseNatPrimeSeamCharge_eq_grade_derivative`, `hasDerivAt_cosh_grade` |
| `S(t) > 1`; two-prime Schur indefiniteness | `hyperbolicGapSinc_gt_one_of_ne_zero`, `hyperbolicGapSinc_pair_indefinite` |
| amplitude law `b_u² = (log p)² p^{-1-u}`, `b_u p^a = b_{u-2a}`, sharp `ℓ²` threshold | `stcDepthZeroAmplitude_sq`, `stcDepthZeroAmplitude_mul_rpow`, `summable_stcDepthZeroAmplitude_sq_iff` |
| (6) bounded operator ⟺ `u > 2|g|` (column obstruction outside) | `exists_hasLpMatrix_stcFlatGapKernel_iff`, `not_exists_hasLpMatrix_of_col` |
| in the chamber: rank ≤ 2, compact, unique | `stcFlatGapKernel_compact_rank_two`, `stcFlatGapKernel_hasLpMatrix_wedge` |
| `g = 0`: kernel vanishes | `stcFlatGapKernel_zero_grade` |
| critical half-density and grade derivative in `ℓ²` for `|g| < 1/2` | `summable_sq_stcCriticalHalfDensity`, `summable_sq_stcCriticalGradeDerivative` |
| critical wedge finite rank, trace class, bounded transport compact | `stcCriticalWedge_traceClass`, `isTraceClass_lpWedge_primes`, `isCompactOperator_transport` |
| vertical phase `p^{iτ}` does not change the conclusion | `stcVerticalPhaseTwist`, `stcCriticalWedge_phaseTwist_traceClass` |
