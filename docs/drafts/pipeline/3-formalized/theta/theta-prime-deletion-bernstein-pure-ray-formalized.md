# The completed theta source is a pure ray of the prime-deletion Bernstein cone — Lean certificate

- **Paper card:** `theta-prime-deletion-bernstein-pure-ray.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaCriticalFluxBernstein` (shared flux/Bernstein
  layer), `GaloisForLFunctions.RHTower.ThetaPrimeDeletionBernsteinPureRay`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 11 listed theorems; no `sorry`.

"Completely monotone on `(0,∞)`" is the corpus notion `CompletelyMonotoneOn` (all signed forward
differences nonnegative, continuous on `(0,∞)`), the notion used by the corpus Bernstein--Widder
theorem. The source class `ThetaFluxSource f` = continuous with `e^{x/2} f` integrable on every right
ray (exactly the condition that makes the flux finite).

| Card item | Lean theorem |
|-|-|
| (2) `b_k(t) = 2π∑ n² e^{-πn²t}` (any atom subset) | `thetaNormalizedFlux_thetaCuspFullSource`, `thetaNormalizedFlux_thetaAtomSum` |
| positive exponential sums are CM | `completelyMonotoneOn_tsum_exp` |
| Bernstein–Widder + Laplace uniqueness ⇒ positive dominated rate measures, `ν₁+ν₂ = ν_k` (3) | `exists_dominated_exp_representation` (with `eq_atomicMeasure_of_le`, `exp_coeff_unique`) |
| translation law; (4) `b_{D_p f}(t) = b_f(t) - p² b_f(p²t)` | `thetaNormalizedFlux_comp_add`, `thetaNormalizedFlux_primeDeletion`, `thetaNormalizedFlux_primeDeletion_eq_tsum` |
| (5) deleted coefficients `a_n - p² a_{n/p} ≥ 0` | `primeDeletion_coeff_nonneg` (sign extraction `tsum_coeff_nonneg_of_completelyMonotoneOn`) |
| zero faces ⇒ `a_n = n² a_1` | `eq_sq_mul_of_prime_recursion` |
| (6) flux determines the source | `hasDerivAt_exp_mul_thetaNormalizedFlux`, `eq_of_thetaNormalizedFlux_eq` |
| `k ∈ C` | `thetaCuspFullSource_mem_primeDeletionCone` |
| **Pure-ray theorem (1)** | `thetaPrimeDeletionCone_pure_ray` |
| sharpness (7): no finite list of prime tests suffices | `thetaPrimeDeletionCone_finite_tests_insufficient` |
