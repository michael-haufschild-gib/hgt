# Floor-Free Arithmetic (FFA) programme

- **ID:** ffa-programme
- **Stage:** 1-in-progress
- **Type:** PROGRAMME
- **Source:** docs/reports/review-1011/obstacles-summary.md §4 (items A121, A123–A131, B170–B173)
- **Statement:** theory of mechanisms without a floor: floors of mechanisms, the four floor-free
  kinds of inequality, AAL as non-attainment, and the search for a producer.

## Goal
Folder `formal/GaloisForLFunctions/FloorFreeArithmetic/`, umbrella `FloorFreeArithmetic.lean`,
foundational README. Deliver the first theorems of the six tracks of §4.5, drive each track to its
kill or its survivor, and record what a producer must be.

## Corpus facts the programme starts from (do not redo)
- Finite top layer: `SurfaceOfSpecZ.ScaleLocality.exists_finite_top_of_not_abscissaLaw`,
  `positiveTopSupport`, `topTrace_eq_positive_sum`, `tendsto_normTrace_sub_topTrace`,
  `zeta_finite_top_negative_windows` (one-sided, length `(k+1)π/67`),
  `asymptoticAbscissaLaw_of_lengthDependent_floors` (N2).
- Vandermonde window bound: `InfiniteRankWeilTheory.exists_pos_forall_window_le_norm_expSum`,
  `exists_pos_forall_window_le_norm_pointSum`.
- Positivity floor (A124): `MultiplicativePositivityGeometry` — `multiFrequency_purchase_le_two`,
  `interior_zero_invisible`, `siegel_member_zero`, `exclusion_iff`.
- Feasibility receiver: `ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_feasible_at_every_aperture`,
  `not_riemannHypothesis_iff_empty_aperture`.
- Projection to the line: `ZeroConfigurationGeometry.criticalProjectionConfig` (counts preserved).
- Local moments: `SurfaceOfSpecZ.ScaleLocality.localPrimeTraceMoment`,
  `riemannHypothesis_iff_localPrimeTraceMoments`.
- Exceptional layer filters (integrality): `ExceptionalLayerTheory` (`LocalFiltersRecoverTheTopDivisor`,
  `DampingFiltersReadTheExceptionalDivisor`).
- Index exit: `ArithmeticOrientationGeometry.riemannHypothesis_iff_encard_rightZeros_lt_two`.

## Tracks, first theorems, state
| Track | Item | Statement | State |
|---|---|---|---|
| 1 | A121 N1 | finite top layer ⇒ `sup_{[T,T+L]}\|normTrace\| ≥ c` for every `L>0`, late `T`; window non-attainment ⇒ AAL | todo |
| 1 | A121 N3 | one exponent for all even moments on late windows ⇒ AAL | todo |
| 1 | A125 N4 | AAL ⇔ no line has a finite positive even number of zeros to its right (unit gap) | todo |
| 1 | A127 | tangent datum; realization by configurations; linear identities are tautologies on it | todo |
| 2 | A128 | feasible set at an aperture as positive measures; extreme points | todo |
| 2 | A129 | prime side of pure objects with ζ's Gamma factor vs atoms on `log ℕ` | todo |
| 3 | A126 | resonance functions of regulators, right-half zero counts | todo |
| 4 | A130 | prime side of the projected divisor; monotone functionals | todo |
| 5 | A131 | prime form of a tensor-uniform bound | todo |
| 6 | A123, A124 | floor of a mechanism (definition, census as theorems) | todo |

## Mathematics fixed so far (paper)
1. **Uniform badness (N1).** Top trace of a finite layer: `P(u)=Re Σ_{z∈S} 2e_z e^{iγ_z u}` =
   exponential sum with the `2|S|` distinct frequencies `±γ_z`. Sample at `u=(M+1+m)h`, nodes
   `e^{±iγ_z h}` distinct for `h<π/max γ`; the inverse Vandermonde bound gives `|P|≥ε` at one of
   `2|S|` consecutive samples, so on every window of length `L≥(2|S|+1)h`. Lower layers die out.
2. **Positivity in tangent form.** At `Θ<1` the normalized prime sum
   `Σ_{p≤x}p^{−Θ}cos(γ log p) ~ −m log log x` has trivial bound `x^{1−Θ}/log x`: positivity of `Λ`
   matches the normalization only at `Θ=1`. Continuous fake: density
   `e^u(1+1_{[0,u₀]}−2e^{−(1−β)u}cos γu) ≥ 0`, `u₀=log2/(1−β)`, transform
   `1/(s−1)−1/(s−ρ)−1/(s−ρ̄)+entire` bounded by `u₀` on `Re s≥1`: exactly the de la Vallée-Poussin
   boundary `(1−β)log γ ≍ 1`.

## Modules (folder `FloorFreeArithmetic/`)
| Module | Content | State |
|---|---|---|

## Log
- 2026-11-10 — created; corpus survey done.
