# Effectivity on balanced complete-cell sections

- **ID:** acs-complete-cell-haar-effectivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [complete-cell index payment](../1-in-progress/acs-complete-cell-index-payment.md)
- **Statement:** One fixed lower arithmetic index gives a uniform original Weil floor for every finite signed balanced whole-cell section. Each finite block admits one common pole-preserving smoothing with a half-mass floor, exact dimension, Riemann–Roch, ampleness, and Hodge index.

## Actual source and exact floor

For `a ≥ 1`, put `l_a = logCellWidth (2*a)`, `r_a = logCellWidth (2*a+1)`, and

`H_a = (r_a/(l_a+r_a)) rawCell (2*a) - (l_a/(l_a+r_a)) rawCell (2*a+1)`.

These are two complete adjacent cells, with no inserted gap. The mean is zero and exact square mass is `M_a = l_a*r_a/(l_a+r_a)`. For arbitrary real signed coefficients, `f = Σ a∈[1,X], c_a H_a` satisfies

`roughWeil f ≥ Σ a∈[1,X], ((1-1/sqrt 2)*log a + 2*gammaHardyPhaseRate 0 - 20)*M_a*c_a²`.

`haarSectionProfile_roughWeil_ge` proves this inequality for the original form, retaining square mass, full Gamma energy, every prime translation, and both signed poles. `exists_haarTail_roughWeil_floor` proves that one fixed `A ≥ 1` gives

`Σ M_a*c_a² ≤ roughWeil f`

for every finite section whose coefficients vanish below `A`, independently of the upper horizon.

## Actual smooth spaces

`smoothHaarBlockMap A d n` maps `c : Fin d → ℝ` to the same pole-preserving regularization of `Σ a∈[A,A+d), c_(a-A) H_a`. It is a proved linear map into compact C² real tests. `smoothHaarBlockTests A d n` is its range; membership uses source synthesis only.

`exists_smooth_haar_positive_spaces` proves that the same fixed `A` works for every `d`: there is one `n` such that the basis images are independent, the original Weil form is strictly positive on every nonzero coefficient vector, and

`(1/2) * ∫ f² ≤ weilPair f f`

throughout the entire range.

`exists_smooth_haar_effectivity` proves exact dimension `d`, Riemann–Roch and ampleness for `l2SourceCone (1/2)` on this source-defined range, and Hodge index for its original scaling subsurface. No sign condition enters membership, and no analytic estimate remains assumed.

## Proof, matched by Lean

1. [Prime payment](acs-balanced-complete-cell-prime-payment.md): actual translated pairings survive only at `(2*a+1)*m=2*b+1`. Every even multiplier vanishes. Divisor sums, the checked prime tail bound, and Young allocation give prime cost at most `Σ (16+log(2*a+1)/sqrt 2)*M_a*c_a²`.
2. [Gamma payment](acs-coherent-mean-zero-gamma-payment.md): the actual completely monotone Gamma kernel pays both charges of every mean-zero interval pair and the exterior charges. Their full-line sum gives reciprocal-width logarithms. Exact pair widths `logCellWidth a ≤ 1/a` yield Gamma gain at least `Σ log(a)*M_a*c_a²`.
3. `HaarCellPoleBound.lean`: exact L¹ mass `2*M_a` and mean cancellation bound each exponential moment by `2*M_a/sqrt(2*a)`. The mass bound yields moment square at most `M_a/(a*(a+1))`. These normalized weights telescope to at most one; weighted Cauchy–Schwarz bounds each section moment square by `Σ M_a*c_a²`. The original pole product therefore costs at most twice that mass.
4. `HaarCellEffectivity.lean`: adding the three checked estimates gives the displayed full-form floor. Since `1-1/sqrt 2 > 0`, choose one integer `A > exp((21-2*gammaHardyPhaseRate 0)/(1-1/sqrt 2))`. Every remaining diagonal coefficient is at least one.
5. `HaarCellSmoothEffectivity.lean`: scalar Weil and square-mass convergence are polarized into entrywise Gram convergence for the original form minus half the square-mass form. Its limiting matrix is positive definite by the concrete tail floor. Finite-matrix stability gives one smoothing scale for all coefficient vectors. Positivity gives injectivity and exact dimension; the verified half-mass floor supplies the source cone's Riemann–Roch, ampleness, and Hodge index.

## Verification

Every exact project file passed `lake --old env lean` from `formal/`, without warnings. All eleven modules are wired into the ACS umbrella; no umbrella build was run. The 33 transitive `#print axioms` audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

New final declarations are in namespace `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`, in `HaarCellPoleBound.lean`, `HaarCellEffectivity.lean`, and `HaarCellSmoothEffectivity.lean`. Supporting source, prime, and Gamma declarations are listed on the linked formalized cards. No stage-2 result was parked.

## Remaining ACS scope

Balanced pairs form a proper subspace. Their complements contain the pair averages and low-index directions. The theorem does not assert positivity of their mixed coupling, a source-complete exhaustion, or RH. Full signed index payment remains on the parent card; no hypothesis replacing that missing sign has been introduced.

## Log

- 2026-10-28 — Original full Weil floor and common-scale smooth source effectivity formalized and audited; moved directly to stage 3.
