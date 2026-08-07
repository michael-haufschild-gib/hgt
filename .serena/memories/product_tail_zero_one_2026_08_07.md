# Kolmogorov 0-1 law for products of laws on ℕ (2026-08-07)

`HTGeometry/ProductTailZeroOne.lean` — green (3007 jobs), axiom-clean, umbrella-wired.

`measure_zero_or_one_of_tail (e : ℕ ≃ ι) (hA : MeasurableSet[limsup (fun n => coordSigma (e n)) atTop] A)
  : infinitePi μ A = 0 ∨ infinitePi μ A = 1`

plus `measure_infiniteHit_eq_zero_or_one` (the dichotomy's qualitative half as an instance).

## How it went through cheaply

- `@[reducible] def coordSigma i = MeasurableSpace.comap (fun k => k i) inferInstance`. The
  `@[reducible]` is REQUIRED: a plain `def` of class type triggers a linter warning that fails the gate.
- **`iIndepFun_infinitePi` IS the independence of the coordinate σ-algebras**: `iIndepFun f μ` unfolds to
  `iIndep (fun i => comap (f i) _) μ`, so `iIndep_coordSigma` needs no proof beyond the instantiation.
- `MeasurableSet[coordSigma i] (localEvent t i)` is `⟨t i, MeasurableSet.of_discrete, rfl⟩` — comap's
  measurable sets are literally preimages.
- Tail-measurability: `Filter.limsup_eq_iInf_iSup_of_nat` + `MeasurableSpace.measurableSet_iInf`
  (measurable in an ⨅ ⟺ measurable in each), then `Filter.limsup_nat_add` to shift the enumeration, then
  `@MeasurableSet.measurableSet_limsup _ (⨆ i ≥ n, coordSigma (e i))` — the lemma applies in ANY
  MeasurableSpace instance, which is what makes the coarse-σ-algebra argument work.
- `le_iSup₂ (f := fun i (_ : n ≤ i) => …) (j+n) (by omega)` for the single-index-into-⨆ step.

## Value

Strictly more general than the hitting dichotomy: applies to every event ignoring finitely many
coordinates (densities, series convergence along the hit set, tail asymptotics). The dichotomy stays
sharper where it applies because it says WHICH of 0/1.
