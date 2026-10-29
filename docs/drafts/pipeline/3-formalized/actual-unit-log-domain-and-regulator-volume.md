# Actual unit logarithm domain and regulator volume

- **ID:** actual-unit-log-domain-and-regulator-volume
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Complete weighted unit-log coordinates to the actual weighted-zero place profile, and identify the actual unit fundamental domain and its regulator volume.

## Exact construction and proof

Mathlib's `logSpace K` omits one distinguished infinite place and records
`mult(v)*log|v(u)|` at every remaining place. Complete a coordinate vector `x`
by setting `y_v=x_v/mult(v)` at retained places and
`y_v0=-(Σx_v)/mult(v0)` at the omitted place. This defines a continuous linear
map with weighted sum zero. The unit product formula proves that applying it
to the actual logarithmic embedding of a unit gives the existing full
`numberFieldUnitPlaceLogEmbeddings`.

Choose Mathlib's actual `basisUnitLattice` and its half-open fundamental
parallelepiped. Its proved lattice action tiles `logSpace K`; the domain is
measurable and bounded, its closure is compact, and its Haar volume is the
actual logarithmic lattice covolume. This is exactly the number-field
regulator. Covolume positivity gives positive volume, including unit rank
zero. Compactness and continuity give one positive bound on all completed
profile coordinates over the domain.

## Lean and verification

[NumberFieldUnitLogFundamentalDomain.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldUnitLogFundamentalDomain.lean)
contains:

- `numberFieldWeightedLogProfile` and its coordinate formulas
- `sum_mult_numberFieldWeightedLogProfile`
- `numberFieldWeightedLogProfile_logEmbedding`
- `continuous_numberFieldWeightedLogProfile`
- `numberFieldUnitLogDomain`
- `isAddFundamentalDomain_numberFieldUnitLogDomain`
- `measurableSet_numberFieldUnitLogDomain`, `isBounded_numberFieldUnitLogDomain`
- `volume_numberFieldUnitLogDomain`, `volume_numberFieldUnitLogDomain_pos`
- `volume_numberFieldUnitLogDomain_eq_regulator`
- `measure_numberFieldUnitLogDomain_lt_top`
- `isCompact_closure_numberFieldUnitLogDomain`
- `exists_bound_numberFieldWeightedLogProfile_unitDomain`

The final direct `lake --old env lean` source audit passes without warnings.
Six transitive axiom checks, including domain-volume positivity through its
consumer, contain only `propext`, `Classical.choice`,
and `Quot.sound`. No proof limit was raised. The module is wired into the
geometry umbrella; no umbrella was compiled. Its required olean is
built for the written unit-averaging consumer. The completed scratch is removed.
The final geometric source imports only the place-log module and Mathlib's
regulator module; its scratch-only Hecke audit import is removed.

The exact complex Mellin/Gamma unfolding remains open. This domain theorem
supplies the actual measure and compactness inputs, not that integral identity.
