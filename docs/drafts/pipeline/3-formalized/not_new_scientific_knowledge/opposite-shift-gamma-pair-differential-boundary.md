# Opposite-shift Gamma pairs have an exact integer-sum differential boundary

- **ID:** `opposite-shift-gamma-pair-differential-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Euler reflection; A. Manenti, *Thermal CFTs in momentum space*, arXiv:1905.01355, equation (7.8); D. Birmingham, I. Sachs, S. N. Solodukhin, *Conformal Field Theory Interpretation of Black Hole Quasi-normal Modes*, arXiv:hep-th/0112055
- **Statement:** For arbitrary complex shifts `a,b`, the genuine meromorphic response `Gamma(z+a) Gamma(-z+b)` is DA exactly when `a+b` is integral and HT otherwise.

## Goal

Extract the asymmetric parent law behind reflected thermal, detector, Coulomb, and black-hole
Gamma responses.  The selector is closure of the two observed shifts under Euler reflection and
integer translation, not a temporal-evolution assumption.

## Gates

- [x] 0 → 1 in-progress: general pair isolated from the symmetric thermal specialization
- [x] 1 → 2 fully-proven: reflection factorization and both directions of the exact boundary
- [x] 2 → 3 formalized: exact module build, direct checks, and standard-only axiom audit pass
- [ ] 3 → 4 publication-ready: not a standalone novelty claim

## Exact relation

In the global meromorphic differential field,

`Gamma(z+a) Gamma(-z+b)`

equals

`reflectionGauge_b(z) * Gamma(z+a) / Gamma(z+1-b)`.

The reflection gauge is nonzero and DA.  The remaining ratio has separation `1-a-b`, so the
translated-Gamma classifier gives DA exactly when `1-a-b` is integral, equivalently when `a+b`
is integral.  Off that lattice the response is HT.

## Corpus value

The prior thermal theorem treated only `a=b=h`.  The new theorem strictly generalizes it to
asymmetric incoming/outgoing weights and removes duplicated reflection-plus-ratio reasoning from
consumers.  `ThermalCFTGammaResponseBoundary.lean` now proves its symmetric classification by
specialization of this parent law.

The theorem directly applies whenever a measured response contains one positive- and one
negative-frequency Gamma leg, including thermal CFT and BTZ sectors.  It does not classify
products with incommensurable frequency scales; that remains the multi-scale open core.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary`

- `gammaOppositeShiftProductMero_eq_gauge_mul_reducedVeneziano`
- `differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSeparation`
- `exists_integer_one_sub_gammaShiftSum_iff_integer_gammaShiftSum`
- `differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSum`
- `hypertranscendentalOver_gammaOppositeShiftProductMero_iff_nonintegerSum`

All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## RH pressure test

This strengthens archimedean cancellation auditing but supplies no prime source, zero-free region,
or sign/positivity input.  It does not close an `RHTower` RH hypothesis.

## Log

- 2026-07-17 — asymmetric reflection parent law formalized; the symmetric thermal theorem was
  reduced to a specialization; exact build, direct checks, and axiom audit passed.
