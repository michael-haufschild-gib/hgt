# Scalar germ gauges cannot trivialize the filtered weld

- **ID:** scalar-germ-gauge-weld-obstruction
- **Stage:** 3-formalized
- **Type:** hypothesis-discharge theorem / local-global gauge no-go
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

The differential-order filtration already distinguishes scalar identity coefficients from the
derivation direction.  A genuine scalar germ-basis gauge therefore lands automatically in the
order-zero coefficient line `(0,r)`; no separate `IsOrderZeroAffineCochain` hypothesis should be
required.

For every nonzero weld rate `theta`, there is no real scalar gauge family
`r : WeldGroup -> R` whose included affine cochain has boundary `weldAffineCocycle theta`.  The same
holds for every complex scalar gauge family after the canonical real readout `log norm`.  At each
prime this gives a hypothesis-free global obstruction, while the previous FE/Schwarz theorem still
provides local normalizing scalars on both fixed and free orbit shapes.

## Attack and verdict

- `[PROVED INFRASTRUCTURE]` `no_orderZeroAffinePrimitive` rules out an order-zero primitive but takes
  order-zero admissibility as a Prop hypothesis.
- `[PROVED EXACT CLASSIFICATION]` Scalar germ gauges automatically satisfy that Prop because
  `weldAffineScalar` has principal symbol zero; conversely, every order-zero affine cochain is
  uniquely a scalar gauge family.  Thus the Prop hides no additional directions.
- `[PROVED INTERFACE NO-GO]` Specializing the existing obstruction rules out every scalar gauge
  family without an admissibility hypothesis; complex gauges reduce through `g |-> log norm(g)`.
- `[HONEST LIMIT]` This does not yet show that a free zero orbit would produce a primitive.  It
  proves that scalar local normalizations cannot supply one even if chosen coherently over every
  weld label.

## Formal theorem surface

- `weldRealScalarGaugeCochain_isOrderZero` discharges admissibility automatically.
- `weldRealScalarGaugeCochain_injective` proves faithful parameterization by scalar families.
- `isOrderZeroAffineCochain_iff_exists_realScalarGauge` identifies the entire order-zero Prop
  exactly with scalar-gauge data.
- `no_weldRealScalarGaugePrimitive` and `prime_no_weldRealScalarGaugePrimitive` eliminate the
  real scalar primitive interface without an admissibility hypothesis.
- `weldComplexScalarGaugeLogNormCochain_isOrderZero`,
  `no_weldComplexScalarGaugeLogNormPrimitive`, and its prime specialization eliminate complex
  scalar gauges after canonical size readout.

The implementation is
`formal/GaloisForLFunctions/RHTower/ScalarGermGaugeWeldObstruction.lean` and is registered in the
`RHTower` umbrella.

## Local/global theorem boundary

The previous gluing theorem proves existence of local complex normalizing scalars on both orbit
shapes.  This theorem proves that even an arbitrary scalar choice over every weld-group label cannot
be a global primitive of a nonzero weld.  The exact remaining implication is now isolated:

> `[OPEN CORE]` Does a free completed zero orbit force a **non-scalar positive-order** weld
> trivialization, while a critical-line orbit admits only order-zero descent?

The scalar version is impossible, not merely unconstructed.  Any future implication from a free
orbit to weld exactness must manufacture a derivation-symbol component; the existing theorem
`weldAffinePrimitive_principalSymbol` says that component is forced to equal the derivation count.

## Novelty and significance gates

- **DERIVABLE INFRASTRUCTURE:** the final contradiction specializes the existing
  `no_orderZeroAffinePrimitive`; it is not a new cohomology computation.
- **NEW INTERFACE KNOWLEDGE:** the order-zero admissibility Prop is classified exactly and removed.
  Actual scalar germ gauges exhaust it, so the global no-go now speaks the same coefficient language
  as local FE/Schwarz normalization.
- **SIGNIFICANT:** the live bridge cannot be scalar.  A free orbit would have to force the precise
  positive-order symbol `weldDerivSymbol`, not merely a coherent family of germ rescalings.
- **NON-TAUTOLOGICAL:** the proof contains no zero-location or RH predicate.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
