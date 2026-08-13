# Primitive–fibre modular renormalization law — formalization certificate

- **ID:** `primitive-fibre-modular-renormalization-law`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/primitive-fibre-modular-renormalization-law.md`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH] [NO COMPUTATION]`

## Formalized theorem

For every `ell > 0`, `0 < r < 1`, and valuation depth `e`, the positive activation atom factors
through Fisher damping and the Gamma valuation atom, while the critical primitive current factors
through the independent promotion gauge.  The corresponding activation-to-current gauge and
promotion gauge diverge with depth.  The two reflected modular currents have fixed product, agree
exactly at modular tilt zero, and every nonzero tilt has an unbounded reflected sewing ratio in
one orientation.

The prime specialization identifies the abstract activation, Fisher, Gamma, and critical-current
profiles with their literal prime-tower formulas.

## Source module and capstones

```text
formal/GaloisForLFunctions/RHTower/PrimitiveFibreModularRenormalizationLaw.lean

primitiveFibreActivationAtom_eq_fisher_mul_gamma
primitiveFibreCriticalCurrent_eq_promotion_mul_gamma
primitiveFibreCriticalCurrent_eq_activationGauge_mul_atom
primitiveFibreModularCurrent_mul_reflection
primitiveFibreModularCurrent_eq_reflection_iff
primitiveFibreReflectedSewingRatio_unbounded
tendsto_primitiveFibrePromotionGauge
tendsto_primitiveFibreActivationToCurrentGauge
primitiveFibreActivationAtom_prime
primitiveFibreFisherDamping_prime
primitiveFibreGammaAtom_prime
primitiveFibreCriticalCurrent_prime
primitiveFibreRenormalization_law
```

## Verification and boundary

The module is registered in the `RHTower` umbrella.  Direct
`lake env lean GaloisForLFunctions/RHTower/PrimitiveFibreModularRenormalizationLaw.lean` and
targeted `lake build GaloisForLFunctions.RHTower.PrimitiveFibreModularRenormalizationLaw` pass.
Scratch `#print axioms` checks for the factorization, reflection, divergence, and certificate
capstones report only `propext`, `Classical.choice`, and `Quot.sound`.

The certificate covers the dependency-closed theorem and exact prime specialization.  It makes no
RH claim and does not convert the preliminary novelty audit into an external priority claim.
