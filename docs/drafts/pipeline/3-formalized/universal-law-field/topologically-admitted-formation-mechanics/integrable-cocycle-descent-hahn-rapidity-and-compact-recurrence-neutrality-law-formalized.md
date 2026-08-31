# Integrable cocycle descent and compact-recurrence neutrality -- Lean certification

- **ID:** ULF-TAFM-7
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/integrable-cocycle-descent-hahn-rapidity-and-compact-recurrence-neutrality-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedIntegrableCocycleDescent`,
  `GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularIntegrableCocycleDescent`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry.UniversalLawField`,
  `GaloisForLFunctions.RHTower`
- **Status:** `[LEAN-CERTIFIED]` `[NO PROJECT AXIOMS]` `[L1/HAAR]` `[RH-EQUIVALENT INTERFACE]`

## Certified mechanism

Lean proves an exact conservation law that needs no compact-boundary continuity. For any additive
formation map into a compact abelian phase group, a real character is the almost-everywhere
translation increment of one Haar-integrable potential exactly when the character is zero.

The proof integrates the covariance equation. Haar invariance preserves the potential integral;
probability normalization adds the character value once. Their equality forces that value to
vanish. This is the gauge law: integrable potential is presentation, translation increment is
gauge-invariant holonomy.

The measurable Hahn specialization is also certified. If the canonical Radon--Nikodym signed-current
density is controlled by Haar probability and obeys the affine translation law, its recovered
formation character is neutral. Integrability comes from signed-measure RN theory, not a premise
invented for the scalar endpoint.

## Certified declarations

- `IntegrableTranslationPotential`;
- `character_eq_zero_of_integrable_measurePreserving_increment`;
- `integrableTranslationPotential_iff`;
- `not_integrableTranslationPotential_of_ne_zero`;
- `character_eq_zero_of_measurableHahnDensity_translationPotential`;
- `PrimeModularIntegrablePotential`;
- `primeModularIntegrablePotential_iff`;
- `ThetaXiPrimeModularIntegrablePotential`;
- `thetaXiPrimeModularIntegrablePotential_iff`;
- `thetaXiPrimeModularIntegrablePotential_lineConj_iff`;
- `forall_thetaXiPrimeModularIntegrablePotential_iff_riemannHypothesis`.

## Exact advance over continuous descent

Earlier compact recurrence required a continuous real-character extension. This certificate lowers
the producer to one `L1` potential with almost-everywhere affine covariance. The potential may be
unbounded and discontinuous. In prime-circle formation, existence still selects zero modular rate;
on theta-source Xi copies it is pointwise equivalent to critical-line placement and globally
equivalent to RH.

This is an interface, not an RH proof. Remaining source producer is divisor-independent
construction of the prime-circle potential plus its finite Haar work and affine covariance.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/TopologicallyAdmittedIntegrableCocycleDescent.lean
lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaSourcePrimeModularIntegrableCocycleDescent.lean
lake build GaloisForLFunctions.HTGeometry.TopologicallyAdmittedIntegrableCocycleDescent
lake build GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularIntegrableCocycleDescent
```

Both named leaf builds pass. Missing dependency oleans were rebuilt by those targets; no umbrella,
theorem-area, or project build was run. Both modules are wired into their umbrellas without building
them. `/tmp` `#print axioms` audits of eight generic and instantiated capstones report only
`propext`, `Classical.choice`, and `Quot.sound`.
