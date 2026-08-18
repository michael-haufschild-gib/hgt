# Quantized proximity, approximate formation, and winding selection law

- **ID:** ULF-DFPM-6-LC
- **Stage:** 3-formalized
- **Type:** LEAN-CERTIFIED APPROXIMATE FORMATION SELECTOR
- **Status:** [UNCONDITIONAL] [EXACT ROOTS NOT REQUIRED] [NO RH PREMISE] [SOURCE APPROXIMATION OPEN]

## Certified mechanism

Let `charge : M -> Z` scale under powers and remain constant under a declared admission relation.
If one carrier is admission-near powers of unbounded depths, then its charge is zero.  Nearness
turns approximation into exact integer divisibility.

For nonvanishing complex loops, the admission relation is fixed by the native floor from zero.
If `eta_n^n` stays closer to `gamma` than that floor for unbounded `n`, dominated straight-line
homotopy and the winding power law give

\[
 \operatorname{wind}(\gamma)=n\operatorname{wind}(\eta_n),
\]

so `wind(gamma)=0`.

## Lean certificate

Module:

`GaloisForLFunctions.HTGeometry.ConstitutiveApproximateFormationSelection`

Certified declarations:

- `charge_eq_zero_of_unbounded_stable_approximatePowers`;
- `charge_eq_zero_of_cofinal_approximatePowers`;
- `tendsto_recoveredPowers_of_formationInterchange`;
- `charge_eq_zero_of_recovered_formationInterchange`;
- `windingNumber_eq_zero_of_unbounded_approximatePowers`;
- `exists_windingFormationGap`;
- `approximateFormationSelection_capstone`.

Scratch elaboration and direct leaf elaboration pass.  Targeted build of only the leaf passes.  The
leaf is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`; that umbrella was not built.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` where needed.

## Exact boundary

The certificate supplies the global selection/properness implication.  It does not construct
critical-half-plane approximate powers for the Euler-shell transfer.  That quantitative source
formation theorem—error below every local distance-to-noninvertibility floor—is now the minimal
DFPM producer.  Exact meromorphic roots remain sufficient but are no longer required.
