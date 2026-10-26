# Arithmetic Polarization programme

- **ID:** apol
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2610/hard-obstacles-summary.md §4
- **Statement:** Develop the field "arithmetic polarization": positive structures on reflection pairs, their mechanisms (equivariant, positive, elliptic, collided, counting, charged), localizers, collisions and completions.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticPolarization/`, umbrella `ArithmeticPolarization.lean`,
foundational README. Answer the eleven questions of §4.4 by theorems or sharp no-gos with survivors;
build the tools of §4.5.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs (in module docstrings and README §4)
- [ ] 2 → 3  axiom audit of every pillar theorem

## Pillars and modules (all checked with `lake --old env lean`)

| Pillar | Module |
|---|---|
| Π1 polarization law, spectral two forms | `ThePolarizationLaw` |
| Π2–Π3 two forms, RH = W = D | `TheOscillatoryCapacity`, `HeckeInvarianceOfTheCollidedPolarizationIsRH` |
| Π4–Π6 classification, definite sectors, dihedral dilemma | `TheEllipticLocalizers` |
| Π7 sectors = twists, twist identity, collision | `TwistedSectorsCollideQuartets` |
| Π8 price: twisted EF, charge, conductor horizon | `ThePriceOfEllipticLocalization` |
| Π9 forcing half | `TheForcingHalfOfEllipticLocalization` |
| Π10 collision law | `TheCollisionLaw` |
| Π11 collision parity | `CouplingCollidesEvenly` |
| Π12 escape kernels collided | `EscapeKernelsAreCollidedForms` |
| Π13 leading-line law, Fejér barrier | `TheFejerBarrierForCoupledContraction` |
| Π14 rigidity ⇒ RH at γ | `RigidityOfTheCoupledClassExcludesItsZeros` |
| Π15 rate neutrality | `TwistsAreRateNeutral` |
| Π16 diagonal collapse | `TheDiagonalCollapse` |
| Π17 first gauge charge | `TheFirstGaugeChargeIsATwist` |

## Open topics (README §8)
Compute the defect `Δ`; forcing half beyond the conductor horizon; odd collisions over `ℤ`;
coupled rigidity at zero-free ordinates; two-variable section count; W8 separating aperture;
equivariant positive forms from counting.

## Log
- 2026-10-26 — created; README draft; 15 modules checked; README rewritten.
