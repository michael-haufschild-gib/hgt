# EWU: structural elimination of pole slack

Status: in progress. Evidence source: current Lean corpus only. No external search or novelty audit, per user instruction.

## Objective

Prove a structural theorem removing an actual obstacle in EWU, not another criterion or an improved estimate. Final claims must be unconditional, compiled, wired, and audited directly with `lake env lean`.

## Verified frontier

- `EvenSectorFullPositivity.weilPositiveEvenAt_one_iff` already identifies the cone at pole weight one.
- `EvenSectorPoleWeightWindow.one_le_of_primeBlindPositiveEvenAt` excludes pole weights below one.
- `EvenSectorDoublePoleExclusion.canonical_or_negative_superpole` eliminates the negative double-pole branch at arbitrary pole weight; a noncanonical source must have negative-part Dirichlet divergence at some exponent greater than one.
- `EvenSectorPoleFreeTwoSidedGrowth` supplies polynomial coefficient growth without an extra assumption.
- `EvenSectorPoleFreeResonatorPositivity` transfers positivity only to nonnegative-coefficient translated packets. Signed coefficients can change sign on the imaginary spectral segment.
- `EvenSectorTwistedArcNull` eliminates that segment at pole weight one using a genuinely null twisted-arc family. Extra pole weight leaves a nonzero budget in the same identity.

## Conjecture ledger

1. Extend the pole-weight-one spectral argument verbatim to arbitrary pole weight. Rejected: the null identity gains the pole budget; assuming it remains null is circular.
2. Multiply the twisted-arc family by the pole annihilator. Unresolved: spectral pole removal is exact, but multiplication differentiates the physical blind kernel; pointwise blindness at logarithmic nodes does not imply derivative blindness. Must not assume this closure.
3. Investigate the signed resonator obstruction and the exact geometry of the imaginary segment. Seek a structural operation that removes this obstruction using existing arithmetic constraints, rather than adding a convergence premise.

## Work discipline

Keep conjecturing after failed mechanisms. Complete a dependency-closed paper proof before adding a research Lean module. Use foreground targeted builds, one at a time; no full or umbrella builds, no numerical experiments, no heartbeat overrides. Leave concurrent work untouched.
