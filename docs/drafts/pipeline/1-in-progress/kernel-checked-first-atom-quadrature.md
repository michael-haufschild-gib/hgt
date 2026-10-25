# Kernel-checked first-atom quadrature

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Preserve the five rational first-atom bounds and rank-four Milnor-to-Steinberg surjectivity while replacing native decision proofs by kernel-checked arithmetic.

## Approach

The finite-index complement follows from cardinality. The rational quadrature needs separate
certificates for mesh endpoints and local polynomial integrals, followed by finite-sum bounds.
Keep every existing theorem statement and analytic dependency unchanged. No external numerical
calculation, added mathematical premise, or raised elaboration limit is permitted.

## Verification

- [x] Replace the finite-index proof.
- [ ] Replace the five rational quadrature checks.
- [ ] Check each changed module with `lake --old env lean` from `formal/`.
- [ ] Audit transitive axioms for the numeric bounds and exported consequences.
- [ ] Confirm umbrella imports and remove scratch artifacts.

## Progress

The finite-index proof now uses cardinality. Scalar and polynomial enclosure proofs, including
the exact endpoint rounding recurrence, pass `lake --old env lean` in scratch. The original
rational polynomial and mass definitions moved unchanged into
`RHTower/PrimeArchThetaFirstAtomQuadratureEnclosures.lean`. The new arithmetic module reduces the
five numerical comparisons to outward rational bounds; its kernel checks remain pending.

The enclosure representation now uses integer numerators over denominator `10^30`, eliminating
repeated rational normalization during polynomial operations. Its full connection to the theta
definitions passes in `/tmp/hgt_first_atom_integer_enclosures.lean`. The earlier rational
certificate build was interrupted and exited with status 130; no Lean process from that build
remains. Only this task's obsolete enclosure olean/ilean were removed before the new support build.

The integer support olean/ilean build passed. The arithmetic module now uses explicit
`Enclosure.lower`/`Enclosure.upper` accessors and is undergoing its five `decide +kernel` checks.
After success: audit `/tmp/hgt_steinberg_axioms.lean` and `/tmp/hgt_first_atom_axioms.lean`, then run
the required direct final checks of both requested source files. Scratch files use the exact
`/tmp/hgt_*` names created during this task; remove only those files after completion.
