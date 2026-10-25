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

The integer support olean/ilean build passed. The arithmetic module uses explicit
`Enclosure.lower`/`Enclosure.upper` accessors. Whole-sum kernel reduction was interrupted (exit
130); the next refinement is separate normalized cell certificates, checked using `norm_num`,
so final comparisons use small certified integer literals. The current probe is
`/tmp/hgt_cell_certificate_probe.lean`. No proof is being treated as complete from the interrupted
whole-sum checks. Whole-cell normalization also reaches the default heartbeat limit, so the
certificate is split further into scalar powers, endpoints, Horner composition steps,
polynomial products, and integration. `/tmp/hgt_make_staged_probe.py` generates the current
`/tmp/hgt_staged_cell_probe.lean` test. It uses `simp only` for certified-value rewrites to avoid
rewriting the dependent predicates of subtype projections, and retains the original Nat-to-Rat
casts in polynomial arguments. Small normalization steps close both the value metavariable and
its equality proof; no trailing `rfl` is needed.

The staged first cell now passes with proof-producing `cbv` at default limits. Its certified lower
numerator is `27845471003506338891421314919` over `10^30`; `#print axioms raw00` lists only
`propext, Classical.choice, Quot.sound`. `norm_num` exceeded the default heartbeat limit on a
large Horner multiplication; `cbv` handles these separate polynomial operations without changing
any limits. Full-cell `cbv` exceeded its default step count, so the intermediate certificates remain
necessary. Next: reusable seed/endpoint certificates, all five rows of 64 cell certificates, then
small kernel-checked sums.
After success: audit `/tmp/hgt_steinberg_axioms.lean` and `/tmp/hgt_first_atom_axioms.lean`, then run
the required direct final checks of both requested source files. Scratch files use the exact
`/tmp/hgt_*` names created during this task; remove only those files after completion.
