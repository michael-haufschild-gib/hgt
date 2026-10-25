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

The reusable implementation now lives in `QuadratureSeeds` (scalar and endpoint certificates),
`QuadratureCertificates` (cell certificate macro), and four `QuadratureCells{0,16,32,48}` modules.
These suffixes abbreviate `PrimeArchThetaFirstAtomQuadrature` in the filenames. Each cell module
contains sixteen cells. The macros expand to ordinary equality declarations; `cbv` produces
proof terms for their arithmetic. All six new modules are wired into the RHTower umbrella.
`QuadratureArithmetic` rewrites the five sums using the certified integer numerators before
kernel reduction. Seed compilation is pending after correcting syntax antiquotation around
field projections. Next checks: compile the certificate macro module, check the last-cell probe
`/tmp/hgt_last_cell_probe.lean`, then compile the four cell modules and arithmetic module.

Definition names in generated `rw` steps must use `$name:ident`, without parentheses; parentheses
make `rw` treat the definition as a value rather than unfold it. This correction is applied in
both seed and cell macros. Seed compilation is running in tool session 27927 (lake PID 87199,
Lean child 87299); wait for that owned process before starting another Lean command. Earlier
failed seed commands exited with code 1 and produced no olean. The minimal macro probe passed,
with an axiom-free integer equality. The static forbidden-token/raised-limit scan is clean.

That seed command was interrupted and exited 130 after a stack sample exposed repeated subtype
projection expansion inside `cbv`. Every certified-value rewrite now has an explicit `dsimp only`
of the referenced certificate before arithmetic normalization. Empty Horner tails use `change []`
instead of evaluating their unused polynomial argument. The updated seed build is running in
session 54451; session 27927 is closed. The sample is `/tmp/hgt_seed_sample.txt` (own scratch).

Session 54451 was interrupted cleanly (130) to isolate the first nonzero endpoint transition,
which the earlier cell-zero prototype did not exercise. `/tmp/hgt_seed_transition_probe.lean`
is a source copy with the endpoint loop restricted to indices 0 and 1 and axiom-print commands.
It is running in session 56059. The full source retains all 64 indices; no scope was removed.

The scalar seed normalizer now uses `norm_num` with explicit arithmetic definitions (the earlier
staged prototype already supported this for scalar operations). This avoids traversing rational
field-instance projections in `cbv`; polynomial cell operations still use `cbv`. Session 56059
exited 130 before replacing its scratch source. The updated first-transition probe is running in
session 44465. Wait for its result; after it passes, build the complete Seeds module, then
Certificates, the last-cell probe, Cells0/16/32/48, and Arithmetic, one Lean process at a time.

The first-transition probe passed (session 44465, exit 0). Both endpoint directions normalize to
literal integer bounds and depend only on `propext, Classical.choice, Quot.sound`.
The complete Seeds olean/ilean build is now running; its session is recorded in the tool transcript.

The complete Seeds build passed with no diagnostics (session 83986, exit 0). Its olean/ilean are
current. Certificates macro-module compilation is now running. The final five sum comparisons
use `norm_num [Enclosure.precision]` after rewriting to the certified integer numerators.

Certificates compiled without diagnostics (session 21390, exit 0). The last-cell probe is running
for all five moment rows at cell 63, including the largest lower and upper polynomial degrees.
It also checks the finite-sum rewrite names and prints transitive axioms for all five numerators.
Active Lean tool session: 50931. No other owned Lean process is running.

The last-cell probe failed at default recursion/simplification limits (session 50931, exit 1).
Its five final certificates therefore remain unproved. Finite-sum rewrite names were verified.
The final polynomial products are now split into one convolution row per equality certificate.
Only this task's obsolete Certificates olean/ilean were unlinked, and its updated macro module
is building in session 17463. The next last-cell probe also prints intermediate axiom sets to
identify any earlier stage requiring further splitting. No limits were raised.

The row-staged Certificates macro module compiled successfully (17463, exit 0). Its new
last-cell check is running in session 93103. Added intermediate axiom diagnostics distinguish
source/delta, Horner composition, Gibbs factors, prefactors, polynomial products, and integration.
One remaining optimization to consider if integration fails: its width-power rewrites should be
followed by `dsimp only` of the 58 width certificates before `cbv`, just like other cached values.

Probe 93103 finished with only the five integration certificates failing recursion depth. All
sources, deltas, Horner compositions, Gibbs factors, prefactors, and polynomial products at cell
63 have clean axiom sets. Explicit width-certificate reduction has now been added to integration.
The next compile is `/tmp/hgt_sum_div_probe.lean`, verifying a common-denominator rewrite for the
final sums; after it finishes, regenerate only the changed Certificates olean/ilean and recheck
the last cell. If width reduction does not suffice, split integration into short polynomial tails.

The common-denominator rewrite passed in `/tmp/hgt_sum_div_probe.lean` (48899, exit 0) and is now
used in Arithmetic before expanding the finite sums. The width-reduction Certificates rebuild
passed (2662, exit 0). The last-cell probe is now running with that version.

Width reduction alone did not resolve the five integration depth failures (59020, exit 1).
All polynomial certificates still have clean axiom sets. Integration now certifies descending
polynomial tails in blocks of at most eight coefficients, with each tail substituted by its
previously proved integer bounds. This preserves the exact recursive addition and division order.
Only the changed Certificates artifacts were unlinked; its new build is running in session 44871.
After it passes, rerun `/tmp/hgt_last_cell_probe.lean`; then compile all four Cells modules and
Arithmetic, and perform the two requested direct source/axiom audits. Full numerical completion
and final audits remain pending.

The eight-coefficient-tail Certificates module compiled successfully (44871, exit 0).
Current last-cell check: session 61016. The probe prints each integration-tail axiom set as well
as the polynomial and final numerator sets, so any remaining failure can be located precisely.

Probe 61016 failed: empty integration tails pass, but even the two-coefficient lower-order-two
tail at degrees 56–57 hits recursion depth. All polynomial certificates remain clean. Block size
therefore is not the root cause; `change` or a subsequent rewrite is expanding high width powers
before their cached certificates apply. `/tmp/hgt_integration_step_probe.lean` generates only the
already validated polynomials and gives that two-term integration proof explicit source lines.
Its current compile will identify the exact failing tactic. No owned Lean process from 61016
remains, and no cell-table olean has been built yet.

The focused probe (97466, exit 1) identifies `change` as the failure, before any cached width-power
rewrite. The new focused probe retains only the needed lower-order-two polynomial and replaces
`change` by two/eight explicit `rw [Enclosure.mass]` steps, followed immediately by the cached
tail and width rewrites. It tests both the final two coefficients and the preceding eight, with
precise source locations. Production Certificates still uses the unverified `change` version;
update it only after this focused rewrite succeeds.

The recurrence-only focused probe (74261) failed because rewriting `Enclosure.mass` could not
match through the polynomial certificate projections. The current probe, session 28036, first
uses `dsimp only [polynomialLo2_63, productLo2_63Row0]`, then the bounded recurrence rewrites.
It prints the polynomial axiom set before checking two- and eight-coefficient tails. The own
sample file `/tmp/hgt_integration_sample.txt` records proof-producing polynomial normalization;
remove it during cleanup. The production macro has not changed yet.

The final direct HT check passed (26180, exit 0): `exists_fin4_fourth`, index independence,
Milnor-to-Steinberg surjectivity, and the quotient-kernel equivalence all depend only on
`propext, Classical.choice, Quot.sound`. Temporary axiom-print commands were removed afterward.
The polynomial-projection probe (28036) still failed at recurrence rewriting. A small independent
probe `/tmp/hgt_mass_recurrence_probe.lean` (33032) checks equation lemmas and a synthetic
58-coefficient list before any further changes to production certificate generation.

The small explicit-equation probe (41885) showed the real mismatch: `List.drop` hides the cons
constructor from rewriting. The list-only probe (66303) passes after
`dsimp only [testPolynomial, List.drop]` and explicit `Enclosure.mass.eq_2` rewrites. The focused
real-polynomial probe now normalizes both its own list and the cached next-tail equation before
recurrence rewriting; width bounds remain substituted before arithmetic. It is checking the
two- and eight-coefficient tails again. Session 33032 was interrupted cleanly (130), and the
second sample `/tmp/hgt_mass_eq_sample.txt` shows import processing, not an arithmetic stall.

Current owned Lean session: 64771 (`/tmp/hgt_integration_step_probe.lean`). The production
Certificates macro now has the same list-tail normalization and explicit nonempty recurrence;
its existing olean/ilean are stale and must be unlinked before its next build. No cell-table
olean exists yet. Both own stack samples have been removed. Final HT audit is complete; PA
integration, all cells, the arithmetic sum module, and the final PA audit remain.

Focused probe 64771 reached the final scalar `cbv` but failed there with recursion depth; list
normalization and recurrence/cached-value rewrites now pass. Temporary module
`formal/HgtFirstAtomPolynomialProbe.lean` contains only the already proved lower-order-two
last-cell polynomial. Its olean/ilean build is session 64928, because the new scratch file
`/tmp/hgt_integration_cached_probe.lean` imports it. This avoids regenerating polynomial proofs
while isolating scalar integration. The cached probe traces the final expression and tries
`norm_num` for the remaining two scalar terms. Remove this temporary module and both its build
artifacts after completion; it is not a production module and is not wired into an umbrella.

The temporary polynomial cache built successfully (64928, exit 0). Its scalar-integration
consumer is now running in session 91829. Most obsolete `/tmp/hgt_*` files were removed by an
exact-name list; retain only `/tmp/hgt_last_cell_probe.lean`,
`/tmp/hgt_integration_step_probe.lean`, and `/tmp/hgt_integration_cached_probe.lean` until the
remaining checks finish. The temporary `formal/HgtFirstAtomPolynomialProbe.lean` and its two
build artifacts remain solely for this consumer.

Root cause found in 91829: the traced scalar expression contains the entire nested width-power
recurrence. `first_atom_widths` normalized its zero case without unfolding `Enclosure.pow`, so
its valid equality certificates carried unevaluated arithmetic instead of literal values.
The width-zero branch now explicitly rewrites `Enclosure.pow`, matching the already-correct
endpoint-power base case. Seeds olean/ilean were unlinked as own stale artifacts and are being
rebuilt in session 79079. Temporary print commands in Seeds inspect widths 0, 1, and 57 plus the
axioms of width 57; remove those diagnostics after success. The cached integration probe now
checks both two- and eight-coefficient tails with the production `cbv` scalar step and no large
trace output. Its polynomial cache does not use width certificates; all its arithmetic
references remain unchanged. No cell table has been built yet.
