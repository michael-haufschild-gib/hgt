# Mass-shifted cofinal positive-schedule rate no-go (2026-08-12)

Formalized module:
`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean`

## New closed knowledge

1. `fixedDegreePositiveLimit_negative_degreeDiagonal`: closed delayed-switch countermodel. Every fixed degree tends to positive limit 1 as mass tends to infinity, while degree-matched diagonal is strictly negative at every grade. Pointwise fixed-degree recession has no diagonal upper-rate content.

2. `exists_xiShiftedCofinalPositiveProjectiveSchedule_above (g)`: for every lower floor `g : ℕ → ℝ`, an unconditional schedule `w(n) ≥ max(n,g(n))` tends to infinity, has actual degree-`n+2` shifted-Xi Hankel block positive definite, and has projective Gauss-root spread tending to infinity.

3. `exists_xiShiftedCofinalPositiveSchedule_spread_and_harmonicWork`: one unconditional schedule simultaneously has positive degree-matched blocks, divergent spread, and harmonic lower bound for literal projective arithmetic surplus at every grade ≥2.

## Scientific conclusion

Cofinal positivity, divergent spread, harmonic source work, and any arbitrarily fast lower escape requirement are all RH-blind far-right recession data. Missing mass-shifted spectral-face datum is restricted diagonal effectivity: an *upper* mass/degree admission rate (e.g. parabolic synchronization), uniform degree-dependent smallest-eigenvalue bound, or equivalent mechanism derived from completed adaptive arithmetic producer. This is effectivity/admission obstruction, not finite-observer orientation loss.

Heavy conjecture loop:
- no cofinal schedule from fixed-degree positivity: failed;
- spread detects off-line zeros: failed;
- faster lower escape restores detection: failed;
- pointwise recession yields upper rate: logically refuted by delayed-switch model.

Paper card:
`docs/drafts/pipeline/3-formalized/mass-shifted-cofinal-positive-schedule-no-go.md`
Route report: equations (9.3.683)–(9.3.687).

Verification: direct Lean and targeted module build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Repository lint failure is unrelated/concurrent unwired RHTower/Sieve modules; new module is wired in `RHTower.lean` and contains no forbidden declarations.