# EGC: complete-copy expanding-contour source

- **ID:** egc-expanding-contour-source-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only EGC entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN CORE] Obtain the expanding-contour passage from the literal shifted source while retaining every multiplicity copy, residue, and sign.

## Goal and plan

This turn concerns EGC only. Earlier thread attempts: XN, HF, IRK, with no qualifying frontier advance credited. The full 44-route objective remains active. An improved estimate, another receiver, or a reformulated RH criterion does not qualify.

1. Inspect current Lean sources and corpus search for the actual missing contour passage; no web or old research Markdown.
2. Conjecture a concrete source construction, attack its analytic and sign requirements, and record failures without retiring the route prematurely.
3. Give a dependency-closed paper proof before new Lean code.
4. Formalize surviving source theorems without extra analytic premises, axioms, computations, or heartbeat changes.
5. Run one owned foreground Lean check at a time, audit axioms in `/tmp`, wire finished modules, run formal lint, and clean owned scratch.

## Current evidence

`PaperEGCCompleteCorrection` already states uniform exhaustion over its entire small-parameter/unbounded-height cylinder and fixed-parameter decay at both vertical ends. The next task is to inspect the exact source domain and correction before proposing any strengthened passage.

## Status

- [x] EGC selected; frontier map read-only.
- [ ] Significant obstacle-removing construction proved.
- [x] Exact inner-contour survivor formalized and verified.
- [ ] User's strict contribution criterion met.

## Conjecture and dependency-closed paper proof

Let `L = XiC'/XiC`, `K_e(a,w) = (a-w)^2 / ((a-w)^2-e^2)`,
and `C_e(w,a) = -e/[2(a-w-e)] + e/[2(a-w+e)]`.
For a source-admissible rectangle `R`, write `S_R` for every enclosed
multiplicity copy. Suppose both prescribed poles `p=w+e`, `q=w-e` are
strict interior and regular for XiC. The literal normalized source contour
satisfies

`I_R(e,w) = sum_(a in S_R) K_e(a,w) + (e/2)(L(p)-L(q))`.

For `|e|,|Re w| <= 1`, the complete source difference is the already
constructed absolutely summable row `C(e,w)`. Since `K_e(a,w)+C_e(w,a)=1`,

`I_R(e,w) = #S_R + C(e,w) - sum_(a in S_R) C_e(w,a)`.

Thus the contour minus its exact integer mass is precisely the exterior-copy
correction, not the full centered correction (which is strictly negative).

Proof:
1. Use `exists_xiC_closedRectangle_factorization` to factor XiC into its exact
   finite interior divisor times an entire cofactor nonvanishing near R.
   Boundary admissibility excludes boundary zeros, so all peeled zeros are
   strict interior.
2. `rectIntegral_mul_inv_sub_mul_logDeriv_multi_zero` with constant weight
   gives the Cauchy-weighted log-derivative integral at p and q, including
   the actual values L(p), L(q). The unweighted rectangle argument principle
   gives the interior mass.
3. Insert the exact resolvent decomposition of K. All three terms are
   continuous on the four edges (XiC and the prescribed denominators are
   nonzero there), so ordinary finite linearity of contour integrals applies.
   Combine the finite sums and retain both source values with their signs.
4. Apply `paperEGCCompleteCorrection_eq_logDeriv`. Pole regularity follows
   from the certified native spectral gap. Combine each enclosed K with its
   own C to get 1. Multiplicities are retained through
   `sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum`.
5. Existing uniform convergence of the complete C row gives a finite cutoff
   F for any positive tolerance, simultaneously for all small shifts, small
   real offsets and every imaginary height. Every admissible R containing F
   and the two prescribed poles then has contour-minus-mass within tolerance.
   No infinite sum is interchanged with a contour integral.
6. Unconditional nonvacuity/cofinality: choose an actual copy a and its
   functional-equation reflection. Their real coordinates straddle
   [-2,2] by the spectral gap; their imaginary coordinates straddle zero.
   Adjoin these copies and F to any requested finite packet, then use the
   existing admissible-rectangle constructor. The resulting rectangle
   contains every centered prescribed pole for |e|,|x|<=1. Hence the uniform
   contour passage has an actual cofinal source realization.

## Adversarial audit

This resolves the enclosed-pole contour passage by exact cancellation, not by
discarding a residue or imposing a decay hypothesis. It also exposes a loss
of information: enclosed copies leave unit mass irrespective of their
distance from the critical line. The outer covariance still ranges across
expanding real coordinates, outside the fixed real observation strip.
This result alone does not establish the user's required significant RH
advance; no such credit is assigned. The route is not retired.

Search: initial deep query completed in 88 seconds, partial=false, indexed
inventory complete but compiler coverage mostly source-only/stale and refresh
deferred to the running background indexer. Its broad semantic candidates
were mostly irrelevant. Focused lexical search for meromorphicCauchyPair
returned 24 declarations; concrete source files supplied the proof above.
No mathematical evidence was taken from search prose/old research Markdown.

## Second conjecture: does cofinal cancellation preserve pair charge?

Candidate: after the full shifted-pole correction is retained and the source
contours exhaust the divisor, their vanishing renormalized contour can force
the rational off-diagonal pair charge to vanish.

Failure mechanism: the exact identity above cancels `K_e(a,w)` against the
matching shifted residue `C_e(w,a)` for each enclosed copy, leaving 1 before
any limit. Therefore this cancellation by itself retains only multiplicity
mass, independently of the copy's real or nonreal spectral coordinate.
The strict centered negative correction cannot be silently replaced by zero;
it is canceled by the finite row's matching excess over unit mass.

Survivor: the literal source contour has an exact exterior-copy defect and
an unconditional cofinal realization. A successful outer argument must
identify a surviving off-line-sensitive term rather than reusing this inner
unit-mass cancellation as a sign argument. No outer sign, global expanding
real-observation control, RH equivalence, or claimed RH proof is supplied.

## Formal progress

`PaperEGCEnclosedPoleCancellation.lean` passes its final focused Lean audit.
It proves the exact enclosed-pole source identity, exact full-copy tail
identity, one uniform cofinal cutoff, and unconditional source rectangles
containing every requested packet and every centered prescribed shift.
The tail is also identified literally with the tsum over every exterior
multiplicity copy. No qualifying frontier credit assigned.

## Final verification

- Canonical audit, exit 0 with no warnings:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.olean GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.lean`
- All six public theorem axiom audits passed: only `propext`,
  `Classical.choice`, `Quot.sound`. Audit file stayed in `/tmp`.
- Separate mathlib API scratch passed, including the uniform-convergence
  and finite/complement summation APIs. No numerical experiments.
- Wired into `GaloisForLFunctions/RHTower.lean` after `PaperEGCSourceLanding`.
  No full or umbrella build, no heartbeat increases, no added axioms or debt.
- `scripts/formal_tools.py index` passed twice. The second refresh addressed
  metadata changed by concurrent work during the first lint.
- Final `scripts/formal_tools.py lint --check-generated` exited 1 on unrelated
  concurrent work: unreachable `PrimeLogLaplaceClosedGraphLiteral`,
  `ZeroAlgebraJetInvariantForms`, `BurnolWeightedShiftStrongContinuity`;
  `ZeroAlgebraJetInvariantForms.lean:382` has `sorry` in
  `exists_posDef_invariantForm`; `formal/LEAN_OVERVIEW.md` changed again and
  was reported stale. No error named the EGC module. This is not a globally
  passing lint result.
- Whitespace checks passed. All owned `/tmp/hgt_egc_*` scratch removed and
  absence verified. No owned jobs remain. Canonical compiled module retained.
- Frontier map was not edited by this attempt. Other sessions changed shared
  files during the work; no claim that the shared worktree stayed unchanged.

The original 44-route objective remains incomplete and active. Attempted in
this thread: XN, HF, IRK, EGC. None is credited with the user's strict
obstacle-removing RH advance. EGC's expanding real-observation outer
covariance and its surviving off-line-sensitive source sign remain open.
