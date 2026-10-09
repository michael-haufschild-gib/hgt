# Generic divergence under arbitrary precision envelopes

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings from this audit are recorded below.

## Target

Remove the remaining subcritical-exponential restriction from generic divergence in the closed unit ball of bounded error parameters. Preserve arbitrary finite history prefixes and allow any strictly positive coordinatewise precision envelope.

More general formulation: there exists a native threshold K such that for every bounded center and bounded weight q with q(k)!=0 at some k>=K, the histories H(u)=center+q*u have unbounded moment terms in every tail at every real shift for a dense residual set of parameters u in the closed supremum-norm unit ball. Signed summability at any real shift is then exceptional.

## Corpus audit

- Direct lexical search `research 'precision residual' --mode lexical --module WeilLogShift --no-refresh --json` returned exactly two eligible declarations, both from `WeilLogShiftExponentialPrecisionGenericity`: existing results restricted to rates below4-pi.
- Exhaustive rg across WeilLogShift sources found no arbitrary-envelope or fixed-direction genericity result.
- Current `WeilLogShiftUniformBallGenericity.lean` supplies the native countable open-tail-event argument through `HTGeometry.dense_and_residual_setOf_forall`, plus origin-to-all-shifts transfer.
- `WeilLogShiftImpulseLineObstruction.lean` proves at most one exceptional amplitude along each sufficiently late impulse line. `WeilLogShiftArbitraryPrecisionImpulse.lean` exposes the two-amplitude alternative and the exact one-coordinate envelope witness. Both leaves are compiled, axiom-audited and indexed; final verification is recorded in `docs/drafts/pipeline/3-formalized/weil-logshift-arbitrary-precision-impulse.md`.

## Paper proof

Fix k>=K with q(k)!=0. At any parameter u in the closed unit ball and any positive neighborhood radius, choose 0<delta<1 with2*delta smaller than that radius. The two parameters

`u_plus=(1-delta)*u+delta*unit(k)` and `u_minus=(1-delta)*u-delta*unit(k)`

both lie in the unit ball, since their norms are at most (1-delta)*norm(u)+delta<=1. Both are within2*delta of u. Their physical histories equal H((1-delta)*u) plus the two distinct impulse amplitudes delta*q(k) and -delta*q(k). The proved two-amplitude alternative gives unbounded moment terms in every tail at every shift for at least one of these histories. Thus the entire good parameter set is dense, including at boundary points of the ball.

Each origin tail-excursion event is open by continuity of bounded multiplication, the affine history map and the native moment coordinates. Each event contains the dense good parameter set and is therefore dense. Apply the existing countable open-dense-event theorem on the complete closed unit ball, followed by origin-to-all-shifts transfer. This proves the dense residual statement without any decay-rate restriction.

For arbitrary positive epsilon and prefix length M, define q(j)=0 for j<M and q(j)=min(1,epsilon(j)) otherwise. This is a bounded continuous function on discrete Nat, obeys0<=q(j)<=epsilon(j), and is positive at every j>=M. Any unit-ball parameter gives |H(u)(j)-center(j)|<=epsilon(j), with exact equality to center on the prefix. Choose k>=max(K,M) to discharge the nonzero-weight requirement.

## Required precision about topology

Genericity is in the supremum-norm closed unit ball of ERROR PARAMETERS. Multiplication by a vanishing envelope need not be open, so do not transfer residuality to its image with the ambient history topology. This is the same topology convention as the prior exponential-precision result.

## Plan

1. [x] Search current Lean corpus and inspect existing genericity mechanism.
2. [ ] Formalise generic bounded-weight perturbations and continuity.
3. [ ] Prove density using two ball-preserving impulse parameters.
4. [ ] Prove dense residual nowhere boundedness and nonsummability.
5. [ ] Specialise to arbitrary positive envelopes with exact finite prefixes, and remove the rate restriction for exponential envelopes as a corollary.
6. [ ] Compile affected leaves, audit public axioms, wire/index/lint, persist and clean scratch.

No theorem for this genericity extension is currently formalised. Strict alternating signs and quadratic-exponent coefficient growth remain separate exposed conjectures.

## Current log

- 2026-10-09 — Fresh corpus search for bounded weights, envelopes, genericity and fixed impulses returned the existing impulse and exponential-precision APIs, with no duplicate arbitrary-weight theorem (fts5,196 hits,81 eligible across46 modules; lexical output has no partial/coverage fields). Current weighted exponential definitions and the native open-dense-event proof were inspected.
- Planned leaves: `WeilLogShiftWeightedGenericity.lean` for bounded multiplication, fixed-impulse density and residual divergence; `WeilLogShiftArbitraryPrecisionGenericity.lean` for capped prefix envelopes, exact error/prefix bounds and all-rate exponential corollaries. Existing exponential APIs remain unchanged; the all-rate corollary must use their exact original parameter family, not merely a capped subfamily.
- The density proof will use parameters `(1-delta)*u+t*unit(k)` for t=+/-delta. The common bounds norm<=1 and distance<=2delta follow directly from norm triangle inequalities. This avoids exposing or changing older private ball-perturbation helpers.

## Implementation checkpoint — 2026-10-09

- Added `WeilLogShiftWeightedGenericity.lean`: weighted affine family, impulse identity, direct density in the closed supremum unit ball, countable open excursion sets, residuality, signed nonsummability, and meagre exceptions. One sufficiently late nonzero weight is enough; no lower bound on its magnitude is assumed.
- Added `WeilLogShiftArbitraryPrecisionGenericity.lean`: capped positive profile with exact finite prefix, componentwise error bound for every parameter, genericity and meagre exceptions, and exact identification with the original exponential family for all nonnegative decay rates.
- Both leaves wired into `RHTower.lean`. Initial weighted compile exposed two subtype-distance coercions; corrected by changing to ambient distance and rewriting `dist_eq_norm`. Final compilation and axiom audit pending.
- Genericity remains explicitly in error-parameter supremum topology. No image-topology transfer is claimed.

### New conjecture exposed: genericity in the actual feasible history set

A stronger statement appears accessible by a separate argument: equip
`{h : BCF | (∀ j < M, h j = center j) ∧ ∀ j, |h j - center j| ≤ ε j}`
with its inherited supremum metric, where every `ε j > 0`. This set is closed in the complete BCF space; no boundedness of the profile is needed. For a late coordinate `k ≥ max(K,M)`, put `a = h k - center k`. Given radius `η > 0`, take `δ = min(1/2, η/(4*ε k))` and the two physical impulses `t± = δ*(±ε k-a)`. They are distinct since `δ>0` and `ε k>0`. Each changed coordinate has error `(1-δ)*a ± δ*ε k`, hence absolute error at most `ε k`, and every other coordinate is unchanged. Each history lies within distance at most `2*δ*ε k < η` of `h`. The native two-amplitude alternative makes at least one history nowhere bounded. Thus each origin excursion set is open dense in this complete feasible set; Baire and the native shift transfer give dense residual nowhere boundedness and nowhere signed summability in the actual history topology.

This is an independent direct-density proof, not an inference that multiplication by a vanishing weight is open. Paper argument recorded; no Lean claim yet. Before formalising, audit this exact feasible-set statement against the local corpus and create its own card.

## Final audit — 2026-10-09

Both leaf modules compile and export cleanly with `lake --old env lean <module> -o <olean>`. A scratch-file `#print axioms` audit covers all 24 public declarations (20 theorems, four definitions): every declaration uses exactly `propext`, `Classical.choice`, and `Quot.sound`; no errors or warnings. Both umbrella imports are unique. `scripts/formal_tools.py index` succeeded, and all 24 public declarations appear in `formal/LEAN_API.md`. Global `scripts/formal_tools.py lint` reports 22 unrelated HTGeometry modules unreachable from their theorem-area umbrella, with no findings in either new leaf. No full build, external source, numerical experiment, heartbeat increase, or old API change.

The arbitrary-weight parameter theorem, every-positive-profile exact-prefix corollaries, and all-rate corollaries for the exact original exponential family are complete. The separate actual-feasible-history topology conjecture above was subsequently formalized and kernel-audited in `WeilLogShiftPrecisionFeasibleSet.lean` and `WeilLogShiftPrecisionFeasibleGenericity.lean`; see `docs/drafts/pipeline/3-formalized/weil-logshift-feasible-history-genericity.md`.
