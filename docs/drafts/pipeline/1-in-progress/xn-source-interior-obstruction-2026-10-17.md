# XN: source control of the Newton-disc interior

- **ID:** XN-INTERIOR-20261017
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** XN — Xi Newton invariant discs
- **Statement:** Seek an unconditional arithmetic mechanism constructing line-centered invariant discs covering Xi zeros, with the interior curvature and nonroot critical poles paid explicitly.

## Goal and scope

One route this turn. The full thread goal remains a significant obstruction-removing contribution for every live route and candidate in the read-only frontier map. No contribution is counted from formalization alone, a new RH receiver, or an improved bound.

Use local Lean statements and proofs as mathematical evidence; no web, literature audit, numerical experiment, full build, new axioms, or hidden source premise. Preserve unrelated worktree changes. The frontier-map SHA-256 at entry is `6e287eaa43d5ee46e7e0ce07051102706936fbd38604e06d7423c895b717da1c`.

## Plan

1. Inspect the actual XN source and search the whole Lean corpus for mechanisms paying the interior defect.
2. State and attack exact conjectures; reject generic maximum-principle repackaging, circular source assumptions, and already-proved claims.
3. Complete a dependency-closed paper proof before adding any theorem.
4. Audit any resulting module with targeted foreground Lean, umbrella wiring, axiom inspection, and formal lint. Keep the overall goal active unless all requested routes are complete.

`update_plan` is unavailable in this tool session; this card holds the executable plan.

## Verified starting frontier

- `XiNewtonDiscCurvature.laplacian_xiNewtonDiscMargin`: the exact Laplacian is `4 (r² - |z-c|²) |xi''(z)|²`, hence nonnegative inside the disc.
- `XiNewtonDiscSourceMargin`: local boundedness/analyticity of the totalized Newton map holds precisely at Xi zeros or points with nonzero derivative; the quotient-free source margin exactly describes disc self-mapping.
- `XiNewtonCriticalPoleExclusion`: every nonroot critical point must lie strictly outside a certified closed disc; the central point `1/2` is always a genuine Newton pole despite being fixed by the totalized expression.

## Conjecture loop

The first question is whether Xi-specific source structure can pay the interior defect. Boundary positivity by itself is insufficient: a nonroot critical pole has negative margin. Pole exclusion plus boundary positivity would only invoke a generic maximum principle; it does not by itself meet the requested contribution threshold.

### C1: regularity plus root attraction produces symmetric discs

**Verdict: FALSE as a source-independent mechanism.** In centered coordinates,
`f(z)=z²-1` has Newton map `N(z)=z-f(z)/f'(z)`. The entire repair
`T(z)=(3z-z³)/2=z-z² f(z)/f'(z)` removes the pole, commutes with
`z ↦ -conj(z)`, fixes both roots, and has derivative zero at both. No
origin-centered disc containing the roots can map into itself under T: the
corpus's two-fixed-point Schwarz rigidity would make T the identity on that
disc, contradicting its derivative at 1. This rules out the proposed inference,
not the Xi route. Scratch Lean verification passed with only `propext`,
`Classical.choice`, and `Quot.sound`; do not count this generic counterexample
as a new research contribution.

### C2: normalized scalar damping of the actual Xi Newton map

Consider `D_A(s)=s-A(xi(s))*xi(s)/xi'(s)` for an entire A with `A(0)=1`.
The normalization preserves the original Newton first jet at every Xi zero,
including multiple zeros. Can one choose A to remove all nonroot critical poles?

The actual corpus supplies the decisive input:
`XiCriticalValueAccumulation.exists_high_nonzero_small_xi_critical_value`.
For every T and epsilon>0 there is p on the critical line above T with
`xi'(p)=0` and `0<|xi(p)|<epsilon`.

**Paper statement and proof.**

1. Exact local cancellation: D_A is analytic at p iff
   `xi(p)=0` or `xi'(p)≠0` or `A(xi(p))=0`.
   The first two cases use the already analytic original Newton map and
   `D_A=s-A(xi)(s-N)`. If `v=xi(p)` and `A(v)=0`, write
   `A(w)=(w-v)B(w)` using the entire divided difference of A. The Newton map
   of `xi-v` is analytic near p because p is an isolated zero. Thus
   `(xi-v)/xi'` is analytic and vanishes at p, and multiplying by `B(xi)*xi`
   gives the totalized formula D_A, including at p. Conversely, continuity
   of D_A and of xi' extends
   `A(xi(s))*xi(s)=(s-D_A(s))*xi'(s)` from the punctured neighborhood to p.
   If xi'(p)=0, its left side must vanish.
2. For any compact K, xi' has finitely many zeros in K by isolated zeros and
   compactness. Let V be the finite set of their nonzero xi-values. The explicit
   polynomial `A_K(w)=prod_{v in V}(1-w/v)(1-w/conj(v))` has `A_K(0)=1` and cancels every
   nonroot critical pole in K by (1). It is entire and D_A is analytic near K.
   Each paired factor is Schwarz real, hence so is A_K. Xi's reflection law
   then makes D_A commute with reflection in the critical line. Pairing adds
   harmless repeated factors when a critical value is real.
3. At any Xi zero rho, `D_A(rho)=N(rho)=rho`. Differentiating
   `D_A=s-A(xi)(s-N)` gives `D_A'(rho)=N'(rho)`, since A(0)=1 and
   `rho-N(rho)=0`. This preserves the local Newton first jet at every root,
   without assuming simplicity.
4. No entire A with A(0)=1 can remove all sufficiently high critical
   poles. Continuity gives epsilon>0 on which A is nonzero. The actual Xi
   critical-value accumulation theorem supplies p above any prescribed T with
   a nonzero xi-value in that neighborhood. The necessary condition in (1)
   fails. In particular no entire normalized scalar damping is globally analytic.
5. In fact the globally analytic scalar dampings are exactly `A=0`. If a
   nonzero entire A vanished on a neighborhood of 0, the identity theorem would
   make it identically zero. Otherwise isolated zeros give a punctured disk
   around 0 on which A is nonzero. A nonzero Xi critical value lies in that disk
   at arbitrarily large height, so (1) again forces a pole. Conversely A=0 gives
   the identity map. No quantitative estimate is used in this classification.

This is a dependency-closed finite-repair/global-obstruction argument. It does
**not** supply line-centered invariant discs or the arithmetic source sign. It
must not be counted as fulfilling the requested significant advance. The
strongest positive survivor is explicit compact-region pole cancellation
preserving reflection and all root first jets. Its working-tree module is
`formal/GaloisForLFunctions/RHTower/XiNewtonScalarDamping.lean`, wired into
`RHTower.lean`; final module and axiom audits passed.

Cancellation still fixes each cancelled critical point: the totalized quotient
is zero there, and the proved analytic extension agrees with that value. A disc
containing both a Xi zero and a distinct cancelled critical point would have
two fixed points. Schwarz rigidity would force the repaired map to be the
identity on that disc. Near the Xi zero, A(xi) is nonzero by A(0)=1, while xi
and xi' are nonzero on a sufficiently small punctured neighborhood. The
identity would then force the nonzero Newton displacement to vanish, a
contradiction. Thus this scalar repair does not remove the geometric
critical-point obstruction; no requested significant advance is claimed.

## Search coverage

Whole-corpus deep searches covered Newton-disc source derivatives, critical
points and signed theta covariance, and entire interpolation. Their returned
declarations/source arguments were treated as leads and checked in Lean
source. Compiler coverage was predominantly source-only and semantic coverage
was reported unavailable. The final scalar-damping search returned useful
critical-value hits but was partial (`text_retrieval: interrupted`). Exhaustive
`rg` searches located the actual XN modules and critical-value accumulation
uses. No external search or novelty claim was made.

## Next conjecture

A successful desingularization must use more than the value xi(s), or must
abandon normalized holomorphic dependence at the accumulating critical value.
Derivative dependence is not yet a solution: the corpus also gives vertical
decay of Xi's first derivative (`XiCDerivStripDecay`). A continuous controller of
the two raw values `(xi,xi')` may be forced to incompatible limits along high
simple roots and high nonroot critical points. This is a new conjecture requiring
its own full paper and Lean audit; it is not asserted as proved.

The remaining positive target is a source-derived construction with an
invariant-region law. Arbitrary entire interpolation supplies no such law and
is rejected as a replacement endpoint.

## Verification

- Targeted final check, from `formal/`, exited 0:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/XiNewtonScalarDamping.olean GaloisForLFunctions/RHTower/XiNewtonScalarDamping.lean`.
- A separate `/tmp` import and `#print axioms` audit of all eight public theorems
  exited 0. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py index` exited 0 and indexed the new declarations.
- `scripts/formal_tools.py lint --check-generated` exited 1. Concurrent,
  out-of-scope modules were unreachable from their theorem-area umbrellas:
  `CHMDBVUniformConvergence`, `CHMDBVUniformGraph`,
  `MobiusDivisorCriticalBVProfile`, `ThetaCuspRatioBoundaryNormOrientation`,
  `BoundedVariationNormAlgebra`, `BoundedVariationPrimitive`, and
  `BoundedVariationUniformJump`. Generated `formal/LEAN_API.md` and
  `formal/LEAN_OVERVIEW.md` were also stale after concurrent source changes.
  No lint error identified the new XN module. Global lint is not claimed to pass.
- `git diff --check` passed. The new module contains no forbidden proof
  placeholder, added axiom, unsafe declaration, or heartbeat override.
- The frontier-map SHA-256 remained identical to its entry value. No web,
  numerical experiment, full build, commit, or push was performed for this work.

## Status

The exact scalar-damping classification and constructive finite-region survivor
have paper proofs and verified Lean proofs. XN's invariant-region/source-sign
obstruction remains open. This does not meet the requested significant frontier
advance; no route has been credited toward the full thread goal. The goal stays
active. Per the one-new-route-per-turn instruction, select a different route or
candidate next turn and retain XN as unfinished.
