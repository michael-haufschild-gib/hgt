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
not the Xi route. Scratch verification is in progress; do not count it as a new
research contribution.

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
   polynomial `A_K(w)=prod_{v in V}(1-w/v)` has `A_K(0)=1` and cancels every
   nonroot critical pole in K by (1). It is entire and D_A is analytic near K.
3. At any Xi zero rho, `D_A(rho)=N(rho)=rho`. Differentiating
   `D_A=s-A(xi)(s-N)` gives `D_A'(rho)=N'(rho)`, since A(0)=1 and
   `rho-N(rho)=0`. This preserves the local Newton first jet at every root,
   without assuming simplicity.
4. No continuous A at 0 with A(0)=1 can remove all sufficiently high critical
   poles. Continuity gives epsilon>0 on which A is nonzero. The actual Xi
   critical-value accumulation theorem supplies p above any prescribed T with
   a nonzero xi-value in that neighborhood. The necessary condition in (1)
   fails. In particular no entire normalized scalar damping is globally analytic.

This is a dependency-closed finite-repair/global-obstruction argument. It does
**not** supply line-centered invariant discs or the arithmetic source sign. It
must not be counted as fulfilling the requested significant advance. The
strongest positive survivor currently identified is explicit compact-region
pole cancellation preserving all root first jets; Lean verification is pending.

## Next conjecture

A successful desingularization must use more than the value xi(s), or must
abandon normalized holomorphic dependence at the accumulating critical value.
The remaining task is a source-derived derivative-sensitive construction with
an invariant-region law. Arbitrary entire interpolation would not supply that
law and is rejected as a replacement endpoint.

## Status

XN remains open. No route has been credited toward the full thread goal.
