# XN scalar damping: verified partial result, full goal still active

## Scope and status
User requests one new route/candidate per turn, significant obstruction-removing RH contributions for all 21 live routes and 23 candidates. XN was attempted this turn. No qualifying frontier advance achieved; no route credited. Keep full goal active; next turn choose a different route/candidate. No external novelty claim, web, numerical experiment, map edits, commit, or push by this session.

Persistent card: `docs/drafts/pipeline/1-in-progress/xn-source-interior-obstruction-2026-10-17.md`. Frontier map read-only, SHA-256 `6e287eaa43d5ee46e7e0ce07051102706936fbd38604e06d7423c895b717da1c`.

## Verified module
`formal/GaloisForLFunctions/RHTower/XiNewtonScalarDamping.lean`, imported into `RHTower.lean`. Namespace `RHTower.XiNewtonCriticalLine`. Define `scalarDampedXiNewton A z = z - A (xi z) * xi z / deriv xi z`.

Eight public results:
- `analyticAt_scalarDampedXiNewton_iff`: for entire A, analytic at p iff xi(p)=0 or xi'(p)≠0 or A(xi(p))=0.
- `scalarDampedXiNewton_root_jet`: A(0)=1 preserves every Xi root and its original Newton derivative, including multiple roots.
- `scalarDampedXiNewton_high_pole`: normalized entire A retains arbitrarily high noncontinuous critical-line poles.
- `no_entire_normalized_scalarDampedXiNewton`: no normalized entire scalar damping yields an entire map.
- `scalarDampedXiNewton_high_pole_of_ne_zero`: every nonzero entire A retains arbitrarily high noncontinuous critical poles.
- `differentiable_scalarDampedXiNewton_iff`: entire damped map iff A=0.
- `scalarDampedXiNewton_lineReflect`: Schwarz-real A yields critical-line reflection equivariance.
- `exists_polynomial_scalarDampedXiNewton_on_closedBall`: for every real R, an explicit normalized polynomial cancels all critical poles near closedBall 0 R, preserves reflection and every root first jet. Product pairs factors for each nonzero critical Xi value v and conjugate v.

Key actual-Xi input: `RHTower.exists_high_nonzero_small_xi_critical_value` from `XiCriticalValueAccumulation`. Nonzero Xi critical values accumulate at 0 at unbounded heights. Entire A nonzero cannot vanish on those values by isolated zeros.

## Limits and next conjecture
Finite pole cancellation leaves critical points fixed. A self-map disc containing a Xi root and a distinct cancelled critical point still contradicts two-fixed-point Schwarz rigidity. No invariant disc or arithmetic source sign constructed. The result is partial structural work, not requested significant RH frontier advance. Generic regularity-plus-root-attraction conjecture falsified by f=z²−1, T=(3z−z³)/2; not counted as research progress.

C3 remains unproved: continuous controller of raw pair (xi,xi') may face incompatible limits at high simple roots and nonroot critical points. Xi derivative vertical decay is a potential input, not a proof. Do not state C3 as theorem or assume enough high simple roots.

## Validation
Targeted foreground final command from formal:
`lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/XiNewtonScalarDamping.olean GaloisForLFunctions/RHTower/XiNewtonScalarDamping.lean` passed (exit 0).
Separate `/tmp` import with #print axioms for all eight public theorems passed; only `[propext, Classical.choice, Quot.sound]`. No proof placeholders, added axioms, unsafe declarations, or heartbeat options. git diff --check passed. index command passed and recorded declarations.
Global `scripts/formal_tools.py lint --check-generated` failed from concurrent out-of-scope unreachable modules CHMDBVUniformConvergence, CHMDBVUniformGraph, MobiusDivisorCriticalBVProfile, ThetaCuspRatioBoundaryNormOrientation, BoundedVariationNormAlgebra, BoundedVariationPrimitive, BoundedVariationUniformJump, plus stale generated LEAN_API/LEAN_OVERVIEW. Do not claim global gate passed or edit those sessions' modules. Shared worktree has concurrent edits/commits; preserve all unrelated work.

All own Lean/search/index/lint handles terminated; exact owned scratch files are being removed after audit. No full builds run. Local research coverage mostly source-only; semantic coverage unavailable; last scalar query partial but useful hits independently verified.