# Exact amplitude cost and budget feasibility

Status: formalized; direct leaf and axiom audits passed, 2026-10-09.

## Corpus evidence

Only local Lean corpus consulted. `WeilLogShiftSharpDualProfile` supplies
evaluation ℓ_y and its sharp C₀ norm profile q(y). `WeilLogShiftSharpDualReceiver`
supplies a single normalization on the actual regular coefficient subspace,
with HasSum at every shift. Local search also found the Hilbert/matrix minimum
cost constructions in `ConstraintFrameRelativity/FrameFillingCapacity` and
`ConstraintMotiveRelativity/CompactObserverHorizon`. Those require inner product
structure; the current amplitude norm is arbitrary. No external novelty claim.

## Paper proof

Let E be a finite-dimensional real normed space and f:E→Lℝ a functional.
The closed unit ball is compact and nonempty, so |f| attains its maximum at v.
Its maximum equals ‖f‖: the operator bound gives ≤, and if the maximum were
smaller, the local mathlib theorem `exists_lt_apply_of_lt_opNorm` would give
a point in the open unit ball with a larger value. Thus ‖v‖≤1 and |f(v)|=‖f‖.

If ‖f‖>0, the operator bound forces ‖v‖=1. For response r, set
a=(r/f(v))v. Then f(a)=r and ‖a‖=|r|/‖f‖. Every other b with f(b)=r obeys
|r|≤‖f‖‖b‖, so a has minimum norm. If ‖f‖=0, f=0 and only r=0 is feasible;
the zero amplitude attains its minimum cost 0. No uniqueness is claimed for
an arbitrary norm.

Consequently, for every real budget A (including negative budgets),

    (∃a, f(a)=r and ‖a‖≤A) iff 0≤A and |r|≤A‖f‖.

Necessity is the operator bound. For sufficiency split ‖f‖=0 (forcing r=0)
and ‖f‖>0, then use the minimizer and divide the budget inequality by ‖f‖.
This formulation handles invisible shifts and zero-dimensional amplitude
spaces without any nonvanishing premise.

Apply the classification to the actual normalized receiver's ℓ_y. Replace
the response equality by HasSum of the literal normalized paired-kernel
series: its existing HasSum contract makes these equivalent by uniqueness
of sums. Obtain both exact budget feasibility and attained minimum cost for
every shift and every response, under one common normalization. No added
analytic premise, inner product, or unique minimizer is assumed.

## Intended value

Previous amplitude escape becomes an exact inverse sensitivity law: cost
is |r|/q(y), with explicit infeasibility at zeros of q. The budget criterion
is unconditional and usable directly against the convergent native series.

## Work log

- [x] Local corpus and relevant predecessor/API source checked.
- [x] Paper proof recorded before implementation.
- [x] Verify API names in /tmp scratch Lean file.
- [x] Prove norm attainment and exact scalar-functional response classification.
- [x] Specialize actual receiver, retaining literal HasSum contracts.
- [x] Direct leaf checks, umbrella wiring, all-declaration axiom audit.
- [x] Index, lint, record results, clean owned scratch files.

## Formal declarations

`formal/GaloisForLFunctions/RHTower/WeilLogShiftExactResponseCost.lean`:

- `exists_finiteDimensional_dual_norm_attainer`: a norm attainer in the closed
  unit ball, without requiring a nontrivial amplitude space.
- `finiteDimensional_dual_minimum_response_iff`: a minimizer with cost
  |r|/‖f‖ exists exactly when r=0 or ‖f‖>0.
- `finiteDimensional_dual_response_budget_iff`: feasibility within any real
  budget A is exactly 0≤A and |r|≤A‖f‖.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftExactResponseReceiver.lean`:

- `exists_weilLogShift_exact_response_cost`: one normalization and a
  nonnegative C₀ profile give both classifications for literal HasSum
  responses, on the actual regular subspace, simultaneously at every shift.

## Verification

Both final `lake --old env lean <leaf> -o <olean>` checks exited 0 without
warnings. All four public declarations passed a /tmp `#print axioms` audit;
each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
Both umbrella imports occur exactly once; both oleans postdate their sources.
`scripts/formal_tools.py index` exited 0. Module-filtered local search returned
all four declarations in the intended modules.

Final `scripts/formal_tools.py lint` exited 1 with exactly eight unrelated
unreachable-module errors, and no proof-debt errors:

- `HTGeometry.LaguerrePolyaImaginaryAxisBounds`
- `HTGeometry.PaperHomogeneousGeneratorIdeal`
- `HTGeometry.PaperSegreNormalEmbedding`
- `HTGeometry.PaperSegreNormalRelations`
- `HTGeometry.QKrawtchoukCompanionTriangular`
- `RHTower.BaezDuarteLogDualCrossEnergy`
- `RHTower.LaguerrePolyaDivideRealZero`
- `RHTower.RiemannKernelLaguerrePolyaSymbol`

API scratch caught an incorrect namespace: `mem_closedBall_zero_iff` is a
global name, not `Metric.mem_closedBall_zero_iff`. The generic cost leaf passed
its first direct check. Receiver elaboration required `simpa only ... using!`
to identify the inherited submodule norm with the ambient norm. No theorem
statement changed. No full/umbrella build, external search, numerical
experiment, added analytic premise, or heartbeat adjustment.

## Follow-up: global optimization over shifts

The attainment bridge and global cost conjecture are proved and formalized in
[weil-logshift-global-response-cost.md](weil-logshift-global-response-cost.md).
One shift, selected before the response and budget, attains global sensitivity
Q and realizes globally minimum cost |r|/Q for every feasible response.
Global budget feasibility is exactly 0≤A and |r|≤AQ, including Q=0.
The full corpus-research objective remains active.
