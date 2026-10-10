# Uniform cost control for exact fixed-node realization

- **ID:** finite-weil-uniform-realization-cost
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean `WeilLogShiftQuadraticSurjection`, `WeilLogShiftGramPacketKernel`, `WeilLogShiftGramExactImage`, `WeilLogShiftGramFiberCost`.
- **Statement:** For every finite coefficient support s, there exist fixed distinct nodes x and C>0 such that every target y is realized by one outer-scale-one test on x with native unit tail cost at most C times ||y||.

## Exact target

For each s:Finset Nat, prove unconditionally:

    exists N, x:Fin N -> Real, C>0,
      Injective x and forall y:s->Real, exists u:Fin N->Real,
        finiteWeilGramCoefficientVector s <N,x,u,1> = y
        and finiteWeilGramTailCost 1 <N,x,u,1> <= C * norm(y).

N, x, C precede y. C may depend on s. Empty support is included. No continuous selection, global optimized-cost minimizer, dimension-independent bound, or convexity claim is intended.

## Local evidence and attack

The exact-image receiver is already compiled and audited. Its analytic proof shows that H(K,t)=(K,q_K(t)) maps neighborhoods of (K0,1) to neighborhoods of (K0,0), using a surjective strict derivative and zero-sum spanning diagonal. The published Lean conclusion retains only range surjectivity and discards amplitude control.

Documented local searches: `quadratic surjective bound` (no hits), then `cost bound` (all 25 hits reconciled using uncapped pages retained in /tmp/hgt-weil-uniform-cost-search*.json). Source-text search found no native-cost/norm bound or bounded-realization statement in WeilLogShift leaves. Read actual `exists_finiteWeilGram_cost_bounds`: it gives weighted sensitivity and certificate LOWER bounds, not this upper bound. Read `exists_finiteWeilGram_signed_cost_dictionary`: it concerns linear mixtures in a fixed dictionary, not one actual test. The singleton upper bounds concern two-test certificates and do not give this all-support single-test receiver.

Verdict: **BRIDGE**, a quantitative strengthening forced by the corpus's strict-local-surjection mechanism. Lower cost-growth theorems prohibit assuming C uniform across cutoffs; they do not contradict a support-dependent constant. No external sources or priority claims.

## Dependency-closed paper proof

1. Reuse the existing strict-derivative construction of H and its surjectivity at (K0,1). Let M=||1||+1>0. The source set A={(K,t):||t||<M} is a neighborhood of (K0,1), by continuity of the second projection and norm. The map-neighborhood equality proved in the existing code makes H(A) a neighborhood of (K0,0). Thus there exist neighborhoods U of K0 and W of 0 with U x W contained in H(A). Choose epsilon>0 with ball(0,epsilon) contained in W. Every K in U and ||z||<epsilon therefore admit q_K(t)=z with ||t||<M. Equality of first components ensures the preimage uses that same K.

2. Fix K in U. For y!=0 choose c=epsilon/(2||y||)>0. Then ||c y||=epsilon/2<epsilon, so step 1 gives t with q_K(t)=c y and ||t||<M. Set r=t/sqrt(c). Quadratic homogeneity gives q_K(r)=y and ||r||^2=||t||^2/c <= (2M^2/epsilon)||y||. For y=0 choose r=0. This yields one constant D=2M^2/epsilon>0, uniform over K in U and all targets.

3. Take the existing balanced actual dictionary and its separated packet kernels. Kernel convergence supplies one finite separation T with K_T in U. This fixes all packet nodes and amplitudes b_(j,i) before the target is chosen. Their actual coefficient vector with amplitude r_j b_(j,i) is q_(K_T)(r), by the existing packet identity.

4. Let Gamma be the unit native cost of the same packet with r identically one. Gamma>=0 by its finite sum definition. For every pair of packet indices, |r_j r_h|<=||r||^2, so termwise comparison in the native cost formula gives cost(packet(r))<=Gamma ||r||^2. Therefore every y has an exact packet realization costing at most Gamma D ||y||. Taking C=Gamma D+1 ensures strict positivity even in the empty case.

5. Flatten the packet index type as in the existing exact-image receiver. Coalesce its fixed node image once, aggregating amplitudes in each fiber. The node image is independent of y. The existing fiber form identity preserves the coefficient vector, and the fiber cost inequality at B=1 and outer scale 1 does not increase cost. Reindex the finite image to obtain fixed distinct nodes with the same upper bound. All helper premises have actual producers.

There is no mathematical open core in this argument. Formalization and the final local duplicate audit remain.

## Working plan

- [x] Exact statement and paper mechanism recorded before new Lean edits.
- [x] Finish local duplicate audit, including uncapped search-page reconciliation.
- [x] Factor the existing strict-derivative proof into a bounded local-image theorem; preserve the existing surjectivity API as a consequence. Avoid duplicating its long derivative proof.
- [x] Quadratic scaling theorem with ||amplitude||^2 <= D||target||.
- [x] Actual packet cost comparison and distinct-node unconditional receiver.
- [x] Native leaf builds, umbrella wiring, every-public-declaration axiom audit, index and lint run (seven unrelated umbrella omissions, no owned diagnostics).
- 2026-10-10: No Lean code for this next card has been changed. Previous cost-kernel geometry card is fully formalized. All work remains local Lean and proof algebra, without computations or external sources.
- 2026-10-10: Uncapped first and second pages reconcile to all 25 hits. Reviewed their descriptions and the previously undescribed signatures. No competing single-test uniform upper bound found. Refactoring the existing quadratic local-surjection proof to retain its bounded source neighborhood; the old surjectivity theorem remains as a consequence. Its three existing downstream leaves (packet kernel, exact image, cost geometry) will be rebuilt to avoid stale owned artifacts.
- 2026-10-10: Refactored WeilLogShiftQuadraticSurjection native build passed cleanly. New bounded local-image theorem fixes M and epsilon before the kernel. Added three leaves for homogeneous quantitative scaling, actual amplitude cost domination, and fixed/distinct-node native cost receivers; their builds and final audits are in progress. No heartbeat changes.
- 2026-10-10: WeilLogShiftQuadraticCostControl and WeilLogShiftGramAmplitudeCost native builds passed cleanly on first attempts. The actual amplitude-cost bound is unconditional and allows arbitrary coincident nodes and signed base amplitudes. Rebuilding the packet-kernel dependency before the assembled receiver. Final audit prepared for all 26 public declarations across the changed/new leaves and the three affected existing descendants, with 92 API terms.
- 2026-10-10: Packet kernel rebuild clean. WeilLogShiftGramUniformCost native build passed cleanly on first attempt: both the fixed-node and distinct-fixed-node receivers are now compiled. Existing exact-image and cost-geometry descendants and final audits remain to be checked.
- 2026-10-10: All seven native artifacts are fresh over their sources and changed dependencies. The interrupted observation of the exact-image build was revalidated: its process was terminal, its log empty, and its new olean newer than the rebuilt packet kernel; the downstream cost-geometry build then passed. Final scratch audit passed with all 26 public declarations using only `propext`, `Classical.choice`, `Quot.sound` and all 92 API terms checked. A scratch-only universe annotation for `smul_smul` was corrected from three levels to two; no mathematical source change was needed. All owned processes terminal.

## Exact Lean delivery and verification

- `WeilLogShiftQuadraticSurjection.lean:65`: bounded local preimages uniformly over nearby kernels; the old surjectivity API remains at line 157.
- `WeilLogShiftQuadraticCostControl.lean`: squared-amplitude linear bound by homogeneity, including zero targets and empty supports.
- `WeilLogShiftGramAmplitudeCost.lean`: unconditional actual native cost domination under bounded amplitude multipliers.
- `WeilLogShiftGramUniformCost.lean:61`: `exists_finiteWeilGram_distinct_fixed_node_cost_control`, the unconditional receiver with fixed distinct nodes, fixed C>0, outer scale one, and exact realization of every target at cost <= C||y||.

Four changed/new leaves plus three affected existing descendants were checked with native `lake --old env lean ... -o ...`. No full build or umbrella build. All seven imports appear exactly once. Index refresh completed and the exact receiver query returns one hit at line 61. Source and dependency freshness, declaration coverage, and whitespace checks passed.

Audit artifacts: `/tmp/hgt-uniform-cost-final-audit.lean`, `/tmp/hgt-uniform-cost-final-audit.log`, `/tmp/hgt-uniform-cost-index.log`, `/tmp/hgt-uniform-cost-receiver-search.json`, `/tmp/hgt-uniform-cost-lint.log`. Native logs use `/tmp/hgt-uniform-quadratic-surjection-build.log`, `/tmp/hgt-quadratic-cost-control-build.log`, `/tmp/hgt-gram-amplitude-cost-build.log`, `/tmp/hgt-uniform-packet-kernel-build.log`, `/tmp/hgt-gram-uniform-cost-build.log`, `/tmp/hgt-uniform-exact-image-build.log`, `/tmp/hgt-uniform-cost-geometry-build.log`.

Global lint reports seven unrelated missing imports: `RHTower.XiGaussianHeatVerticalLineReceiver`, `HTGeometry.PaperMoebiusPrimeLSeries`, `HTGeometry.PaperPrimeExponentialRange`, `HTGeometry.PaperPrimeTransportAnalytic`, `HTGeometry.PaperPrimeTransportConormal`, `HTGeometry.PaperPrimeTransportXi`, `HTGeometry.QKrawtchoukCompanionTriangular`. No edits to those shared-worktree files.

## Research assessment / next cycle

The finite-support cost-control gap is closed, using the actual native cost and one fixed node set. This is a quantitative corpus bridge, without an external novelty claim. No convexity or globally optimal cost claim follows, and no support-independent constant is asserted. The follow-up `finite-weil-coordinate-isolation-cost.md` is now formalized: polynomial cost to produce one coordinate versus exponential cost to isolate some coordinate at large cutoffs. This targets the growth of necessary constants rather than repeating qualitative realizability. The next paper-proved card is `../3-formalized/finite-weil-cost-leakage-tradeoff.md`.
