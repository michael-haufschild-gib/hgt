# Root continuation across polynomial deformation squares

- **ID:** POLYNOMIAL-ROOT-SQUARE-CONTINUATION-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; paper proof and Lean audits complete
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Target:** Continuous families of monic polynomials over compact bases have proper root projection. Where roots are simple this is a covering; over a simply connected base each selected root extends uniquely to a continuous root section. Apply to deformation squares of the actual polynomial family while a chosen target loop avoids every critical value.

## Corpus audit

The lexical query `polynomial monodromy homotopy deformation root covering` returned no declarations. Source search found `HTGeometry/ContinuousMonicRootCovering.lean`: it proves local homeomorphism for continuous simple-root families, not properness or covering. `MonicCoefficientRootCovering.lean` supplies the universal coefficient relation and analytic/simple-root charts. `ParametricRootBaseChange.lean` gives charts directly from a nonzero vertical derivative; no separability adapter is needed for the actual family. `Bottcher/BranchContinuation.lean` supplies a monic root bound. The inspected covering theorem and `IsCoveringMap.existsUnique_continuousMap_lifts` supply the remaining topology after properness is proved. No external sources used; external novelty unverified.

## Complete core paper proof [PROVED HERE]

Fix d>0 and a continuous coefficient family c:X→C^d, with X compact Hausdorff. Set P_x(Z)=Z^d+∑_{i<d}c_i(x)Z^i. The lower sum has degree less than d, so P_x is monic of exact degree d. The joint relation R(x,z)=P_x(z) is continuous. Its zero locus E in X×C is therefore closed. The inspected monic root bound gives, at every root, |z|≤max(1,∑_{i<d}|c_i(x)|). The right side is a continuous real function on compact X and has a uniform upper bound C. Hence E is a closed subset of compact X×closedBall(0,C), so E is compact. The projection E→X is continuous and thus proper.

If every root has nonzero derivative, the universal coefficient analytic relation has nonzero vertical differential at each selected root. The inspected continuous base-change chart theorem makes E→X a local homeomorphism. Properness now makes it a covering. If X is simply connected and locally path connected, lift the identity map of X through this covering from a prescribed root above x_0. The unique lift is exactly a continuous root section z(x) with P_x(z(x))=0 and z(x_0)=z_0: the first component of the lift is x, and the second is the root. Conversely any such root section gives a lift of the identity, proving uniqueness. This handles every initial root individually and uses no numerical continuation.

For X=I×I, contractibility (hence simple connectedness), compactness, and local path connectedness follow from the inspected interval/product and convex-set topology. Therefore root continuation around the two routes along a square's edges has the same endpoint: both are restrictions of the unique global root section. This is the precise root-transport mechanism needed for monodromy invariance under a deformation.

## Actual critical-value application [PROVED HERE on paper]

Let v:I→Parameter n be continuous, and let γ:I→C be a target loop such that γ(s) differs from every ordered critical value B_j(v(t)) for all s,t. Consider P_{v(t)}(Z)−γ(s), a monic polynomial of fixed degree n+2. Its coefficients are continuous by the already proved smoothness of the actual additive-polynomial coefficients. At a root z, if its derivative vanished, z would equal one of the explicitly enumerated critical positions; then γ(s)=P_{v(t)}(z)=B_j(v(t)), contradicting avoidance. Thus every root in this square is simple, and the core theorem supplies unique root sections through every starting sheet. The commuting boundary transports conjugate the polynomial monodromies at t=0 and t=1 by transport along the basepoint edge.

The preceding collision-endpoint theorem constructs a parameter limit when critical values merge. Once that parameter curve is extended continuously by its limit, this square theorem preserves monodromy of every target loop staying away from the merging critical values, including loops surrounding whole clusters. This does not identify those cluster loops with an arbitrarily prescribed transposition factorization; that combinatorial/topological identification remains explicit.

## Remaining realization obligations

Prescribed planar polynomial monodromy, products of peripheral permutations under chosen critical-value collisions, and compatible finite planar completions of actual Xi pieces remain open. Parameter-cover monodromy transitivity alone does not settle them. The actual Xi global embedding and unconditional RH remain the fixed target.

## Exact transport mechanism [PROVED HERE on paper]

For continuous v:I→Parameter n and w:I→C avoiding all critical values pointwise, define transport from the root fiber at 0 to the root fiber at 1 by the unique root section through each initial root. This map is injective: two sections sharing their endpoint coincide by the same section theorem based at 1. It is surjective: start a section at any prescribed endpoint, then recover that section from its initial root by uniqueness based at 0. Thus transport is a bijection, with no choice of sheet labels.

For a deformation square, restrict the unique global root section to all four edges. Uniqueness on each edge identifies those restrictions with the respective transports. Both edge routes therefore end at the same root at (1,1). For a target loop, its two horizontal transports are polynomial monodromies, and both vertical edges are the same basepoint transport; the commuting square is exactly their conjugacy. This conclusion concerns actual polynomial roots, not the unrelated parameter-cover action.

- 2026-10-09 — generic compact-root covering and unique section theorem pass scratch Lean with an empty log (8 declarations). Production leaf build running. The actual additive-polynomial application and deformation-square corollary are written for the next compiler check. No final audit or prescribed-monodromy claim yet.

- 2026-10-09 — all three production leaf builds now pass (29 declarations). `OrderedCriticalValueMap.rootTransport_square` identifies both boundary transports on every actual root; `rootTransportEquiv_square` gives equality of the resulting fiber bijections. A rewriting proof exceeded default heartbeats; direct edge equalities pass without raising limits. All-public axiom and final-source audits are next. The following actual construction is `../3-formalized/ordered-critical-value-collision-path-lifting.md`, with its full paper proof already recorded.

## Final certificate

Three modules, 29 explicit public declarations: all production leaf builds, all standard-only public axiom audits, and all final actual-source `lake env lean` checks pass. Final logs are empty. All three modules are wired into HTGeometry.

- `CompactMonicRootCovering.lean` — 8 declarations: compact root loci, proper simple-root covering, unique root sections over compact simply connected bases.
- `OrderedPolynomialRootContinuation.lean` — 10 declarations: actual fiber polynomials, coefficient continuity, critical-value avoidance discharging simplicity, actual interval and square root sections.
- `OrderedPolynomialRootTransport.lean` — 11 declarations: root transport is a bijection; both boundary routes in every avoiding deformation square coincide on every actual root and as fiber equivalences.

Axiom log: `/tmp/hgt-root-transport-axioms.log`. Final logs: `/tmp/hgt-CompactMonicRootCovering-final.log`, `/tmp/hgt-OrderedPolynomialRootContinuation-final.log`, `/tmp/hgt-OrderedPolynomialRootTransport-final.log`. No heartbeat limit changes, numerical experiments or external sources. External novelty unverified. Parameter collision-path construction is next; prescribed planar monodromy, finite Xi completions and RH remain unresolved.

- 2026-10-09 — actual terminal-collision path lifting is fully audited: two modules, three declarations, all builds, standard-only axiom audits and final-source checks pass; see `../3-formalized/ordered-critical-value-collision-path-lifting.md`. Every value path regular before its final time lifts uniquely to a closed parameter path through its collision. Next combinatorial construction: `../3-formalized/tree-factorization-hurwitz-transitivity.md`. Actual meridian exchanges and prescribed polynomial monodromy remain open.
