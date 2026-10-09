# Global compactness of normalized surface embeddings

- **ID:** NORMALIZED-EMBEDDING-COMPACTNESS-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); generic exhaustion criterion
- **Parent:** `../1-in-progress/xi-capped-surface-uniformization.md`.
- **Source:** checked `OneFiberDiskGrowth.lean`, `Bottcher/W4LinWinding.lean:imageInv_analytic`, installed complex Schwarz lemma.

## Purpose and audit

**BRIDGE.** The finite polynomial prototype now has verified coverings and locally uniform convergence. It does not construct embeddings for the actual Xi surface. The finite-exhaustion attack also needs compactness of normalized embeddings, independently of finite planar realization. This card addresses that explicit obligation while retaining both realization and global embedding as open targets. External novelty is unverified; these local analytic ingredients are not presented as novel scientific discovery.

Searches for normalized injective disk derivative bounds gave no lexical hits. A broader analytic-inverse query found the existing generic inverse theorem, which is reused. It requires nonvanishing derivative; that condition is retained explicitly here, not inferred without proof from injectivity.

## Precise local statement [PROVED HERE on paper]

There is a universal constant C>0 such that for every R>0 and every f analytic on D(0,R), injective there, with derivative nonzero throughout, f(0)=0 and f'(0)=1, we have |f(z)|≤C R on |z|≤R/2.

Proof. If D(0,2R) were contained in f(D(0,R)), the checked analytic inverse g on the image would be analytic on D(0,2R), take values in D(0,R), and satisfy g(0)=0. Differentiating f∘g=id at zero gives g'(0)=1. The installed Schwarz derivative bound would instead give |g'(0)|≤R/(2R)=1/2, a contradiction. Thus some a with |a|<2R is omitted by f on D(0,R).

Take the universal B>1 from the checked one-center-fiber omitted-value theorem. Injectivity gives its unique-center-fiber condition. On the half disk, |f(z)−a|≤B|f(0)−a|=B|a|. Hence |f(z)|≤(B+1)|a|≤2(B+1)R. Set C=2(B+1). All prerequisites are listed and already proved in the corpus; no uniformization theorem is used.

## Initial surface proposal (historical; discharged below)

For a sequence of local biholomorphic embeddings on increasing open pieces exhausting a connected second-countable analytic surface, normalize at one fixed chart center. The local theorem supplies a common bound on a smaller initial chart. One-fiber omitted-value bounds should propagate control through overlapping charts: a previously controlled point outside a new chart supplies an omitted value, and a controlled overlap point anchors the ratio bound. Need prove the chart-chain construction and constants with exact quantifiers, then diagonal Montel compactness, analytic limit, nonzero normalized derivative, and injectivity preservation. None of those global statements is asserted proved here.

Finite planar completion and polynomial realization remain separate unresolved obligations. Success of this local compactness step would not establish actual Xi uniformization or RH.

## Log

- 2026-10-09 — complete local argument derived from actual corpus; formalization next. No numerical experiments or web sources.

## Intermediate surface argument (historical; sharpened and discharged below)

Precise proposed criterion: let M be a connected Hausdorff second-countable complex analytic surface, Uₙ an increasing open exhaustion, and uₙ:Uₙ→C analytic embeddings with analytic inverses on their images. A fixed chart centered at x₀ lies in every sufficiently late Uₙ; in that chart uₙ(x₀)=0 and derivative is one. Then some subsequence should converge locally uniformly on M to an analytic open embedding with the same normalization. This criterion is conditional on the entire exhaustion of local embeddings; it is not an unconditional Xi result.

For local boundedness, define S as points having a neighborhood V and constants N,C with |uₙ|≤C throughout V for n≥N. The local disk theorem makes x₀∈S. S is open by definition. For y≠x₀ in its closure, choose a chart disk about y whose compact closure avoids x₀. Compactness and the increasing exhaustion put that closure in one U_N. Choose x∈S in a sufficiently small concentric disk. A disk centered at x can have a half disk containing a neighborhood of y while staying inside the chosen chart. Every sufficiently late uₙ omits zero there, since its sole zero is x₀ outside the chart. The universal one-fiber bound with omitted value zero bounds its half-disk values by B|uₙ(x)|. Membership x∈S bounds those center values eventually. Thus y∈S, making S closed; connectedness gives S=M.

Choose countably many coordinate disks with smaller disks covering M. Local boundedness and compactness of their closures provide a bound and tail index for each. The inspected `MontelOpenSetSubsequence` theorem supplies subsequences on each disk; a diagonal extraction must preserve local convergence on all disks. On overlaps, pointwise uniqueness identifies the limits, producing a global analytic map. The installed locally uniform analytic-limit and derivative-limit theorems should preserve derivative one at x₀. The precise countable chart/diagonal adapters remain to be checked in Lean.

For injectivity, suppose distinct x,y have equal limit values. Choose a disk around x avoiding y. The functions uₙ(·)−uₙ(y) are nonzero on that disk. Their locally uniform limit vanishes at x. If this limit is nonzero as a germ, an isolated-zero circle and the inspected `HurwitzZeroLimit.eventually_exists_zero_of_tendstoUniformlyOn` force a zero for all sufficiently late n, contradicting injectivity. Otherwise the limit is locally constant; the analytic identity theorem on connected M would make it globally constant, contradicting normalized derivative one. Thus the limit is injective. The local open mapping theorem then makes it an open embedding. The manifold identity-theorem adapter is an explicit remaining obligation.

This isolates a concrete construction path for the compactness mechanism. Finite planar realization is still required to supply the exhaustion; this argument does not replace that construction with an assumption in the final target.

- 2026-10-09 — local result now passes scratch Lean, production leaf build, and both standard-only public axiom audits in `HTGeometry/NormalizedEmbeddingDiskBound.lean`. The build reused `Bottcher.imageInv_analytic` and rebuilt its leaf dependency. Index refresh passed; final actual-source check passed with an empty log. Global lint reports seven unrelated unreachable modules and no own-module or forbidden-declaration errors.

The completed local theorem and its proof/audits are recorded separately in `../3-formalized/normalized-embedding-disk-bound.md`. The full surface criterion is now formalized as recorded below.

## Exact propagation theorem [PROVED HERE on paper]

Let X be a connected T1 space covered by open partial homeomorphisms eᵢ:X⇄C. Let Uₙ be increasing open subsets with union X, and Fₙ:X→C functions whose restrictions to Uₙ are injective. Assume Fₙ(x₀)=0 for every n, and Fₙ∘eᵢ⁻¹ is holomorphic on eᵢ.target∩(eᵢ⁻¹)⁻¹(Uₙ). Define local eventual boundedness at x to mean: there exist V∈N(x) and C∈R such that eventually in n, every y∈V satisfies |Fₙ(y)|≤C. If this holds at x₀, it holds at every point of X. This is the exact generic propagation step; existence of the exhaustion embeddings for Xi remains unproved.

Proof with fixed radii and quantifiers. Let S be that set of bounded points. An open neighborhood inside the witnessing V proves S open. For y∈closure(S), if y=x₀ the conclusion is given. Otherwise choose e with y∈source, put c=e(y), and choose r>0 such that closedBall(c,4r) lies in target and its inverse image avoids x₀. This follows from continuity of e⁻¹ at c and T1 separation from x₀. Its inverse image K is compact. The open increasing cover Uₙ gives N with K⊂U_N, hence K⊂Uₙ for n≥N.

Choose x∈S∩source with |e(x)−c|<r/2, using y∈closure(S). A witness at x gives C and eventual |Fₙ(x)|≤C. For each sufficiently late n, e⁻¹(ball(e(x),2r)) lies in K⊂Uₙ; the coordinate function is holomorphic and injective there and omits zero because x₀∈Uₙ eventually and K avoids x₀. Its unique center fiber therefore satisfies the checked universal one-fiber bound. Every z∈ball(c,r/2) has |z−e(x)|<r=(2r)/2. Thus |Fₙ(e⁻¹(z))|≤B|Fₙ(x)|≤BC on that disk, simultaneously for all sufficiently late n. Its inverse image is a neighborhood of y. Hence y∈S. S is closed and contains x₀; connectedness gives S=X.

The point x₀ must also belong to the sufficiently late Uₙ in the omission argument. That cutoff is intersected with the compact-stage and center-bound cutoffs; it is not silently assumed to hold for every n.

## Convergence propagation through Vitali [PROVED HERE on paper]

The actual corpus `VitaliConvergence.lean` yields a sharper compactness mechanism: one initial subsequence can propagate through the whole connected surface, with no countable atlas or global diagonal argument. The exact generic statement below assumes a covering family eᵢ of complex open partial homeomorphisms and, at every x, a chart i with x in its source and R>0,C such that ball(eᵢ(x),R) is in its target and, for all sufficiently late n, Fₙ∘eᵢ⁻¹ is holomorphic and bounded by C on that disk. If pointwise convergence exists throughout any neighborhood of one point, then a global locally uniform limit exists.

Proof. First adapt the checked disk Vitali theorem to an eventually holomorphic, eventually bounded family: replace its finitely many initial functions by zero. A positive enlarged bound handles these replacements. The replaced family is eventually identical to the original, so every pointwise and locally uniform limit is unchanged.

Let W consist of points having a neighborhood on which pointwise limits exist. W is open and nonempty. For y∈closure W choose its controlled coordinate disk of radius R. The preimage of ball(e(y),R/6) meets W at x. A neighborhood V of x consists of convergent points. In the coordinate plane, Y=ball(e(y),R/3)∩e⁻¹⁻¹(V) is a neighborhood of e(x); it therefore accumulates at e(x), lies in the third-radius disk, and has pointwise convergence. Disk Vitali gives locally uniform convergence throughout that third-radius disk, so y∈W. Hence W is closed, and connectedness gives pointwise limits everywhere.

Choose the unique pointwise limit G(x). Apply disk Vitali at each y using all points of its third-radius disk as Y. Its local analytic limit equals G∘e⁻¹ by uniqueness of pointwise limits. On the closed sixth-radius disk convergence is uniform, by compactness and local uniform convergence. Pulling back through e gives a uniformly convergent family on a neighborhood of y. Such neighborhoods at every point give global locally uniform convergence. The same local limits show chartwise analyticity of G. Every use of a local family has its own finite cutoff; eventual equality handles them independently.

For the active exhaustion family, the already proved local-bound propagation plus compact coordinate disks supply the controlled-chart hypothesis. Extract a subsequence on just one normalized chart using checked Montel; strict monotonicity preserves all eventual local controls. Vitali then continues that same subsequence globally. This removes countable diagonal extraction from the proposed proof, but does not supply the still-missing finite planar realizations.

- 2026-10-09 — `SurfaceLocalBoundPropagation.lean` passes scratch Lean with an empty log. The paper proof caught and retained the necessary eventual membership of the fixed-zero anchor in Uₙ. Production checks underway. Next: formalize eventual disk Vitali and surface convergence propagation.

The precise compactness consequence requires only a connected source covered by complex charts and eventual local analytic bounds; second countability is unnecessary. At a chosen point, replace the finite bad prefix on one controlled disk by zero and apply the checked one-disk Montel theorem (equivalently, use a sufficiently late tail). The resulting increasing subsequence converges pointwise on an open chart neighborhood. Its indices tend to infinity, preserving every eventual controlled-chart statement. The surface Vitali theorem above then gives global locally uniform convergence, continuity, and an analytic germ in a chart at every point. The proof uses one extraction, not an unproved compatibility of independently selected chart limits.

- 2026-10-09 — global Vitali propagation, controlled-chart extraction from an exhaustion, and one-extraction surface Montel now pass scratch Lean with an empty log in `SurfaceVitaliCompactness.lean`. The stronger statement needs no second-countability assumption. Production checks underway. The still-active step is exclusion of a constant limit and preservation of injectivity; actual finite realization remains unresolved.

## Identity and injectivity preservation [PROVED HERE on paper]

A scalar function analytic in a complex chart near every point of a connected source satisfies the identity theorem without any pre-existing global coordinate. For each constant b, its local zero set is either a whole neighborhood or an isolated point, by the checked analytic germ dichotomy. Let S be points where the function equals b throughout a neighborhood. S is open. At a point of closure(S), the isolated-zero alternative is impossible: a nearby point in S, distinct from that point if necessary, is a zero. Hence S is also closed. If S is nonempty, connectedness makes the function identically b.

Consequently a locally uniform limit G of injective holomorphic maps on an increasing open exhaustion is either injective or constant. If x≠y and G(x)=G(y), assume the limit is not constant. The identity theorem implies that G−G(y) is a nonzero germ at x. In a chart at x choose a closed disk avoiding y, contained in the chart and one sufficiently late exhaustion stage, with G∘e⁻¹−G(y) nonzero on its boundary. The coordinate differences Fₙ∘e⁻¹−Fₙ(y) converge uniformly on this closed disk, since the original family converges locally uniformly and Fₙ(y) converges. A late tail is holomorphic on a neighborhood of the closed disk. The inspected disk Hurwitz theorem forces zeros in that disk for sufficiently late n. But injectivity of Fₙ on Uₙ and y outside the disk forbid such zeros once both the disk and y lie in Uₙ. This is a contradiction.

A fixed nonzero normalized derivative excludes the constant alternative: locally uniform convergence on the normalization chart preserves the derivative by the installed derivative convergence theorem. Thus the limit derivative remains one. These are construction steps within the conditional exhaustion criterion, not a construction of the actual Xi exhaustion.

## Complete normalized-exhaustion criterion [PROVED HERE on paper]

Fix a connected T1 space X with a covering family of complex charts eᵢ, an increasing open exhaustion Uₙ, and maps Fₙ:X→C injective on Uₙ. In every chart require Fₙ∘eᵢ⁻¹ holomorphic with derivative nonzero on target∩(eᵢ⁻¹)⁻¹(Uₙ). Fix x₀ and chart e₀ with e₀(x₀)=0. Require Fₙ(x₀)=0 for all n and eventually (Fₙ∘e₀⁻¹)′(0)=1. Then there are a strictly increasing subsequence and a global chartwise analytic open embedding G:X→C, with locally uniform convergence along that subsequence, G(x₀)=0 and (G∘e₀⁻¹)′(0)=1.

Proof. Choose a closed coordinate disk centered at zero inside e₀.target. Its inverse image is compact, hence lies in some U_N. Every sufficiently late coordinate function is injective, holomorphic, has nonzero derivative, and has the fixed normalization there. The checked normalized disk bound supplies eventual boundedness on the half disk; pulling back gives local boundedness at x₀. The proved propagation theorem gives it everywhere. The compact-stage adapter supplies eventual analytic controlled charts. One-disk Montel plus surface Vitali gives a globally locally uniform subsequence with continuous chartwise analytic limit G.

Values at x₀ pass to the limit. To pass the derivative, first choose any U_N containing x₀ and a smaller coordinate disk mapped into U_N. Monotonicity ensures every sufficiently late subsequence map is holomorphic there; the installed locally uniform derivative-limit theorem gives derivative one for G. Therefore G is nonconstant. The proved exhaustion Hurwitz argument gives global injectivity. The installed local open-mapping theorem, with the chartwise identity theorem excluding local constancy, gives openness. Continuity, injectivity and openness give an open embedding.

This exact criterion constructs the limit from the specified exhaustion; the exhaustion remains a required input to this generic theorem. Producing those finite embeddings for the actual Xi completed surface is still the core missing construction. No such input has been added as a premise to an alleged unconditional Xi or RH theorem.

The limit is analytic in every supplied chart, not merely in one chosen chart at each point. For any target point z of chart eᵢ, choose an exhaustion stage containing eᵢ⁻¹(z). Continuity of the chart inverse gives a coordinate disk mapped into that stage. Every sufficiently late map is holomorphic there, and global local uniform convergence pulls back through the chart. The installed analytic-limit theorem makes the limit holomorphic on that disk. Since z was arbitrary, the limit is analytic throughout the chart target. This strengthens the criterion to an exact atlas-compatible analytic embedding.


## Lean certificate

Four modules are wired into `HTGeometry.lean`:

- `HTGeometry/SurfaceLocalBoundPropagation.lean`: three explicit public declarations; eventual local bounds propagate across the connected surface.
- `HTGeometry/SurfaceVitaliCompactness.lean`: eight declarations; eventual disk Vitali, surface continuation, and one-extraction Montel compactness.
- `HTGeometry/SurfaceHurwitzEmbedding.lean`: seven declarations; chartwise identity theorem, injectivity and openness of the nonconstant limit, and derivative preservation.
- `HTGeometry/NormalizedSurfaceEmbeddingLimit.lean`: three declarations; normalization supplies the initial bound, all-chart analyticity, and `exists_openEmbedding_limit_of_normalized_exhaustion`.

All four production leaf builds pass. All 21 explicit public axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. Final `lake env lean` checks of all four actual source files pass with empty logs. The initial axiom invocation ran before the fourth build finished and failed with a missing object-file error; the completed-build audit above passes. No result relies on that failed invocation.

The criterion needs neither a countable atlas nor Hausdorff separation beyond T1. Its hypotheses include the actual increasing exhaustion and normalized analytic embeddings with nonzero chart derivatives. Those inputs have not been constructed for Xi; finite planar completion and polynomial realization remain open on the parent and `../1-in-progress/finite-planar-polynomial-realization.md`. This is a proved bridge, not an unconditional Xi uniformization or RH theorem. External novelty remains unverified.

Index refresh passed (`/tmp/hgt-surface-compactness-index.log`). Authoritative global lint reports three unrelated unreachable modules: `RHTower.PaperCirclePosteriorProjective`, `RHTower.PaperCircleSplitBitPosterior`, and `RHTower.WeilLogShiftFixedMinorant`. No own-module or forbidden-declaration error appears (`/tmp/hgt-surface-compactness-lint.log`).
