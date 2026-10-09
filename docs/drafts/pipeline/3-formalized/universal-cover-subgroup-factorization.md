# Constructing the exact image cover from a universal cover

- **ID:** UNIVERSAL-COVER-SUBGROUP-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; topological construction and actual Xi specialization)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`
- **Statement:** Starting with a surjective simply connected covering p:E→B, construct the connected covering whose fundamental-group image is a prescribed subgroup H≤π₁(B).

## Why this is the next obligation

The actual Xi image subgroup must determine an actual analytic covering before the checked cap and logarithmic-growth theorems apply. A corpus deep query for subgroup-cover construction returned path-lifting and quotient tools, but no complete matching construction. The corpus does supply `Bottcher.isCoveringMap_lambdaPunct`, with simply connected upper-half-plane source, for the twice-punctured target. Generic classification is not being assumed as an axiom.

## First dependency-closed ingredient

For a covering p with simply connected, locally path-connected E, any two points e₀,e₁ in one fiber are related by a unique covering-preserving homeomorphism d:E→E satisfying d(e₀)=e₁.

Paper proof: lift the continuous map p:E→B through p with initial point e₁ to obtain d; reverse the chosen points to obtain d'. Both composites are lifts of p fixing the corresponding initial point. Uniqueness of continuous lifts makes the composites identities. Thus d,d' form a homeomorphism. Uniqueness follows from uniqueness of lifts. This uses the actual corpus `IsCoveringMap.existsUnique_continuousMap_lifts`, not a recalled deck-transformation theorem.

## Deck group and quotient-cover presentation: paper proof

Covering-preserving homeomorphisms form a subgroup of Homeomorph(E,E), acting by evaluation. A deck transformation fixing one point is the identity by uniqueness of lifts on connected E, so the action is free. The preceding sheet-moving lemma makes its orbits exactly the fibers of p. The action is continuous because each element is a homeomorphism. Together with the given surjective covering map, these facts satisfy the corpus equivalence `isQuotientCoveringMap_iff_isCoveringMap_and`. Hence p is a quotient covering by its full deck group. The corpus then identifies π₁(B) with the opposite deck group through `fundamentalGroupToMulOpposite`; its map is bijective because E is simply connected and path connected.

This avoids assuming that the particular modular subgroup used in an existing construction is already the full deck group. Its quotient map need not have been proved degree one for this argument.

## Construction obligations, now discharged through step 4

1. Assemble covering-preserving homeomorphisms into the deck group and prove its free transitive action on every fiber.
2. Identify that group, with the appropriate opposite convention, with π₁(B) using the corpus monodromy/fiber equivalence.
3. For a subgroup H, quotient E by its action. Over a connected evenly covered base neighborhood, deck transformations permute the sheets; quotient sheets are indexed by H-orbits. Construct the corresponding product trivialization.
4. Prove the fundamental-group image is exactly H through the closed-lift criterion, then lift the actual source map to this cover.
5. Transfer the analytic chart structure from the target and cap finite peripheral cycles. The already checked puncture-deletion and power-root extension results apply at this stage.

The quotient construction and exact image computation are now proved below. Analytic capping and intrinsic uniformization remain unproved and are tracked in `xi-image-cover-analytic-capping.md`. No external novelty claim; no web or numerical experiment.

## Formal progress

The sheet-moving homeomorphism, intrinsic deck group, free continuous action, exact fiber-orbit equality and quotient-cover presentation all pass Lean, warning-free. Promoted to `HTGeometry/UniversalCoverDeckGroup.lean`; production leaf build and audits passed. This completes the first construction ingredient. Applying the corpus's `IsQuotientCoveringMap.fundamentalGroupEquiv` now identifies the fundamental group with the opposite intrinsic deck group.

Intermediate obstacle, subsequently resolved: right cancellation of covering maps. For the subgroup orbit map r:E→E/H and proposed q:E/H→B, both r and q∘r=p are coverings, while q is a local homeomorphism by mathlib's `IsLocalHomeomorphOn.of_comp_right`. The existing `Bottcher/CoveringCancellation.lean` cancels the *outer* covering and does not supply this direction. Either prove the required right-cancellation under the actual locally simply connected base hypotheses, or construct quotient-sheet trivializations directly. Do not reuse the existing theorem with its arrows reversed.

## Stronger right-cancellation theorem: complete paper argument

Proposed exact statement: if q∘r:E→B is a covering, r:E→Y is a surjective local homeomorphism, Y is Hausdorff and B locally connected, then q:Y→B is a covering. In particular r need not itself be a covering, and no local simple-connectedness premise is required.

Fix b∈B. Choose a trivializing neighborhood for q∘r and shrink it to its open connected component U containing b. Each sheet supplies a continuous section t_i:U→E. Put s_i=r∘t_i; then q∘s_i is inclusion U→B. The map q is a local homeomorphism by `IsLocalHomeomorphOn.of_comp_right` and surjectivity of r. Each s_i is an open embedding by the corpus continuous-section theorem `IsLocalHomeomorph.isOpenEmbedding_of_comp`.

If two section images intersect, applying q identifies their base arguments. Their sections therefore agree at one point of U. Uniqueness of continuous lifts through the locally injective q, using connectedness of U and Hausdorff Y, makes them agree everywhere. Otherwise their images are disjoint. Index the distinct section images by their values over b, which are exactly q⁻¹{b}: surjectivity of r supplies every such value. The images cover q⁻¹(U), again by surjectivity of r and the original sheet decomposition. Thus they form a disjoint family of open sheets, each homeomorphic to U, giving the required trivialization.

This theorem is now formalized, with stronger hypotheses removal exposed by the construction. The subgroup-cover construction will still need the subgroup orbit action, quotient topology and exact fundamental-group image; the cancellation theorem alone does not finish it.

The formal proof uses Hausdorffness only to separate distinct points of one q-fiber. The stronger statement therefore assumes `IsSeparatedMap q`, with the Hausdorff version as a corollary. Empty fibers are handled directly from the original evenly covered neighborhood, so the composite need not be surjective in mathlib's convention.

Right cancellation is now verified in production: `HTGeometry/CoveringRightCancellation.lean`, leaf build PASS (1103 jobs), both axiom audits standard-only, final actual-source check PASS. Full theorem and proof recorded in `../3-formalized/covering-right-cancellation.md`.

## Subgroup quotient: complete paper construction

For a quotient covering p:E→B with group G and H≤G, let E/H be the orbit quotient with its quotient topology. The map r:E→E/H is a quotient covering: continuity of each H-translation and the disjoint-neighborhood property are inherited from G. The rule q([e])=p(e) is well-defined and q∘r=p.

To prove that q separates points of one fiber, write two representatives as e=g·e'. Choose an open neighborhood V of e' disjoint from each nontrivial G-translate. The open sets r(gV) and r(V) contain the two orbit classes. An intersection would give u,v∈V and h∈H with h·v=g·u. Hence (g⁻¹h)·v=u, forcing g⁻¹h=1 by the disjoint-neighborhood property. Then g∈H and the original classes coincide. Thus distinct classes have disjoint neighborhoods. The new right-cancellation theorem now makes q a covering when B is locally connected. This argument needs no Hausdorff premise on E/H.

The exact fundamental-group image criterion is proved below: a loop belongs to the image precisely when its lift to E ends in the H-orbit of its initial point. The corpus monodromy-to-opposite-group map expresses this as the preimage of Hᵐᵒᵖ.

## Exact fundamental-group image: proved and formalized

The preceding obligation is now discharged. For any covering, a based loop lies in the induced fundamental-group image if and only if its lifted endpoint equals its initial point. Necessity follows by lifting the image of a source loop. For sufficiency, the lifted path has equal endpoints and is itself a loop mapping to the original homotopy class. This uses the corpus path-homotopy lifting theorem.

Monodromy commutes with a continuous map of covering spaces over the same base: map the lifted path through the intermediate map and use uniqueness of lifts. Apply this to r:E→E/H. The loop lifts closed downstairs precisely when r(g·e)=r(e), where g is its deck-monodromy element. This equality means h·e=g·e for some h∈H; freeness forces h=g. Thus the exact image is the inverse image of Hᵐᵒᵖ under `fundamentalGroupToMulOpposite`.

If E is simply connected, that homomorphism is injective. Given any K≤π₁(B), take H to be the unop of the image of K. The just-proved inverse-image formula returns exactly K. No residual-finiteness or finite-packet approximation enters this argument.

All construction and image results pass Lean in `HTGeometry/SubgroupCover.lean`. Production leaf build PASS, 1709 jobs, warning-free. All ten axiom audits are standard-only and the final actual-source check passed. `ImageCoverLift.lean` now supplies the source lift and proves its induced fundamental-group map onto; all four declarations passed their leaf build, axiom audits and final source check. Analytic capping and uniformization remain unproved.

## Deck-presentation verification completed

- `UniversalCoverDeckGroup.lean` production leaf build PASS, 1708 jobs, warning-free.
- All seven public declarations, including the subgroup and action instances: axiom audit PASS, only standard axioms. `/tmp/hgt-universal-deck-axioms.log`.
- Final direct actual-source check PASS, exit 0, empty `/tmp/hgt-universal-deck-final.log`.
- Index refreshed and umbrella wired. Latest global lint FAIL on nineteen unrelated unreachable modules, with no new-module or forbidden-declaration errors; exact snapshot `/tmp/hgt-universal-deck-lint.log`.
- This earlier deck-presentation checkpoint has been superseded by the complete topological construction and actual Xi specialization below.

## Actual Xi specialization and completed verification

`RHTower/XiMarkedImageCover.lean` transports the corpus modular-lambda covering to the marked target by negation, proves openness and local path connectedness of the actual finite-mark source domains, and applies the exact-image construction. `coordinate_exact_image_cover_factorization` works for every actual marked coordinate. `xi_exact_image_cover_factorization` has no parameters or mathematical hypotheses: the untwisted Xi map factors through the subgroup cover, and the lifted source map induces a surjection on fundamental groups. The theorem does not assert surjectivity onto the fundamental group of the original target.

- Xi production leaf build PASS, 11119 jobs; new module warning-free, existing dependency warnings replayed.
- All twelve Xi declarations' axiom audits PASS: only `propext`, `Classical.choice`, `Quot.sound`. `/tmp/hgt-xi-image-cover-axioms.log`.
- Final actual-source check PASS, exit 0, empty `/tmp/hgt-xi-image-cover-final.log`.
- Four new modules (`CoveringRightCancellation`, `SubgroupCover`, `ImageCoverLift`, `XiMarkedImageCover`) are wired, indexed and verified. All 28 declarations audited.
- Latest global lint FAIL on seven unrelated unreachable modules: RHTower.XiRealRootedApproxEigenLimitRH, RHTower.XiRealRootedEigenGaussianGrowthRH; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No new-module or forbidden-declaration errors. Snapshot `/tmp/hgt-exact-image-cover-lint.log`.

The topological construction card is promoted to stage 3. Analytic capping, completed-surface simple connectedness, intrinsic uniformization and exterior-cover classification remain active in `xi-image-cover-analytic-capping.md` and the parent route. No RH proof or external novelty is claimed.
