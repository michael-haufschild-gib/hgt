# Analytic completion of the exact Xi image cover

- **ID:** XI-IMAGE-COVER-CAPPING-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`
- **Statement:** Complete the exact Xi image cover over the twice-punctured plane by attaching one ramification point to every finite peripheral cycle, extend its projection and actual Xi lift analytically, and prove the completed surface is simply connected.

## Current result: construction complete [PROVED HERE]

`RHTower.XiMarkedMonodromy.xi_analytic_simplyConnected_capped_factorization` in `RHTower/XiCappedAnalyticAtlas.lean` proves the stated actual factorization with no mathematical hypotheses. The constructed space is Hausdorff, second countable, noncompact, and a complex analytic one-manifold; the selected exact-image completion is simply connected. Both the actual Xi lift and completed projection are analytic. The projection remains a covering over C minus {0,−1}, and every cap has the exact formula b+ζⁿ/4 with n>0.

The final analytic tranche comprises `HTGeometry/ContinuousAnalyticRoot.lean`, `HTGeometry/ComplexPowerAtlas.lean` and `RHTower/XiCappedAnalyticAtlas.lean`. All three production leaf builds pass, all twenty-one explicit public declarations have standard-only axiom audits, and all three final actual-source checks pass with empty logs. Audit input/output: `/tmp/hgt-xi-analytic-atlas-axioms.lean` and `.log`; final logs `/tmp/hgt-{ContinuousAnalyticRoot,ComplexPowerAtlas,XiCappedAnalyticAtlas}-final.log`. The earlier topology and extension modules have their own checked certificates below and in the linked cards. All modules are wired and indexed. Latest global lint has eight unrelated unreachable modules and no own-module or forbidden-declaration errors; see the final checkpoint below.

Intrinsic uniformization is a distinct next obligation, tracked in `../1-in-progress/xi-capped-surface-uniformization.md`. Exact Xi target-monodromy surjectivity and RH remain unproved. No external novelty claim is certified.

## Final analytic argument [PROVED HERE]

A continuous positive-degree root s of an analytic germ f is analytic, allowing f to vanish. If f is locally zero, the power identity forces s locally zero. Otherwise isolated zeros make f nonzero on a punctured neighborhood. At a zero, the checked punctured-root theorem extends s analytically by zero, and the power identity forces its existing center value to be zero. At a nonzero center, the earlier continuous-root upgrade applies. This proves both the germ and open-domain versions in `ContinuousAnalyticRoot.lean`.

For a continuous projection p, define a power coordinate to be an open partial homeomorphism e with p(x)=b+c·e(x)^n on its source, c≠0 and n>0. Given two such coordinates, the transition into the second is continuous and its nth power is the explicit polynomial obtained by substituting the first projection formula into the second. The root theorem makes this transition analytic on its open source, including any zeros. A covering family therefore supplies an analytic complex atlas. In every chart the projection itself is a polynomial. A continuous lift from C whose projection is analytic is analytic in every chart by the same root argument. `ComplexPowerAtlas.lean` proves these statements with mathlib's `ChartedSpace`, `IsManifold` and `ContMDiff` definitions.

On the actual completed cover, compose the inverse old-body embedding with a local covering coordinate. This gives a degree-one power chart with offset zero and scale one. Compose the inverse cap embedding with the full-disk inclusion into C to obtain each cap chart, with its checked degree, marked offset and scale 1/4. Old points and cap centers belong to their respective chart domains, so these charts cover. The generic atlas theorem applies to the existing topology, preserving its already proved Hausdorffness and second countability.

The completed projection is continuous and polynomial in these charts, hence analytic. The checked global Xi lift is continuous and projects to the actual entire Xi, hence the generic lift theorem makes it analytic. The checked commuting-diagram fundamental-group argument proves simple connectedness of the selected exact-image completion. Finally, the old subgroup-cover projection is onto the unmarked target. A compact completion would have bounded continuous projection image, contradicting arbitrarily large positive real values in that target. This proves noncompactness without an additional analytic premise.

## Historical construction log

The entries below preserve the conjectures, intermediate obligations and checks that led to the completed construction. Their pending statuses refer to those earlier checkpoints; the current certificate is above.

## Established inputs

`HTGeometry/SubgroupCover.lean` constructs intermediate covers and computes their exact fundamental-group images. `HTGeometry/ImageCoverLift.lean` constructs the source lift and proves its fundamental-group map onto. The actual Xi specialization is in `RHTower/XiMarkedImageCover.lean`: production leaf build PASS (11119 jobs), all twelve axiom audits standard-only; final direct actual-source audit PASS, exit 0, empty log. Full topological construction card: `../3-formalized/universal-cover-subgroup-factorization.md`.

`OpenCapFamily.lean` proves that attaching an arbitrary family of simply connected open caps with path-connected overlaps and pairwise cap overlaps contained in the old space makes inclusion of the old space onto on fundamental groups. `PuncturedPowerRoot.lean` gives the exact local extension and ramification-order classification for a holomorphic lift in a power chart.

## Original construction obligations

1. Give the unramified cover its analytic chart structure by composing covering charts with the target coordinate. Prove Hausdorffness and second countability from the quotient-cover construction, not as new structural assumptions.
2. Classify each connected component above a small punctured disk. A finite peripheral orbit of length n must be analytically equivalent to a punctured disk with projection ζ↦b+ζⁿ. An infinite orbit must be an infinite cyclic covering end. Construct this classification using the corpus exponential and power coverings and their fundamental-group images.
3. Attach points only in the finite case. Specify topology and atlas, prove Hausdorffness, and verify all chart overlaps. Distinct punctures have disjoint small base disks; distinct peripheral components above a fixed disk are disjoint. These facts should supply the open-cap hypotheses.
4. Show the actual source lift enters a finite peripheral component near each deleted source point. Its local loop projects to a finite power of the target meridian because the analytic source zero has finite order. The fixed orbit relation should force that component's cycle length to divide the source order. Apply the checked power-root extension theorem.
5. After extension, inclusion of the old cover induces a surjection on fundamental groups. The old source lift already induces a surjection. All its loops become null after extending across the simply connected source plane. Hence the completed cover is simply connected.

These steps remain proof obligations. Neither a global cap atlas nor intrinsic uniformization is assumed to exist.

## Immediate comparison lemma: complete paper proof

Two path-connected, locally path-connected coverings of the same base with matching based fundamental-group images are uniquely isomorphic over the base once matching initial points are chosen. The corpus lifting criterion lifts each projection through the other cover. The two composites preserve the projection and fix the chosen points. Uniqueness of covering lifts makes both composites identities. Thus the lifts are inverse homeomorphisms. This generalizes the already checked universal-cover deck-homeomorphism construction; it does not require either source to be simply connected.

The exact comparison statement is fully verified in `HTGeometry/CoveringComparison.lean`: production leaf build PASS (1708 jobs), standard-only axiom audit PASS, final actual-source check PASS with an empty log. Card: `../3-formalized/pointed-covering-image-comparison.md`. Combined with the still-unproved cyclic subgroup calculation for the punctured disk, it should construct the required finite peripheral chart. Holomorphy must then be derived from the local projection identities.

## Corpus audit

The first deep search for finite peripheral capping returned mainly unrelated cyclic-action results; no applicable cap construction was retrieved. Coverage was complete as source inventory, while most compiler metadata remained pending or stale. A rephrased punctured-disk/exponential-cover query also returned mainly irrelevant candidates, with no applicable classification. A lexical covering/homeomorph/range query returned no hits; these searches do not certify absence. Actual source reads confirm mathlib provides `Complex.isCoveringMap_exp`, `isCoveringMap_npow`, and their quotient-cover versions. No claim of exhaustive absence or external novelty. No web sources or numerical experiments.

## Chart construction refinement

The corpus `IsLocalHomeomorph.chartedSpace` pushes an existing atlas along a surjective local homeomorphism; it is not the pullback construction needed here. For q:Y→B⊆ℂ, compose q with the open target inclusion and take the inverses of `IsLocalHomeomorph.localInverseAt` as charts. Every chart's forward coordinate is the same projection, so coordinate changes are identity wherever defined. This should give the unramified analytic atlas directly. For second countability, `Topology.IsQuotientMap.secondCountableTopology` applies to the open quotient ℍ→ℍ/H. Fiber separation plus continuity over Hausdorff B should supply Hausdorffness of Y. These refinements are still unformalized.

The comparison lemma is fully integrated and verified. Latest global lint reports eleven unrelated unreachable modules and no new-module or forbidden-declaration errors; `/tmp/hgt-cover-comparison-lint.log`.

## Explicit completion design, conditional only on the still-unproved local classification

Choose disjoint small disks around 0 and −1. Over each punctured disk, index connected covering components. For each finite peripheral component of degree n, its proposed classification chart identifies it with 0<|ζ|<1 and gives projection b+Rζⁿ. Add one new point for that component. Extend its chart by sending the new point to ζ=0. The completed underlying set is the old cover disjoint-union the set of finite components; no points are added for infinite components.

Use these full-disk charts together with old covering charts to define the topology and analytic atlas. Distinct caps above one puncture are disjoint because their punctured components are disjoint; caps above different punctures project into disjoint disks. An old point and a new point have distinct projected values and can be separated by inverse images of disjoint base neighborhoods. Two old points are separated inside the open old cover. These are the explicit cases needed for Hausdorffness.

There are only countably many cap charts: the old cover is second countable, so any family of disjoint nonempty open peripheral components is countable. The old countable basis plus countably many disk bases then makes the completion second countable. On old/old chart overlaps the transition is identity. On a cap/old overlap the projection is b+Rζⁿ with nonzero derivative; the corpus analytic inverse theorem supplies analytic transitions in both directions. On disjoint cap charts there is no overlap. The extended projection is therefore analytic and still a covering away from {0,−1}; this covering statement is the exact property needed later, without separately assuming a claim about asymptotic values.

To extend the actual source lift at a deleted point, choose a source disk where f−b has its isolated zero of order m>0 and no other deleted points. The punctured disk is connected, so the lift lands in a single peripheral component. The local source meridian maps to the m-th power of the target meridian. Since it lifts closed, its peripheral orbit has finite length dividing m. The finite component chart then turns the source lift into a punctured holomorphic n-th root of (f−b)/R. The already proved `PuncturedPowerRoot` theorem extends it analytically by zero.

This spells out the construction rather than asserting a completion theorem. Formal obligations still include the finite/infinite peripheral classification, local meridian/order identity in the required coordinate form, all chart and separation verifications, and the global extension/gluing argument.

## Punctured-disk model construction: paper proof

Let D*={z∈ℂ:0<|z|<1} and L={w∈ℂ:Re(w)<0}. The exponential projection L→D* is a surjective covering: restrict the corpus exponential cover to D*, whose full inverse image is L because |exp(w)|=exp(Re(w)). L is convex, hence simply connected, and open, hence locally path connected. The restriction has the same integer imaginary-translation fibers as the full exponential cover.

For n>0, ζ↦ζⁿ is a covering D*→D*. Restrict the corpus power covering to D*; its full inverse image is D* because |ζ|ⁿ<1 is equivalent to |ζ|<1. Positive scaling w↦w/n is a homeomorphism L→L. Therefore w↦exp(w/n) is another universal cover of D*, and its composition with the n-th power map is exp(w). These exact projection identities are the models to compare with a peripheral component. The cyclic-image classification remains to be proved.

The targeted corpus query `research 'punctured fundamental' --mode lexical` returned five hits, including homeomorphic winding base change and the already checked puncture-deletion theorem; none supplied this classification. Direct source inspection found arbitrary power-loop winding in `Bottcher/Pi1CMinusZero.lean`, while `AnnulusRoot.lean` supplies analytic logs/dyadic roots under a core-winding condition. Their precise applicability will be verified rather than presumed.

## Peripheral classification through explicit deck subgroups

The disk models now pass Lean. A more direct classification avoids separately transferring the winding isomorphism from ℂ*: let ℤ act on L by w↦w+2πik. The corpus exponential-fiber identity makes this a free action with fibers exactly the orbits, presenting exp:L→D* as a quotient covering.

Every subgroup of ℤ has the form nℤ for n≥0: choose a generator using the corpus cyclic-subgroup theorem and replace its sign by its absolute value. For n>0, exp(w/n) has fibers exactly nℤ-orbits. Since it is a surjective covering, its quotient homeomorphism identifies L/(nℤ) with D*. The remaining projection is ζ↦ζⁿ by the checked exact identity. For n=0, the quotient is L itself and the remaining projection is exp.

An arbitrary connected, locally path-connected cover of D* has an exact subgroup cover from the preceding turn. The checked pointed-cover comparison identifies it with that quotient. Therefore it is topologically isomorphic over D* either to exp:L→D* or to a positive power cover D*→D*. This is a complete paper argument relative to the listed corpus results, with the integer action, subgroup normalization, quotient identifications and final comparison still being formalized. Analytic chart compatibility remains a separate step after this topological classification.

All those topological ingredients now pass Lean in `HTGeometry/PuncturedDiskCoverClassification.lean`, including `puncturedDisk_cover_classification`. Production leaf build PASS (2564 jobs), warning-free. The underlying model module `PuncturedDiskCover.lean` also passed its production leaf build (2428 jobs). Axiom and final actual-source audits are pending.

## Stronger source-end exclusion exposed by the root theorem

The logarithmic alternative can be excluded near a finite-order source zero without first computing a local meridian's winding. A holomorphic logarithm ℓ of f on a punctured neighborhood supplies a holomorphic n-th root exp(ℓ/n) there for every n>0. The checked punctured-root extension theorem then makes every n divide the finite zero order m. Taking n=m+1 contradicts m>0. Hence an actual finite-order source zero cannot approach a logarithmic peripheral component.

After the topological model chart is constructed, holomorphy of the logarithmic coordinate follows from the corpus continuous-lift/local-analytic-inverse theorem for exp, whose derivative never vanishes. This gives an explicit replacement for the source meridian/order calculation in the cap-extension step. The logarithm obstruction and this application still require Lean verification; the argument does not presuppose the cap or extend the source lift by fiat.

A further simplification uses only the already checked continuous-root upgrade in `Bottcher/AnalyticRoot.lean`. The roots exp(ℓ/n) are continuous and their analytic power f is nonzero on the punctured neighborhood. Therefore they are holomorphic there; divisibility gives the same contradiction. No separate differentiability theorem for logarithmic lifts is needed. In the finite power case, the same continuous-root upgrade followed by `PuncturedPowerRoot.lean` proves the chart coordinate extends analytically and gives its exact order identity.

The resulting local theorem has no finite-sheet hypothesis: if q:Y→D* is a connected covering and an analytic germ vanishing at a admits a continuous punctured lift through q, then q is a positive power model and that lifted chart coordinate extends analytically by zero. This is the precise local source-end theorem being formalized next. The global cap atlas and component-restriction/gluing steps remain unproved.

This local theorem now passes Lean, warning-free: `analytic_zero_lift_has_power_chart` in `HTGeometry/AnalyticZeroCoverCap.lean`. It also proves the exact order identity. Its proof uses `not_exists_punctured_continuous_logarithm`, which requires no finite-order hypothesis: nonvanishing on the punctured neighborhood rules out the locally zero germ, and the remaining positive finite order cannot be divisible by its successor. The same module proves the continuous-root analyticity upgrade and cap-coordinate extension. Production verification is in progress.

## Remaining global assembly, sharpened after the local theorem

The local source-end theorem removes the separate meridian/order calculation. The remaining bridge is to restrict the actual image cover to each connected component over a small punctured target disk, prove that component projection is a covering, and place the actual source lift in one such component. The latter follows from connectedness of a sufficiently small punctured source disk.

For the covering restriction, use a connected evenly covered base neighborhood. Each sheet section has connected image, so its intersection with a clopen source component is either empty or the whole sheet. Retaining precisely the sheets meeting the component gives a covering trivialization for its restricted projection. Local path connectedness makes the peripheral components open, while connected components are closed. This is the next explicit topological proof obligation; no matching restriction theorem was found in the inspected mathlib covering files.

Then attach the finite component charts, prove atlas/separation/countability properties, glue the now-checked local source extensions, and apply `OpenCapFamily.lean` to prove simple connectedness of the completed surface. Those global steps remain unproved.

## Verified local classification and analytic cap mechanism

All three new modules have now passed production leaf builds, all forty-nine public declarations have standard-only axiom audits, and all three final actual-source checks pass with empty logs. Cards: `../3-formalized/punctured-disk-cover-classification.md` and `../3-formalized/analytic-zero-cover-cap.md`. The audit harness initially concatenated imports between commands; moving imports to the header fixed that harness error. No mathematical proof change was needed. Global index/lint refresh remains pending.

The next formal lemma restricts a covering to any clopen part of its source over a locally connected base, including empty fibers. A connected sheet has constant membership in the clopen subset. Restrict the original trivializing homeomorphism to the retained sheets, then specialize to connected components. This supplies the component-cover premise rather than assuming it.

## Component bridge and topology inputs

`CoveringComponentRestriction.lean` now proves clopen-source restriction, connected-component restriction and component restriction above an open target set. Its leaf build, all three standard-only axiom audits and final source check pass. `PeripheralCoverComponent.lean` combines that bridge with the power/exponential classification and analytic zero extension. `SubgroupCoverTopology.lean` derives Hausdorffness and second countability of the subgroup cover and countability of connected components in its open pieces. These last two modules passed scratch Lean checks; production builds/audits are underway.

## Direct topology construction, avoiding a preliminary global atlas

The finite peripheral components are pairwise disjoint open subsets Uᵢ of the old cover: components above one puncture are disjoint, and the two chosen target disks are disjoint. Each has a homeomorphism with D*. Form the underlying completion Y⊔I, where I indexes finite components. The cap map from the full unit disk sends 0 to the new point i and nonzero ζ to the old point in Uᵢ with coordinate ζ.

Define openness in Y⊔I by openness of every inverse image under old inclusion and all cap maps. This is a topology directly: inverse images preserve unions and finite intersections. Old inclusion and the cap maps are continuous by definition. They are open embeddings: the old part of a cap image is open by its punctured homeomorphism, and distinct caps have empty overlap. Conversely a cap's inverse image of an open old set is open away from 0. Thus old Y is open, every cap is an open disk, and their pairwise intersections are empty.

The old projection and cap polynomial projections agree on overlaps and define a continuous completed projection. An old point and a cap point have distinct projected values because old Y avoids both marked values; separate them by projection neighborhoods. Two distinct cap points have disjoint caps. Old/old separation follows from the open Hausdorff old subspace. Countably many caps plus second countability of Y and the disk give second countability of the completion.

This construction should supply the topology and open-cap hypotheses before defining the analytic atlas. It still requires formalization; no completed surface is asserted yet. Projection separation is essential: gluing an arbitrary punctured-disk end to an arbitrary Hausdorff space does not by itself guarantee a Hausdorff completion.

All six local/component/topology-input modules are now fully verified: production leaf builds, all fifty-nine public-declaration axiom audits (standard-only), and six final actual-source checks pass. All are wired and indexed. Global lint reports seven unrelated unreachable modules and no own-module or forbidden-declaration errors; exact list and proof details on `../3-formalized/peripheral-component-bridge.md`. The next scratch formalization constructs the direct completion topology and proves open embeddings of its pieces.

## Direct cap topology now checked

`DisjointPointCaps.lean` constructs that topology for general disjoint punctured regions. Its `PointCapData` contains the punctured-region homeomorphisms and their openness/disjointness. It proves old and cap maps are open embeddings, their union covers, distinct caps are disjoint, and maps out are continuous exactly when continuous on the pieces. A continuous projection distinguishing old values from center values proves Hausdorffness. A countable cap index proves second countability. Production leaf build PASS (912 jobs), all twenty-six explicit public-declaration axiom audits standard-only, final actual-source check PASS with empty log. It is wired; the next index/lint refresh will include it.

This is the generic completion construction, not yet its assembled actual Xi instance. Next: identify body/cap intersections with the original punctured regions, apply the checked open-cap fundamental-group theorem, construct the actual Xi cap data, and glue its source extensions. Analytic atlas and uniformization remain unproved.

The first two next steps now pass Lean in `DisjointPointCapsFundamentalGroup.lean`: exact body/cap intersections, path-connected overlaps, simply connected caps, old-body fundamental-group surjectivity and path connectedness of the completion. Leaf build PASS (1754 jobs), all six standard-only axiom audits and final actual-source check PASS. Combined completion card: `../3-formalized/disjoint-point-cap-completion.md`.

## Next actual-source assembly

Choose explicit disjoint target disks of radius less than 1/2 around 0 and −1 and normalize their punctured charts to D*. For each actual subgroup image cover, take connected components over these disks and retain exactly those admitting a positive power model. The checked classification says the excluded components are logarithmic. The checked local analytic-zero theorem shows the actual source lift near each deleted point lies in a retained component. Second countability gives a countable component index.

Select one power chart per retained component and use it as the `PointCapData.chart`. Its polynomial projection agrees with the old projection. The completed projection therefore satisfies `t2Space_of_projection`; `secondCountableTopology` applies to the countable index. `fundamentalGroup_body_surjective` and `pathConnectedSpace` then supply the global topological conclusions.

The existential chart produced by the local analytic-zero theorem need not be the selected cap chart. This is not a new obstruction: in any selected positive power chart the actual lifted coordinate is continuous and its nth power equals the normalized analytic source germ. The checked continuous-root upgrade and punctured-root extension therefore apply directly to that selected chart. This observation still needs to be included in the actual global gluing proof.

After extension, combine old-source loop surjectivity with the source plane's simple connectedness to prove simple connectedness of the completed surface. This algebraic/topological deduction is established on paper but not yet connected in Lean to an actual completed Xi surface. Then construct the analytic atlas and attack intrinsic uniformization. These remain obligations, not new assumptions on an unconditional RH statement.

## Verification checkpoint

Eight modules, ninety-one explicit public declarations: all production leaf builds, standard-only axiom audits and final actual-source checks pass. All eight modules are wired and indexed. Latest global lint reports eight unrelated unreachable modules: RHTower.{PaperCircleSubgridProbability,StretchedBoseDefect} and HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,ComplexRateGammaIntegral}. No own-module or forbidden-declaration errors; `/tmp/hgt-caps-completion-lint.log`. This is a snapshot of concurrent work, not a reason to alter those modules. Implementation scratch copies removed after verification; audit inputs and logs retained.

## Actual peripheral data construction underway

Use Bool to index the centers b=false↦0 and b=true↦−1. The target chart is ζ=4(z−b), on the actual marked target intersected with |z−b|<1/4. Its inverse is b+ζ/4. Both inverse charts avoid the other marked value because |ζ/4|<1/4; the two chart regions are disjoint by the triangle inequality. The corpus lexical query `punctured disk marked chart` returned no matches; this is not an absence or novelty certificate. The explicit charts are being checked in Lean.

For an arbitrary subgroup H of the actual modular-cover deck group, index peripheral components by the disjoint union over the two centers of `ConnectedComponents` of the corresponding preimage. Choose a representative for each component. The component region in the old cover is the image of that representative's connected component under subtype inclusion; it is open. Distinct indices give disjoint regions, using disjoint base charts or distinct connected components. Countability follows from the checked topology of subgroup covers.

Retain exactly component indices admitting a positive power chart, expressed as the nonemptiness of a structure containing degree, positive-degree proof, homeomorphism, and exact projection identity. Choose one such structure per retained index. Compose its inverse homeomorphism with the punctured full-disk identification and the component-to-region homeomorphism to construct `PointCapData`. The projection on each cap is exactly b+ζⁿ/4, including its center, so its continuity and old/new separation are explicit. These steps are the current formalization target for the actual cover family; global Xi lift extension remains separate.

## Local-to-global extension proof refined

At a deleted source point a, the actual Xi value is one of the two marks b. The identity principle and xi(0)=1/2 exclude local constancy at either mark, so their inverse-image points are isolated. Choose a sufficiently small punctured source disk contained in the old source and mapping into the b-target chart. Its lift is continuous and its domain connected, hence its image lies in one peripheral component. Use the component quotient to identify this with the chosen representative's component; no chosen-basepoint equality is assumed.

Extend this component-valued map arbitrarily outside the punctured disk, using a fixed point of the component. Openness of the punctured disk makes the extension continuous at each point inside it. Apply the checked analytic-zero theorem to the normalized germ 4(xi−b). This proves that the component belongs to the finite index set. Now use its already selected power chart, which may differ from the existential chart in that theorem.

The selected chart coordinate u has |u(z)|<1 everywhere, even outside the local disk, because the arbitrarily extended map still takes values in the same component. The checked root theorem makes update(u,a,0) analytic at a. Updating by zero preserves |u|<1 globally. Thus update(u,a,0) defines a full-disk-valued map whose composition with the selected cap is continuous at a and agrees with the original old lift throughout the small punctured disk. Its projection at a is b=xi(a).

Define the global extended lift to equal the old lift on the old source and, at each deleted point, the value of one chosen local extension. At old points continuity follows from openness of the old source. At a deleted point, a neighborhood contains no other deleted point; hence the global extension agrees with its selected local extension throughout that neighborhood. This gives global continuity and exact projection equality without assuming a global extension theorem or compatibility of different arbitrary chart choices. The argument is complete on paper relative to the listed local ingredients; its domain restriction, isolated-zero and gluing details still require Lean verification.

## Actual cap family now builds

`RHTower/XiPeripheralTargetCharts.lean`, `HTGeometry/PuncturedDiskCapModel.lean`, `RHTower/XiPeripheralComponents.lean` and `RHTower/XiPeripheralCaps.lean` now pass production leaf builds. They construct the actual cap data for every subgroup of the transported modular-cover deck group, with countable disjoint component regions, chosen power charts, a Hausdorff/second-countable/path-connected completion, and the exact polynomial cap projection. The old body maps onto its fundamental group.

`cappedMarkedProjection_unmarked_iff` proves exactly that the unmarked part is the old cover; `cappedMarkedUnmarkedHomeomorph` identifies these spaces; `isCoveringMap_cappedMarkedProjection_unmarked` proves the completed projection remains a covering away from 0 and −1. This property is proved directly, without substituting a claim about asymptotic values. Sixty-one explicit public-declaration axiom audits and final source checks are pending. The actual global Xi lift and simple connectedness still require the extension argument above.

`PuncturedSourceDisk.lean` now proves the affine punctured-disk identification, path connectedness and containment in any punctured neighborhood. `PuncturedLocalGluing.lean` proves the global continuous gluing theorem with exact projection preservation. `XiIsolatedMarkedPunctures.lean` proves actual marked fibers locally isolated using the identity principle and xi(0)=1/2, and constructs the required small punctured source disks. All three production leaf builds pass. All seven modules' seventy-one explicit public declarations now have standard-only axiom audits; the final seven actual-source checks are running sequentially.

The next scratch file implements the actual local lift into a selected finite cap, the global gluing argument, and an unconditional capped factorization theorem retaining the exact-image source lift's fundamental-group surjection. These new factorization claims have not yet passed Lean; no global Xi extension is claimed at this checkpoint.

All seven supporting modules now pass their final actual-source checks with empty logs, and all seventy-one explicit public declarations have standard-only axiom audits. Cards: `../3-formalized/xi-peripheral-topological-completion.md` and `../3-formalized/xi-isolated-source-gluing.md`. Global lint reports thirteen unrelated unreachable modules: RHTower.{SincSeparatorContour,SincSeparatorMellin,StretchedBoseDefect,StretchedBoseSeparator} and HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,ComplexRateGammaIntegral,PaperFourierLLogL.Thermal.Obtain,PaperFourierLLogL.Thermal.Tilted,PaperFourierThermalMetric}. No own-module or forbidden-declaration errors; `/tmp/hgt-xi-actual-caps-lint.log`. The actual factorization scratch proof is now being checked.

## Formal simple-connectedness deduction prepared

The old parameter space Y is homeomorphic to the body image of the completion; therefore its inclusion induces a surjection on fundamental groups, by composing the homeomorphic isomorphism with the checked body-inclusion surjection.

In a commuting diagram with maps f:A→Y, i:Y→M, j:A→Z, g:Z→M and g∘j=i∘f, suppose f and i induce surjections on fundamental groups, Z is simply connected and M path connected. Then (g∘j) induces a surjection. The images of all source loops under j coincide in π₁(Z), so all elements of π₁(M,g(j(a))) coincide. Basepoint transport gives triviality at every point; every loop is null-homotopic, and M is simply connected.

For the actual construction, take A to be the old Xi source, Y its exact image cover, Z the source plane, and M the capped cover. The global extension supplies the commuting diagram, while both surjections are already available. This deduction has a scratch formalization prepared but is not yet checked. Once the current local/global Xi extension passes, this is the next proof required to complete the topological stage. The analytic atlas and intrinsic uniformization remain later obligations.

The generic simple-connectedness deduction and actual local/global Xi extensions now pass scratch checks with empty logs. Both production leaf builds pass. The unconditional actual simple-connectedness capstone is being checked; axiom and final-source audits of these additions remain pending.

## Analytic atlas mechanism, next obligation

Use inverse covering charts on the old body, whose forward coordinate is the completed projection, and the full-disk cap charts. Old/old changes are identity. Cap-to-old changes are the explicit polynomial b+ζⁿ/4. Old-to-cap changes are continuous roots of 4(z−b), hence analytic by the checked nonvanishing-root upgrade. Distinct cap ranges are disjoint; a cap's transition to itself is identity. Thus these charts should define an analytic one-dimensional complex manifold on the already constructed topology. This remains a construction to check, not an assumed atlas.

For the global Xi lift in cap coordinates, strengthen the continuous-root upgrade to allow zeros of the analytic power. An analytic germ is either locally zero or nonzero throughout a punctured neighborhood. In the first case its positive-degree root is locally zero. In the second case, if the germ vanishes at the center, the checked punctured-root extension is analytic and agrees with the continuous root, including its center value forced by the power identity. If the germ is nonzero at the center, the existing upgrade applies. This proves analyticity of a continuous root wherever its positive power is analytic, without a nonvanishing hypothesis. It will make the analytic nature of the global lift independent of which local extensions were selected. Formalization is next.

The zero-allowing root theorem now passes Lean, with its open-set version. This exposes a stronger uniform atlas mechanism: suppose each open complex coordinate e satisfies p(x)=b+c·e(x)^n, with c≠0 and n>0. On any overlap, the transition into a second such chart is continuous and its positive power is an explicit polynomial in the first coordinate. The new root theorem therefore makes every transition analytic, without separating old/old, old/cap and cap/cap cases. A covering family of these coordinates defines an analytic complex one-manifold. A continuous lift whose projected function is analytic is analytic in every such coordinate by the same argument. The generic atlas proof and actual capped-cover chart family are drafted for Lean checking.

The unconditional actual theorem `xi_simplyConnected_capped_factorization` now passes its production leaf build. Together with the two supporting factorization modules, all seven explicit public declarations have standard-only axiom audits; final actual-source checks are pending. This closes the mathematical topological stage, while the analytic atlas and uniformization remain open at this checkpoint.

## Final verification checkpoint

The actual cap, isolated-source/gluing, global extension/simple-connectedness, analytic atlas and planar-image rigidity tranches comprise fifteen new modules and 103 explicit public declarations. All production leaf builds, all standard-only axiom audits and all final actual-source checks pass; all final logs are empty. All modules are wired and indexed. Verified implementation scratch copies have been removed; audit inputs and logs are retained.

Latest index refresh passes: `/tmp/hgt-xi-analytic-completion-index.log`. Global formal lint exits 1 with exactly eight unrelated unreachable modules: RHTower.{SquareResidueQuadraticCompletion,SquareResidueQuadraticInterval,StretchedBoseNonDensity} and HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra}. No errors involve this work or forbidden declarations. Snapshot: `/tmp/hgt-xi-analytic-completion-lint.log`; concurrent unrelated modules were not modified.

The completed construction has moved to stage 3. The active route continues in `../1-in-progress/xi-capped-surface-uniformization.md`, with the same parent exact Xi monodromy target. The latest checked rigidity theorem excludes bounded analytic embeddings and proves every analytic open embedding into C is surjective, but existence of such an embedding remains unproved. RH remains unproved.
