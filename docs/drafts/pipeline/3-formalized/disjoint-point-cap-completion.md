# Constructing a Hausdorff cap completion with no new loop classes

- **ID:** DISJOINT-POINT-CAP-COMPLETION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Disjoint open punctured regions admit an explicit completion by one point per region, with open cap embeddings. A separating continuous projection supplies Hausdorffness; countably many caps preserve second countability. Simply connected caps with path-connected punctured parts introduce no new fundamental-group classes.

## Complete paper proof

[PROVED HERE, relative to the checked open-cap fundamental-group theorem]

Let Y be the old space, D a cap model with center o, and Uᵢ pairwise disjoint open subsets of Y equipped with homeomorphisms D\{o}→Uᵢ. Form the set Y⊔I. Include Y by the left injection. The ith cap map sends o to the new point i and all other points into Uᵢ through the chosen homeomorphism.

Declare a set open when its inverse images under old inclusion and every cap map are open. Inverse images preserve arbitrary unions and finite intersections, giving a topology. The maps are continuous by definition. Each cap map is injective; its image of an open set has open old inverse image through the punctured-region homeomorphism, open inverse image under itself, and empty inverse image under every other cap. It is therefore open. If the cap model is T1, the punctured model is open; the same calculation proves the old inclusion open. Thus all pieces are open embeddings and cover the completion.

Suppose a continuous old projection p:Y→Z and center values bᵢ extend continuously over every cap, with p(y)≠bᵢ for every old y and every i, and Z Hausdorff. The piecewise projection is continuous by the definition of topology. Distinct old points separate inside open Hausdorff Y. Distinct new points have disjoint cap images. An old point and a new point separate by projection preimages. Hence the completion is Hausdorff.

If Y and D are second countable and I countable, the old piece together with the cap pieces form a countable open cover by second countable spaces. The completion is second countable.

The old body meets the ith cap in exactly the image of Uᵢ. If D\{o} is path connected, this overlap is path connected. If D is simply connected, so is each cap image. The checked `OpenCapFamily` theorem now makes old-body inclusion onto on fundamental groups. Finally every cap point joins a punctured point in its cap and thence an old basepoint, so a path-connected old body gives a path-connected completion.

## Exact scope

The projection condition in the Hausdorff theorem is material. Arbitrary punctured-region attachments need not give a Hausdorff space. This condition will be supplied by the actual covering projection, whose old values avoid the marked target points, and by the polynomial cap projections.

`PointCapData` is the actual input record, not an assertion that Xi data has already been assembled. The specific peripheral index set, selected power charts, extended Xi lift, analytic atlas and simple connectedness of the actual completion remain on the parent card. No external novelty claim, web sources, numerical experiments, or RH conclusion.

## Verification

- `HTGeometry/DisjointPointCaps.lean`: twenty-six explicit public declarations; production leaf build PASS, 912 jobs.
- `HTGeometry/DisjointPointCapsFundamentalGroup.lean`: six public theorems; production leaf build PASS, 1754 jobs.
- All thirty-two declarations have standard-only axiom audits: `/tmp/hgt-disjoint-point-caps-axioms.log` and `/tmp/hgt-disjoint-caps-fundamental-axioms.log`.
- Both final direct actual-source `lake env lean` checks PASS, empty `/tmp/hgt-disjoint-point-caps-final.log` and `/tmp/hgt-disjoint-caps-fundamental-final.log`.
- Both modules wired and index refreshed. Final lint snapshot recorded on parent card.
