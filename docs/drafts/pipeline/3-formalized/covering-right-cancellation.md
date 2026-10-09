# Connected sheets descend through a surjective local homeomorphism

- **ID:** COVERING-RIGHT-CANCELLATION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `universal-cover-subgroup-factorization.md`
- **Statement:** If q∘r is a covering, r is a surjective local homeomorphism, q separates distinct points in each fiber, and the base is locally connected, then q is a covering. A Hausdorff intermediate space supplies fiber separation.

## Corpus audit and purpose

The corpus search for right cancellation found the opposite cancellation direction in `Bottcher/CoveringCancellation.lean`, and compact/proper local-homeomorphism results that do not apply to arbitrary infinite subgroup quotients. No matching theorem was retrieved. This supplies the descent step for the subgroup cover in the Xi image-cover construction. External novelty remains unverified; no web sources used.

## Complete paper proof

[PROVED HERE, relative to the stated corpus theorems]

The remaining factor q is a local homeomorphism by local cancellation and surjectivity of r. At b, shrink an evenly covered neighborhood of q∘r to its open connected component W containing b. Compose every sheet section with r. Each resulting section of q over W is an open embedding. Two such sections whose images meet agree at the same base point; separation within fibers and local injectivity make their equality locus both open and closed in W. Thus they agree everywhere.

Choose one section for each point of q⁻¹{b}. Their images are open, pairwise disjoint and exhaustive, by surjectivity of r. Restricting q to each image gives a homeomorphism with W. These sheets give the required trivialization. If q⁻¹{b} is empty, the original covering trivialization and surjectivity of r give an empty inverse image neighborhood directly. Thus surjectivity of the composite is unnecessary.

## Verification

- `HTGeometry/CoveringRightCancellation.lean`, two public theorems, wired to its umbrella.
- Production leaf build PASS, 1103 jobs, warning-free.
- Both declarations' axiom audits PASS: only `propext`, `Classical.choice`, `Quot.sound`. `/tmp/hgt-cover-right-cancel-axioms.log`.
- Final actual-source `lake env lean` PASS, exit 0, empty `/tmp/hgt-cover-right-cancel-final.log`.
- Index refreshed. Global lint reports seven unrelated unreachable modules, with no new-module or forbidden-declaration errors; `/tmp/hgt-exact-image-cover-lint.log`.

This theorem completes one construction step. It does not construct the analytic cap atlas, prove uniformization, or settle the actual Xi monodromy conjecture or RH.
