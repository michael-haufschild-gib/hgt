# Exact image covers with a fundamental-group-surjective source lift

- **ID:** EXACT-IMAGE-COVER-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `universal-cover-subgroup-factorization.md`
- **Statement:** A continuous map from a path-connected, locally path-connected source to a locally connected base with a surjective simply connected, locally path-connected covering factors through a connected covering representing its exact fundamental-group image. The lifted source map induces a surjection on fundamental groups.

## Purpose and corpus boundary

This constructs the cover required by the actual Xi image-cover route. The corpus supplied universal-cover lifting, deck monodromy and quotient-cover tools, but the search did not retrieve this subgroup construction or exact-image factorization. External novelty remains unverified. No web sources or numerical experiments used.

## Complete paper proof

[PROVED HERE, relative to the cited corpus and previously checked local results]

Present the given universal covering p:E→B as a quotient by its full deck group G, using `UniversalCoverDeckGroup.lean`. For H≤G, form the orbit space E/H. Its quotient map r is a quotient covering: the continuous action and neighborhoods with disjoint nonidentity translates restrict from G to H. The rule q([e])=p(e) is well-defined.

Distinct H-orbits in a p-fiber have representatives g·e and e. Choose an open neighborhood V of e with disjoint nonidentity G-translates. The open quotient images r(gV), r(V) are disjoint: an intersection gives h·v=g·u for h∈H and u,v∈V, forcing g⁻¹h=1. Otherwise the original H-orbits would be equal. Thus q separates points in each fiber. The checked right-cancellation theorem makes q a covering.

A loop is in a covering's induced fundamental-group image if and only if its lifted path closes. Monodromy commutes with r, by uniqueness of path lifts. If g is the original loop's deck-monodromy element, the quotient lift closes exactly when r(g·e)=r(e), which by freeness is equivalent to g∈H. Therefore q has image equal to the inverse image of Hᵐᵒᵖ under the deck-monodromy homomorphism. For simply connected E, that homomorphism is injective. Taking H to be the unop of the image of a prescribed subgroup K realizes exactly K. The quotient is path connected because E is path connected.

Take K to be the image of the given source map f. Equality of the two images supplies the corpus covering-space lifting criterion, producing F with q∘F=f. For any loop δ in E/H, q₍*₎δ=f₍*₎γ for some source loop γ. Then q₍*₎F₍*₎γ=q₍*₎δ. Covering maps induce injections on fundamental groups, so F₍*₎γ=δ. Hence the lifted map induces a surjection.

## Verified modules

- `HTGeometry/SubgroupCover.lean`: ten declarations, including exact image formula and realization of any prescribed subgroup. Production leaf build PASS, 1709 jobs. All ten axiom audits PASS, standard axioms only. Final actual-source check PASS, empty `/tmp/hgt-subgroup-cover-final.log`.
- `HTGeometry/ImageCoverLift.lean`: four theorems, including factorization from any universal cover. Production leaf build PASS, 1711 jobs. All four axiom audits PASS, standard axioms only. Final actual-source check PASS, exit 0, empty `/tmp/hgt-image-cover-lift-final.log`.
- Both modules wired into the HTGeometry umbrella and indexed. Global lint reports seven unrelated unreachable modules, with no new-module or forbidden-declaration errors; `/tmp/hgt-exact-image-cover-lint.log`.

The analytic cap construction, intrinsic uniformization and exterior-cover classification remain unproved. This result neither proves the actual Xi monodromy map onto the original target nor proves RH.
