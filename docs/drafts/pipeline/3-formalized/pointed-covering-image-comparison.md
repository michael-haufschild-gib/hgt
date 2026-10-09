# Equal fundamental-group images determine a pointed covering isomorphism

- **ID:** POINTED-COVER-COMPARISON-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `xi-image-cover-analytic-capping.md`
- **Statement:** Two coverings with path-connected, locally path-connected sources and equal based fundamental-group images admit a unique pointed homeomorphism commuting with the projections.

## Purpose and corpus audit

This supplies the comparison step for classifying peripheral components as power or exponential covers. Neither covering source is required to be simply connected. The corpus provides the lifting criterion and uniqueness of lifts; a lexical covering/homeomorph/range query returned no matching result, and direct covering-source searches found only special cases. No exhaustive absence or external novelty claim.

## Complete paper proof

[PROVED HERE, relative to the corpus lifting criterion]

Let p:E→B and q:Y→B be the covers, with q(y₀)=p(e₀) and matching fundamental-group images at that common basepoint. The covering lifting criterion gives d:E→Y with d(e₀)=y₀ and q∘d=p. Transporting the same subgroup equality to the other basepoint convention supplies the reverse inclusion needed to lift q through p, giving d':Y→E with d'(y₀)=e₀ and p∘d'=q.

The composite d'∘d and identity are continuous lifts of p through p agreeing at e₀. Uniqueness of lifts on the connected E makes them equal. The same argument on Y gives d∘d'=identity. Hence d is a homeomorphism with inverse d'. Any other pointed covering-preserving homeomorphism is another lift of p through q agreeing at e₀, so equals d.

## Verification

- `HTGeometry/CoveringComparison.lean`, `existsUnique_covering_homeomorph_of_range_eq`.
- Production leaf build PASS, 1708 jobs, warning-free.
- Axiom audit PASS: only `propext`, `Classical.choice`, `Quot.sound`; `/tmp/hgt-cover-comparison-axioms.log`.
- Final actual-source `lake env lean` PASS, exit 0, empty `/tmp/hgt-cover-comparison-final.log`.
- Wired to umbrella and index refreshed. Latest global lint reports eleven unrelated unreachable modules: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, LegendreHalfCoordinates, and PaperFourierLLogL.Compress.{Fraction,Low,Observe,Phase,Thinning}, all under HTGeometry. No new-module or forbidden-declaration errors; `/tmp/hgt-cover-comparison-lint.log`.

Peripheral cyclic-image calculations and the analytic cap atlas remain unproved. This comparison theorem alone does not complete the local or global classification.
