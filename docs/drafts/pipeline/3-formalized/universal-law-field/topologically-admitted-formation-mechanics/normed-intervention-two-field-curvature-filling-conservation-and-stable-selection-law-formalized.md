# Normed intervention two-field, curvature--filling conservation, and stable selection law — Lean formalization

- **ID:** ULF-TAFM-12
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** `../../../2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/normed-intervention-two-field-curvature-filling-conservation-and-stable-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.NormedInterventionTwoField`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified object

`NormedInterventionTwoField C₂ C₁ O` is the bounded presentation

`C₂ → C₁ → O`

with observer-boundary composite zero. `C₁` carries signed histories, `C₂` carries legal rewrite
fillings, and `O` is an observer quotient. `NormedInterventionTwoField.Hom` is the bounded
three-level representation preserving boundary and observation. Identity and serial composition
are constructed.

## Certified laws

1. `observer_boundary_apply`: every legal rewrite is observer-neutral.
2. `formationFilling_current_conservation`: exact winding current equals integrated curvature plus
   residual current.
3. `formationFilling_residual_observerClosed`: filling an observer-closed history leaves an
   observer-closed residual.
4. `formationFilling_current_budget`: operator norms give the complete positive action bound.
5. `currentOpenLift_forces_linear_fillingBudget`: an observer-hidden nonzero current forces linear
   curvature-plus-residual work.
6. `Hom.curvature_natural`: curvature transports through every route representation.
7. `Hom.formationFilling_map` and `Hom.observerClosed_map`: fillings and closure transport.
8. `Hom.pullbackCurrent_comp`: current pullback is associative under serial routes.
9. `Gauge.fillingBudget_eq`: every isometric route gauge preserves the complete
   curvature-plus-residual budget exactly.
10. `cofinal_sublinear_filling_selects_zero`: cofinally sublinear normalized work selects zero
   current.
11. `flat_exact_filling_selects_zero`: one positive exact fill kills a flat current.
12. `normedInterventionTwoField_selection_capstone`: selection and observer-closed residual
    conservation in one theorem.

## Verification

- Direct foreground elaboration: `lake env lean GaloisForLFunctions/HTGeometry/NormedInterventionTwoField.lean`
- Targeted leaf build only: `2997/2997` jobs passed
- Umbrella wiring: imported by `HTGeometry.UniversalLawField`; umbrella not built
- Axiom audit: ten capstones report only `propext`, `Classical.choice`, and `Quot.sound`

## Exact remaining producer

Construct the literal divisor-independent arithmetic intervention two-field, its observer-return
history, and cofinal legal fillings whose curvature-plus-residual budget is sublinear in winding.
This is strictly weaker than separately bounding every elementary edge current. No arithmetic
existence or RH claim is formalized here.
