# Hecke ideal elements as global-unit orbits

- **ID:** hecke-ideal-elements-as-unit-orbits
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Lean:** `HeckeLFunctions/NonzeroIdealElementsAreGlobalUnitOrbits.lean`

For every actual nonzero integral ideal `b`, its nonzero elements are in
explicit bijection with pairs `(I,u)`, where `I` is a nonzero integral ideal
in ordinary class `[b]⁻¹` and `u` is a global unit. The inverse sends
`(I,u)` to `u*g_I`, for a chosen generator of the proved principal ideal
`I*b`. Its principal ideal is exactly `I*b`, and its absolute field norm is
`N(I)*N(b)`.

## Proof and Lean declarations

`nonzeroIdealElementsEquivPrincipalUnits` groups nonzero elements by their
principal ideals. A generator is chosen from actual principality. Equal
principal ideals have associated generators, and nonzero cancellation makes
the unit unique. This first equivalence holds in every integral domain.

`inverseClassIntegralIdealsEquivPrincipal` multiplies inverse-class ideals
by `b`. The class-group product criterion proves principality; ideal
containment gives an integral quotient for the inverse map, and nonzero
ideal cancellation proves uniqueness.

`nonzeroIdealElementsEquivClassUnits` composes these equivalences.
`nonzeroIdealElementsEquivClassUnits_symm_apply` retains the exact
unit-times-generator formula.
`span_nonzeroIdealElementsEquivClassUnits_symm` and
`norm_nonzeroIdealElementsEquivClassUnits_symm` give the exact principal
ideal and norm formulas. The norm identity follows from
`Ideal.absNorm_span_singleton` and multiplicativity of `Ideal.absNorm`.

## Verification and scope

Scratch compilation passed. Four transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Final source check passed
with `lake --old env lean`; module imported by the Hecke umbrella without
compiling the umbrella. No extra hypotheses or computation shortcuts.

This algebraic equivalence supplies the indexing for weighted Hecke-series
unfolding. It does not assert any unproved exchange of sums or integrals.

The three index-type aliases are transparent `abbrev` declarations so that
subtype coercions remain usable during sum reindexing. The final source
audit also passed after this representation adjustment. Its changed olean
is regenerated only for the already written importing consumer.
