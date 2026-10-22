# Leading-symbol degeneracy magnitude-survival universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/WeightPolynomialDependence.lean`
  - `weightPolynomial_class44_dependence`
- `HTGeometry/LogSuperlacunaryMagnitudeHypertranscendence.lean`
  - `hypertranscendental_of_eventually_logSuperlacunary`
- `HTGeometry/MagnitudeDistinctSurvival.lean`
  - theorem surface documenting minimal-valuation survival without a leading-symbol hypothesis

## Universal law

The explicit degree-four, order-four differential polynomial

`Y₃Y₁Y₀² - 2Y₂²Y₀² + Y₂Y₁²Y₀`

is nonzero, but its balanced falling-factorial leading symbol vanishes identically.  Nevertheless it
cannot annihilate any entire function whose Taylor magnitudes are eventually positive and
log-superlacunary.

Thus balanced leading-symbol nondegeneracy is sufficient but not necessary for magnitude survival:
minimal-valuation dominance detects a universal family of relations lying in the exact blind spot
of the balanced-symbol method.

## Paper proof

The existing class-`(4,4)` falling-factorial identity proves that the balanced leading symbol is
zero.  The differential polynomial itself is nonzero: evaluating the value, first derivative, and
third derivative variables at one and the second derivative variable at zero gives one.  Eventual
log-superlacunary Taylor magnitudes force hypertranscendence, so no nonzero polynomial in the point,
value, and finitely many derivatives can vanish identically.  Applying this to the explicit
third-order polynomial proves survival despite exact symbol cancellation.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/LeadingSymbolDegeneracyMagnitudeSurvivalUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/LeadingSymbolDegeneracyMagnitudeSurvivalUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search stated
the class-`(4,4)` leading-symbol degeneration and general log-superlacunary hypertranscendence on
separate theorem surfaces, but did not instantiate the general theorem on the explicit degenerate
relation to prove a sharp method-separation law.
