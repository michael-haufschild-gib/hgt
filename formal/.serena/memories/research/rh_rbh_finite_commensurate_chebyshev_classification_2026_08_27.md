# RBH finite commensurate Chebyshev classification (2026-08-27)

Formal module: `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatFiniteCommensurateChebyshevClassification.lean`.

For every finite real coefficient packet `a : Fin N → ℝ`,
`Σ_i a_i sinh((i+1)t) = sinh(t) Q_a(cosh t)`, where
`Q_a = Σ_i a_i U_i` is explicit in second-kind Chebyshev polynomials.
Consequently the reporter has exactly the forced wall zero `t=0` iff
`Q_a(u) ≠ 0` for every `u>1`. This includes `N=0` without assumptions.

The canonical physical packet at apertures `x^(i+1)` factors as the common
nonzero multiplicity-leading coefficient times this reporter. Every
wall-selective packet therefore gives an exact RH equivalence.

Verification: direct `lake env lean`, targeted `lake build`, and axiom audit passed.
Axioms are only `propext`, `Classical.choice`, `Quot.sound`.

Remaining RBH boundary: finite incommensurate rates, collision-grouped
non-diagonal matrix channels, infinite/non-polynomial packets.

Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-finite-commensurate-chebyshev-classification.md`.