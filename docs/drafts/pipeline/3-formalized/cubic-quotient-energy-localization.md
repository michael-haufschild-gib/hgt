# Bounded cutoff localization of quotient energy

- **ID:** cubic-quotient-energy-localization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every smooth compact positive-height cutoff `χ` supported in an injective quotient chart, there is `Cχ≥0` such that every compact smooth quotient test satisfies `‖χ(f∘π)‖H¹²≤Cχ(‖f‖₂²+E(f))`.

The localized lift is smooth with compact support, hence Schwartz and in
the actual Euclidean weak-gradient space. Leibniz bounds its derivative
square by twice the cutoff-weighted source derivative square and twice
the cutoff derivative square times source mass. On the cutoff support,
height is bounded above and away from zero, and the cutoff and its
derivative are bounded. The exact injective measure chart bounds local
hyperbolic mass and energy by their global quotient integrals.
Lebesgue measure is at most `b³` times hyperbolic measure at height at most
`b`, giving the asserted bound.

Lean: `MetaplecticMobiusDescent/LocalizingTheCubicEnergy.lean`,
`kernelLocalizedField_energy_bound`, `kernelLocalEnergy_le`,
`kernelLocalMass_le`, and `kernelLocalizedH1_bounded`.
Transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

The bound extends localization continuously to the completed energy graph.
A separate mass-only bound extends the same localized mass from dense
smooth tests to quotient `L²`. Equality on the dense core identifies these
two mass maps. Since the Euclidean weak-gradient mass embedding is
injective, zero quotient mass forces the full localized `H¹` vector to vanish.

Lean: `MetaplecticMobiusDescent/LocalizingTheCompletedCubicEnergy.lean`,
`kernelEnergyLocalize_core`, `kernelL2Localize_core`,
`kernelEnergyLocalize_mass`, and `kernelEnergyLocalize_eq_zero_of_mass_zero`.
The same transitive axiom audit passed.

Adapted from OpenAI `Eisenstein/LocalCutoffs.lean` and
`CubicSieve/PaddedPassage.lean`. Global gradient closability still requires
the reverse localization estimate and cutoff faithfulness.
