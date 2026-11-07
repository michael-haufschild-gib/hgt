# Closability of the cubic quotient gradient

- **ID:** cubic-quotient-gradient-closability
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The completed cubic quotient energy graph embeds injectively in quotient `L²`. The actual smooth gradient is closable, and its closure has dense domain.

Reverse Leibniz controls a cutoff of the fundamental-domain gradient by
the Euclidean localized `H¹` norm and quotient mass. On each compact
positive-height support, both hyperbolic density and height are bounded,
so the pointwise bound integrates and extends by density to the completed
graph. Zero quotient mass kills the localized `H¹` vector and thus every
cutoff of the gradient. The nonzero regions of the constructed cutoffs
cover hyperbolic space. Lindelöf gives a countable subcover, allowing the
almost-everywhere equalities to hold simultaneously; the gradient is zero.
The closed graph therefore has unique gradient over each mass vector.

Lean: `MetaplecticMobiusDescent/TheCubicGradientIsClosable.lean`,
`kernelCutoffGradient_core_bounded`, `kernelCutoffGradient_faithful`,
`kernelEnergyMass_injective`, `kernelInitialGradient_isClosable`,
`kernelWeakGradient_closed`, and `kernelWeakGradient_dense_domain`.
Transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

Adapted from OpenAI `Eisenstein/VariationalLaplacian.lean`. This identifies
the actual energy space; compact-core restriction and exterior coercivity
remain distinct inputs to spectral continuation.
