# The half-line logarithmic form has its actual inverse

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** On positive-half-line L², causal convolution `W` by the explicit density `v` has range exactly the finite energy domain for `Ψ(ξ)=1+(1/2)log(1+ξ²)`. Every L² forcing has unique finite-energy variational solution `WW*f`.

## Proof

The literal Schur convolution is a contraction and has Fourier multiplier
`κ(2πiξ)⁻¹`. Its outputs have finite logarithmic energy. Conversely, multiply
the Fourier transform of a finite-energy vector by `κ(2πiξ)`. The proved
support-preservation theorem places its inverse transform on the positive
half-line; convolution recovers the original vector. Hence the range of `W`
is exactly the form domain.

The pointwise modulus identity `|κ(2πiξ)|²=Ψ(2πξ)` and Plancherel give
`q(Wu,Wv)=⟨u,v⟩`. All mixed form integrals are absolutely convergent.
Adjunction gives `q(v,WW*f)=⟨v,f⟩` for every finite-energy test. Expressing
any competing solution in causal coordinates proves uniqueness.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicFormHasItsActualInverse.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `hasLogarithmicEnergy_iff_integrable`
- `integrable_logarithmicHalfLineForm`
- `hasLogarithmicEnergy_iff_mem_range`
- `logarithmicHalfLineForm_causalOperator`
- `logarithmicHalfLineGreenOperator_solves`
- `existsUnique_logarithmicHalfLine_solution`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
