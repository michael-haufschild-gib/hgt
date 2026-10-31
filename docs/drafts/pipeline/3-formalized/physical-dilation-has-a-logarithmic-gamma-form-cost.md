# Physical dilation has a logarithmic Gamma form cost

- **ID:** physical-dilation-has-a-logarithmic-gamma-form-cost
- **Stage:** 3-formalized
- **Statement:** For every real compact C² source `g` and every `r>0`,
  `|r A(g(r·))−A(g)|≤10 |log r|∫g²`.

## Proof

Fourier scaling gives `F[g(r·)](ξ)=r⁻¹ F[g](ξ/r)`. Changing variables
in the actual archimedean form therefore gives
`r A(g(r·))=∫2γ(2πrξ)|F[g](ξ)|²`.
Subtract the original form. The proved symbol modulus bounds the difference
integrand by `10|log r||F[g](ξ)|²`, using the explicit symbol constant five.
It is integrable by Plancherel; integrating and applying Plancherel again
gives the claimed bound. This also proves integrability of the scaled symbol term.

## Lean

`ArithmeticIncidencePositivity/GammaDilationControlsTheArchimedeanForm.lean`:
`mul_archForm_comp_mul` and `archForm_logarithmic_dilation_bound`.
Direct Lean check and transitive axiom audits passed for both theorems and the
existential wrapper. Dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
