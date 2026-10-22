# Formalization certificate — `ccm-rational-residual-finite-evans-matrix-law`

- **Card:** `ccm-rational-residual-finite-evans-matrix-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMRationalResidualEvansMatrix.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 18 declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(1)` `b_a = p_a/(1+ξ²)^{L}`, `deg p_a = 2L` | `residualPoly`, `natDegree_residualPoly` |
| `(5)` `R_L = span{x^j e^{±x} : j<L}` | `charMode_one_mem_residualSpace`, `charMode_neg_one_mem_residualSpace` |
| `(5)` `dim R_L = 2L = d_a` | `finrank_residualSpace` |
| `(10)` Bessel tail stable under differentiation | `deriv_besselTail`, `natDegree_besselTail_le` |
| `(11)` right cross block lands in `R_L` | `crossKernel_expansion_right` |
| `(12)` left cross block lands in `R_L` | `crossKernel_expansion_left` |
| `(15)` `⟪f, Gram f⟫ = ‖M f‖²` | `evansGram_quadratic` |
| `(7)` injective ⟺ posDef ⟺ `det > 0` | `posDef_evansGramMatrix_iff`, `det_evansGramMatrix_pos_iff` |

## Declarations

`residualPoly`, `residualPoly_ne_zero`, `natDegree_residualPoly`,
`rootMultiplicity_residualPoly_one`, `rootMultiplicity_residualPoly_neg_one`, `residualSpace`,
`finrank_residualSpace`, `charMode_one_mem_residualSpace`, `charMode_neg_one_mem_residualSpace`,
`crossKernel_expansion_right`, `crossKernel_expansion_left`, `deriv_besselTail`,
`natDegree_besselTail_le`, `evansGramMatrix`, `posSemidef_evansGramMatrix`, `evansGram_quadratic`,
`dotProduct_star_self_eq_zero_iff`, `evansGramMatrix_mulVec_eq_zero_iff`,
`det_evansGramMatrix_ne_zero_iff`, `posDef_evansGramMatrix_iff`, `det_evansGramMatrix_pos_iff`
(all in `GaloisForLFunctions.RHTower`).

## Deliberately outside the Lean statement

- the unbounded logarithmic Dirichlet realization `C_{a,I}` and its inverse `(3)`, `(5)`;
- the identification `(9)` of `k_L` as the inverse Fourier transform of `(1+ξ²)^{-L}`;
- the endpoint distributions `(13)` and the distributional identity `(14)`;
- the `L²` continuity of the exterior moments.

The card's remaining open gates (`det Gram_a > 0` for every aperture; RH) are route gates, not
statements of this card.
