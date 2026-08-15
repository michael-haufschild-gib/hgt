# Formalization certificate — `ccm-screw-null-global-log-regularity-law`

- **Card:** `ccm-screw-null-global-log-regularity-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMScrewNullLogRegularity.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 9 declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(6)` → `(7)` local operator restores `p_a` | `polySymbol_eq_zero_of_dampedFactor` |
| `(4)` interior trace smooth, in `F_a` | `contDiff_of_mem_solutionSpace`, `finrank_interiorTrace_space` |
| `(8)` interior trace locally `L²` | `integrableOn_normSq_of_mem_solutionSpace` |
| empty-characteristic branch | `solutionSpace_eq_bot_of_natDegree_eq_zero`, `eq_zero_of_mem_solutionSpace_of_natDegree_eq_zero` |
| `(12)` first equivalence (kernel transport) | `map_eq_bot_iff_of_linearEquiv` |
| `(12)` determinant equivalence | `eq_bot_iff_det_evansGramMatrix_pos` |

## Declarations

`polySymbol_eq_zero_of_dampedFactor`, `contDiff_of_mem_solutionSpace`,
`integrableOn_normSq_of_mem_solutionSpace`, `finrank_interiorTrace_space`,
`finiteDimensional_modeSpace`, `solutionSpace_eq_bot_of_natDegree_eq_zero`,
`eq_zero_of_mem_solutionSpace_of_natDegree_eq_zero`, `map_eq_bot_iff_of_linearEquiv`,
`eq_bot_iff_det_evansGramMatrix_pos` (all in `GaloisForLFunctions.RHTower`).

## Deliberately outside the Lean statement

- the logarithmic multiplier `c_a(D)` on compactly supported `L²` and the distributional reading
  of `(2)`;
- the coercive Dirichlet realization `C_{a,I}`, its inverse and its unique solvability `(5)`,
  `(10)`;
- the bounded cross-boundary block `(9)` and the `L²` membership `(3)`.

The card's retracted `(13)` is deliberately not formalized. Its remaining open gates
(`det(M_a^*M_a) > 0` for every aperture; RH) are route gates, not statements of this card.
