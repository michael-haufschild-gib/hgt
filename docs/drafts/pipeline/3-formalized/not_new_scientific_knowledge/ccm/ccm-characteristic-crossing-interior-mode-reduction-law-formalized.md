# Formalization certificate — `ccm-characteristic-crossing-interior-mode-reduction-law`

- **Card:** `ccm-characteristic-crossing-interior-mode-reduction-law.md`
- **Stage:** 3-formalized / not-new
- **Lean modules:**
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialPolynomialModes.lean` (new infrastructure)
  - `formal/GaloisForLFunctions/HTGeometry/CharacteristicModeDimension.lean` (new infrastructure)
  - `formal/GaloisForLFunctions/RHTower/CCM/CCMCharacteristicCrossingModes.lean` (card module)
- **Umbrellas:** `formal/GaloisForLFunctions/HTGeometry.lean`, `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 49 declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(2)` real characteristic set finite | `RHTower.finite_realZeroSet_of_tendsto_atTop` |
| `(3)` bounded rational zero factor | `RHTower.dampedFactor`, `RHTower.modePoly`, `RHTower.natDegree_modePoly` |
| `(4)` corrected quotient `c_a = W_a/b_a` | `RHTower.symbolQuotient`, `RHTower.symbolQuotient_mul` |
| `(5)` zero-free invertible multiplier | `RHTower.multiplier_injective`, `RHTower.inverse_multiplier` |
| `(11)` `(1+D²)^{L}b_a = p_a` | `RHTower.localOperator_dampedFactor` |
| `(6)`+`(7)`+`(10)`+`(11)` ⟹ `(8)` | `RHTower.polynomial_symbol_eq_zero` |
| `(9)` mode frequencies and multiplicities | `RHTower.rootMultiplicity_modePoly`, `RHTower.realConstCoeffOp_charMode_modePoly` |
| `(9)` exhaustiveness | `RHTower.exists_characteristic_packet`, `HTGeometry.exists_characteristic_modes` |
| dimension exactly `d_a` | `RHTower.finrank_characteristicPacket`, `HTGeometry.finrank_solutionSpace` |

## New reusable infrastructure

`ExponentialPolynomialModes` (block calculus of a constant-coefficient operator):

- `GaloisForLFunctions.HTGeometry.expShiftLM`, `blockOp`, `blockOp_mul`, `blockOp_XsubC`,
  `blockOp_XsubC_pow`
- `iteratedDeriv_polyExp`, `realConstCoeffOp_polyExp`
- `natDegree_expShiftLM_le`, `natDegree_expShiftLM_pow_le`, `coeff_expShiftLM_pow`, `coeff_blockOp`,
  `blockOp_ne_zero`
- `polyExp_eq_zero_poly`, `polyExp_eq_zero_iff`
- `realConstCoeffOp_sum`, `realConstCoeffOp_zero`
- `eq_zero_of_sum_polyExp_eq_zero` (independence of distinct frequencies)
- `iterate_derivative_ne_zero`, `natDegree_lt_rootMultiplicity_of_blockOp_eq_zero`
- `blockSpan`, `expMonomialSpace_le_blockSpan`, `exists_characteristic_modes`

`CharacteristicModeDimension` (the exact dimension of the solution space):

- `charMode`, `CharIndex`, `charFamily`, `modeSpace`, `solutionSpace`
- `polyExp_finsetSum`, `polyExp_monomial`, `polyExp_eq_sum_charMode`, `contDiff_charMode`
- `blockOp_X_pow_eq_zero`, `realConstCoeffOp_charMode`
- `linearIndependent_charFamily`, `card_charIndex`, `finrank_modeSpace`
- `realConstCoeffOp_add`, `realConstCoeffOp_smul`
- `modeSpace_le_solutionSpace`, `solutionSpace_le_modeSpace`, `solutionSpace_eq_modeSpace`
- **`finrank_solutionSpace`** — the smooth solution space of `L(D) g = 0` has dimension `deg L`

## Deliberately outside the Lean statement

Cited analytic parents:

- the explicit symbol `(1)` (digamma block, prime sum, aperture polar block `P_a`) and its
  asymptotic `(2)`;
- the smooth extension of `W_a/b_a` across each crossing and the uniform lower bound `(5)` after
  increasing `L_a`;
- localization of the multiplier identities to `D'(I)` and the distributional-to-classical passage
  in `(9)`;
- the nonlocal exterior compatibility `(12)`–`(13)`, treated by
  `ccm-characteristic-evans-boundary-infinite-rank-law.md`.

The card's remaining open gates (does the corrected symbol have real zeros; construct the infinite
Evans relation, its Schur complement, and prove its kernel vanishes; RH) are route gates, not
statements of this card.
