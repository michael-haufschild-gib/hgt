# Formalization certificate — `ccm-log-symbol-dirichlet-exterior-reconstruction-law`

- **Card:** `ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMLogSymbolDirichlet.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 4 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(2)` positive infimum `γ_a` | `exists_pos_lower_bound_of_tendsto_atTop` |
| `(14)`–`(15)` Carleman domination | `log_cross_kernel_le_carleman` (+ reused `exterior_displacement_split`) |
| `(17)`–`(18)` coercive inverse bound | `norm_le_of_coercive` |
| `(8)`–`(9)` observability, `F_a^adm = F_a` | `observability_bound` |

## Deliberately outside the Lean statement

- the heat-semigroup representation `(13)` and the explicit kernel `(14)`;
- the boundedness of the Carleman operator;
- the first representation theorem and the multiplier calculus;
- the symbol asymptotics `(10)`–`(12)`.

The card's remaining open gates (prove `E_a^eff` injective for every aperture; RH) are route gates,
not statements of this card.
