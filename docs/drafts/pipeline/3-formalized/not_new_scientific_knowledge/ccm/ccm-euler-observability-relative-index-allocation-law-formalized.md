# Formalization certificate — `ccm-euler-observability-relative-index-allocation-law`

- **Card:** `ccm-euler-observability-relative-index-allocation-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMEulerObservabilityAllocation.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 5 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(4)` jet rank bound | `jet_rank_le` |
| `(7)`–`(8)` injectivity on invisible directions | `domRestrict_ker_injective` |
| `(9)` deficit ≤ relative rank | `finrank_ker_le_finrank_range` |
| `(10)`, `(15d)` allocation inequality | `observability_allocation` |
| `(17)` cofinal index growth | `index_ge_of_bounded_jet` |

## Deliberately outside the Lean statement

- the Vandermonde faithfulness `(5)`;
- the signed-Cauchy index theorem `(13)` (kernel algebra in `CCMRelativeLogDerivCoordinateIndex`);
- the residue-birth statement `(15e)`;
- the divisor-convergence bound `(18)`.
