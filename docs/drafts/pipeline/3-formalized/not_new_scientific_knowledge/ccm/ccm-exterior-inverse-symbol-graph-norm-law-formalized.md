# Formalization certificate — `ccm-exterior-inverse-symbol-graph-norm-law`

- **Card:** `ccm-exterior-inverse-symbol-graph-norm-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMExteriorInverseSymbol.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]`; `range_incidence` and
  `range_incidence_unique` depend on no axioms at all
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(6a)` positivity | `symbol_quadratic_nonneg` |
| `(6a)` injectivity | `symbol_quadratic_eq_zero` |
| `(8)`–`(9)` modulated packets vanish | `tendsto_integral_modulated_symbol` |
| `(6)`, `(10)` no lower bound | `not_boundedBelow_of_tendsto_zero` |
| `(12a)`–`(12b)` range incidence | `range_incidence`, `range_incidence_unique` |

## Deliberately outside the Lean statement

- the characteristic factorization `(1)` and symbol growth `(2)`–`(3)`;
- Plancherel and modulation covariance;
- the exterior compression `(5)` and its contractivity;
- the closed-range step and the self-adjointness identity `(6b)`.

The card's remaining open gates (construct the closed graph/relation for `(11)`, its Fredholm
Feshbach map, the coupling to the finite packet and anchors, zero kernel at every aperture, RH)
are route gates, not statements of this card.
