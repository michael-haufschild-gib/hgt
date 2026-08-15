# Formalization certificate — `ccm-real-spectral-loggraph-transverse-vanishing-law`

- **Card:** `ccm-real-spectral-loggraph-transverse-vanishing-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRealSpectralLogGraph.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 4 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(7)` Cauchy insertion split | `CCMTwoChannelGraph.cauchy_insertion_split` (reused) |
| `(7)` coordinate is nonzero | `antiCausal_coordinate_ne_zero` |
| distinct pole coordinates cannot cancel | `cauchy_coeff_eq_zero_of_vanishing_on_real` |
| `(8)`–`(9)` limit of zero stages | `eq_zero_of_tendsto_of_forall_eq_zero` |
| section 3 compression step | `eq_zero_of_forall_compression_zero` |

## Deliberately outside the Lean statement

- the Smirnov maximum principle and Smirnov-class membership, hence `(3)`–`(4)`;
- the Hardy characterization of zero Hankel symbols;
- the analytic construction of `D_Ξ` and the equivalence `(6)`;
- the CCM simple-even hypothesis and aperture-phase removal.

The card's remaining open gates (prove the CCM divisor limit or the cofinal Weil floor; RH) are
route gates, not statements of this card.
