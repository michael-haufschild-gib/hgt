# Formalization certificate — `ccm-universal-boundary-laplace-frame-saturation-law`

- **Card:** `ccm-universal-boundary-laplace-frame-saturation-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMBoundaryLaplaceSaturation.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 5 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(5)` exact polar two-edge expansion | `polar_two_edge_expansion` |
| `(5)` uniform `O_f(1)` remainder | `polar_two_edge_remainder_le` |
| `(9)` exponential character factors the autocorrelation | `expWeight_autocorrelation_eq` |
| `(9)` Fubini: weighted autocorrelation `= |F_-|²` | `integral_expWeight_autocorrelation` |
| `(13)`–`(16)` frame saturation | `tendsto_frame_saturation` |

## Deliberately outside the Lean statement

- the prime number theorem and the weak convergence `(8)`;
- the two-edge correlation `(7)` and the norm identity `(3)`;
- the Gamma/Riemann–Lebesgue bound `(12)`;
- the analysis map `B_a`, the level `μ_a` and its asymptotic `(14)`.

The card's remaining open gates (the one-sided subleading lower-frame remainder; RH) are route
gates, not statements of this card.
