# Formalization certificate — `ccm-euler-gamma-radon-nikodym-frame-law`

- **Card:** `ccm-euler-gamma-radon-nikodym-frame-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMEulerGammaRadonNikodym.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 9 theorems
- **Hypotheses:** only `2 ≤ p` and `1 ≤ k`; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(1)`–`(2)` the two weights | `gammaDampingProfile`, `eulerAtom`, `gammaDiagSq` |
| `(4)` exact Gamma diagonal | `gammaDiagSq_eq` |
| `(3)`, `(5)` exact Radon–Nikodym correction | `radonNikodym`, `radonNikodym_eq` |
| `(6)` bounded positive contraction | `radonNikodym_lower`, `radonNikodym_upper` |
| `(7)` exact matching of the Euler atom | `radonNikodym_mul_gammaDiagSq` |
| `(10)` prime-power tail summability | `tsum_eulerAtom_tail_le` |
| `(13)`–`(15)` critical correction and its lower bound | `vonMangoldtMagnitude`, `criticalCorrection`, `criticalCorrection_lower` |
| `(16)` cofinal recession | `criticalCorrection_unbounded` |

## Deliberately outside the Lean statement

- the Gamma cyclic representation and the synthesis columns `(8)`;
- the Hilbert–Schmidt and trace identities `(9)`, `(11)`, `(12)`;
- the prime sum `∑_p 1/(p (log p)²) < ∞`.

The exponential divided-difference kernel `(17)` is carried by
`CCMTwoChannelGraph.bilateral_atom_factorization` (card
`ccm-logderivative-closed-two-channel-graph-law`).

The card's remaining open gates (the distinguished Sonin compression and its relative trace-slope
bound, the archimedean/boundary relative channel, cofinal Pick inertia transport, RH) are route
gates, not statements of this card.
