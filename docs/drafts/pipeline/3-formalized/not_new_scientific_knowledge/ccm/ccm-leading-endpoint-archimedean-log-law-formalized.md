# Formalization certificate — `ccm-leading-endpoint-archimedean-log-law`

- **Card:** `ccm-leading-endpoint-archimedean-log-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMEndpointArchimedeanLog.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 7 declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(11)` sawtooth mass `π²/12` | `hasSum_sawtoothEnergy`, `tsum_sawtoothEnergy` |
| `(9)` `M(Lη)/log L → 1` | `tendsto_logMultiplier_ratio` |
| `(15)` constant `8π/33` | `endpoint_constant_eq` |
| `(12)`–`(15)` endpoint scale limit | `tendsto_endpoint_archimedean_scale`, `endpoint_scale_factorization` |
| `(17)` lower-order prime response | `tendsto_lowerOrder_response` |

## Declarations

`sawtoothCoeffSq`, `hasSum_sawtoothEnergy`, `tsum_sawtoothEnergy`, `tendsto_logMultiplier_ratio`,
`endpoint_constant_eq`, `endpoint_scale_factorization`, `tendsto_endpoint_archimedean_scale`,
`tendsto_lowerOrder_response` (all in `GaloisForLFunctions.RHTower`).

## Deliberately outside the Lean statement

- the digamma multiplier `(1)` and its asymptotic `(2)`;
- the semiclassical measure `(8)` and the stationary-phase argument;
- the logarithmic energy estimate `(10)` and the cutoff removals;
- the PSWF endpoint interface and the signed prime theorem `(16)`.

The card's remaining open gates (the renormalized exact-tail remainder `(19)`, the Weil
Rayleigh-excess comparison, the cofinal floor/determinant transfer) are route gates, not statements
of this card.
