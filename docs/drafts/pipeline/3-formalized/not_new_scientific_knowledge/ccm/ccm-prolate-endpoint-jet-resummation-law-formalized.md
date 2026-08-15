# Formalization certificate — `ccm-prolate-endpoint-jet-resummation-law`

- **Card:** `ccm-prolate-endpoint-jet-resummation-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMProlateEndpointJet.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 5 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(2)` endpoint identity | `prolate_endpoint_identity` |
| `(4)` scaled endpoint logarithmic derivative | `hasDerivAt_scaledMode`, `scaled_logDeriv_eq` |
| `(6)` critical scale `−2π²λ³` | `critical_scale_logDeriv` |
| `(11)`–`(12)` growth of the jet ratio | `jet_ratio_ge` |

## Deliberately outside the Lean statement

- the prolate operator and fixed-mode regularity;
- the eigenvalue asymptotic `(5)` and the laws `(8)`, `(14)`;
- the integration-by-parts expansion `(10)`;
- the two-scale radial-prolate boundary laws.

The card's remaining open gates (exact radial-prolate boundary profile, arithmetic correlations,
Weil Rayleigh-excess and parity transfer) are route gates, not statements of this card.
