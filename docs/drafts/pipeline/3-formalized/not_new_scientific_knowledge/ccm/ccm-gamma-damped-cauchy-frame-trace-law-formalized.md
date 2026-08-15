# Formalization certificate — `ccm-gamma-damped-cauchy-frame-trace-law`

- **Card:** `ccm-gamma-damped-cauchy-frame-trace-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMGammaDampedCauchyFrame.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 10 declarations
- **Hypotheses:** only the defining data of a pointed unitary system (unit vector, norm preservation,
  group law) and `2 ≤ p`; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(1)` rank-one compression | `rankOneProj_compression` |
| `(2)`–`(3)` canonical half-density | `halfDensity`, `halfDensity_sq`, `halfDensity_pos` |
| `(4)`–`(5)` channel norms | `norm_sq_synthesis_column`, `sum_norm_sq_synthesis` |
| `(9)` additive diagonal trace | `sum_channel_energy` |
| `(8)` full Gamma covariance in the Gram | `gram_entry_synthesis` |
| `(10)` exact prime diagonal | `gammaDiagSq_prime` |

## Deliberately outside the Lean statement

- the archimedean cyclic measure `μ_∞` and the realization `H_∞ = L²(μ_∞)`;
- the Hilbert–Schmidt synthesis extension and trace-class statement;
- the quoted summability theorem for the Gamma-damped Cauchy packet.

The card's remaining open gates (realizing the synthesis inside the Gauss-paired
Hardy–Titchmarsh/Sonin carrier, the archimedean/boundary relative channel, cofinal Pick inertia,
RH) are route gates, not statements of this card.
