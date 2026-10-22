# Formalization certificate — `ccm-limiting-radial-first-row-weber-bound`

- **Card:** `ccm-limiting-radial-first-row-weber-bound.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMLimitingRadialWeber.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 8 declarations
- **Hypotheses:** only the positivity/quantified data of each statement; no `sorry`, `axiom`,
  `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(7)` bulk difference phase and derivative | `radialPhase`, `radialPhaseDeriv`, `hasDerivAt_radialPhase` |
| `(8)` unique critical point `r = 1/k` | `radialPhaseDeriv_critical` |
| `(8)` curvature `−(k²−1)/k` | `radialPhaseSecondDeriv`, `hasDerivAt_radialPhaseDeriv`, `radialPhaseSecondDeriv_critical` |
| `(10)` endpoint phase nonstationary | `weberPhase`, `hasDerivAt_weberPhase`, `weberPhase_deriv_ne_zero` |
| `(4)` weighted first row `O(c^{-1/2})` | `weighted_firstRow_le`, `tsum_weighted_firstRow_le` |

Reused, not rebuilt: `GaloisForLFunctions.summable_log_div_sq`
(`RHTower/ArcsineZetaTransform.lean`).

## Deliberately outside the Lean statement

- Dunster's radial Bessel model `(1)`–`(2)`;
- the Bessel symbol decomposition `(5)`;
- the stationary-phase lemma and the dyadic estimates `(6)`, `(9)`, `(11)`;
- the coalescence expansion `(12)` and the Weber transform `(13)`.

The card's remaining open gate (exact nonzero-`σ` and Dunster-remainder transfer) is a route gate,
not a statement of this card.
