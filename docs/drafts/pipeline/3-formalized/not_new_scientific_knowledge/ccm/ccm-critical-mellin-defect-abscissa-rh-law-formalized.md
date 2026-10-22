# Formalization certificate — `ccm-critical-mellin-defect-abscissa-rh-law`

- **Card:** `ccm-critical-mellin-defect-abscissa-rh-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMCriticalMellinAbscissa.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 5 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `∫_1^X (log t)²/t = (log X)³/3` | `integral_log_sq_div_self` |
| `(9)` endpoint term `O(h²)` | `vonKoch_endpoint_bound` |
| `(9)` integral term `O(h³)` | `vonKoch_integral_bound` |
| `(10)` → `(ii)` polynomial ⟹ subexponential | `eventually_le_exp_of_poly_bound` |
| `(ii)` → `(iii)` abscissa vanishes | `tendsto_logAbscissa_zero` |

## Deliberately outside the Lean statement

- the Laplace–Stieltjes identity `(2)` and its integrated form `(5)`;
- the continuation/identity-theorem step and the zeta zero-to-pole correspondence `(6)`, hence
  `(3) → (4)` and `(12)`–`(13)`;
- the von Koch theorem `(8)` and the partial-summation identity `(9)`.

The card's remaining open gates (prove `ω_R = 0` from the Euler–Gamma source; RH) are route gates,
not statements of this card.
