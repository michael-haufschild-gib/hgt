# Formalization certificate — `ccm-polar-euler-frame-minus-level-law`

- **Card:** `ccm-polar-euler-frame-minus-level-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMPolarEulerFrameLevel.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 9 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(2)`–`(3)` digamma resolvent summands | `re_inv_add_mul_I`, `digamma_term_identity`, `digamma_term_nonneg` |
| `(7)` prime translation-difference square | `normSq_one_sub_exp`, `prime_difference_square` |
| `(10)` polar even/odd splitting | `polar_kernel_split` |
| `(14)` → `(15)` even sector | `frame_minus_level_even` |
| `(16)` odd sector | `frame_minus_level_odd` |
| `(17)` lower-frame restatement | `lower_frame_iff` |

## Deliberately outside the Lean statement

- the digamma partial-fraction series and its rescaling;
- Plancherel and the resolvent/translation operators `(4)`, `(8)`, `(13)`;
- the Paley–Wiener compression and the corrected aperture symbol;
- Yoshida's even Weil criterion.

The card's remaining open gates (prove the lower-frame inequality `(17)`; RH) are route gates, not
statements of this card.
