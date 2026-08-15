# Formalization certificate — `ccm-restricted-weil-square-evans-determinant-law`

- **Card:** `ccm-restricted-weil-square-evans-determinant-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilSquareEvans.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` (one theorem uses `[propext]` only)
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(3)`–`(4)` equal dimensions, square map | `finrank_source_eq_target` |
| `(9)` determinant criterion | `det_eq_zero_iff_ker_ne_bot` |
| `(8)`–`(9)` eigenspace ⟺ determinant | `eigenspace_eq_bot_iff_det_ne_zero` |
| `(18)` Morse formula | reused `CCMSpectralParameterEvans.sum_finrank_ker_eq` |
| `(22)` parity grading | `parity_split_dim` |

## Deliberately outside the Lean statement

- the restricted Weil form `(11)` and its Toeplitz compression `(12)`;
- the logarithmic Dirichlet reconstruction `(5)` and the Carleman cross block `(16)`;
- the Bessel residual computation `(6)`;
- the determinant-line identification `(10)`.

The card's remaining open gates (nonvanishing on `λ ≤ 0` at every aperture; RH) are route gates,
not statements of this card.
