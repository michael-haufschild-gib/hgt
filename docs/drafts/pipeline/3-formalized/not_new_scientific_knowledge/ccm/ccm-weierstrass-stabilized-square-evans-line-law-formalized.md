# Formalization certificate — `ccm-weierstrass-stabilized-square-evans-line-law`

- **Card:** `ccm-weierstrass-stabilized-square-evans-line-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMWeierstrassStabilizedEvans.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 6 theorems
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| conjugate values of a real polynomial | `eval_conj_of_real` |
| `(2)` claim 2: conjugate pairing of stabilized roots | `isRoot_conj_iff` |
| `(2)` claim 3: root-free monic factor is positive | `eval_pos_of_monic_no_real_root` |
| `(3)` positivity of the quotient | `one_add_sq_pow_pos`, `stabilized_quotient_pos` |
| `(12)` empty zero divisor restatement | `evans_zero_divisor_empty_iff` |

## Deliberately outside the Lean statement

- Weierstrass preparation and the chart construction `(2)`;
- the analytic solution bundle `(9)` and the square map `(4)`;
- the Grushin reduction, determinant-line functor `(10)`, gluing `(6)`;
- analytic Fredholm multiplicity `(7)`;
- the logarithmic decomposition `(8)`.

The card's remaining open gates (prove the zero divisor avoids `λ ≤ 0` at every aperture; RH) are
route gates, not statements of this card.
