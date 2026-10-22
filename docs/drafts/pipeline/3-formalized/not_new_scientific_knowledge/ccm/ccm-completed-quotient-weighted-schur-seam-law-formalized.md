# The completed causal quotient must remain contractive across one exponential-weight seam — formalized closure

- **ID:** `ccm-completed-quotient-weighted-schur-seam-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-completed-quotient-weighted-schur-seam-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMWeightedSchurSeam` (new)
- `GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity` — pre-existing
  `hasDerivAt_normSq_comp`, reused rather than redefined.
- `GaloisForLFunctions.RHTower.CCM.CCMHalfUnitCauchySeam` — `re_hadamardPair_pos`, the positivity of
  `Re (X′/X)` beyond the seam.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(6)` | `re_hadamardPair_pos` (companion card) | `Re (X′/X) > 0` termwise for `Re w > 1/2` |
| `(7)` | `strictMonoOn_normSq_shift`, `re_mul_conj_eq_normSq_mul` | `\|X(c+t)\|²` is strictly increasing along the segment |
| `(2)` | `normSq_lt_normSq_shift` | the completed causal quotient is a strict contraction |
| `(10d)` | `normSq_shift_difference` | the exact factorwise comparison `4ω(d − Re μ)` |
| `(10b)`, `(10e)` | `normSq_shift_le` | each paired factor is no larger on the left line |
| `(11)`, `(25a)` | `distinguishedExponent`, `distinguishedExponent_sub_safeWidth` | the invariant prelimit deficit is exactly `1/2` |
| `(12)` | `shifted_quotient_arguments` | conjugation by `a_ω` gives the symmetric shifted form |
| `(15)`, `(16)` → `(14)` | `schur_denominator_substitution` | the Schur denominator becomes the shifted Cauchy denominator |
| `(30)` | `blaschkeZero`, `re_blaschkeZero_pos` | the Blaschke zero of an off-line zero lies in the right half-plane |

## Axioms

`#print axioms` on all nine declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Hadamard product `(5)` with locally uniform symmetric summation.
- The Smirnov maximum principle upgrading the boundary comparison `(10e)` to the `H^∞` bound
  `(10b)`, and the Paley–Wiener multiplier theorem.
- The shifted Hermite–Biehler/Suzuki criterion and the negative-index formula `(17)`.
- The inner–outer factorization `(18)`–`(21)`, the model-space dimension count, and the
  Poisson–Müntz range identification `(28)`.
- The card's open gate: proving from the Euler–Gamma source that every denominator model space
  vanishes; and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMWeightedSchurSeam`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
