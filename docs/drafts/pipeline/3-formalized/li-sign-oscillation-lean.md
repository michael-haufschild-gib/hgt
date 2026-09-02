# Li coefficients are never eventually negative

- **ID:** LI-LEAN-OSC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `5-failed/position-independent-integer-loop.md`
- **Statement:** off the line the paired Li coefficients are positive for arbitrarily large `n`;
  unconditionally they are never eventually negative. Abstract form for any symmetric family with
  a non-unimodular non-real member.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.LiSignOscillation` | `exists_ge_pow_sub_one_lt`, `exists_re_sum_pow_neg` (mean value on the torus), `pow_mul_div_pow_cancel`, `exists_ge_re_tsum_liTerm_pos`, `exists_ge_re_xiLiPaired_pos_of_not_riemannHypothesis`, `not_eventually_re_xiLiPaired_neg` |

Inputs: `LiPositivityFails` (`exists_pos_pow_sub_one_lt`, `finite_far_set`,
`summable_re_liTerm_of_one_le`), `LiTermBound.norm_liTerm_le`, `LiCoefficientXi`, `LiCriterion`
(`xiRootV`, `liTerm_xiRootV`, `riemannHypothesis_iff_xi_zero_re_eq_half`). Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3.
