# Global parity wall: odd-order critical zeros above every height; copies dichotomy

- **ID:** WALL-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** no-go closure of `5-failed/metaplectic-transfer-operator-kramers.md`; Hardy chain
  (`false_of_hardyXiDensity_tail_sign`), `HardySignFlipOddOrder`.
- **Statement:** `Ξ` takes both strict signs above every height; hence ξ has critical-line
  zeros of odd order above every height, and not every order of ξ is even. For `f^e · u` with
  `u` nonvanishing, the order is `e` times the order of `f`; an even `e` makes all orders even,
  an odd `e` preserves parity; for ξ the parity of `ξ^e · u` is void or violated.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.GlobalParityWall` | `Xi_eq_re_xi_linePt`, `false_of_Xi_eventually_nonneg`, `false_of_Xi_eventually_nonpos`, `exists_Xi_neg_gt`, `exists_Xi_pos_gt`, `exists_Xi_sign_flip_gt`, `exists_odd_order_line_zero_gt`, `exists_odd_order_zero_xi`, `not_forall_even_order_xi`, `not_forall_two_dvd_order_xi`, `analyticOrderAt_pow_mul_unit`, `toNat_analyticOrderAt_pow_mul_unit`, `even_order_of_even_copies`, `odd_order_copies_iff`, `xi_copies_parity_dichotomy`, `det_involution_symmetric` |

Axioms: `propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3.
