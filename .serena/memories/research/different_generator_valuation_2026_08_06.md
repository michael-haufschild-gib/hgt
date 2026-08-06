# The different as a valuation statement (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 50,
`DifferentExponentTame.lean`.  See [[research/tame_different_exponent_assembled_2026_08_06]].

## Added

- `addVal_eq_of_span_singleton_eq` — generators of the same principal ideal have equal valuation
  (via `Ideal.span_singleton_le_span_singleton` both ways + `addVal_le_iff_dvd`).
- **`addVal_generator_differentIdeal`** — any generator `y` of `differentIdeal A B` has
  `addVal B y = e − 1`.

This is **literally the `hjac` hypothesis of the horizon theorem** ("the Jacobian factor has order
`e − 1` at each prime divisor").  The `e − 1` of card equation (8) is no longer data anywhere in
the local theory.

## Lean note

`omit` **cannot drop an instance that another retained instance depends on** — trying to omit
`IsDedekindDomain B` while keeping the DVR structure gives "cannot omit referenced section
variable".  Fix: put the low-dependency lemma in its **own `section` with its own minimal
`variable` block**, before the heavy bundle, rather than fighting `omit`.

## Remaining for Theorem A

1. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
2. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
3. Corollary B: MMP.
