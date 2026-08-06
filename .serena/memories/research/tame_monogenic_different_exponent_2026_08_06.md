# Tame different exponent for a monogenic extension (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **37**.
Continues [[research/tame_monic_different_exponent_2026_08_06]].

## `TameMonogenicDifferentExponent.lean`

- **`le_addVal_map_of_addVal_ne_zero`** — a coefficient in the maximal ideal of `A` has
  `addVal B (ψ c) ≥ e`, because `addVal_map_eq_mul_ramification` makes the index multiply
  valuations.  This is precisely the bound the exact computation requires, so the coefficient
  hypothesis of module 36 is *derived* rather than assumed.
- **`addVal_eval_derivative_map_eisenstein`** — for `ψ : A →+* B` of DVRs with ramification index
  `e`, an Eisenstein `g : A[X]` monic of degree `e`, `x` a uniformizer of `B`, and `e` a unit at
  the place: `addVal B (eval x (derivative (g.map ψ))) = e − 1`.

The `e − 1` of the card's order law (8) is now proved for **every monogenic tame totally ramified
extension** — hypotheses are the extension plus its Eisenstein presentation, nothing about the
polynomial's shape and no explicit coefficient bound.

## Lean notes (v4.32.2 deprecations — these fail the gate)

- `mul_le_mul_left'` → deprecated; `gcongr` handles `e * 1 ≤ e * x` cleanly instead.
- `ENat.one_le_iff_ne_zero` → `Order.one_le_iff_ne_zero` (different namespace, dot notation
  changes).

## Remaining for Theorem A

1. Existence of the Eisenstein presentation itself (monogenicity of a totally ramified extension —
   standard for complete DVRs, needs Hensel/completeness in Lean).
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
