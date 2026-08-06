# The conductor of a monogenic extension (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **45**.
Continues [[research/monogenic_adjoin_top_2026_08_06]].

## `ConductorAdjoinTop.lean`

- **`conductor_eq_top_of_adjoin_eq_top`** — general: `Algebra.adjoin R {x} = ⊤ ⟹ conductor R x = ⊤`.
  `conductor R x` has carrier `{a | ∀ b, a * b ∈ R<x>}`, so the condition is vacuous.
- **`conductor_eq_top_of_uniformizer`** — the DVR case, via `adjoin_singleton_eq_top`.

## Position in the chain toward the different proper

mathlib: `conductor A x * differentIdeal A B = span {aeval x (derivative (minpoly A x))}`
(hypothesis `Algebra.adjoin K {algebraMap B L x} = ⊤`, **fraction-field level**).

- conductor factor: **done** (this module).
- generation hypothesis at fraction-field level: **still to transport** from the ring-level
  `adjoin_singleton_eq_top`.  Sketch: `A[x] = B ⊆ adjoin K {x}`; `adjoin K {x}` is a field because
  `x` is algebraic over `K` and it is a finite-dimensional domain over a field; a field containing
  `B` contains `Frac B = L`.

## Lean note

`Ideal.eq_top_iff_one` takes the ideal **explicitly**: `(Ideal.eq_top_iff_one _).mpr`.

## Remaining for Theorem A

1. Fraction-field transport ⇒ `differentIdeal A B = (maximalIdeal B)^(e−1)`.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
