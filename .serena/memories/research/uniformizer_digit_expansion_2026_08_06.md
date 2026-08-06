# Digit expansion in a uniformizer (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **43**.
Continues [[research/tame_different_free_extension_2026_08_06]].

## `UniformizerDigitExpansion.lean`

- `dvd_of_addVal_ne_zero` — positive valuation ⟹ divisible by a uniformizer
  (`addVal_le_iff_dvd` + `Order.one_le_iff_ne_zero`).
- **`exists_digit_expansion`** — with the residue extension trivial
  (`∀ b, ∃ a : A, addVal B (b − ψ a) ≠ 0`), for every `n` and `b`:

      b = ∑_{i<n} ψ (c i) * x^i + x^n * b'

  Induction on `n`, generalizing `b`.

Carried to `n = e`, and since `x^e` and `ψ π_A` are associates, this says the powers `x^i`, `i < e`,
generate `B` **modulo `m_A B`**.  Nakayama would then give `B = A[x]` — the last step to upgrade
"derivative of the characteristic polynomial" to "the different" (see module 42).

## Lean notes

- Building the digit function as `fun i => if i = 0 then a0 else d (i - 1)` and then using it
  inside `Finset.sum_range_succ'` leaves an unreduced `if True then …`; `simp only [if_pos rfl]`
  does **not** fire.  Fix: `set c := … with hc` and prove `c 0 = a0`, `c (i+1) = d i` as separate
  `have`s, then rewrite with those — never let the `if` reach `ring`.
- `linear_combination (norm := ring_nf) hq` turns `b − ψ a0 = x * q` into `b = ψ a0 + x * q`
  cleanly.

## Remaining for Theorem A

1. Nakayama ⇒ `B = A[x]` (then module 42's statement becomes the different proper).
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
