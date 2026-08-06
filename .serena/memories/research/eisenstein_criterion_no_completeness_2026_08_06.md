# The Eisenstein criterion, without completeness (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **40**.
Continues [[research/addval_strict_min_principle_2026_08_06]].

## `EisensteinCriterion.lean`

**`eisenstein_of_monic_uniformizer_root`** — for `ψ : A →+* B` of DVRs with ramification index `e`,
`x` a uniformizer of `B` (`addVal B x = 1`), and `g : A[X]` monic of degree `e` with
`eval x (g.map ψ) = 0`:

    (∀ i < e, addVal A (g.coeff i) ≠ 0) ∧ addVal A (g.coeff 0) = 1

i.e. **`g` is Eisenstein**.

Proof shape: term `i` has valuation `e·v(c_i) + i`; these are pairwise distinct because their
residues mod `e` are the distinct indices `i < e`; `Finset.exists_min_image` picks the minimiser;
`Order.add_one_le_of_lt` upgrades minimality to the strict gap needed by
`addVal_sum_eq_of_strict_min`; the sum's valuation is `v(x^e) = e`, so the minimiser is `≡ 0 mod e`
hence `0`, giving `v(c_0) = 1`; every other index then exceeds `e`, giving `v(c_i) ≥ 1`.

## The finding

**Completeness is not needed for this direction.**  I had recorded monogenicity as blocked on
Hensel/completeness; that is only true for the *existence* of the monic relation (`B = A[x]`).
Given the relation, Eisenstein-ness is pure valuation arithmetic.

## Lean notes

- `set f := … with h` makes `h : f = …`; `rw [← h]` then fails on goals already displaying the
  unfolded form.  Use `show <unfolded> ; rw [named lemma]` instead.
- To prove `t i₀ ≠ 0` when a valuation formula for `t i₀` is in hand, do **not** chase injectivity
  of `ψ` (which can fail): rewrite the formula under `t i₀ = 0` and contradict `⊤ ≠ ↑n`.
- `Order.add_one_le_of_lt` is the ℕ∞-safe way from `a < b` to `a + 1 ≤ b`.

## Remaining for Theorem A

1. `B = A[x]` — existence of the monic degree-`e` relation (still needs completeness).
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
