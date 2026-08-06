# The strict minimum principle for valuations (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **39**.
Continues [[research/different_exponent_consolidated_2026_08_06]].

## `AddValuationStrictMin.lean`

- `lt_add_one_of_ne_zero` — `addVal B x < addVal B x + 1` for `x ≠ 0`.  Needed because
  **`lt_add_one` is unavailable in ℕ∞** (`⊤ + 1 = ⊤`); cast up from ℕ.
- **`addVal_sum_eq_of_strict_min`** — a finite sum with one term of valuation strictly below every
  other has exactly that valuation.  Proof: `Finset.add_sum_erase` + `le_addVal_sum` on the tail +
  `AddValuation.map_add_of_distinct_val`.
- `addVal_sum_lt_of_strict_min`.

The corpus previously had only the **inequality** direction (`le_addVal_sum`, in
`TameEisensteinDifferentExponent.lean`).  This is the exact statement, which converts valuation
estimates into valuation computations.

## Why it was built: the plan for monogenicity

For the Eisenstein *criterion* (deriving Eisenstein-ness rather than assuming it): if `x` is a
uniformizer satisfying a monic degree-`e` relation `x^e = −Σ_{i<e} ψ(c_i) x^i` over `A`, the terms
have valuations `e·v_A(c_i) + i`, which are **pairwise distinct modulo `e`** for `i ∈ [0,e)`.
Hence the minimum is attained exactly once and the sum's valuation equals it.  Since the sum's
valuation is `v(x^e) = e`, the minimizing index must be `0` (the only one `≡ 0 mod e`), giving
`v_A(c_0) = 1`, and every other term must exceed `e`, giving `v_A(c_i) ≥ 1`.

**No completeness or Hensel is needed for this direction** — that was the expected obstacle, and it
turns out to be avoidable.  What still needs completeness is only that `B = A[x]` (that a monic
relation of degree exactly `e` exists at all).

## Lean note

`s.erase i₀` appearing in a *statement* requires `[DecidableEq ι]` as an explicit binder;
`classical` inside the proof is too late.

## Remaining for Theorem A

1. Existence of the degree-`e` monic relation (`B = A[x]` — needs completeness).
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
