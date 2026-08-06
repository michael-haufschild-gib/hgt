# The powers of a uniformizer are a basis (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **48**.
Continues [[research/different_ideal_monogenic_2026_08_06]].

## `UniformizerPowerBasis.lean`

- **`linearIndependent_pow`** — `x^i`, `i : Fin e`, are linearly independent over `A`.
  Same skeleton as the Eisenstein criterion (module 40): valuations `e·v(g i) + i` are pairwise
  distinct mod `e`, `Finset.exists_min_image` + `Order.add_one_le_of_lt` +
  `addVal_sum_eq_of_strict_min` give the sum a **finite** valuation, contradicting `= 0` (⊤).
  Uses `linearIndependent_iff'`.
- **`uniformizerPowBasis`** — with `span_pow_eq_top`, `Module.Basis.mk` gives a basis.
- **`finrank_eq_ramificationIndex`** — `Module.finrank A B = e`, **proved rather than assumed**.

## Why this matters

Earlier modules (42, and the different chain) *hypothesised* `Module.finrank A B = e`
("totally ramified").  It is now a consequence of: finite extension of DVRs + trivial residue
extension + `algebraMap πA ∣ x^e`.  It is also the degree identification the different statement
needs (`natDegree (minpoly A x) = e` will follow from the power basis).

## Pattern worth reusing

The "distinct residues mod e ⇒ unique valuation minimum ⇒ sum has finite valuation" argument has
now been used three times (Eisenstein criterion, this independence proof, and implicitly in the
different).  `addVal_sum_eq_of_strict_min` (module 39) is the reusable core.

## Remaining for Theorem A

1. `natDegree (minpoly A x) = e` from the power basis ⇒ `differentIdeal A B = (maximalIdeal B)^(e−1)`.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
