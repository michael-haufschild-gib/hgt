import Mathlib

/-!
# The target occurs among its twists

Twisting by the `n`-th power residue symbol of `a^n` is the trivial twist, so a row `u` of a family
of twists occurs again at every index `u a^n`. If the rows of the long family have a mean square
`T`, the rows that occur `m` times have mean square at most `T/m`
(`card_mul_sum_le_of_injective`): positivity in the place of a comparison.

In exponents: a generic mean square `P Z` of the Möbius sums of length `Z` over the twists of norm
up to `P = Z^θ`, the principal twists included, bounds the square of the target by
`P^{1 − 1/n} Z`, that is the half-plane `positiveFormBoundary n θ = ½ + (1 − 1/n) θ/2`. For the
sextic symbol this is `11/12` at `θ = 1`, `7/8` at `θ = 9/10`, `13/15` at `θ = 22/25` and `5/6`
at `θ = 4/5`; the line `½` is `θ = 0` for every order.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory

open Finset

/-- **Amplification by multiplicity.** If every row `u` is dominated by `C` times the row
`ι (u, a)` of a longer family, for an injective `ι`, then `card A` times the sum over the rows is
at most `C` times the sum over the longer family. -/
theorem card_mul_sum_le_of_injective {U A V : Type*} [Fintype U] [Fintype A] [Fintype V]
    [DecidableEq V] (ι : U × A → V) (hι : Function.Injective ι) {f : U → ℝ} {g : V → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ v, 0 ≤ g v) (h : ∀ u a, f u ≤ C * g (ι (u, a))) :
    (Fintype.card A : ℝ) * ∑ u, f u ≤ C * ∑ v, g v := by
  have h1 : (Fintype.card A : ℝ) * ∑ u, f u = ∑ p : U × A, f p.1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Finset.sum_const, Finset.card_univ]
  have h2 : ∑ p : U × A, f p.1 ≤ ∑ p : U × A, C * g (ι p) :=
    Finset.sum_le_sum fun p _ => h p.1 p.2
  have h3 : ∑ p : U × A, g (ι p) ≤ ∑ v, g v := by
    rw [← Finset.sum_image (s := Finset.univ) (g := ι) (f := g) fun x _ y _ hxy => hι hxy]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => hg v
  calc (Fintype.card A : ℝ) * ∑ u, f u = ∑ p : U × A, f p.1 := h1
    _ ≤ ∑ p : U × A, C * g (ι p) := h2
    _ = C * ∑ p : U × A, g (ι p) := by rw [Finset.mul_sum]
    _ ≤ C * ∑ v, g v := mul_le_mul_of_nonneg_left h3 hC

/-- The half-plane given by a generic mean square over the twists of norm up to `Z^θ`, when the
principal twists are the `n`-th powers. -/
noncomputable def positiveFormBoundary (n θ : ℝ) : ℝ := 1 / 2 + (1 - 1 / n) * θ / 2

/-- The exponent count: `P^{1/n} · Z^{2β} ≤ P · Z` with `P = Z^θ` is `β ≤ ½ + (1 − 1/n) θ/2`. -/
theorem le_positiveFormBoundary_iff (n θ β : ℝ) :
    θ / n + 2 * β ≤ θ + 1 ↔ β ≤ positiveFormBoundary n θ := by
  unfold positiveFormBoundary
  constructor <;> intro h <;> linarith [mul_one_div θ n, one_div_mul_eq_div n θ]

theorem positiveFormBoundary_six (θ : ℝ) : positiveFormBoundary 6 θ = 1 / 2 + 5 * θ / 12 := by
  unfold positiveFormBoundary
  ring

/-- Family as long as the sums: the balanced boundary `11/12`. -/
theorem positiveFormBoundary_six_one : positiveFormBoundary 6 1 = 11 / 12 := by
  norm_num [positiveFormBoundary]

/-- The published boundary `7/8` is the family length `θ = 9/10`. -/
theorem positiveFormBoundary_six_nine_tenths : positiveFormBoundary 6 (9 / 10) = 7 / 8 := by
  norm_num [positiveFormBoundary]

/-- The floor `13/15` of the budget is the family length `θ = 22/25`. -/
theorem positiveFormBoundary_six_floor : positiveFormBoundary 6 (22 / 25) = 13 / 15 := by
  norm_num [positiveFormBoundary]

/-- The barrier `5/6` of the low side is the family length `θ = 4/5`. -/
theorem positiveFormBoundary_six_barrier : positiveFormBoundary 6 (4 / 5) = 5 / 6 := by
  norm_num [positiveFormBoundary]

/-- The line is the family of length zero, for every order of the symbol. -/
theorem positiveFormBoundary_zero (n : ℝ) : positiveFormBoundary n 0 = 1 / 2 := by
  norm_num [positiveFormBoundary]

/-- A shorter family gives a lower boundary. -/
theorem positiveFormBoundary_mono {n θ θ' : ℝ} (hn : 1 ≤ n) (h : θ ≤ θ') :
    positiveFormBoundary n θ ≤ positiveFormBoundary n θ' := by
  unfold positiveFormBoundary
  have h1 : 0 ≤ 1 - 1 / n := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hn
  nlinarith [mul_le_mul_of_nonneg_left h h1]

end GaloisForLFunctions.FamilyContinuationTheory
