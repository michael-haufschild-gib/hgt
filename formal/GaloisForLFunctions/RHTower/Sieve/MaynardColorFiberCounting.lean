import GaloisForLFunctions.RHTower.Sieve.MaynardAllShortFiniteSet

/-!
# Summing pointwise selections over color fibres

Box/group selection assigns every large ordinate a finite label.  Arbitrary-finset Huxley controls
each label fibre.  These lemmas perform the exact final summation, with either label-dependent
thresholds or one uniform lower threshold.
-/

namespace RHTower.Sieve

open Finset

/-- Exact cardinal decomposition into all fibres of a finite coloring. -/
theorem card_eq_sum_color_fibres
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset α) (color : α → κ) :
    S.card = ∑ c : κ, (S.filter fun a => color a = c).card := by
  exact Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _

/-- Label-dependent weighted fibre bounds sum to a bound for the original finite set. -/
theorem card_le_sum_div_sq_of_color_fibre_bounds
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset α) (color : α → κ) (V H : κ → ℝ)
    (hV : ∀ c, 0 < V c)
    (hbound : ∀ c,
      (((S.filter fun a => color a = c).card : ℕ) : ℝ) * (V c) ^ 2 ≤ H c) :
    (S.card : ℝ) ≤ ∑ c : κ, H c / (V c) ^ 2 := by
  have hcast : (S.card : ℝ) =
      ∑ c : κ, (((S.filter fun a => color a = c).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  rw [hcast]
  apply Finset.sum_le_sum
  intro c _hc
  exact (le_div_iff₀ (sq_pos_of_pos (hV c))).mpr (hbound c)

/-- Uniform form: number of labels is the only counting loss once all fibre estimates share a
common lower threshold and upper majorant. -/
theorem card_mul_sq_le_card_labels_mul_of_color_fibre_bounds
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset α) (color : α → κ) {Vmin Hmax : ℝ}
    (hVmin : 0 < Vmin) (V H : κ → ℝ)
    (hV : ∀ c, Vmin ≤ V c) (hH : ∀ c, H c ≤ Hmax)
    (hbound : ∀ c,
      (((S.filter fun a => color a = c).card : ℕ) : ℝ) * (V c) ^ 2 ≤ H c) :
    (S.card : ℝ) * Vmin ^ 2 ≤ (Fintype.card κ : ℝ) * Hmax := by
  have hfibre : ∀ c,
      (((S.filter fun a => color a = c).card : ℕ) : ℝ) * Vmin ^ 2 ≤ Hmax := by
    intro c
    have hsq : Vmin ^ 2 ≤ (V c) ^ 2 :=
      pow_le_pow_left₀ hVmin.le (hV c) 2
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans
      ((hbound c).trans (hH c))
  have hcast : (S.card : ℝ) =
      ∑ c : κ, (((S.filter fun a => color a = c).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  calc
    (S.card : ℝ) * Vmin ^ 2 =
        ∑ c : κ, (((S.filter fun a => color a = c).card : ℕ) : ℝ) * Vmin ^ 2 := by
      rw [hcast, Finset.sum_mul]
    _ ≤ ∑ _c : κ, Hmax := Finset.sum_le_sum fun c _ => hfibre c
    _ = (Fintype.card κ : ℝ) * Hmax := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end RHTower.Sieve
