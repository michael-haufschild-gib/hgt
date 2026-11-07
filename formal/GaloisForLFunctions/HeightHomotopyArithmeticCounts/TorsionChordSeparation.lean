import GaloisForLFunctions.HeightHomotopyArithmeticCounts.RadialLogarithmicKernel
import Mathlib.Algebra.Field.GeomSum

/-!
# Elementary torsion separation

A vanishing geometric sum forces a nontrivial root of unity of order dividing
`L` to lie at distance at least `1/L` from one. Squared inverse chords therefore
admit a polynomial conductor bound without choosing angular coordinates.
-/

noncomputable section
open Finset Complex
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

private theorem unit_pow_chord_le (u : ℂ) (hu : ‖u‖ = 1) (k : ℕ) :
    ‖u^k-1‖ ≤ (k : ℝ)*‖u-1‖ := by
  induction k with
  | zero => simp only [pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    calc
      ‖u^(k+1)-1‖ = ‖u^k*(u-1)+(u^k-1)‖ := by congr 1; ring
      _ ≤ ‖u^k*(u-1)‖+‖u^k-1‖ := norm_add_le _ _
      _ ≤ ‖u-1‖+(k:ℝ)*‖u-1‖ := by
        rw [norm_mul, _root_.norm_pow, hu, one_pow, one_mul]
        exact add_le_add (le_refl _) ih
      _ = ((k+1:ℕ):ℝ)*‖u-1‖ := by push_cast; ring

/-- Elementary separation of a nontrivial torsion point from one. -/
theorem root_chord_conductor_bound (L : ℕ) (hL : 0 < L) (u : ℂ)
    (hu : ‖u‖=1) (hne : u≠1) (hp : u^L=1) :
    1 ≤ (L:ℝ)*‖1-u‖ := by
  have hsum : ∑ k ∈ range L, u^k = 0 := by
    rw [geom_sum_eq hne, hp, sub_self, zero_div]
  have heq : (∑ k ∈ range L, (1-u^k)) = (L:ℂ) := by
    rw [sum_sub_distrib, hsum, sub_zero]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hb : (L:ℝ) ≤ (L:ℝ)*((L:ℝ)*‖1-u‖) := by
    calc
      (L:ℝ) = ‖∑ k ∈ range L, (1-u^k)‖ := by
        rw [heq, Complex.norm_natCast]
      _ ≤ ∑ k ∈ range L, ‖1-u^k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range L, (L:ℝ)*‖1-u‖ := by
        apply sum_le_sum
        intro k hk
        rw [norm_sub_rev]
        calc ‖u^k-1‖ ≤ (k:ℝ)*‖u-1‖ := unit_pow_chord_le u hu k
          _ ≤ (L:ℝ)*‖1-u‖ := by
            rw [norm_sub_rev u 1]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hk).le) (norm_nonneg _)
      _ = (L:ℝ)*((L:ℝ)*‖1-u‖) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
  have hLr : (0:ℝ)<L := by exact_mod_cast hL
  by_contra hn
  have hc := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hLr
  exact (not_lt_of_ge hb) (by simpa only [mul_one] using hc)

/-- Squared inverse chords have a polynomial conductor majorant. -/
theorem inverse_chord_le_conductor_sq (L : ℕ) (hL : 0 < L) (u : ℂ)
    (hu : ‖u‖=1) (hne : u≠1) (hp : u^L=1) :
    1/‖1-u‖^2 ≤ (L:ℝ)^2 := by
  have hd : 0 < ‖1-u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  rw [div_le_iff₀ hd]
  have h := root_chord_conductor_bound L hL u hu hne hp
  have hs := sq_nonneg ((L:ℝ)*‖1-u‖-1)
  nlinarith only [h, hs]

#print axioms inverse_chord_le_conductor_sq
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
