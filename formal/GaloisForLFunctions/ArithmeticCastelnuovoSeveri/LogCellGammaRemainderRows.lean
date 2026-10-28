import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment

/-!
# Endpoint losses in logarithmic Gamma rows

Replacing a cell interaction by its farthest-endpoint weight loses a difference
of two monotone kernel readings. On nearby nonadjacent cells, four shifts
telescope the whole outgoing row. The resulting bound is independent of index.
-/

noncomputable section
open Finset
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry SpacingScaleHarmonicAnalysis

private theorem sum_range_drop (g : ℕ → ℝ) (s N : ℕ) :
    (∑ n ∈ range N, (g (s + n) - g (s + n + 1))) = g s - g (s + N) := by
  induction N with
  | zero => simp only [sum_range_zero, Nat.add_zero, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_succ]
    ring

private theorem sum_shift_drop_le (g : ℕ → ℝ) (hpos : ∀ n, 0 ≤ g n)
    (hanti : Antitone g) (N k : ℕ) :
    (∑ n ∈ range N, (g n - g (n + k))) ≤ (k : ℝ) * g 0 := by
  have hblock (n : ℕ) : g n - g (n + k) =
      ∑ j ∈ range k, (g (n + j) - g (n + j + 1)) := (sum_range_drop g n k).symm
  calc
    _ = ∑ j ∈ range k, ∑ n ∈ range N, (g (j + n) - g (j + n + 1)) := by
      simp_rw [hblock]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _hj
      apply sum_congr rfl
      intro n _hn
      rw [Nat.add_comm n j]
    _ = ∑ j ∈ range k, (g j - g (j + N)) :=
      sum_congr rfl fun j _ => sum_range_drop g j N
    _ ≤ ∑ _j ∈ range k, g 0 := sum_le_sum fun j _ =>
      (sub_le_self (g j) (hpos (j + N))).trans (hanti (Nat.zero_le j))
    _ = (k : ℝ) * g 0 := by simp only [sum_const, card_range, nsmul_eq_mul]

/-- Upper-side endpoint loss from nonadjacent cells up to twice the source index. -/
def gammaCellNearUpperRemainder (a : ℕ) : ℝ :=
  ∑ n ∈ range (a - 1), logCellWidth (a + 2 + n) *
    (archLevyDensity (Real.log ((a + 2 + n : ℕ) : ℝ) - Real.log ((a + 1 : ℕ) : ℝ)) -
      archLevyDensity (Real.log ((a + 3 + n : ℕ) : ℝ) - Real.log (a : ℝ)))

/-- Four monotone shifts pay the whole nearby nonadjacent Gamma row, uniformly in its index. -/
theorem gammaCellNearUpperRemainder_le {a : ℕ} (ha : 1 ≤ a) :
    gammaCellNearUpperRemainder a ≤ 6 * Real.exp (1 / 2) := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  let G : ℕ → ℝ := fun n => archLevyDensity
    (Real.log ((a + 2 + n : ℕ) : ℝ) - Real.log ((a + 1 : ℕ) : ℝ))
  have harg (n : ℕ) : 0 < Real.log ((a + 2 + n : ℕ) : ℝ) -
      Real.log ((a + 1 : ℕ) : ℝ) := by
    apply sub_pos.mpr
    apply Real.log_lt_log (by positivity)
    exact_mod_cast (show a + 1 < a + 2 + n by omega)
  have hGpos (n : ℕ) : 0 ≤ G n := (archLevyDensity_pos (harg n)).le
  have hGanti : Antitone G := by
    intro n m hnm
    apply strictAntiOn_archLevyDensity.antitoneOn (harg n) (harg m)
    apply sub_le_sub_right
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show a + 2 + n ≤ a + 2 + m by omega)
  have hterm (n : ℕ) (hn : n ∈ range (a - 1)) :
      logCellWidth (a + 2 + n) *
        (G n - archLevyDensity (Real.log ((a + 3 + n : ℕ) : ℝ) - Real.log (a : ℝ))) ≤
      (1 / (a : ℝ)) * (G n - G (n + 4)) := by
    let b := a + 2 + n
    have hb : 1 ≤ b := by dsimp only [b]; omega
    have hba : a ≤ b := by dsimp only [b]; omega
    have hb2a : (b : ℝ) ≤ 2 * a := by
      exact_mod_cast (show b ≤ 2 * a by have := mem_range.mp hn; dsimp only [b]; omega)
    have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
    have hfar : 0 < Real.log (((b + 1 : ℕ) : ℝ)) - Real.log (a : ℝ) := by
      apply sub_pos.mpr
      apply Real.log_lt_log ha0
      exact_mod_cast (show a < b + 1 by omega)
    have hratio : (((b + 1 : ℕ) : ℝ) / (a : ℝ)) ≤
        (((b + 4 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
      apply (div_le_div_iff₀ ha0 (by positivity)).mpr
      push_cast
      nlinarith only [hb2a, ha1]
    have hlog := Real.log_le_log (div_pos (by positivity) ha0) hratio
    rw [Real.log_div (by positivity) ha0.ne', Real.log_div (by positivity) (by positivity)] at hlog
    have hb1 : b + 1 = a + 3 + n := by dsimp only [b]; omega
    have hb4 : b + 4 = a + 2 + (n + 4) := by dsimp only [b]; omega
    rw [hb4] at hlog
    have hshift : G (n + 4) ≤
        archLevyDensity (Real.log ((a + 3 + n : ℕ) : ℝ) - Real.log (a : ℝ)) := by
      have h := strictAntiOn_archLevyDensity.antitoneOn hfar (harg (n + 4)) hlog
      rw [hb1] at h
      exact h
    have hw : logCellWidth b ≤ 1 / (a : ℝ) :=
      (logCellWidth_le_inv hb).trans
        (one_div_le_one_div_of_le ha0 (by exact_mod_cast hba))
    calc
      _ ≤ logCellWidth b * (G n - G (n + 4)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hshift _) (logCellWidth_pos hb).le
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr (hGanti (by omega)))
  have hG0 : G 0 ≤ Real.exp (1 / 2) * ((a : ℝ) + 2) / 2 := by
    have hw0 := logCellWidth_pos (show 1 ≤ a + 1 by omega)
    have hw1 : logCellWidth (a + 1) ≤ 1 :=
      (logCellWidth_le_inv (by omega)).trans
        ((div_le_one (by positivity : (0 : ℝ) < (a + 1 : ℕ))).mpr (by exact_mod_cast (show 1 ≤ a + 1 by omega)))
    have hlower : 1 / ((a : ℝ) + 2) ≤ logCellWidth (a + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one,
        show (a : ℝ) + 1 + 1 = (a : ℝ) + 2 by ring] using
        inv_add_one_le_logCellWidth (show 1 ≤ a + 1 by omega)
    have hmul := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ (a : ℝ) + 2)
    have he : ((a : ℝ) + 2) * (1 / ((a : ℝ) + 2)) = 1 := by field_simp
    rw [he] at hmul
    have hscaled := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (1 / 2)).le
    calc
      G 0 = archLevyDensity (logCellWidth (a + 1)) := by
        simp only [G, logCellWidth, Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero,
          show (a : ℝ) + 1 + 1 = (a : ℝ) + 2 by ring]
      _ ≤ Real.exp (1 / 2) / (2 * logCellWidth (a + 1)) :=
        archLevyDensity_le_sqrt_e_div hw0 hw1
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hw0)).mpr
        nlinarith only [hscaled]
  calc
    gammaCellNearUpperRemainder a ≤
        (1 / (a : ℝ)) * ∑ n ∈ range (a - 1), (G n - G (n + 4)) := by
      rw [mul_sum]
      exact sum_le_sum hterm
    _ ≤ (1 / (a : ℝ)) * ((4 : ℝ) * G 0) :=
      mul_le_mul_of_nonneg_left (sum_shift_drop_le G hGpos hGanti (a - 1) 4) (by positivity)
    _ ≤ (1 / (a : ℝ)) * (4 * (Real.exp (1 / 2) * ((a : ℝ) + 2) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG0 (by norm_num)) (by positivity)
    _ = (2 * Real.exp (1 / 2) * ((a : ℝ) + 2)) / a := by ring
    _ ≤ 6 * Real.exp (1 / 2) := by
      apply (div_le_iff₀ ha0).mpr
      have h := mul_nonneg (Real.exp_pos (1 / 2)).le (sub_nonneg.mpr ha1)
      nlinarith only [h]

#print axioms gammaCellNearUpperRemainder_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
