import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment

/-!
# Endpoint losses in logarithmic Gamma rows

Replacing a cell interaction by its farthest-endpoint weight loses a difference
of two monotone kernel readings. Four forward shifts and two backward shifts
telescope the nearby nonadjacent rows. Both bounds are independent of index.
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

private theorem sum_range_backward_two (g : ℕ → ℝ) (N : ℕ) :
    (∑ b ∈ range (N + 1), (g b - g (b - 2))) =
      g N + g (N - 1) - 2 * g 0 := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.zero_sub, zero_add]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      show N + 1 - 2 = N - 1 by omega, show N + 1 - 1 = N by omega]
    ring

/-- Lower-side endpoint loss from nonadjacent cells whose indices are at least half the source index. -/
def gammaCellNearLowerRemainder (a : ℕ) : ℝ :=
  ∑ b ∈ (Icc 1 (a - 2)).filter (fun b => a ≤ 2 * b), logCellWidth b *
    (archLevyDensity (Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ)) -
      archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ)))

/-- Two backward shifts pay the whole lower nearby Gamma row, uniformly in source index. -/
theorem gammaCellNearLowerRemainder_le {a : ℕ} (ha : 1 ≤ a) :
    gammaCellNearLowerRemainder a ≤ 2 * Real.exp (1 / 2) := by
  by_cases ha3 : 3 ≤ a
  · have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    let G : ℕ → ℝ := fun b => if b = 0 then 0 else archLevyDensity
      (Real.log (a : ℝ) - Real.log ((min b (a - 2) + 1 : ℕ) : ℝ))
    have harg (b : ℕ) : 0 < Real.log (a : ℝ) -
        Real.log ((min b (a - 2) + 1 : ℕ) : ℝ) := by
      apply sub_pos.mpr
      apply Real.log_lt_log (by positivity)
      exact_mod_cast (show min b (a - 2) + 1 < a by have := min_le_right b (a - 2); omega)
    have hGzero : G 0 = 0 := by simp only [G, if_pos rfl]
    have hGpos (b : ℕ) : 0 ≤ G b := by
      by_cases hb : b = 0
      · rw [hb, hGzero]
      · simp only [G, if_neg hb]
        exact (archLevyDensity_pos (harg b)).le
    have hGmono : Monotone G := by
      intro b c hbc
      by_cases hb : b = 0
      · rw [hb, hGzero]
        exact hGpos c
      have hc : c ≠ 0 := by omega
      simp only [G, if_neg hb, if_neg hc]
      apply strictAntiOn_archLevyDensity.antitoneOn (harg c) (harg b)
      apply sub_le_sub_left
      apply Real.log_le_log (by positivity)
      exact_mod_cast (Nat.add_le_add_right (min_le_min hbc le_rfl) 1)
    let S := (Icc 1 (a - 2)).filter (fun b => a ≤ 2 * b)
    have hbase (b : ℕ) (hb : b ∈ S) :
        G b = archLevyDensity (Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ)) := by
      have hb1 := (mem_Icc.mp (mem_filter.mp hb).1).1
      have hba := (mem_Icc.mp (mem_filter.mp hb).1).2
      simp only [G, if_neg (show b ≠ 0 by omega), min_eq_left hba]
    have hterm (b : ℕ) (hb : b ∈ S) :
        logCellWidth b * (G b -
          archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ))) ≤
        (2 / (a : ℝ)) * (G b - G (b - 2)) := by
      have hb1 := (mem_Icc.mp (mem_filter.mp hb).1).1
      have hba := (mem_Icc.mp (mem_filter.mp hb).1).2
      have hhalf := (mem_filter.mp hb).2
      have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
      have hfar : 0 < Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
        apply sub_pos.mpr
        apply Real.log_lt_log hb0
        exact_mod_cast (show b < a + 1 by omega)
      have hshift : G (b - 2) ≤
          archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ)) := by
        by_cases hb2 : b ≤ 2
        · rw [show b - 2 = 0 by omega, hGzero]
          exact (archLevyDensity_pos hfar).le
        · have hp0 : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          have hnum : ((a + 1 : ℕ) : ℝ) * ((b - 1 : ℕ) : ℝ) ≤ (a : ℝ) * b := by
            rw [Nat.cast_sub hb1]
            push_cast
            have hbaR : (b : ℝ) ≤ a := by exact_mod_cast (show b ≤ a by omega)
            nlinarith only [hbaR]
          have hratio := (div_le_div_iff₀ hb0 hp0).mpr hnum
          have hlog := Real.log_le_log (div_pos (by positivity) hb0) hratio
          rw [Real.log_div (by positivity) hb0.ne', Real.log_div ha0.ne' hp0.ne'] at hlog
          have hmin : min (b - 2) (a - 2) = b - 2 := min_eq_left (by omega)
          have hp : b - 2 + 1 = b - 1 := by omega
          have hnear := harg (b - 2)
          rw [hmin, hp] at hnear
          simp only [G, if_neg (show b - 2 ≠ 0 by omega), hmin, hp]
          exact strictAntiOn_archLevyDensity.antitoneOn hfar hnear hlog
      have hw : logCellWidth b ≤ 2 / (a : ℝ) :=
        (logCellWidth_le_inv hb1).trans ((div_le_div_iff₀ hb0 ha0).mpr
          (by simpa only [one_mul] using (show (a : ℝ) ≤ 2 * b by exact_mod_cast hhalf)))
      calc
        _ ≤ logCellWidth b * (G b - G (b - 2)) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left hshift _) (logCellWidth_pos hb1).le
        _ ≤ _ := mul_le_mul_of_nonneg_right hw
          (sub_nonneg.mpr (hGmono (Nat.sub_le b 2)))
    have hsum : (∑ b ∈ S, (G b - G (b - 2))) ≤ 2 * G (a - 2) := by
      have hsub : S ⊆ range (a - 1) := by
        intro b hb
        have hba := (mem_Icc.mp (mem_filter.mp hb).1).2
        exact mem_range.mpr (by omega)
      calc
        _ ≤ ∑ b ∈ range (a - 1), (G b - G (b - 2)) :=
          sum_le_sum_of_subset_of_nonneg hsub fun b _ _ =>
            sub_nonneg.mpr (hGmono (Nat.sub_le b 2))
        _ = G (a - 2) + G (a - 2 - 1) - 2 * G 0 := by
          rw [show a - 1 = (a - 2) + 1 by omega, sum_range_backward_two]
        _ ≤ 2 * G (a - 2) := by
          rw [hGzero, mul_zero, sub_zero]
          have h := hGmono (Nat.sub_le (a - 2) 1)
          linarith only [h]
    have hGend : G (a - 2) ≤ Real.exp (1 / 2) * (a : ℝ) / 2 := by
      have hw0 := logCellWidth_pos (show 1 ≤ a - 1 by omega)
      have hw1 : logCellWidth (a - 1) ≤ 1 :=
        (logCellWidth_le_inv (by omega)).trans
          ((div_le_one (by exact_mod_cast (show 0 < a - 1 by omega))).mpr
            (by exact_mod_cast (show 1 ≤ a - 1 by omega)))
      have he : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
        exact_mod_cast (show a - 1 + 1 = a by omega)
      have hlower : 1 / (a : ℝ) ≤ logCellWidth (a - 1) := by
        simpa only [he] using inv_add_one_le_logCellWidth (show 1 ≤ a - 1 by omega)
      have hmul := mul_le_mul_of_nonneg_left hlower ha0.le
      rw [mul_one_div_cancel ha0.ne'] at hmul
      have hscaled := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (1 / 2)).le
      calc
        G (a - 2) = archLevyDensity (logCellWidth (a - 1)) := by
          simp only [G, if_neg (show a - 2 ≠ 0 by omega), min_self,
            show a - 2 + 1 = a - 1 by omega, logCellWidth, he]
        _ ≤ Real.exp (1 / 2) / (2 * logCellWidth (a - 1)) :=
          archLevyDensity_le_sqrt_e_div hw0 hw1
        _ ≤ _ := by
          apply (div_le_iff₀ (mul_pos (by norm_num) hw0)).mpr
          nlinarith only [hscaled]
    calc
      gammaCellNearLowerRemainder a = ∑ b ∈ S, logCellWidth b *
          (G b - archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ))) := by
        apply sum_congr rfl
        intro b hb
        rw [hbase b hb]
      _ ≤ (2 / (a : ℝ)) * ∑ b ∈ S, (G b - G (b - 2)) := by
        rw [mul_sum]
        exact sum_le_sum hterm
      _ ≤ (2 / (a : ℝ)) * (2 * G (a - 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (2 / (a : ℝ)) * (2 * (Real.exp (1 / 2) * (a : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGend (by norm_num)) (by positivity)
      _ = 2 * Real.exp (1 / 2) := by field_simp
  · obtain rfl | rfl : a = 1 ∨ a = 2 := by omega
    all_goals (norm_num [gammaCellNearLowerRemainder]; positivity)

#print axioms gammaCellNearLowerRemainder_le

#print axioms gammaCellNearUpperRemainder_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
