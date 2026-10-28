import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaRemainderRows
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaPairRemainder

/-!
# Finite nearby Gamma rows

Every truncated nonadjacent row is contained in its complete monotone row.
Translation preserves the integrated endpoint error exactly.
-/

noncomputable section
open Finset
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

private theorem upper_endpoint_loss_nonneg {a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    0 ≤ logCellWidth b *
      (archLevyDensity (Real.log (b : ℝ) - Real.log ((a + 1 : ℕ) : ℝ)) -
        archLevyDensity (Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ))) := by
  have hb : 1 ≤ b := by omega
  have hgap : 0 < Real.log (b : ℝ) - Real.log ((a + 1 : ℕ) : ℝ) := by
    apply sub_pos.mpr
    exact Real.log_lt_log (by positivity) (by exact_mod_cast (show a + 1 < b by omega))
  have haStep : Real.log (a : ℝ) ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show a ≤ a + 1 by omega))
  have hbStep : Real.log (b : ℝ) ≤ Real.log ((b + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show b ≤ b + 1 by omega))
  have hfar : 0 < Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ) := by
    linarith only [hgap, haStep, hbStep]
  exact mul_nonneg (logCellWidth_pos hb).le
    (sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn hgap hfar
      (by linarith only [haStep, hbStep])))

/-- Any finite subset of the upper nearby row has the same uniform endpoint-loss bound. -/
theorem gammaCellNearUpper_subset_le {a : ℕ} (ha : 1 ≤ a) (S : Finset ℕ)
    (hS : ∀ b ∈ S, a + 2 ≤ b ∧ b ≤ 2 * a) :
    (∑ b ∈ S, logCellWidth b *
      (archLevyDensity (Real.log (b : ℝ) - Real.log ((a + 1 : ℕ) : ℝ)) -
        archLevyDensity (Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ)))) ≤
      6 * Real.exp (1 / 2) := by
  let f : ℕ → ℝ := fun b => logCellWidth b *
    (archLevyDensity (Real.log (b : ℝ) - Real.log ((a + 1 : ℕ) : ℝ)) -
      archLevyDensity (Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ)))
  have hsub : S ⊆ Icc (a + 2) (2 * a) := fun b hb => mem_Icc.mpr (hS b hb)
  have he : (∑ b ∈ Icc (a + 2) (2 * a), f b) =
      ∑ n ∈ range (a - 1), f (a + 2 + n) := by
    apply sum_bij (fun b _ => b - (a + 2))
    · intro b hb
      have h := mem_Icc.mp hb
      exact mem_range.mpr (by omega)
    · intro b hb c hc he
      have h1 := mem_Icc.mp hb
      have h2 := mem_Icc.mp hc
      omega
    · intro n hn
      have h := mem_range.mp hn
      refine ⟨a + 2 + n, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro b hb
      have h := mem_Icc.mp hb
      rw [show a + 2 + (b - (a + 2)) = b by omega]
  have hrow : (∑ n ∈ range (a - 1), f (a + 2 + n)) = gammaCellNearUpperRemainder a := by
    unfold gammaCellNearUpperRemainder
    apply sum_congr rfl
    intro n _hn
    dsimp only [f]
    rw [show a + 2 + n + 1 = a + 3 + n by omega]
  calc
    _ ≤ ∑ b ∈ Icc (a + 2) (2 * a), f b :=
      sum_le_sum_of_subset_of_nonneg hsub fun b hb _ =>
        upper_endpoint_loss_nonneg ha (mem_Icc.mp hb).1
    _ = gammaCellNearUpperRemainder a := he.trans hrow
    _ ≤ _ := gammaCellNearUpperRemainder_le ha

/-- Any finite subset of the lower nearby row has its uniform endpoint-loss bound. -/
theorem gammaCellNearLower_subset_le {a : ℕ} (ha : 1 ≤ a) (S : Finset ℕ)
    (hS : ∀ b ∈ S, 1 ≤ b ∧ b + 2 ≤ a ∧ a ≤ 2 * b) :
    (∑ b ∈ S, logCellWidth b *
      (archLevyDensity (Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ)) -
        archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ)))) ≤
      2 * Real.exp (1 / 2) := by
  let T := (Icc 1 (a - 2)).filter (fun b => a ≤ 2 * b)
  have hsub : S ⊆ T := by
    intro b hb
    obtain ⟨hb1, hba, hhalf⟩ := hS b hb
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hb1, by omega⟩, hhalf⟩
  have hnn (b : ℕ) (hb : b ∈ T) : 0 ≤ logCellWidth b *
      (archLevyDensity (Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ)) -
        archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ))) := by
    have hb1 := (mem_Icc.mp (mem_filter.mp hb).1).1
    have hba := (mem_Icc.mp (mem_filter.mp hb).1).2
    have hgap : 0 < Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ) := by
      apply sub_pos.mpr
      exact Real.log_lt_log (by positivity) (by exact_mod_cast (show b + 1 < a by omega))
    have haStep : Real.log (a : ℝ) ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show a ≤ a + 1 by omega))
    have hbStep : Real.log (b : ℝ) ≤ Real.log ((b + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show b ≤ b + 1 by omega))
    have hfar : 0 < Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
      linarith only [hgap, haStep, hbStep]
    exact mul_nonneg (logCellWidth_pos hb1).le
      (sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn hgap hfar
        (by linarith only [haStep, hbStep])))
  exact (sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => hnn b hb).trans
    (gammaCellNearLowerRemainder_le ha)

/-- Actual integrated upper endpoint losses obey the same finite uniform bound after any translation. -/
theorem gamma_logCell_nearUpper_sum_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, a + 2 ≤ b ∧ b ≤ 2 * a) :
    (∑ b ∈ S, gammaIntervalPairDefect (s + Real.log (a : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ))
      (s + Real.log ((b + 1 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (6 * Real.exp (1 / 2) * logCellWidth a) := by
  let f : ℕ → ℝ := fun b => logCellWidth b *
    (archLevyDensity (Real.log (b : ℝ) - Real.log ((a + 1 : ℕ) : ℝ)) -
      archLevyDensity (Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ)))
  have hnn (b : ℕ) (hb : b ∈ S) : 0 ≤ f b :=
    upper_endpoint_loss_nonneg ha (hS b hb).1
  have hpoint (b : ℕ) (hb : b ∈ S) :
      gammaIntervalPairDefect (s + Real.log (a : ℝ)) (s + Real.log ((a + 1 : ℕ) : ℝ))
        (s + Real.log (b : ℝ)) (s + Real.log ((b + 1 : ℕ) : ℝ)) ≤
        ENNReal.ofReal (logCellWidth a * f b) := by
    have hab := (hS b hb).1
    have hb1 : 1 ≤ b := by omega
    have hA : Real.log (a : ℝ) < Real.log ((a + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show a < a + 1 by omega))
    have hB : Real.log (b : ℝ) < Real.log ((b + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show b < b + 1 by omega))
    have hgap : Real.log ((a + 1 : ℕ) : ℝ) < Real.log (b : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show a + 1 < b by omega))
    rw [gammaIntervalPairDefect_translate]
    refine (gammaIntervalPairDefect_le_endpoints hA hgap hB).trans_eq ?_
    congr 1
    simp only [f, logCellWidth, Nat.cast_add, Nat.cast_one]
    ring
  calc
    _ ≤ ∑ b ∈ S, ENNReal.ofReal (logCellWidth a * f b) := sum_le_sum hpoint
    _ = ENNReal.ofReal (logCellWidth a * ∑ b ∈ S, f b) := by
      rw [mul_sum, ENNReal.ofReal_sum_of_nonneg fun b hb => mul_nonneg (logCellWidth_pos ha).le (hnn b hb)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := mul_le_mul_of_nonneg_left (gammaCellNearUpper_subset_le ha S hS) (logCellWidth_pos ha).le
      dsimp only [f]
      nlinarith only [h])

/-- Actual integrated lower endpoint losses obey the finite two-exponential row bound. -/
theorem gamma_logCell_nearLower_sum_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, 1 ≤ b ∧ b + 2 ≤ a ∧ a ≤ 2 * b) :
    (∑ b ∈ S, gammaIntervalPairDefect (s + Real.log (a : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ))
      (s + Real.log ((b + 1 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (2 * Real.exp (1 / 2) * logCellWidth a) := by
  let f : ℕ → ℝ := fun b => logCellWidth b *
    (archLevyDensity (Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ)) -
      archLevyDensity (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ)))
  have hpoint (b : ℕ) (hb : b ∈ S) :
      gammaIntervalPairDefect (s + Real.log (a : ℝ)) (s + Real.log ((a + 1 : ℕ) : ℝ))
        (s + Real.log (b : ℝ)) (s + Real.log ((b + 1 : ℕ) : ℝ)) ≤
        ENNReal.ofReal (logCellWidth a * f b) := by
    obtain ⟨hb1, hba, _⟩ := hS b hb
    have hA : Real.log (a : ℝ) < Real.log ((a + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show a < a + 1 by omega))
    have hB : Real.log (b : ℝ) < Real.log ((b + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show b < b + 1 by omega))
    have hgap : Real.log ((b + 1 : ℕ) : ℝ) < Real.log (a : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast (show b + 1 < a by omega))
    rw [gammaIntervalPairDefect_translate, gammaIntervalPairDefect_comm]
    refine (gammaIntervalPairDefect_le_endpoints hB hgap hA).trans_eq ?_
    congr 1
    simp only [f, logCellWidth, Nat.cast_add, Nat.cast_one]
    ring
  have hnn (b : ℕ) (hb : b ∈ S) : 0 ≤ f b := by
    obtain ⟨hb1, hba, _⟩ := hS b hb
    have hgap : 0 < Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ) := by
      apply sub_pos.mpr
      exact Real.log_lt_log (by positivity) (by exact_mod_cast (show b + 1 < a by omega))
    have hA := (logCellWidth_pos ha)
    have hB := (logCellWidth_pos hb1)
    simp only [logCellWidth] at hA hB
    have hfar : 0 < Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
      push_cast
      push_cast at hgap
      linarith only [hgap, hA, hB]
    have hdist : Real.log (a : ℝ) - Real.log ((b + 1 : ℕ) : ℝ) ≤
        Real.log ((a + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
      push_cast
      linarith only [hA, hB]
    exact mul_nonneg (logCellWidth_pos hb1).le
      (sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn hgap hfar hdist))
  calc
    _ ≤ ∑ b ∈ S, ENNReal.ofReal (logCellWidth a * f b) := sum_le_sum hpoint
    _ = ENNReal.ofReal (logCellWidth a * ∑ b ∈ S, f b) := by
      rw [mul_sum, ENNReal.ofReal_sum_of_nonneg fun b hb => mul_nonneg (logCellWidth_pos ha).le (hnn b hb)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := mul_le_mul_of_nonneg_left (gammaCellNearLower_subset_le ha S hS) (logCellWidth_pos ha).le
      dsimp only [f]
      nlinarith only [h])

#print axioms gamma_logCell_nearUpper_sum_le
#print axioms gamma_logCell_nearLower_sum_le

#print axioms gammaCellNearUpper_subset_le
#print axioms gammaCellNearLower_subset_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
