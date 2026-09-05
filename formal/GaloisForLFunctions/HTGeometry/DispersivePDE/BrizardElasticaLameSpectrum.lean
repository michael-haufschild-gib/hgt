import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Tactic

/-!
# Lamé separation parameter in arXiv:2607.21750

Section VII introduces `ε² = 1 - m/(2q₀)` for the separated periodic NLS solution.  The paper
checks nonnegativity in the positive classical chamber and then extends the formula to negative
parameters.  This module gives the global sign classification, sharp classical interval, exact
torsionless value, and the additional inequality required in physical Region II.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Spectral quantity in paper equation (100). -/
noncomputable def lameEpsilonSq (P : Parameters) : ℝ :=
  1 - P.modulus / (2 * (P.q₀ : ℝ))

theorem lameEpsilonSq_fraction (P : Parameters) :
    lameEpsilonSq P =
      (2 * (P.q₀ : ℝ) - P.modulus) / (2 * (P.q₀ : ℝ)) := by
  rw [lameEpsilonSq]
  field_simp [P.q₀.ne_zero]

/-- Exact sign law, including both positive and negative scale chambers. -/
theorem lameEpsilonSq_nonneg_iff (P : Parameters) :
    0 ≤ lameEpsilonSq P ↔
      (0 < (P.q₀ : ℝ) ∧ P.modulus ≤ 2 * (P.q₀ : ℝ)) ∨
      ((P.q₀ : ℝ) < 0 ∧ 2 * (P.q₀ : ℝ) ≤ P.modulus) := by
  rw [lameEpsilonSq_fraction, div_nonneg_iff]
  constructor
  · rintro (h | h)
    · left
      have hqnonneg : 0 ≤ (P.q₀ : ℝ) := by linarith [h.2]
      have hqpos : 0 < (P.q₀ : ℝ) :=
        lt_of_le_of_ne hqnonneg P.q₀.ne_zero.symm
      exact ⟨hqpos, by linarith [h.1]⟩
    · right
      have hqnonpos : (P.q₀ : ℝ) ≤ 0 := by linarith [h.2]
      have hqneg : (P.q₀ : ℝ) < 0 :=
        lt_of_le_of_ne hqnonpos P.q₀.ne_zero
      exact ⟨hqneg, by linarith [h.1]⟩
  · rintro (h | h)
    · left
      constructor <;> linarith [h.1, h.2]
    · right
      constructor <;> linarith [h.1, h.2]

/-- Positive classical Lamé chamber used in the paper. -/
abbrev ClassicalLameParameters :=
  {P : Parameters // 0 < P.modulus ∧ P.modulus ≤ (P.q₀ : ℝ)}

/-- The paper's nonnegative bound sharpens to `1/2 ≤ ε² < 1`. -/
theorem classical_lameEpsilonSq_bounds (P : ClassicalLameParameters) :
    1 / 2 ≤ lameEpsilonSq P.val ∧ lameEpsilonSq P.val < 1 := by
  have hq : 0 < (P.val.q₀ : ℝ) := lt_of_lt_of_le P.property.1 P.property.2
  have hratioUpper :
      P.val.modulus / (2 * (P.val.q₀ : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (P.val.q₀ : ℝ))]
    linarith [P.property.2]
  have hratioPositive : 0 < P.val.modulus / (2 * (P.val.q₀ : ℝ)) :=
    div_pos P.property.1 (by positivity)
  rw [lameEpsilonSq]
  constructor <;> linarith

/-- On either torsionless wall `q₀=m`, the separated eigenvalue is exactly one half. -/
theorem torsionless_lameEpsilonSq (m : ℝˣ) :
    lameEpsilonSq { modulus := (m : ℝ), q₀ := m } = 1 / 2 := by
  rw [lameEpsilonSq]
  field_simp [m.ne_zero]
  ring

/-- Region I lies strictly above the torsionless spectral value. -/
theorem physicalRegionI_lameEpsilonSq_gt_half (P : PhysicalRegionI) :
    1 / 2 < lameEpsilonSq P.val := by
  rw [lameEpsilonSq]
  have hq := P.property.1
  have hratio :
      P.val.modulus / (2 * (P.val.q₀ : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * (P.val.q₀ : ℝ))]
    linarith [P.property.2.1]
  linarith

/-- Region II lies below one half; reality of `ε` needs one further linear inequality. -/
theorem physicalRegionII_lameEpsilonSq_lt_half (P : PhysicalRegionII) :
    lameEpsilonSq P.val < 1 / 2 := by
  rw [lameEpsilonSq]
  have hb := physicalRegionII_bounds P
  have hratio : 1 / 2 < P.val.modulus / (2 * (P.val.q₀ : ℝ)) := by
    rw [lt_div_iff_of_neg (by linarith [hb.2.2] : 2 * (P.val.q₀ : ℝ) < 0)]
    linarith [hb.2.1]
  linarith

theorem physicalRegionII_lameEpsilonSq_nonneg_iff (P : PhysicalRegionII) :
    0 ≤ lameEpsilonSq P.val ↔
      2 * (P.val.q₀ : ℝ) ≤ P.val.modulus := by
  rw [lameEpsilonSq_nonneg_iff]
  have hq := P.property.1
  simp only [not_lt_of_ge (le_of_lt hq), false_and, false_or]
  exact and_iff_right hq

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
