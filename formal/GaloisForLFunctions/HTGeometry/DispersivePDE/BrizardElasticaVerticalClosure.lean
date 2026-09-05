import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaClosureBounds
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Tactic

/-!
# Vertical-period closure and Region I exclusion

The linear drift in paper equation (89) vanishes exactly when `q₀=Q(m)`.  Integral bounds prove
that this closure graph cannot intersect physical Region I: on its classical half `Q≥1-m>1/2`,
while on its negative half `Q≥1+m`, contradicting the Region I speed wall.  This replaces the
paper's graphical exclusion with a closed analytic theorem.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Coefficient of the nonperiodic linear term in paper equation (89). -/
noncomputable def verticalClosureDrift (P : Parameters) : ℝ :=
  1 + gammaSq P / 2 +
    1 / (P.q₀ : ℝ) *
      (completeEllipticE P.modulus / completeEllipticK P.modulus - 1)

/-- The vertical drift is the normalized displacement from the closure graph `q₀=Q(m)`. -/
theorem verticalClosureDrift_eq (P : Parameters) :
    verticalClosureDrift P =
      (closureQ P.modulus - (P.q₀ : ℝ)) / (2 * (P.q₀ : ℝ)) := by
  simp only [verticalClosureDrift, gammaSq, closureQ]
  simp only [div_eq_mul_inv]
  field_simp [P.q₀.ne_zero]
  all_goals ring

/-- Paper equation (91): zero vertical drift is exactly `q₀=Q(m)`. -/
theorem verticalClosureDrift_eq_zero_iff (P : Parameters) :
    verticalClosureDrift P = 0 ↔ closureQ P.modulus = (P.q₀ : ℝ) := by
  rw [verticalClosureDrift_eq]
  have hden : 2 * (P.q₀ : ℝ) ≠ 0 := mul_ne_zero two_ne_zero P.q₀.ne_zero
  rw [div_eq_zero_iff]
  simp only [hden, or_false]
  exact sub_eq_zero

theorem one_sub_modulus_le_closureQ_classical (m : ClassicalModulus) :
    1 - (m : ℝ) ≤ closureQ m := by
  have hK : 0 < completeEllipticK m := completeEllipticK_classical_pos m
  have hratio : 1 - (m : ℝ) ≤ completeEllipticE m / completeEllipticK m :=
    (le_div_iff₀ hK).2 (one_sub_mul_completeK_le_completeE m)
  calc
    1 - (m : ℝ) ≤
        2 * (completeEllipticE m / completeEllipticK m) - (1 - (m : ℝ)) := by
      linarith
    _ = closureQ m := by rw [closureQ]; ring

/-- Transported lower bound on the extended closure branch. -/
theorem one_add_modulus_le_closureQ_negative (m : NegativeModulus) :
    1 + (m : ℝ) ≤ closureQ m := by
  let n : ClassicalModulus := extendedToClassical m
  have hK : 0 < completeEllipticK n := completeEllipticK_classical_pos n
  have hratio : 1 - (n : ℝ) ≤ completeEllipticE n / completeEllipticK n :=
    (le_div_iff₀ hK).2 (one_sub_mul_completeK_le_completeE n)
  have hcore : 1 - 2 * (n : ℝ) ≤ classicalClosureCore n := by
    rw [classicalClosureCore]
    have hrewrite : 2 * completeEllipticE n / completeEllipticK n =
        2 * (completeEllipticE n / completeEllipticK n) := by ring
    rw [hrewrite]
    linarith
  have hfactor : 0 ≤ (1 - (n : ℝ))⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr n.property.2)).le
  have hmul := mul_le_mul_of_nonneg_left hcore hfactor
  have hid : (1 - (n : ℝ))⁻¹ * (1 - 2 * (n : ℝ)) = 1 + (m : ℝ) := by
    have hm0 : (m : ℝ) < 0 := m.property
    dsimp only [n]
    rw [transformedComplement, extendedToClassical]
    have hm : 1 - (m : ℝ) ≠ 0 := by linarith [hm0]
    field_simp [hm]
    ring
  rw [closureQ_negative_transform]
  change 1 + (m : ℝ) ≤
    (1 - (n : ℝ))⁻¹ * classicalClosureCore n
  rw [← hid]
  exact hmul

/-- The vertical-closure graph has no point in the paper's physical Region I. -/
theorem physicalRegionI_not_on_closureGraph (P : PhysicalRegionI) :
    closureQ P.val.modulus ≠ (P.val.q₀ : ℝ) := by
  intro hclosure
  have hb := physicalRegionI_bounds P
  rcases lt_trichotomy P.val.modulus 0 with hmneg | hmzero | hmpos
  · let m : NegativeModulus := ⟨P.val.modulus, hmneg⟩
    have hl := one_add_modulus_le_closureQ_negative m
    change 1 + P.val.modulus ≤ closureQ P.val.modulus at hl
    rw [hclosure] at hl
    linarith [P.property.1, P.property.2.2]
  · rw [hmzero, closureQ_zero] at hclosure
    linarith [hb.2.2.2]
  · let m : ClassicalModulus :=
      ⟨P.val.modulus, hmpos, lt_trans hb.2.1 (by norm_num)⟩
    have hl := one_sub_modulus_le_closureQ_classical m
    change 1 - P.val.modulus ≤ closureQ P.val.modulus at hl
    rw [hclosure] at hl
    linarith [hb.2.1, hb.2.2.2]

/-- Consequently every physical Region I profile has nonzero vertical drift and is open. -/
theorem physicalRegionI_verticalClosureDrift_ne_zero (P : PhysicalRegionI) :
    verticalClosureDrift P.val ≠ 0 := by
  rw [Ne, verticalClosureDrift_eq_zero_iff]
  exact physicalRegionI_not_on_closureGraph P

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
