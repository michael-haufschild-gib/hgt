import GaloisForLFunctions.HilbertMetric.ThreePointCorrelation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Correlation-angle criterion for three-point matrices

The Castano--Paksoy--Zhang correlation-angle triangle criterion is specialized to the radially
ordered positive chamber used by the Riemann theta source.
-/

namespace HilbertMetric

/-- A radially ordered nonnegative correlation triple is positive semidefinite when its long-gap
correlation angle is subadditive across the two adjacent gaps. -/
theorem threePointCorrelationMatrix_posSemidef_of_arccos_subadditive
    {p q r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hrp : r ≤ p) (hrq : r ≤ q)
    (htriangle : Real.arccos r ≤ Real.arccos p + Real.arccos q) :
    Matrix.PosSemidef (threePointCorrelationMatrix 1 p q r) := by
  let α := Real.arccos p
  let β := Real.arccos q
  let γ := Real.arccos r
  have hp1le : p ≤ 1 := hp1.le
  have hr1 : r ≤ 1 := hrp.trans hp1le
  have hα0 : 0 ≤ α := Real.arccos_nonneg p
  have hβ0 : 0 ≤ β := Real.arccos_nonneg q
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg r
  have hαhalf : α ≤ Real.pi / 2 := by
    exact Real.arccos_le_pi_div_two.mpr hp0
  have hβhalf : β ≤ Real.pi / 2 := by
    exact Real.arccos_le_pi_div_two.mpr hq0
  have hγhalf : γ ≤ Real.pi / 2 := by
    exact Real.arccos_le_pi_div_two.mpr hr0
  have hγπ : γ ≤ Real.pi := hγhalf.trans (by linarith [Real.pi_pos])
  have hcosα : Real.cos α = p := by
    exact Real.cos_arccos (by linarith) hp1le
  have hcosβ : Real.cos β = q := by
    exact Real.cos_arccos (by linarith) hq1
  have hcosγ : Real.cos γ = r := by
    exact Real.cos_arccos (by linarith) hr1
  have hαγ : α ≤ γ := by
    exact Real.arccos_le_arccos hrp
  have hβγ : β ≤ γ := by
    exact Real.arccos_le_arccos hrq
  have habs : |α - β| ≤ γ := by
    rw [abs_le]
    constructor <;> linarith
  have hsumπ : α + β ≤ Real.pi := by linarith
  have hcosLower : Real.cos (α + β) ≤ Real.cos γ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hγ0 hsumπ htriangle
  have hcosUpper : Real.cos γ ≤ Real.cos |α - β| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hγπ habs
  have hlower :
      p * q - Real.sin α * Real.sin β ≤ r := by
    calc
      p * q - Real.sin α * Real.sin β = Real.cos (α + β) := by
        rw [Real.cos_add, hcosα, hcosβ]
      _ ≤ Real.cos γ := hcosLower
      _ = r := hcosγ
  have hupper :
      r ≤ p * q + Real.sin α * Real.sin β := by
    calc
      r = Real.cos γ := hcosγ.symm
      _ ≤ Real.cos |α - β| := hcosUpper
      _ = Real.cos (α - β) := Real.cos_abs _
      _ = p * q + Real.sin α * Real.sin β := by
        rw [Real.cos_sub, hcosα, hcosβ]
  have hsq :
      (r - p * q) ^ (2 : ℕ) ≤ (Real.sin α * Real.sin β) ^ (2 : ℕ) := by
    have hleft :
        -(Real.sin α * Real.sin β) ≤ r - p * q := by linarith
    have hprod :
        0 ≤ (Real.sin α * Real.sin β - (r - p * q)) *
          (Real.sin α * Real.sin β + (r - p * q)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsinαsq : Real.sin α ^ (2 : ℕ) = 1 - p ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hsinβsq : Real.sin β ^ (2 : ℕ) = 1 - q ^ (2 : ℕ) := by
    nlinarith [Real.sin_sq_add_cos_sq β]
  have hsinProdSq :
      (Real.sin α * Real.sin β) ^ (2 : ℕ) =
        (1 - p ^ (2 : ℕ)) * (1 - q ^ (2 : ℕ)) := by
    rw [mul_pow, hsinαsq, hsinβsq]
  have hdet : 0 ≤ threePointCorrelationDeterminant 1 p q r := by
    rw [show threePointCorrelationDeterminant 1 p q r =
      (1 - p ^ (2 : ℕ)) * (1 - q ^ (2 : ℕ)) - (r - p * q) ^ (2 : ℕ) by
        unfold threePointCorrelationDeterminant
        ring]
    rw [← hsinProdSq]
    linarith
  exact (threePointCorrelationMatrix_posSemidef_iff
    (by norm_num) hp0 hp1).2 hdet

/-- At the normalized seam `p = 1`, radial ordering forces `r = q`; the resulting duplicated-node
correlation matrix is positive semidefinite throughout the closed interval `0 ≤ q ≤ 1`. -/
theorem threePointCorrelationMatrix_posSemidef_left_seam
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Matrix.PosSemidef (threePointCorrelationMatrix 1 1 q q) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [threePointCorrelationMatrix]
  · intro v
    have hform :
        star v ⬝ᵥ (threePointCorrelationMatrix 1 1 q q).mulVec v =
          ((1 + q) / 2) * (v 0 + v 1 + v 2) ^ (2 : ℕ) +
            ((1 - q) / 2) * (v 0 + v 1 - v 2) ^ (2 : ℕ) := by
      simp [threePointCorrelationMatrix, dotProduct, Matrix.mulVec,
        Fin.sum_univ_three]
      ring
    rw [hform]
    exact add_nonneg
      (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _))
      (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _))

/-- **Closed correlation-angle criterion.**  Radial ordering and angle subadditivity imply
positive semidefiniteness even when the first adjacent correlation equals the diagonal. -/
theorem threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
    {p q r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hrp : r ≤ p) (hrq : r ≤ q)
    (htriangle : Real.arccos r ≤ Real.arccos p + Real.arccos q) :
    Matrix.PosSemidef (threePointCorrelationMatrix 1 p q r) := by
  rcases hp1.eq_or_lt with rfl | hp1
  · have hr1 : r ≤ 1 := hrp
    have hangle : Real.arccos r ≤ Real.arccos q := by
      simpa using htriangle
    have hqr : q ≤ r := by
      have hcos :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (Real.arccos_nonneg r) (Real.arccos_le_pi q) hangle
      rw [Real.cos_arccos (by linarith) hq1,
        Real.cos_arccos (by linarith) hr1] at hcos
      exact hcos
    have hrqeq : r = q := le_antisymm hrq hqr
    subst r
    exact threePointCorrelationMatrix_posSemidef_left_seam hq0 hq1
  · exact threePointCorrelationMatrix_posSemidef_of_arccos_subadditive
      hp0 hp1 hq0 hq1 hr0 hrp hrq htriangle

end HilbertMetric
