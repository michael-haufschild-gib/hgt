import GaloisForLFunctions.HTGeometry.CirclePolynomialSupBound

/-!
# Uniform complex bounds for the hard-edge Cayley packets

The hard-edge coordinate `(a² - z²)/(a² + z²)` is the Zhukovsky image of the disc variable
`w = (a + iz)/(a - iz)`, which stays within `(a+R)/(a-R)` of the unit circle on every disc of
radius `R`.  A polynomial of degree at most `d` in the hard-edge coordinate is therefore bounded
on that disc by its circle energy times `((a+R)/(a-R))^{d+2}`, and the last factor is at most
`exp(2R(d+2)/(a-R))`.  When the degree grows proportionally to `a`, the whole bound is uniform:
this is the normality hypothesis of the hard-edge limit.
-/

open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The disc variable of the hard-edge Cayley chart. -/
def hardEdgeDiskVariable (a : ℝ) (z : ℂ) : ℂ := ((a : ℂ) + z * I) / ((a : ℂ) - z * I)

/-- The hard-edge coordinate is the Zhukovsky image of the disc variable. -/
theorem zhukovsky_hardEdgeDiskVariable (a : ℝ) (z : ℂ)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    (hardEdgeDiskVariable a z + (hardEdgeDiskVariable a z)⁻¹) / 2
      = ((a : ℂ) ^ 2 - z ^ 2) / ((a : ℂ) ^ 2 + z ^ 2) := by
  have hprod : ((a : ℂ) - z * I) * ((a : ℂ) + z * I) = (a : ℂ) ^ 2 + z ^ 2 := by
    linear_combination (-(z ^ 2)) * Complex.I_sq
  have hne : (a : ℂ) ^ 2 + z ^ 2 ≠ 0 := by
    rw [← hprod]
    exact mul_ne_zero h₂ h₁
  have hnum : ((a : ℂ) + z * I) * ((a : ℂ) + z * I) + ((a : ℂ) - z * I) * ((a : ℂ) - z * I)
      = 2 * ((a : ℂ) ^ 2 - z ^ 2) := by
    linear_combination (2 * z ^ 2) * Complex.I_sq
  rw [hardEdgeDiskVariable, inv_div, div_add_div _ _ h₂ h₁, hprod, hnum]
  field_simp

theorem hardEdgeDiskVariable_ne_zero (a : ℝ) (z : ℂ)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    hardEdgeDiskVariable a z ≠ 0 :=
  div_ne_zero h₁ h₂

/-- On a disc of radius `R` the disc variable stays within `(a+R)/(a-R)` of the unit circle. -/
theorem max_norm_hardEdgeDiskVariable_le {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a) {z : ℂ}
    (hz : ‖z‖ ≤ R) :
    max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹ ≤ (a + R) / (a - R) := by
  have hzI : ‖z * I‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hnorma : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hR hRa.le)]
  have hsubpos : 0 < a - R := by linarith
  have hlow₂ : a - R ≤ ‖(a : ℂ) - z * I‖ := by
    have h := norm_sub_norm_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hlow₁ : a - R ≤ ‖(a : ℂ) + z * I‖ := by
    have h := norm_sub_norm_le ((a : ℂ)) (-(z * I))
    rw [hnorma, norm_neg, hzI, sub_neg_eq_add] at h
    linarith
  have hup₁ : ‖(a : ℂ) + z * I‖ ≤ a + R := by
    have h := norm_add_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hup₂ : ‖(a : ℂ) - z * I‖ ≤ a + R := by
    have h := norm_sub_le ((a : ℂ)) (z * I)
    rw [hnorma, hzI] at h
    linarith
  have hpos₁ : 0 < ‖(a : ℂ) + z * I‖ := lt_of_lt_of_le hsubpos hlow₁
  have hpos₂ : 0 < ‖(a : ℂ) - z * I‖ := lt_of_lt_of_le hsubpos hlow₂
  have hw : ‖hardEdgeDiskVariable a z‖ = ‖(a : ℂ) + z * I‖ / ‖(a : ℂ) - z * I‖ := by
    rw [hardEdgeDiskVariable, norm_div]
  have hwinv : ‖hardEdgeDiskVariable a z‖⁻¹ = ‖(a : ℂ) - z * I‖ / ‖(a : ℂ) + z * I‖ := by
    rw [hw, inv_div]
  refine max_le ?_ ?_
  · rw [hw]
    exact div_le_div₀ (by linarith) hup₁ hsubpos hlow₂
  · rw [hwinv]
    exact div_le_div₀ (by linarith) hup₂ hsubpos hlow₁

/-- The ratio power is controlled by an exponential in the degree over the aperture. -/
theorem ratio_pow_le_exp {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a) (n : ℕ) :
    ((a + R) / (a - R)) ^ n ≤ Real.exp (2 * R * n / (a - R)) := by
  have hsubpos : 0 < a - R := by linarith
  have hstep : (a + R) / (a - R) = 1 + 2 * R / (a - R) := by
    field_simp
    ring
  have hexp : (1 : ℝ) + 2 * R / (a - R) ≤ Real.exp (2 * R / (a - R)) := by
    have h := Real.add_one_le_exp (2 * R / (a - R))
    linarith
  have hnonneg : (0 : ℝ) ≤ 1 + 2 * R / (a - R) := by positivity
  calc ((a + R) / (a - R)) ^ n = (1 + 2 * R / (a - R)) ^ n := by rw [hstep]
    _ ≤ (Real.exp (2 * R / (a - R))) ^ n := pow_le_pow_left₀ hnonneg hexp n
    _ = Real.exp (n * (2 * R / (a - R))) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp (2 * R * n / (a - R)) := by
        congr 1
        field_simp

/-- **Uniform bound for a hard-edge packet on a complex disc.**  A polynomial of degree at most
`d` in the hard-edge coordinate is bounded on the disc of radius `R` by its circle energy times
`exp(2R(d+2)/(a-R))`. -/
theorem norm_eval_hardEdgeCoordinate_le {a R : ℝ} (hR : 0 ≤ R) (hRa : R < a)
    (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d) {z : ℂ} (hz : ‖z‖ ≤ R)
    (h₁ : (a : ℂ) + z * I ≠ 0) (h₂ : (a : ℂ) - z * I ≠ 0) :
    ‖P.eval (((a : ℂ) ^ 2 - z ^ 2) / ((a : ℂ) ^ 2 + z ^ 2))‖
      ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P)
          * Real.exp (2 * R * (d + 2) / (a - R)) := by
  have hwne := hardEdgeDiskVariable_ne_zero a z h₁ h₂
  have hzhu := zhukovsky_hardEdgeDiskVariable a z h₁ h₂
  have hbase := norm_eval_cayley_le' d P hd hwne
  rw [hzhu] at hbase
  refine hbase.trans ?_
  have hcoef : 0 ≤ Real.sqrt (2 * d + 2) * Real.sqrt (cayleyEnergy P) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  have hmax := max_norm_hardEdgeDiskVariable_le hR hRa hz
  have hmaxpos : 0 ≤ max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  calc (max ‖hardEdgeDiskVariable a z‖ ‖hardEdgeDiskVariable a z‖⁻¹) ^ (d + 2)
      ≤ ((a + R) / (a - R)) ^ (d + 2) := pow_le_pow_left₀ hmaxpos hmax _
    _ ≤ Real.exp (2 * R * (d + 2) / (a - R)) := by
        have := ratio_pow_le_exp hR hRa (d + 2)
        simpa using this

end RHTower

end
