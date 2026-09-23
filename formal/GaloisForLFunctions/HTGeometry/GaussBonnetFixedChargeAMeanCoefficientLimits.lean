import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanQuadratic

/-!
# First nonconstant critical coefficients of the even equilibrium equation

The exact moment remainder of the logarithm supplies all three limits.
No numerical fitting or assumed differentiability at the endpoint is used.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanQuadraticA_remainder (τ φ : ℝ) :
    (egbFixedChargeAMeanQuadraticA τ φ - 12 * egbFixedChargeAFraction φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      4 * egbFixedChargeAFraction φ * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) + egbCoexistenceALogKernel τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticA
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticB_remainder (τ φ : ℝ) :
    (egbFixedChargeAMeanQuadraticB τ φ - 6 * (1 + egbFixedChargeAFraction φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      4 - 2 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) + egbFixedChargeAFraction φ *
        (-2 * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - 8 -
          4 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) + 4 * egbCoexistenceALogKernel τ -
          2 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbCoexistenceALogKernel τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticB
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticC_remainder (τ : ℝ) :
    (egbFixedChargeAMeanQuadraticC τ - 1) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      -1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) + (egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticC
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticA_remainder_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanQuadraticA τ φ - 12 * egbFixedChargeAFraction φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (92 * egbFixedChargeAFraction φ / 5)) := by
  simp only [egbFixedChargeAMeanQuadraticA_remainder]
  have h := (tendsto_const_nhds (x := 4 * egbFixedChargeAFraction φ)).mul
    (egbCoexistenceALogKernel_asymmetry_quadratic_limit.add egbCoexistenceALogKernel_tendsto_critical)
  convert h using 1 <;> ring

theorem egbFixedChargeAMeanQuadraticB_remainder_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanQuadraticB τ φ - 6 * (1 + egbFixedChargeAFraction φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (4 + 4 * egbFixedChargeAFraction φ / 5)) := by
  simp only [egbFixedChargeAMeanQuadraticB_remainder]
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have hH := egbCoexistenceALogKernel_tendsto_critical
  have h1 : Tendsto (fun τ => -2 * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - 8 - 4 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (-56 / 5 : ℝ)) := by
    convert (((tendsto_const_nhds (x := (-2 : ℝ))).mul egbCoexistenceALogKernel_asymmetry_quadratic_limit).sub
      (tendsto_const_nhds (x := (8 : ℝ)))).sub ((tendsto_const_nhds (x := (4 : ℝ))).mul hd) using 1 <;> norm_num
  have h2 : Tendsto (fun τ => -2 * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - 8 -
      4 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) + 4 * egbCoexistenceALogKernel τ - 2 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbCoexistenceALogKernel τ)
      atBot (𝓝 (4 / 5 : ℝ)) := by
    convert (h1.add ((tendsto_const_nhds (x := (4 : ℝ))).mul hH)).sub
      (((tendsto_const_nhds (x := (2 : ℝ))).mul hd).mul hH) using 1 <;> norm_num
  have h3 : Tendsto (fun τ => 4 - 2 * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (4 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (4 : ℝ))).sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hd)
  convert h3.add ((tendsto_const_nhds (x := egbFixedChargeAFraction φ)).mul h2) using 1 <;> ring

theorem egbFixedChargeAMeanQuadraticC_remainder_limit :
    Tendsto (fun τ => (egbFixedChargeAMeanQuadraticC τ - 1) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (-1 : ℝ)) := by
  simp only [egbFixedChargeAMeanQuadraticC_remainder]
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  simpa using ((tendsto_const_nhds (x := (-1 : ℝ))).sub hd).add (hd.pow 2)

theorem egbFixedChargeAMeanQuadraticA_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanQuadraticA τ φ) atBot (𝓝 (12 * egbFixedChargeAFraction φ)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have h := ((egbFixedChargeAMeanQuadraticA_remainder_limit φ).mul hd).add (tendsto_const_nhds (x := 12 * egbFixedChargeAFraction φ))
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticB_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanQuadraticB τ φ) atBot (𝓝 (6 * (1 + egbFixedChargeAFraction φ))) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have h := ((egbFixedChargeAMeanQuadraticB_remainder_limit φ).mul hd).add (tendsto_const_nhds (x := 6 * (1 + egbFixedChargeAFraction φ)))
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticC_critical_limit :
    Tendsto egbFixedChargeAMeanQuadraticC atBot (𝓝 (1 : ℝ)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have h := (egbFixedChargeAMeanQuadraticC_remainder_limit.mul hd).add (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
