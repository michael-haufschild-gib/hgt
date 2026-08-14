import GaloisForLFunctions.HTGeometry.FresnelConstant

/-!
# The Watson scaling of the half-power oscillatory integral

Scaling `u = Lη` turns the half-power oscillatory integral over a fixed window into a truncated
Fresnel integral:

`∫₀^A η^{-1/2} e^{iηL} dη = L^{-1/2} ∫₀^{LA} u^{-1/2} e^{iu} du`,

so with the quantitative Watson approximation the left side is `√π e^{iπ/4} L^{-1/2}` up to
`2 A^{-1/2} L^{-1}`.  This is the leading low-frequency term of the half-log scattering map.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The half-power oscillatory integrand at frequency `L`. -/
def scaledFresnel (L η : ℝ) : ℂ :=
  ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp ((η * L : ℝ) * I)

theorem fresnelKernel_mul {L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    fresnelKernel (L * η) = ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) * scaledFresnel L η := by
  rw [fresnelKernel, scaledFresnel]
  have hpow : (L * η) ^ (-(1:ℝ)/2) = L ^ (-(1:ℝ)/2) * η ^ (-(1:ℝ)/2) :=
    Real.mul_rpow hL.le hη.le
  rw [hpow]
  have hexp : ((L * η : ℝ) : ℂ) * I = ((η * L : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

/-- **The Watson scaling identity.** -/
theorem integral_scaledFresnel {L A : ℝ} (hL : 0 < L) (hA : 0 < A) :
    (∫ η in (0:ℝ)..A, scaledFresnel L η)
      = ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)⁻¹ * ((L : ℝ) : ℂ)⁻¹ * fresnelTruncated (L * A) := by
  have hcomp : (∫ η in (0:ℝ)..A, fresnelKernel (L * η))
      = (L : ℝ)⁻¹ • ∫ u in (L * 0)..(L * A), fresnelKernel u :=
    intervalIntegral.integral_comp_mul_left (fun u => fresnelKernel u) (ne_of_gt hL)
  rw [mul_zero] at hcomp
  have hcongr : (∫ η in (0:ℝ)..A, fresnelKernel (L * η))
      = ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) * ∫ η in (0:ℝ)..A, scaledFresnel L η := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with η hη
    have hη0 : 0 < η := by
      rw [Set.uIoc_of_le hA.le] at hη
      exact hη.1
    exact fresnelKernel_mul hL hη0
  rw [hcongr] at hcomp
  have hLne : ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hLne' : ((L : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hL
  have hsmul : (L : ℝ)⁻¹ • (∫ u in (0:ℝ)..(L * A), fresnelKernel u)
      = ((L : ℝ) : ℂ)⁻¹ * fresnelTruncated (L * A) := by
    rw [fresnelTruncated, Complex.real_smul]
    push_cast
    ring
  rw [hsmul] at hcomp
  rw [mul_assoc, ← hcomp, ← mul_assoc, inv_mul_cancel₀ hLne, one_mul]

/-- **The leading low-frequency term.**  The half-power oscillatory integral over a fixed window is
the Watson constant times `L^{-1/2}`, with an error `2 A^{-1/2} L^{-1}`. -/
theorem norm_integral_scaledFresnel_sub_watson_le {L A : ℝ} (hL : 0 < L) (hA : 0 < A) :
    ‖(∫ η in (0:ℝ)..A, scaledFresnel L η)
        - ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
          * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))‖
      ≤ 2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)) := by
  have hLA : 0 < L * A := mul_pos hL hA
  have hscale := integral_scaledFresnel hL hA
  have hinv : ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)⁻¹ * ((L : ℝ) : ℂ)⁻¹ = ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) := by
    have hposL : (0:ℝ) < L ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hL _
    have hmul : L ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)/2) = L⁻¹ := by
      rw [← Real.rpow_add hL]
      rw [show -(1:ℝ)/2 + -(1:ℝ)/2 = -(1:ℝ) by ring, Real.rpow_neg_one]
    have hval : (L ^ (-(1:ℝ)/2))⁻¹ * L⁻¹ = L ^ (-(1:ℝ)/2) := by
      rw [← hmul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hposL), one_mul]
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hval
    push_cast at hcast
    exact hcast
  rw [hscale, mul_assoc, ← mul_assoc, hinv]
  have hdiff : ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) * fresnelTruncated (L * A)
      - ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))
      = -(((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * ((((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))
          - fresnelTruncated (L * A))) := by ring
  rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _)]
  have htail := norm_watson_sub_fresnelTruncated_le hLA
  have hsplit : (L * A) ^ (-(1:ℝ)/2) = L ^ (-(1:ℝ)/2) * A ^ (-(1:ℝ)/2) :=
    Real.mul_rpow hL.le hA.le
  rw [hsplit] at htail
  have hLpow : L ^ (-(1:ℝ)/2) * (L ^ (-(1:ℝ)/2)) = L ^ (-(1:ℝ)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpos : (0:ℝ) < L ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hL _
  calc L ^ (-(1:ℝ)/2)
        * ‖((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)
            - fresnelTruncated (L * A)‖
      ≤ L ^ (-(1:ℝ)/2) * (2 * (L ^ (-(1:ℝ)/2) * A ^ (-(1:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left htail hpos.le
    _ = 2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)) := by
        rw [← hLpow]
        ring

end

end GaloisForLFunctions.HTGeometry
