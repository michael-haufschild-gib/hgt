import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap

/-!
# The two low odd charges below the fifth harmonic gap

Removing the first and third Legendre projections gives the fifth harmonic
gap. Expanding their mass and energy retains their exact negative charges on
arbitrary odd tests, including all cross terms with the remaining function.
-/

noncomputable section
open Real MeasureTheory Set Filter
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

private def oddLowCoefficient (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n

private def oddLowProjection (F : ℝ → ℝ) : ℝ → ℝ :=
  regionalLegendreSum {1, 3} (oddLowCoefficient F)

private theorem oddLowProjection_expansion (F : ℝ → ℝ) (x : ℝ) :
    oddLowProjection F x = (3 / 2 : ℝ) * regionalLegendreMoment F 1 * legP 1 x +
      (7 / 2 : ℝ) * regionalLegendreMoment F 3 * legP 3 x := by
  norm_num [oddLowProjection, regionalLegendreSum, oddLowCoefficient]

private theorem contDiff_oddLowProjection (F : ℝ → ℝ) :
    ContDiff ℝ 1 (oddLowProjection F) := contDiff_regionalLegendreSum _ _

private theorem oddLowProjection_odd (F : ℝ → ℝ) (x : ℝ) :
    oddLowProjection F (-x) = -oddLowProjection F x := by
  rw [oddLowProjection_expansion, oddLowProjection_expansion, legP_neg, legP_neg]
  norm_num
  ring

private theorem oddLowProjection_moment (F : ℝ → ℝ) {n : ℕ} (hn : n ∈ ({1, 3} : Finset ℕ)) :
    regionalLegendreMoment (oddLowProjection F) n = regionalLegendreMoment F n := by
  rw [oddLowProjection, regionalLegendreMoment_sum, if_pos hn, oddLowCoefficient]
  have hp : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hp]

private theorem integral_mul_oddLowProjection {H : ℝ → ℝ} (hH : Continuous H) (F : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, H x * oddLowProjection F x) =
      (3 / 2 : ℝ) * regionalLegendreMoment F 1 * regionalLegendreMoment H 1 +
      (7 / 2 : ℝ) * regionalLegendreMoment F 3 * regionalLegendreMoment H 3 := by
  have hi (n : ℕ) : Integrable (fun x => H x * legP n x) ν :=
    (hH.mul (continuous_legP n)).integrableOn_Icc
  have he : (fun x => H x * oddLowProjection F x) = fun x =>
      ((3 / 2 : ℝ) * regionalLegendreMoment F 1) * (H x * legP 1 x) +
      ((7 / 2 : ℝ) * regionalLegendreMoment F 3) * (H x * legP 3 x) := by
    funext x
    rw [oddLowProjection_expansion]
    ring
  rw [he, integral_add ((hi 1).const_mul _) ((hi 3).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

private theorem oddLowProjection_mass (F : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, oddLowProjection F x ^ 2) =
      (3 / 2 : ℝ) * regionalLegendreMoment F 1 ^ 2 +
      (7 / 2 : ℝ) * regionalLegendreMoment F 3 ^ 2 := by
  have h := integral_mul_oddLowProjection (contDiff_oddLowProjection F).continuous F
  rw [oddLowProjection_moment F (by simp : 1 ∈ ({1, 3} : Finset ℕ)),
    oddLowProjection_moment F (by simp : 3 ∈ ({1, 3} : Finset ℕ))] at h
  simpa only [pow_two, mul_assoc] using h

private theorem pair_oddLowProjection {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) (F : ℝ → ℝ) :
    regionalLogPair H (oddLowProjection F) =
      3 * regionalLegendreMoment F 1 * regionalLegendreMoment H 1 +
      (77 / 6 : ℝ) * regionalLegendreMoment F 3 * regionalLegendreMoment H 3 := by
  have hi (n : ℕ) : Integrable (fun x => H x * legP n x) ν :=
    (hH.continuous.mul (continuous_legP n)).integrableOn_Icc
  have hop (x : ℝ) : regionalLogOperator (oddLowProjection F) x =
      3 * regionalLegendreMoment F 1 * legP 1 x +
      (77 / 6 : ℝ) * regionalLegendreMoment F 3 * legP 3 x := by
    rw [oddLowProjection, regionalLogOperator_legendreSum]
    norm_num [oddLowCoefficient, regionalLogEigenvalue, Finset.sum_range_succ]
    ring
  have he : (fun x => H x * regionalLogOperator (oddLowProjection F) x) = fun x =>
      (3 * regionalLegendreMoment F 1) * (H x * legP 1 x) +
      ((77 / 6 : ℝ) * regionalLegendreMoment F 3) * (H x * legP 3 x) := by
    funext x
    rw [hop]
    ring
  rw [regionalLogPair_eq_integral hH (contDiff_oddLowProjection F), he,
    integral_add ((hi 1).const_mul _) ((hi 3).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

private theorem residual_odd_moment {F : ℝ → ℝ} (hF : Continuous F) {n : ℕ}
    (hn : n ∈ ({1, 3} : Finset ℕ)) :
    regionalLegendreMoment (fun x => F x - oddLowProjection F x) n = 0 := by
  have hiF : Integrable (fun x => F x * legP n x) ν :=
    (hF.mul (continuous_legP n)).integrableOn_Icc
  have hiP : Integrable (fun x => oddLowProjection F x * legP n x) ν :=
    ((contDiff_oddLowProjection F).continuous.mul (continuous_legP n)).integrableOn_Icc
  unfold regionalLegendreMoment
  simp_rw [sub_mul]
  rw [integral_sub hiF hiP]
  change regionalLegendreMoment F n - regionalLegendreMoment (oddLowProjection F) n = 0
  rw [oddLowProjection_moment F hn, sub_self]

private theorem even_moment_of_odd {H : ℝ → ℝ} (ho : ∀ x, H (-x) = -H x)
    {n : ℕ} (hn : (-1 : ℝ) ^ n = 1) : regionalLegendreMoment H n = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun x => H x * legP n x) (a := (-1 : ℝ)) (b := 1)
  simp only [ho, legP_neg, hn, one_mul, neg_mul, intervalIntegral.integral_neg, neg_neg] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  unfold regionalLegendreMoment
  linarith only [h]

/-- Retaining the two low odd projections gives the exact charges below the fifth gap. -/
theorem regionalLogEnergy_ge_fifth_gap_sub_low_odd_moments {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (ho : ∀ x, F (-x) = -F x) :
    (137 / 30 : ℝ) * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (77 / 20 : ℝ) * regionalLegendreMoment F 1 ^ 2 -
      (63 / 20 : ℝ) * regionalLegendreMoment F 3 ^ 2 ≤ regionalLogEnergy F := by
  have hP := contDiff_oddLowProjection F
  have hR : ContDiff ℝ 1 (fun x => F x - oddLowProjection F x) := hF.sub hP
  have hRo (x : ℝ) : F (-x) - oddLowProjection F (-x) = -(F x - oddLowProjection F x) := by
    rw [ho, oddLowProjection_odd]
    ring
  have hm : ∀ n < 5, regionalLegendreMoment (fun x => F x - oddLowProjection F x) n = 0 := by
    intro n hn
    interval_cases n
    · exact even_moment_of_odd hRo (by norm_num)
    · exact residual_odd_moment hF.continuous (by simp)
    · exact even_moment_of_odd hRo (by norm_num)
    · exact residual_odd_moment hF.continuous (by simp)
    · exact even_moment_of_odd hRo (by norm_num)
  have hgap := regionalLogEnergy_moment_gap hR 5 hm
  norm_num [regionalLogEigenvalue, Finset.sum_range_succ] at hgap
  have hFP := integral_mul_oddLowProjection hF.continuous F
  have hPP := oddLowProjection_mass F
  have hiFF : Integrable (fun x => F x ^ 2) ν := (hF.continuous.pow 2).integrableOn_Icc
  have hiPP : Integrable (fun x => oddLowProjection F x ^ 2) ν :=
    (hP.continuous.pow 2).integrableOn_Icc
  have hiFP : Integrable (fun x => F x * oddLowProjection F x) ν :=
    (hF.continuous.mul hP.continuous).integrableOn_Icc
  have hiSum : Integrable (fun x => F x ^ 2 + oddLowProjection F x ^ 2) ν := hiFF.add hiPP
  have hmass : (∫ x in Icc (-1 : ℝ) 1, (F x - oddLowProjection F x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
        (3 / 2 : ℝ) * regionalLegendreMoment F 1 ^ 2 -
        (7 / 2 : ℝ) * regionalLegendreMoment F 3 ^ 2 := by
    have he : (fun x => (F x - oddLowProjection F x) ^ 2) = fun x =>
        F x ^ 2 + oddLowProjection F x ^ 2 - 2 * (F x * oddLowProjection F x) := by
      funext x
      ring
    rw [he, integral_sub hiSum (hiFP.const_mul 2),
      integral_add hiFF hiPP, integral_const_mul, hFP, hPP]
    ring
  have hpair := pair_oddLowProjection hF F
  have henergy : regionalLogEnergy (oddLowProjection F) =
      3 * regionalLegendreMoment F 1 ^ 2 + (77 / 6 : ℝ) * regionalLegendreMoment F 3 ^ 2 := by
    have h := pair_oddLowProjection hP F
    rw [oddLowProjection_moment F (by simp : 1 ∈ ({1, 3} : Finset ℕ)),
      oddLowProjection_moment F (by simp : 3 ∈ ({1, 3} : Finset ℕ))] at h
    simpa only [regionalLogEnergy, pow_two, mul_assoc] using h
  rw [hmass, regionalLogEnergy_sub hF hP, henergy, hpair] at hgap
  nlinarith only [hgap]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_ge_fifth_gap_sub_low_odd_moments
