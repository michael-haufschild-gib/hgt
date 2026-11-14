import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap

/-!
# The two low even charges below the fourth harmonic gap

Removing the constant and quadratic Legendre projections gives the fourth harmonic
gap. Expanding their mass and energy retains their exact negative charges on
arbitrary even tests, including all cross terms with the remaining function.
-/

noncomputable section
open Real MeasureTheory Set Filter
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

private def evenLowCoefficient (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n

private def evenLowProjection (F : ℝ → ℝ) : ℝ → ℝ :=
  regionalLegendreSum {0, 2} (evenLowCoefficient F)

private theorem evenLowProjection_expansion (F : ℝ → ℝ) (x : ℝ) :
    evenLowProjection F x = (1 / 2 : ℝ) * regionalLegendreMoment F 0 * legP 0 x +
      (5 / 2 : ℝ) * regionalLegendreMoment F 2 * legP 2 x := by
  norm_num [evenLowProjection, regionalLegendreSum, evenLowCoefficient]

private theorem contDiff_evenLowProjection (F : ℝ → ℝ) :
    ContDiff ℝ 1 (evenLowProjection F) := contDiff_regionalLegendreSum _ _

private theorem evenLowProjection_even (F : ℝ → ℝ) (x : ℝ) :
    evenLowProjection F (-x) = evenLowProjection F x := by
  rw [evenLowProjection_expansion, evenLowProjection_expansion, legP_neg, legP_neg]
  norm_num

private theorem evenLowProjection_moment (F : ℝ → ℝ) {n : ℕ} (hn : n ∈ ({0, 2} : Finset ℕ)) :
    regionalLegendreMoment (evenLowProjection F) n = regionalLegendreMoment F n := by
  rw [evenLowProjection, regionalLegendreMoment_sum, if_pos hn, evenLowCoefficient]
  have hp : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hp]

private theorem integral_mul_evenLowProjection {H : ℝ → ℝ} (hH : Continuous H) (F : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, H x * evenLowProjection F x) =
      (1 / 2 : ℝ) * regionalLegendreMoment F 0 * regionalLegendreMoment H 0 +
      (5 / 2 : ℝ) * regionalLegendreMoment F 2 * regionalLegendreMoment H 2 := by
  have hi (n : ℕ) : Integrable (fun x => H x * legP n x) ν :=
    (hH.mul (continuous_legP n)).integrableOn_Icc
  have he : (fun x => H x * evenLowProjection F x) = fun x =>
      ((1 / 2 : ℝ) * regionalLegendreMoment F 0) * (H x * legP 0 x) +
      ((5 / 2 : ℝ) * regionalLegendreMoment F 2) * (H x * legP 2 x) := by
    funext x
    rw [evenLowProjection_expansion]
    ring
  rw [he, integral_add ((hi 0).const_mul _) ((hi 2).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

private theorem evenLowProjection_mass (F : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, evenLowProjection F x ^ 2) =
      (1 / 2 : ℝ) * regionalLegendreMoment F 0 ^ 2 +
      (5 / 2 : ℝ) * regionalLegendreMoment F 2 ^ 2 := by
  have h := integral_mul_evenLowProjection (contDiff_evenLowProjection F).continuous F
  rw [evenLowProjection_moment F (by simp : 0 ∈ ({0, 2} : Finset ℕ)),
    evenLowProjection_moment F (by simp : 2 ∈ ({0, 2} : Finset ℕ))] at h
  simpa only [pow_two, mul_assoc] using h

private theorem pair_evenLowProjection {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) (F : ℝ → ℝ) :
    regionalLogPair H (evenLowProjection F) =
      (15 / 2 : ℝ) * regionalLegendreMoment F 2 * regionalLegendreMoment H 2 := by
  have hop (x : ℝ) : regionalLogOperator (evenLowProjection F) x =
      (15 / 2 : ℝ) * regionalLegendreMoment F 2 * legP 2 x := by
    rw [evenLowProjection, regionalLogOperator_legendreSum]
    norm_num [evenLowCoefficient, regionalLogEigenvalue, Finset.sum_range_succ]
    ring_nf
    simp
  have he : (fun x => H x * regionalLogOperator (evenLowProjection F) x) = fun x =>
      ((15 / 2 : ℝ) * regionalLegendreMoment F 2) * (H x * legP 2 x) := by
    funext x
    rw [hop]
    ring
  rw [regionalLogPair_eq_integral hH (contDiff_evenLowProjection F), he, integral_const_mul]
  rfl

private theorem residual_even_moment {F : ℝ → ℝ} (hF : Continuous F) {n : ℕ}
    (hn : n ∈ ({0, 2} : Finset ℕ)) :
    regionalLegendreMoment (fun x => F x - evenLowProjection F x) n = 0 := by
  have hiF : Integrable (fun x => F x * legP n x) ν :=
    (hF.mul (continuous_legP n)).integrableOn_Icc
  have hiP : Integrable (fun x => evenLowProjection F x * legP n x) ν :=
    ((contDiff_evenLowProjection F).continuous.mul (continuous_legP n)).integrableOn_Icc
  unfold regionalLegendreMoment
  simp_rw [sub_mul]
  rw [integral_sub hiF hiP]
  change regionalLegendreMoment F n - regionalLegendreMoment (evenLowProjection F) n = 0
  rw [evenLowProjection_moment F hn, sub_self]

private theorem odd_moment_of_even {H : ℝ → ℝ} (ho : ∀ x, H (-x) = H x)
    {n : ℕ} (hn : (-1 : ℝ) ^ n = -1) : regionalLegendreMoment H n = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun x => H x * legP n x) (a := (-1 : ℝ)) (b := 1)
  simp only [ho, legP_neg, hn, neg_one_mul, mul_neg, intervalIntegral.integral_neg, neg_neg] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  unfold regionalLegendreMoment
  linarith only [h]

/-- Retaining the two low even projections gives the exact charges below the fourth gap. -/
theorem regionalLogEnergy_ge_fourth_gap_sub_low_even_moments {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (ho : ∀ x, F (-x) = F x) :
    (25 / 6 : ℝ) * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (25 / 12 : ℝ) * regionalLegendreMoment F 0 ^ 2 -
      (35 / 12 : ℝ) * regionalLegendreMoment F 2 ^ 2 ≤ regionalLogEnergy F := by
  have hP := contDiff_evenLowProjection F
  have hR : ContDiff ℝ 1 (fun x => F x - evenLowProjection F x) := hF.sub hP
  have hRo (x : ℝ) : F (-x) - evenLowProjection F (-x) = F x - evenLowProjection F x := by
    rw [ho, evenLowProjection_even]
  have hm : ∀ n < 4, regionalLegendreMoment (fun x => F x - evenLowProjection F x) n = 0 := by
    intro n hn
    interval_cases n
    · exact residual_even_moment hF.continuous (by simp)
    · exact odd_moment_of_even hRo (by norm_num)
    · exact residual_even_moment hF.continuous (by simp)
    · exact odd_moment_of_even hRo (by norm_num)
  have hgap := regionalLogEnergy_moment_gap hR 4 hm
  norm_num [regionalLogEigenvalue, Finset.sum_range_succ] at hgap
  have hFP := integral_mul_evenLowProjection hF.continuous F
  have hPP := evenLowProjection_mass F
  have hiFF : Integrable (fun x => F x ^ 2) ν := (hF.continuous.pow 2).integrableOn_Icc
  have hiPP : Integrable (fun x => evenLowProjection F x ^ 2) ν :=
    (hP.continuous.pow 2).integrableOn_Icc
  have hiFP : Integrable (fun x => F x * evenLowProjection F x) ν :=
    (hF.continuous.mul hP.continuous).integrableOn_Icc
  have hiSum : Integrable (fun x => F x ^ 2 + evenLowProjection F x ^ 2) ν := hiFF.add hiPP
  have hmass : (∫ x in Icc (-1 : ℝ) 1, (F x - evenLowProjection F x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
        (1 / 2 : ℝ) * regionalLegendreMoment F 0 ^ 2 -
        (5 / 2 : ℝ) * regionalLegendreMoment F 2 ^ 2 := by
    have he : (fun x => (F x - evenLowProjection F x) ^ 2) = fun x =>
        F x ^ 2 + evenLowProjection F x ^ 2 - 2 * (F x * evenLowProjection F x) := by
      funext x
      ring
    rw [he, integral_sub hiSum (hiFP.const_mul 2),
      integral_add hiFF hiPP, integral_const_mul, hFP, hPP]
    ring
  have hpair := pair_evenLowProjection hF F
  have henergy : regionalLogEnergy (evenLowProjection F) =
      (15 / 2 : ℝ) * regionalLegendreMoment F 2 ^ 2 := by
    have h := pair_evenLowProjection hP F
    rw [evenLowProjection_moment F (by simp : 2 ∈ ({0, 2} : Finset ℕ))] at h
    simpa only [regionalLogEnergy, pow_two, mul_assoc] using h
  rw [hmass, regionalLogEnergy_sub hF hP, henergy, hpair] at hgap
  nlinarith only [hgap]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_ge_fourth_gap_sub_low_even_moments
