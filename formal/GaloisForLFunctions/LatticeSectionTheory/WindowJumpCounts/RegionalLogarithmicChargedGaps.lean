import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap

/-!
# Regional logarithmic gaps with their lower moment charges

Subtracting the finite Legendre projection retains its exact mass and energy.
The harmonic gap on the orthogonal remainder gives a charged inequality at
any cutoff, including the first three even moments beneath the sixth gap.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws
local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

private def projectionCoefficient (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n
private def lowProjection (F : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  regionalLegendreSum (Finset.range m) (projectionCoefficient F)

private theorem integral_mul_projection {H : ℝ → ℝ} (hH : Continuous H) (F : ℝ → ℝ) (m : ℕ) :
    (∫ x in Icc (-1 : ℝ) 1, H x * lowProjection F m x) =
      ∑ n ∈ Finset.range m, projectionCoefficient F n * regionalLegendreMoment H n := by
  have hi (n : ℕ) : Integrable (fun x => projectionCoefficient F n * (H x * legP n x)) ν :=
    (continuous_const.mul (hH.mul (continuous_legP n))).integrableOn_Icc
  unfold lowProjection regionalLegendreSum regionalLegendreMoment
  simp_rw [Finset.mul_sum, show ∀ n x, H x * (projectionCoefficient F n * legP n x) =
    projectionCoefficient F n * (H x * legP n x) by intros; ring]
  rw [integral_finsetSum _ (fun n _ => hi n)]
  simp_rw [integral_const_mul]

private theorem projection_moment (F : ℝ → ℝ) {m n : ℕ} (hn : n < m) :
    regionalLegendreMoment (lowProjection F m) n = regionalLegendreMoment F n := by
  rw [lowProjection, regionalLegendreMoment_sum, if_pos (Finset.mem_range.mpr hn), projectionCoefficient]
  field_simp [show (2 * (n : ℝ) + 1) ≠ 0 by positivity]

private theorem pair_projection {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (m : ℕ) :
    regionalLogPair F (lowProjection F m) =
      ∑ n ∈ Finset.range m, regionalLogEigenvalue n * ((2 * (n : ℝ) + 1) / 2) *
        regionalLegendreMoment F n ^ 2 := by
  unfold lowProjection
  rw [regionalLogPair_eq_integral hF (contDiff_regionalLegendreSum _ _)]
  simp_rw [regionalLogOperator_legendreSum, Finset.mul_sum]
  have hi (n : ℕ) : Integrable (fun x => F x *
      (projectionCoefficient F n * regionalLogEigenvalue n * legP n x)) ν :=
    (hF.continuous.mul (continuous_const.mul (continuous_legP n))).integrableOn_Icc
  rw [integral_finsetSum _ (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n _
  have he : (fun x => F x * (projectionCoefficient F n * regionalLogEigenvalue n * legP n x)) =
      fun x => (projectionCoefficient F n * regionalLogEigenvalue n) * (F x * legP n x) := by
    funext x
    ring
  rw [he, integral_const_mul]
  change projectionCoefficient F n * regionalLogEigenvalue n * regionalLegendreMoment F n = _
  dsimp [projectionCoefficient]
  ring

private theorem projection_residual_mass {F : ℝ → ℝ} (hF : Continuous F) (m : ℕ) :
    (∫ x in Icc (-1 : ℝ) 1, (F x - lowProjection F m x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
        ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2 := by
  let P := lowProjection F m
  let B := ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2
  have hP : ContDiff ℝ 1 P := contDiff_regionalLegendreSum _ _
  have hFP : (∫ x in Icc (-1 : ℝ) 1, F x * P x) = B := by
    rw [integral_mul_projection hF F m]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [projectionCoefficient]
    ring
  have hPP : (∫ x in Icc (-1 : ℝ) 1, P x ^ 2) = B := by
    have h := integral_mul_projection hP.continuous F m
    have he : (∑ n ∈ Finset.range m, projectionCoefficient F n * regionalLegendreMoment P n) = B := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [projection_moment F (Finset.mem_range.mp hn)]
      dsimp [projectionCoefficient]
      ring
    rw [he] at h
    simpa only [pow_two] using h
  have hmass : (∫ x in Icc (-1 : ℝ) 1, (F x - P x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) - B := by
    have hiFF : Integrable (fun x => F x ^ 2) ν := (hF.pow 2).integrableOn_Icc
    have hiPP : Integrable (fun x => P x ^ 2) ν := (hP.continuous.pow 2).integrableOn_Icc
    have hiFP : Integrable (fun x => F x * P x) ν := (hF.mul hP.continuous).integrableOn_Icc
    have hiSum : Integrable (fun x => F x ^ 2 + P x ^ 2) ν := hiFF.add hiPP
    have he : (fun x => (F x - P x) ^ 2) = fun x => F x ^ 2 + P x ^ 2 - 2 * (F x * P x) := by
      funext x
      ring
    rw [he, integral_sub hiSum (hiFP.const_mul 2), integral_add hiFF hiPP,
      integral_const_mul, hFP, hPP]
    ring
  exact hmass

/-- The first Legendre moments consume no more than the square mass of the source. -/
theorem regionalMass_ge_low_moments {F : ℝ → ℝ} (hF : Continuous F) (m : ℕ) :
    (∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2) ≤
      ∫ x in Icc (-1 : ℝ) 1, F x ^ 2 := by
  have h : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, (F x - lowProjection F m x) ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg (F x - lowProjection F m x))
  rw [projection_residual_mass hF m] at h
  linarith only [h]

/-- Removing all projections below a cutoff retains their exact charges beneath its harmonic gap. -/
theorem regionalLogEnergy_ge_gap_sub_low_moments {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (m : ℕ) :
    regionalLogEigenvalue m * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (∑ n ∈ Finset.range m, (regionalLogEigenvalue m - regionalLogEigenvalue n) *
        ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2) ≤ regionalLogEnergy F := by
  let P := lowProjection F m
  let B := ∑ n ∈ Finset.range m, ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2
  let C := ∑ n ∈ Finset.range m, regionalLogEigenvalue n *
    ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2
  have hP : ContDiff ℝ 1 P := contDiff_regionalLegendreSum _ _
  have hm : ∀ n < m, regionalLegendreMoment (fun x => F x - P x) n = 0 := by
    intro n hn
    have hiF : Integrable (fun x => F x * legP n x) ν :=
      (hF.continuous.mul (continuous_legP n)).integrableOn_Icc
    have hiP : Integrable (fun x => P x * legP n x) ν :=
      (hP.continuous.mul (continuous_legP n)).integrableOn_Icc
    unfold regionalLegendreMoment
    simp_rw [sub_mul]
    rw [integral_sub hiF hiP]
    change regionalLegendreMoment F n - regionalLegendreMoment P n = 0
    rw [projection_moment F hn, sub_self]
  have hmass := projection_residual_mass hF.continuous m
  have hpair : regionalLogPair F P = C := pair_projection hF m
  have henergy : regionalLogEnergy P = C := by
    dsimp only [P, lowProjection]
    rw [regionalLogEnergy_legendreSum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [projectionCoefficient]
    field_simp [show (2 * (n : ℝ) + 1) ≠ 0 by positivity]
  have hgap := regionalLogEnergy_moment_gap (hF.sub hP) m hm
  rw [hmass, regionalLogEnergy_sub hF hP, henergy, hpair] at hgap
  have he : (∑ n ∈ Finset.range m, (regionalLogEigenvalue m - regionalLogEigenvalue n) *
      ((2 * (n : ℝ) + 1) / 2) * regionalLegendreMoment F n ^ 2) = regionalLogEigenvalue m * B - C := by
    dsimp [B, C]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  nlinarith only [hgap]

private theorem odd_moment_even {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x)
    {n : ℕ} (hn : (-1 : ℝ) ^ n = -1) : regionalLegendreMoment F n = 0 := by
  have h := intervalIntegral.integral_comp_neg (f := fun x => F x * legP n x)
    (a := (-1 : ℝ)) (b := 1)
  simp only [he, legP_neg, hn, neg_one_mul, mul_neg, intervalIntegral.integral_neg, neg_neg] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  unfold regionalLegendreMoment
  linarith only [h]

/-- The first three even moments retain the exact charges below the sixth harmonic gap. -/
theorem regionalLogEnergy_ge_sixth_gap_sub_low_even_moments {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (he : ∀ x, F (-x) = F x) :
    (49 / 10 : ℝ) * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (49 / 20 : ℝ) * regionalLegendreMoment F 0 ^ 2 -
      (19 / 4 : ℝ) * regionalLegendreMoment F 2 ^ 2 -
      (33 / 10 : ℝ) * regionalLegendreMoment F 4 ^ 2 ≤ regionalLogEnergy F := by
  have h := regionalLogEnergy_ge_gap_sub_low_moments hF 6
  have h1 : regionalLegendreMoment F 1 = 0 := odd_moment_even he (by norm_num)
  have h3 : regionalLegendreMoment F 3 = 0 := odd_moment_even he (by norm_num)
  have h5 : regionalLegendreMoment F 5 = 0 := odd_moment_even he (by norm_num)
  norm_num [Finset.sum_range_succ, regionalLogEigenvalue, h1, h3, h5] at h
  linarith only [h]

/-- Three even Legendre moments consume mass with weights `1/2`, `5/2`, and `9/2`. -/
theorem regionalMass_ge_three_even_moments {F : ℝ → ℝ}
    (hF : Continuous F) (he : ∀ x, F (-x) = F x) :
    (1 / 2 : ℝ) * regionalLegendreMoment F 0 ^ 2 +
      (5 / 2 : ℝ) * regionalLegendreMoment F 2 ^ 2 +
      (9 / 2 : ℝ) * regionalLegendreMoment F 4 ^ 2 ≤
        ∫ x in Icc (-1 : ℝ) 1, F x ^ 2 := by
  have h := regionalMass_ge_low_moments hF 6
  have h1 : regionalLegendreMoment F 1 = 0 := odd_moment_even he (by norm_num)
  have h3 : regionalLegendreMoment F 3 = 0 := odd_moment_even he (by norm_num)
  have h5 : regionalLegendreMoment F 5 = 0 := odd_moment_even he (by norm_num)
  norm_num [Finset.sum_range_succ, h1, h3, h5] at h
  linarith only [h]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_ge_gap_sub_low_moments
#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_ge_sixth_gap_sub_low_even_moments

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalMass_ge_three_even_moments
