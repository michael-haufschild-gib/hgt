import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicLowOddMoments

/-!
# The first odd charge below the third harmonic gap

Bessel's inequality for the first and third Legendre projections removes the
third charge from the fifth-gap estimate. The exact surviving charge is `5/2`.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

private theorem legendre_product_integral (j k : ℕ) :
    (∫ x in Icc (-1 : ℝ) 1, legP j x * legP k x) =
      if j = k then 2 / (2 * (j : ℝ) + 1) else 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  by_cases h : j = k
  · subst k
    rw [if_pos rfl]
    simpa only [pow_two] using legP_sq_integral j
  · rw [if_neg h]
    exact legP_orthog h

private theorem first_third_moment_mass_bound {F : ℝ → ℝ} (hF : Continuous F) :
    (3 / 2 : ℝ) * regionalLegendreMoment F 1 ^ 2 +
      (7 / 2 : ℝ) * regionalLegendreMoment F 3 ^ 2 ≤
        ∫ x in Icc (-1 : ℝ) 1, F x ^ 2 := by
  let a := (3 / 2 : ℝ) * regionalLegendreMoment F 1
  let b := (7 / 2 : ℝ) * regionalLegendreMoment F 3
  have hn : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, (F x - a * legP 1 x - b * legP 3 x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have he : (fun x => (F x - a * legP 1 x - b * legP 3 x) ^ 2) = fun x =>
      F x ^ 2 + a ^ 2 * (legP 1 x * legP 1 x) + b ^ 2 * (legP 3 x * legP 3 x) +
      (2 * a * b) * (legP 1 x * legP 3 x) -
      (2 * a) * (F x * legP 1 x) - (2 * b) * (F x * legP 3 x) := by
    funext x
    ring
  rw [he] at hn
  have hFF : IntegrableOn (fun x => F x ^ 2) (Icc (-1 : ℝ) 1) :=
    (hF.pow 2).integrableOn_Icc
  have hPP (j k : ℕ) : IntegrableOn (fun x => legP j x * legP k x) (Icc (-1 : ℝ) 1) :=
    ((continuous_legP j).mul (continuous_legP k)).integrableOn_Icc
  have hFP (j : ℕ) : IntegrableOn (fun x => F x * legP j x) (Icc (-1 : ℝ) 1) :=
    (hF.mul (continuous_legP j)).integrableOn_Icc
  have hS1 : IntegrableOn (fun x => F x ^ 2 + a ^ 2 * (legP 1 x * legP 1 x))
      (Icc (-1 : ℝ) 1) := hFF.add ((hPP 1 1).const_mul (a ^ 2))
  have hS2 : IntegrableOn (fun x => F x ^ 2 + a ^ 2 * (legP 1 x * legP 1 x) +
      b ^ 2 * (legP 3 x * legP 3 x)) (Icc (-1 : ℝ) 1) :=
    hS1.add ((hPP 3 3).const_mul (b ^ 2))
  have hS3 : IntegrableOn (fun x => F x ^ 2 + a ^ 2 * (legP 1 x * legP 1 x) +
      b ^ 2 * (legP 3 x * legP 3 x) + (2 * a * b) * (legP 1 x * legP 3 x))
      (Icc (-1 : ℝ) 1) := hS2.add ((hPP 1 3).const_mul (2 * a * b))
  have hS4 : IntegrableOn (fun x => F x ^ 2 + a ^ 2 * (legP 1 x * legP 1 x) +
      b ^ 2 * (legP 3 x * legP 3 x) + (2 * a * b) * (legP 1 x * legP 3 x) -
      (2 * a) * (F x * legP 1 x)) (Icc (-1 : ℝ) 1) := hS3.sub ((hFP 1).const_mul (2 * a))
  rw [integral_sub hS4 ((hFP 3).const_mul (2 * b)),
    integral_sub hS3 ((hFP 1).const_mul (2 * a)),
    integral_add hS2 ((hPP 1 3).const_mul (2 * a * b)),
    integral_add hS1 ((hPP 3 3).const_mul (b ^ 2)),
    integral_add hFF ((hPP 1 1).const_mul (a ^ 2))] at hn
  simp only [integral_const_mul] at hn
  norm_num [legendre_product_integral] at hn
  dsimp [a, b] at hn
  unfold regionalLegendreMoment at hn ⊢
  nlinarith only [hn]

/-- Below the third harmonic gap, the first odd moment is the only remaining charge. -/
theorem regionalLogEnergy_ge_third_gap_sub_first_odd_moment {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (ho : ∀ x, F (-x) = -F x) :
    (11 / 3 : ℝ) * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (5 / 2 : ℝ) * regionalLegendreMoment F 1 ^ 2 ≤ regionalLogEnergy F := by
  have h := regionalLogEnergy_ge_fifth_gap_sub_low_odd_moments hF ho
  have hm := first_third_moment_mass_bound hF.continuous
  linarith only [h, hm]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_ge_third_gap_sub_first_odd_moment
