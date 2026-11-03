import GaloisForLFunctions.SelbergClass.SubcriticalEulerRigidity
import GaloisForLFunctions.RHTower.SelbergClass.FiniteOrder

/-!
# Entire continuation in degree zero

With no Gamma factors, the functional equation reflects the only possible
pole at one to a regular point at zero. Filling its forced value therefore
gives an entire function. The original finite-order bound survives removal
of this single singularity.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

/-- An empty Gamma product leaves only the real conductor exponential. -/
theorem gammaFactor_eq_exp_of_rank_zero (D : RHTower.SelbergGammaData)
    (hD : D.rank = 0) (s : ℂ) :
    D.gammaFactor s = Complex.exp ((Real.log D.Q : ℂ) * s) := by
  have hp : archGammaFactor D s = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have := j.isLt
    omega
  rw [gammaFactor_eq_exp_mul_archGammaFactor, hp, mul_one]

private theorem gammaFactor_analytic_of_rank_zero (D : RHTower.SelbergGammaData)
    (hD : D.rank = 0) (s : ℂ) : AnalyticAt ℂ D.gammaFactor s := by
  have heq : D.gammaFactor = fun z => Complex.exp ((Real.log D.Q : ℂ) * z) :=
    funext (gammaFactor_eq_exp_of_rank_zero D hD)
  rw [heq]
  fun_prop

private theorem gammaFactor_ne_zero_of_rank_zero (D : RHTower.SelbergGammaData)
    (hD : D.rank = 0) (s : ℂ) : D.gammaFactor s ≠ 0 := by
  rw [gammaFactor_eq_exp_of_rank_zero D hD]
  exact Complex.exp_ne_zero _

/-- The multiplier in the uncompleted degree-zero functional equation. -/
def degreeZeroReflectionFactor (F : RHTower.ExtendedSelbergClass) (s : ℂ) : ℂ :=
  F.gammaData.rootNumber * star (F.gammaData.gammaFactor (1 - star s)) /
    F.gammaData.gammaFactor s

private theorem degreeZeroReflectionFactor_analytic (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) (s : ℂ) :
    AnalyticAt ℂ (degreeZeroReflectionFactor F) s :=
  (analyticAt_const.mul (RHTower.analyticAt_selbergConjugateReflection
    (gammaFactor_analytic_of_rank_zero F.gammaData hF (1 - star s)))).div
      (gammaFactor_analytic_of_rank_zero F.gammaData hF s)
      (gammaFactor_ne_zero_of_rank_zero F.gammaData hF s)

/-- The degree-zero functional equation is pointwise away from zero and one. -/
theorem degreeZero_functionalEquation (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    F s = degreeZeroReflectionFactor F s * star (F (1 - star s)) := by
  have hr1 : 1 - star s ≠ 1 := by
    intro h
    have hz : star s = 0 := by linear_combination -h
    exact hs0 (by simpa using congrArg star hz)
  have hcomp (z : ℂ) (hz : z ≠ 1) :
      AnalyticAt ℂ (RHTower.selbergCompletedValue F.gammaData F.continuation) z :=
    (gammaFactor_analytic_of_rank_zero F.gammaData hF z).mul
      (F.continuation.analyticAt_value_of_ne_one hz)
  have he := F.completedFE_eq_of_analytic_pair (hcomp s hs1) (hcomp (1 - star s) hr1)
  change F.gammaData.gammaFactor s * F s = F.gammaData.rootNumber *
    star (F.gammaData.gammaFactor (1 - star s) * F (1 - star s)) at he
  rw [star_mul] at he
  have hg := gammaFactor_ne_zero_of_rank_zero F.gammaData hF s
  dsimp only [degreeZeroReflectionFactor]
  field_simp
  linear_combination he

/-- The norm of the reflected multiplier has no vertical growth. -/
theorem norm_degreeZeroReflectionFactor (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) (s : ℂ) :
    ‖degreeZeroReflectionFactor F s‖ = Real.exp (Real.log F.gammaData.Q * (1 - 2 * s.re)) := by
  have hg (z : ℂ) : ‖F.gammaData.gammaFactor z‖ =
      Real.exp (Real.log F.gammaData.Q * z.re) := by
    rw [gammaFactor_eq_exp_of_rank_zero F.gammaData hF, Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  simp only [degreeZeroReflectionFactor, norm_div, norm_mul, F.gammaData.rootNumber_norm,
    one_mul, norm_star, hg]
  rw [← Real.exp_sub]
  simp only [sub_re, one_re, RCLike.star_def, conj_re]
  congr 1
  ring

/-- Fill the only possible pole with the value forced by reflection. -/
def degreeZeroValue (F : RHTower.ExtendedSelbergClass) : ℂ → ℂ :=
  Function.update F 1 (degreeZeroReflectionFactor F 1 * star (F 0))

theorem degreeZeroValue_eq (F : RHTower.ExtendedSelbergClass) {s : ℂ} (hs : s ≠ 1) :
    degreeZeroValue F s = F s := Function.update_of_ne hs _ _

/-- Degree zero removes the possible pole at one, without an extra regularity hypothesis. -/
theorem degreeZeroValue_analyticOnNhd (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) : AnalyticOnNhd ℂ (degreeZeroValue F) univ := by
  intro s _
  by_cases hs : s = 1
  · subst s
    have ha : AnalyticAt ℂ (fun z => degreeZeroReflectionFactor F z *
        star (F (1 - star z))) 1 :=
      (degreeZeroReflectionFactor_analytic F hF 1).mul
        (RHTower.analyticAt_selbergConjugateReflection
          (by
            simpa only [star_one, sub_self, RHTower.ExtendedSelbergClass.value] using
              F.continuation.analyticAt_value_of_ne_one (by norm_num : (0 : ℂ) ≠ 1)))
    apply ha.congr
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds
      (by norm_num : (1 : ℂ) ≠ 0)] with z hz
    by_cases hz1 : z = 1
    · subst z
      simp [degreeZeroValue]
    · rw [degreeZeroValue_eq F hz1]
      exact (degreeZero_functionalEquation F hF hz hz1).symm
  · apply (F.continuation.analyticAt_value_of_ne_one hs).congr
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hs] with z hz
    exact (degreeZeroValue_eq F hz).symm

/-- The filled continuation has the same exponential-power growth outside a disk. -/
theorem degreeZeroValue_growth_outside (F : RHTower.ExtendedSelbergClass) :
    RHTower.HasExponentialPowerGrowthOutside (degreeZeroValue F) := by
  obtain ⟨A, B, ρ, hA, hB, hρ, hbound⟩ := F.continuation.regularized.growth
  refine ⟨A, B, ρ, 2, hA, hB, hρ, by norm_num, fun s hs => ?_⟩
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hden : 1 ≤ ‖s - 1‖ := by
    have h := norm_add_le (s - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  rw [degreeZeroValue_eq F hs1]
  change ‖F.continuation.regularized s / (s - 1) ^ F.continuation.poleOrder‖ ≤ _
  rw [norm_div, norm_pow]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hden)).trans (hbound s)

/-- The degree-zero continuation as an entire finite-order function. -/
def degreeZeroEntire (F : RHTower.ExtendedSelbergClass) (hF : F.gammaData.rank = 0) :
    RHTower.EntireFiniteOrder :=
  RHTower.EntireFiniteOrder.ofOutside (degreeZeroValue F)
    (degreeZeroValue_analyticOnNhd F hF) (degreeZeroValue_growth_outside F)

@[simp] theorem degreeZeroEntire_apply (F : RHTower.ExtendedSelbergClass)
    (hF : F.gammaData.rank = 0) (s : ℂ) : degreeZeroEntire F hF s = degreeZeroValue F s := rfl

end GaloisForLFunctions.SelbergClass
