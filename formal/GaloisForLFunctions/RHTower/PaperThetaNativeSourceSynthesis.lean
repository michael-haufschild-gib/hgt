import GaloisForLFunctions.RHTower.PaperThetaGaussianNativeSeries
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianFaithfulness
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteNativeDensity

/-! # Faithfulness of the actual infinite native source synthesis

The native moment map and the original source Mellin map both commute with
their paid series. Their exact block identity identifies the whole source
sum. Global Xi synthesis then proves that no original class is lost.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource
open scoped DeningerMeyerNaturalTopology

def nativeGaussianOriginalSource (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) (ε : ℝ) (hε : 0 < ε) : DeningerMeyerStrongLogTarget :=
  ∑' n, S.xiBlockSource
    (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
    (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n

theorem nativeGaussianSource_transform (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) (u : ℂ) :
    boundedThetaMomentCLM (thetaContourParameter u) (nativeGaussianSource S g ε hε) =
      (I*(u-1/2)/(thetaSource.mass : ℂ))*
        deningerMeyerStrongLogMellin (nativeGaussianOriginalSource S g ε hε) u := by
  let F := deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)
  have hF : Differentiable ℂ F := (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable
  have hs := S.gaussian_xiBlockSource_summable g hε
  have hn := gaussian_nativeXiBlock_summable S g hε
  let c : ℂ := I*(u-1/2)/(thetaSource.mass : ℂ)
  have he := (c • deningerMeyerStrongLogMellinJetCLM 0 u).map_tsum hs
  simp only [smul_apply, smul_eq_mul,
    deningerMeyerStrongLogMellinJetCLM_apply, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_zero, DeningerMeyerXiContourSchedule.xiBlockSource_mellin] at he
  unfold nativeGaussianSource
  rw [ContinuousLinearMap.map_tsum _ hn]
  exact (tsum_congr (fun n => nativeXiBlock_transform S F hF n u)).trans he.symm

/-- The infinite synthesis contains no exceptional constant mode. -/
theorem nativeGaussianSource_theta_mean_zero (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    boundedThetaMomentCLM 0 (nativeGaussianSource S g ε hε) = 0 := by
  simpa [thetaContourParameter] using nativeGaussianSource_transform S g hε (1/2)

/-- The kernel is exactly the genuine Poisson boundary range. -/
theorem nativeGaussianSource_eq_zero_iff (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    nativeGaussianSource S g ε hε = 0 ↔
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 := by
  constructor
  · intro hz
    have he : deningerMeyerStrongLogMellin (nativeGaussianOriginalSource S g ε hε) =
        fun _ => (0:ℂ) := by
      apply Continuous.ext_on (dense_compl_singleton (1/2:ℂ))
        (deningerMeyerStrongLogMellin_entireRegular (nativeGaussianOriginalSource S g ε hε)).differentiable.continuous
        continuous_const
      intro u hu
      have hne : u ≠ 1/2 := hu
      have hc : I*(u-1/2)/(thetaSource.mass : ℂ) ≠ 0 :=
        div_ne_zero (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hne))
          (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)
      have hm := nativeGaussianSource_transform S g hε u
      rw [hz, map_zero] at hm
      exact (mul_eq_zero.mp hm.symm).resolve_left hc
    have hsrc : nativeGaussianOriginalSource S g ε hε = 0 := by
      apply deningerMeyerStrongLogMellin_injective
      funext u
      change deningerMeyerStrongLogMellin (nativeGaussianOriginalSource S g ε hε) u =
        deningerMeyerStrongLogMellin (0 : DeningerMeyerStrongLogTarget) u
      rw [congrFun he u]
      exact (show deningerMeyerStrongLogMellin (0 : DeningerMeyerStrongLogTarget) u = 0 from
        (deningerMeyerStrongLogMellinLM u).map_zero).symm
    apply (deningerMeyer_gaussian_boundary_iff g hε).mp
    rw [← S.gaussian_sum_class g hε]
    change (Submodule.Quotient.mk (nativeGaussianOriginalSource S g ε hε) :
      DeningerMeyerStrongLogCohomology) = 0
    rw [hsrc]
    rfl
  · intro hg
    obtain ⟨H, hH, hdiv⟩ := deningerMeyer_entireXiDivision_of_boundary g hg
    have hh : Differentiable ℂ (fun s : ℂ => exp ((ε:ℂ)*s^2)*H s) := by fun_prop
    have hb (n : ℕ) : nativeXiBlock S
        (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
        (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n = 0 := by
      apply nativeXiBlock_of_entire_division S _ hh _ n
      intro s
      dsimp [deningerGaussianMellinRegularization]
      rw [hdiv]
      ring
    simp only [nativeGaussianSource, hb, tsum_zero]

end RHTower.PaperThetaEndpoint
