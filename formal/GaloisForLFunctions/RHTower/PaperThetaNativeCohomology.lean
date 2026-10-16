import GaloisForLFunctions.RHTower.PaperThetaNativeSourceSynthesis
import GaloisForLFunctions.RHTower.PaperThetaStripSeries

/-! # A faithful native realization of the whole original Meyer quotient -/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open scoped DeningerMeyerNaturalTopology

theorem nativeXiBlock_sub (S : DeningerMeyerXiContourSchedule)
    {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    nativeXiBlock S (fun s => F s-G s) (hF.sub hG) n =
      nativeXiBlock S F hF n-nativeXiBlock S G hG n := by
  apply BoundedContinuousFunction.ext
  intro x
  cases n with
  | zero => exact nativeXiContour_sub hF hG S.central_nonzero x
  | succ n =>
      simp only [nativeXiBlock, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.sub_apply, nativeXiContourBCF_apply,
        nativeXiContour_sub hF hG (S.upper_nonzero n),
        nativeXiContour_sub hF hG (S.lower_nonzero n)]
      ring

theorem nativeXiBlock_const_mul (S : DeningerMeyerXiContourSchedule)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (n : ℕ) :
    nativeXiBlock S (fun s => c*F s) (by fun_prop) n = c • nativeXiBlock S F hF n := by
  apply BoundedContinuousFunction.ext
  intro x
  cases n with
  | zero => exact nativeXiContour_const_mul F _ _ c x
  | succ n =>
      simp only [nativeXiBlock, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.smul_apply, smul_eq_mul, nativeXiContourBCF_apply,
        nativeXiContour_const_mul]
      ring

theorem nativeGaussianSource_sub (S : DeningerMeyerXiContourSchedule)
    (g h : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    nativeGaussianSource S (g-h) ε hε = nativeGaussianSource S g ε hε-nativeGaussianSource S h ε hε := by
  have he : deningerGaussianMellinRegularization ε
      (deningerMeyerStrongLogMellin (g-h : DeningerMeyerStrongLogTarget)) =
      fun s => deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g) s-
        deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin h) s := by
    funext s
    change exp ((ε:ℂ)*s^2)*(deningerMeyerStrongLogMellinLM s (g-h)) =
      exp ((ε:ℂ)*s^2)*(deningerMeyerStrongLogMellinLM s g)-
        exp ((ε:ℂ)*s^2)*(deningerMeyerStrongLogMellinLM s h)
    rw [map_sub, mul_sub]
  unfold nativeGaussianSource
  simp only [he, nativeXiBlock_sub S
    (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable
    (deningerMeyerStrongLogMellin_gaussianRegular h hε).differentiable]
  exact (gaussian_nativeXiBlock_summable S g hε).tsum_sub (gaussian_nativeXiBlock_summable S h hε)

theorem nativeGaussianSource_smul (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) (c : ℂ) :
    nativeGaussianSource S (c • g) ε hε = c • nativeGaussianSource S g ε hε := by
  have he : deningerGaussianMellinRegularization ε
      (deningerMeyerStrongLogMellin (c • g : DeningerMeyerStrongLogTarget)) =
      fun s => c*deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g) s := by
    funext s
    change exp ((ε:ℂ)*s^2)*(deningerMeyerStrongLogMellinLM s (c • g)) =
      c*(exp ((ε:ℂ)*s^2)*(deningerMeyerStrongLogMellinLM s g))
    rw [map_smul, smul_eq_mul]
    ring
  unfold nativeGaussianSource
  simp only [he, nativeXiBlock_const_mul S
    (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable c]
  exact (gaussian_nativeXiBlock_summable S g hε).tsum_const_smul c

def nativeGaussianSourceLM (S : DeningerMeyerXiContourSchedule) (ε : ℝ) (hε : 0 < ε) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] NativeContinuousSpace where
  toFun g := nativeGaussianSource S g ε hε
  map_add' g h := by
    have he := nativeGaussianSource_sub S (g+h) h hε
    rw [add_sub_cancel_right] at he
    exact sub_eq_iff_eq_add.mp he.symm
  map_smul' c g := nativeGaussianSource_smul S g hε c

def nativeGaussianClassMap (S : DeningerMeyerXiContourSchedule) (ε : ℝ) (hε : 0 < ε) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] NativeContinuousSpace :=
  (LinearMap.range deningerMeyerStrongLogSumLM).liftQ (nativeGaussianSourceLM S ε hε) (by
    rintro _ ⟨f, rfl⟩
    change nativeGaussianSource S (deningerMeyerStrongLogSumLM f) ε hε = 0
    apply (nativeGaussianSource_eq_zero_iff S _ hε).mpr
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr ⟨f, rfl⟩)

@[simp] theorem nativeGaussianClassMap_mk (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) (g : DeningerMeyerStrongLogTarget) :
    nativeGaussianClassMap S ε hε (Submodule.Quotient.mk g) = nativeGaussianSource S g ε hε := rfl

theorem nativeGaussianClassMap_injective (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) : Function.Injective (nativeGaussianClassMap S ε hε) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨g, rfl⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM)) q
  change nativeGaussianSource S g ε hε = 0 at hq
  change (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0
  exact (nativeGaussianSource_eq_zero_iff S g hε).mp hq

theorem nativeGaussianClassMap_control (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) (q : DeningerMeyerStrongLogCohomology) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖nativeGaussianClassMap S ε hε q‖ ≤ C ∧
      ∀ x y, ‖nativeGaussianClassMap S ε hε q y-nativeGaussianClassMap S ε hε q x‖ ≤
        C*|stripCutControl (3/2) y-stripCutControl (3/2) x| := by
  obtain ⟨g, rfl⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM)) q
  obtain ⟨c, hc, hb⟩ := gaussian_nativeXiBlock_control S g hε
  refine ⟨∑' n, c n, tsum_nonneg (fun n => (hb n).1), ?_, ?_⟩
  · exact tsum_of_norm_bounded hc.hasSum (fun n => (hb n).2.1)
  · exact stripSeries_increment hc (fun n => (hb n).2.1) (fun n => (hb n).2.2)

theorem nativeGaussianClassMap_boundedVariation (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) (q : DeningerMeyerStrongLogCohomology) :
    BoundedVariationOn (nativeGaussianClassMap S ε hε q) univ := by
  obtain ⟨C, hC, _, hi⟩ := nativeGaussianClassMap_control S ε hε q
  exact boundedVariationOn_of_strip_control hC hi

end RHTower.PaperThetaEndpoint
