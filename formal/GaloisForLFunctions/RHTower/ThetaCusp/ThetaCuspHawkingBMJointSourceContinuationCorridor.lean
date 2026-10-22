import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceCompleteL2Meromorphy

/-! The genuine source germ reaches an original Green convergence chamber along an explicit band corridor. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMLaplaceRadial
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual continued L² class is exactly the original complete source vector in its Green chamber. -/
theorem continuedCuspResidualL2_eq_original (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hc : PrincipalChamber q w) :
    continuedCuspResidualL2 q branch a w =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w) hc := by
  have hr := principalChamber_re_pos hc
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  have he : continuedCuspResidualForcing q branch w a =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      cuspResidualForcing q branch w a (onsetTransform (2*physicalRate q branch) w) := by
    have ht : ∀ᵐ t ∂radialMeasure, t < 0 := ae_restrict_mem measurableSet_Iio
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with p hp
    exact continuedCuspResidualForcing_eq_original q branch w a hw (by linarith) (by linarith) p.1 hp p.2
  unfold continuedCuspResidualL2
  rw [l2Family_congr_ae _ _ (fun _ => cuspResidualForcing q branch w a
    (onsetTransform (2*physicalRate q branch) w)) w he]
  exact l2Family_eq_toLp _ _ _ (cuspResidualForcing_memLp q branch w a _ hc)

/-- The exact three Xi principal frequencies all admit a common source chamber inside the continuation band. -/
theorem principalFrequency_abs_im_lt_three_halves (q : XiZeroCopy) (i : Fin 3) :
    |(principalFrequency q i).im| < 3/2 := by
  have hx := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hx
  norm_num [xiSpectralPoint] at hx
  fin_cases i <;> norm_num [principalFrequency,principalExponent]
  all_goals rw [abs_lt]; constructor <;> linarith [hx.1,hx.2]

/-- Every point of the continued band is joined to an original source chamber by one explicit
continuous frequency corridor on which the full original source remains genuinely L²-meromorphic. -/
theorem continuedCuspResidualL2_original_corridor (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ γ 0 = w ∧ PrincipalChamber q (γ 1) ∧
      (∀ r ∈ Icc (0:ℝ) 1, (γ r).im ≠ 0 ∧ |(γ r).re| < 2 ∧
        MeromorphicAt (continuedCuspResidualL2 q branch a) (γ r)) := by
  let γ : ℝ → ℂ := fun r => w+((r*(7/4-w.re):ℝ):ℂ)
  have hγ (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : (γ r).im ≠ 0 ∧ |(γ r).re| < 2 := by
    have hs := abs_lt.mp hwr
    have hlo := mul_nonneg (sub_nonneg.mpr hr.2) (le_of_lt (show 0 < w.re+2 by linarith))
    have hhi := mul_nonneg (sub_nonneg.mpr hr.2) (le_of_lt (show 0 < 2-w.re by linarith))
    have hμ : (γ r).im = w.im := by simp [γ]
    have hρ : (γ r).re = w.re+r*(7/4-w.re) := by simp [γ]
    refine ⟨by rwa [hμ],?_⟩
    rw [hρ,abs_lt]
    constructor <;> nlinarith [hr.1,hr.2]
  refine ⟨γ,by dsimp [γ]; fun_prop,by simp [γ],?_,fun r hr =>
    ⟨(hγ r hr).1,(hγ r hr).2,continuedCuspResidualL2_meromorphicAt q branch _ a (hγ r hr).1 (hγ r hr).2⟩⟩
  intro i
  change |(principalFrequency q i).im| < (γ 1).re
  have he : (γ 1).re = 7/4 := by simp [γ]
  rw [he]
  linarith [principalFrequency_abs_im_lt_three_halves q i]

/-- The actual norm-valued source germ and the exact original field equation hold together on the whole band. -/
theorem continuedOriginalSource_meromorphic_admitted_germ (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MeromorphicAt (continuedCuspResidualL2 q branch a) w ∧
    ∀ᶠ u in 𝓝[≠] w,
      MemLp (continuedCuspResidualForcing q branch u a) 2 (radialMeasure.prod D4BMModularCore.measure) ∧
      ∀ t < 0, ∀ z : UpperHalfPlane,
        originalForcing (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u)
            (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t =
          fieldWave u (continuedExplicitField q branch u a) t (coordinates z)+
            continuedCuspResidualForcing q branch u a (t,z) := by
  refine ⟨continuedCuspResidualL2_meromorphicAt q branch w a hw hwr,?_⟩
  have hn : ∀ᶠ u in 𝓝[≠] w, u.im ≠ 0 ∧ |u.re| < 2 :=
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,originalForcing_continuedField_germ q branch w a hw (abs_lt.mp hwr).1] with u hu he
  exact ⟨continuedCuspResidualForcing_band_memLp q branch u a hu.1 hu.2,he⟩

/-- Every fundamental Xi QNM has the full source meromorphic in the actual joint L² norm,
together with admission and the original field equation on one common punctured germ. -/
theorem continuedOriginalSource_allXi_fundamental_meromorphic_germ (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
    MeromorphicAt (continuedCuspResidualL2 q branch a) w ∧
    ∀ᶠ u in 𝓝[≠] w,
      MemLp (continuedCuspResidualForcing q branch u a) 2
        (radialMeasure.prod D4BMModularCore.measure) ∧
      ∀ t < 0, ∀ z : UpperHalfPlane,
        originalForcing (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u)
            (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t =
          fieldWave u (continuedExplicitField q branch u a) t (coordinates z)+
            continuedCuspResidualForcing q branch u a (t,z) := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  intro w hw
  have hstrip : w.im ≠ 0 ∧ |w.re| < 2 := by
    simp only [mem_insert_iff,mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
        Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
    all_goals norm_num
    · exact ⟨hq,abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩⟩
    · exact ⟨hq,abs_lt.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩⟩
  exact continuedOriginalSource_meromorphic_admitted_germ q branch w a hstrip.1 hstrip.2


end
end RHTower.D4BMJointSource
