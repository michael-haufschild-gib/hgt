import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuedAdmission

/-! The complete original source decomposition and actual joint L² admission on one QNM germ. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open Complex D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Throughout one punctured frequency neighborhood, the actual continued field solves the full
source equation modulo its complete, genuinely square-integrable residual. -/
theorem continuedOriginalSource_admitted_germ (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : w.re < 0) :
    ∀ᶠ u in 𝓝[≠] w,
      MemLp (continuedCuspResidualForcing q branch u a) 2
        (radialMeasure.prod D4BMModularCore.measure) ∧
      ∀ t < 0, ∀ z : UpperHalfPlane,
        originalForcing (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u)
            (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t =
          fieldWave u (continuedExplicitField q branch u a) t (coordinates z)+
            continuedCuspResidualForcing q branch u a (t,z) := by
  have hi : ∀ᶠ u in 𝓝[≠] w, u.im ≠ 0 :=
    (Complex.continuous_im.continuousAt.eventually_ne hw).filter_mono nhdsWithin_le_nhds
  have hr : ∀ᶠ u in 𝓝[≠] w, -2 < u.re :=
    (Complex.continuous_re.continuousAt.eventually_const_lt hwre).filter_mono nhdsWithin_le_nhds
  have hn : ∀ᶠ u in 𝓝[≠] w, u.re < 0 :=
    (Complex.continuous_re.continuousAt.eventually_lt_const hwr).filter_mono nhdsWithin_le_nhds
  filter_upwards [hi,hr,hn,originalForcing_continuedField_germ q branch w a hw hwre] with u hui hur hun he
  exact ⟨continuedCuspResidualForcing_memLp q branch u a hui hur hun.le,he⟩

/-- Every fundamental Xi QNM admits the complete continued original source on one common germ.
Neither source admission nor a nonresonance assumption is provided to this conclusion. -/
theorem continuedOriginalSource_allXi_fundamental_admitted_germ (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
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
  have hstrip : w.im ≠ 0 ∧ -2 < w.re ∧ w.re < 0 := by
    simp only [mem_insert_iff,mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
        Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
    all_goals norm_num
    · exact ⟨hq,by linarith [hs.1],by linarith [hs.2]⟩
    · exact ⟨hq,by linarith [hs.2],by linarith [hs.1]⟩
  exact continuedOriginalSource_admitted_germ q branch w a hstrip.1 hstrip.2.1 hstrip.2.2

end
end RHTower.D4BMJointSource
