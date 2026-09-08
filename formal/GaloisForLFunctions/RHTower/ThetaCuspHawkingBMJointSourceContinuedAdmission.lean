import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalHorizonBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuedFieldWave

/-! Admission of the complete continued native source at the actual fundamental Xi QNMs. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open Complex D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem exponential_bound_memLp {F : ℝ → ℂ} (hF : ContinuousOn F (Iio 0))
    (b C : ℝ) (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ t < 0, ‖F t‖ ≤ C*Real.exp (b*t)) : MemLp F 2 radialMeasure := by
  have hE := laplaceProfile_memLp (b:ℂ) (by simpa using hb) (fun _ => (C:ℂ)) continuousOn_const
  apply MemLp.of_le hE (hF.aestronglyMeasurable measurableSet_Iio)
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  have he : ‖Complex.exp ((b:ℂ)*(t:ℂ))*(C:ℂ)‖ = C*Real.exp (b*t) := by
    rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  rw [he]
  exact hbound t ht

/-- Every actual continued cutoff coefficient has two additional powers of horizon decay. -/
theorem continuedCutoffRadialCoefficient_norm_le_exp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : w.re ≤ 0) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0,
      ‖continuedCutoffRadialCoefficient q branch w a i t‖ ≤ C*Real.exp ((w.re+2)*t) := by
  obtain ⟨C,hC,hb⟩ := continuedPrincipalDifference_norm_le_exp q branch w a hw hwre hwr i
  refine ⟨4*C,by positivity,fun t ht => ?_⟩
  rw [continuedCutoffRadialCoefficient,norm_mul]
  calc
    _ ≤ (4*Real.exp (2*t))*(C*Real.exp (w.re*t)) :=
      mul_le_mul (horizonCoordinate_norm_le_exp t ht) (hb t ht) (norm_nonneg _) (by positivity)
    _ = (4*C)*(Real.exp (2*t)*Real.exp (w.re*t)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- The entire actual continued principal cutoff coefficient is square-integrable, including
its totalized values at connection zeros. No endpoint or admission premise is supplied. -/
theorem continuedCutoffRadialCoefficient_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : w.re ≤ 0) (i : Fin 3) :
    MemLp (continuedCutoffRadialCoefficient q branch w a i) 2 radialMeasure := by
  obtain ⟨C,hC,hb⟩ := continuedCutoffRadialCoefficient_norm_le_exp q branch w a hw hwre hwr i
  have hF : ContinuousOn (continuedCutoffRadialCoefficient q branch w a i) (Iio 0) := by
    intro t ht
    exact (((horizonCoordinate_hasDerivAt t).ofReal_comp).continuousAt.mul
      ((continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht).1.continuousAt)).continuousWithinAt
  exact exponential_bound_memLp hF (w.re+2) C (by linarith) hC hb

private theorem continued_separated_memLp {f : ℝ → ℂ} {g : UpperHalfPlane → ℂ}
    (hf : MemLp f 2 radialMeasure) (hg : MemLp g 2 D4BMModularCore.measure) :
    MemLp (fun p : ℝ × UpperHalfPlane => f p.1*g p.2) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × UpperHalfPlane => f p.1*g p.2)
      (radialMeasure.prod D4BMModularCore.measure) :=
    (hf.aestronglyMeasurable.aemeasurable.comp_fst.mul
      hg.aestronglyMeasurable.aemeasurable.comp_snd).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).mul_prod
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  simpa only [norm_mul,mul_pow] using hi

/-- Complete continued source admission: native squared-source remainder and all three original
cutoff commutators, throughout the nonreal negative-frequency strip. -/
theorem continuedCuspResidualForcing_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : w.re ≤ 0) :
    MemLp (continuedCuspResidualForcing q branch w a) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hmain := continued_separated_memLp
    (reducedCoefficient_memLp_horizon (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) hwre)
    (squareResidual_memLp q)
  have hsum := memLp_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    continued_separated_memLp (continuedCutoffRadialCoefficient_memLp q branch w a hw hwre hwr i)
      (cutoffCommutator_memLp (principalExponent q i)))
  exact hmain.add hsum

/-- Both fundamental QNMs of every Xi copy have the complete native forcing admitted in the
actual joint square-integrable space; no continuation, nonresonance, or admission hypothesis is supplied. -/
theorem continuedCuspResidualForcing_allXi_fundamental_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      MemLp (continuedCuspResidualForcing q branch w a) 2
        (radialMeasure.prod D4BMModularCore.measure) := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  intro w hw
  have hstrip : w.im ≠ 0 ∧ -2 < w.re ∧ w.re ≤ 0 := by
    simp only [mem_insert_iff,mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
        Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
    all_goals norm_num
    · exact ⟨hq,by linarith [hs.1],by linarith [hs.2]⟩
    · exact ⟨hq,by linarith [hs.2],by linarith [hs.1]⟩
  exact continuedCuspResidualForcing_memLp q branch w a hstrip.1 hstrip.2.1 hstrip.2.2

end
end RHTower.D4BMJointSource
