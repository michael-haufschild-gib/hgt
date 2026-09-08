import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeLaplace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceResidualAssembly
import GaloisForLFunctions.RHTower.L2SeparatedProductDensity

/-! The actual delayed reduced source is admitted in the original joint spatial Hilbert space. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- Each actual time slice has a continuous radial coefficient. -/
theorem timeReducedCoefficient_continuous (s a : ℂ) (τ : ℝ) :
    Continuous (timeReducedCoefficient s a τ) := by
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hA : Continuous (sourceAmplitude s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (sourceAmplitude_hasDerivAt s 0 a 1 t).continuousAt)
  have hP : Continuous (fun t : ℝ => reducedPolynomial s 0 (radialUnit t)) := by
    unfold reducedPolynomial liftSecondPolynomial amplitudeRate
    fun_prop
  have hB : Continuous (radialLiftFirst s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (radialLiftFirst_hasDerivAt s 0 a 1 t).continuousAt)
  have hH : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnset_hasDerivAt (2*s) u).continuousAt)
  have hH' : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt (2*s) u).continuousAt)
  unfold timeReducedCoefficient reducedCoefficient
  exact ((hA.mul hP).mul (hH.comp (continuous_const.add continuous_id))).add
    ((continuous_const.mul hB).mul (hH'.comp (continuous_const.add continuous_id)))

/-- The delayed onset cuts every radial time slice to a finite interval before the original horizon. -/
theorem timeReducedCoefficient_memLp (s a : ℂ) (τ : ℝ) :
    MemLp (timeReducedCoefficient s a τ) 2 radialMeasure := by
  let b : ℝ := min (-τ) 0
  have hc := timeReducedCoefficient_continuous s a τ
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc b 0) hc.continuousOn
  have hm : MemLp (timeReducedCoefficient s a τ) 2 (volume.restrict (Icc b 0)) := by
    apply MemLp.of_bound hc.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hC t ht
  have hi : MemLp ((Icc b 0).indicator (timeReducedCoefficient s a τ)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr hm
  apply (hi.restrict (Iio (0:ℝ))).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  by_cases hb : t ∈ Icc b 0
  · exact indicator_of_mem hb _
  · rw [indicator_of_notMem hb]
    have htb : t < b := by
      by_contra h
      exact hb ⟨le_of_not_gt h,ht.le⟩
    have hneg : τ+t < 0 := by have := min_le_left (-τ) (0:ℝ); dsimp [b] at htb; linarith
    exact (timeReducedCoefficient_zero_before_onset s a τ t hneg).symm

/-- Actual time-dependent native square remainder; the three cutoff-principal response terms are separate. -/
def timeCuspMainForcing (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  timeReducedCoefficient (physicalRate q branch) a τ p.1*squareResidual q (coordinates p.2)

/-- Original joint L² admission holds for every time slice without a spatial integrability premise. -/
theorem timeCuspMainForcing_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ) :
    MemLp (timeCuspMainForcing q branch a τ) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  let f := timeReducedCoefficient (physicalRate q branch) a τ
  let g := fun z : UpperHalfPlane => squareResidual q (coordinates z)
  have hf : MemLp f 2 radialMeasure := timeReducedCoefficient_memLp _ _ τ
  have hg : MemLp g 2 D4BMModularCore.measure := squareResidual_memLp q
  apply (l2SeparatedFun_memLp (hf.toLp f) (hg.toLp g)).ae_eq
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.coeFn_toLp,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.coeFn_toLp] with p hp hq
  change hf.toLp f p.1*hg.toLp g p.2 = f p.1*g p.2
  exact congrArg₂ (fun x y : ℂ => x*y) hp hq

/-- The actual admitted time-source vector in the original spatial Hilbert space. -/
def timeCuspMainVector (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ) : SpatialSpace :=
  (timeCuspMainForcing_memLp q branch a τ).toLp (timeCuspMainForcing q branch a τ)

theorem timeCuspMainVector_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ) :
    timeCuspMainVector q branch a τ =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      timeCuspMainForcing q branch a τ :=
  (timeCuspMainForcing_memLp q branch a τ).coeFn_toLp

/-- The source vector itself vanishes before static time zero in the actual spatial quotient. -/
theorem timeCuspMainVector_zero_before_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ : ℝ) (hτ : τ ≤ 0) : timeCuspMainVector q branch a τ = 0 := by
  apply Lp.ext
  have ht : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.1 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_fst measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    exact Eventually.of_forall (fun _ => ht)
  filter_upwards [timeCuspMainVector_ae q branch a τ,ht,Lp.coeFn_zero (ℂ) 2
    (radialMeasure.prod D4BMModularCore.measure)] with p hp ht hz
  simp only [Pi.zero_apply] at hz
  rw [hp,hz,timeCuspMainForcing,timeReducedCoefficient_zero_before_onset _ _ _ _ (by linarith),zero_mul]

/-- Every original spatial point has an absolutely convergent native time-source transform. -/
theorem timeCuspMainForcing_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : (2*physicalRate q branch).re < w.re) (p : ℝ × UpperHalfPlane) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeCuspMainForcing q branch a τ p) (Ioi 0) := by
  apply ((timeReducedCoefficient_integrable (physicalRate q branch) a w hw p.1).mul_const
    (squareResidual q (coordinates p.2))).congr
  filter_upwards [] with τ
  simp only [timeCuspMainForcing,mul_assoc]

/-- The native time source transforms into exactly the square-remainder channel of the
admitted original frequency residual. The cutoff-principal channels remain separate. -/
theorem timeCuspMainForcing_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : (2*physicalRate q branch).re < w.re) (p : ℝ × UpperHalfPlane) (hp : p.1 ≤ 0) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeCuspMainForcing q branch a τ p) =
      reducedCoefficient (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w) p.1*
        squareResidual q (coordinates p.2) := by
  simp only [timeCuspMainForcing,← mul_assoc]
  rw [integral_mul_const,timeReducedCoefficient_laplace (physicalRate q branch) a w hw p.1 hp]

end
end RHTower.D4BMJointSource
