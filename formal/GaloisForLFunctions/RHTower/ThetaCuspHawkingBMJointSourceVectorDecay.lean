import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeDecay
import GaloisForLFunctions.HTGeometry.L2DominatedContinuity

/-! Genuine strong continuity and time decay of the original radial and spatial L² source vectors. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- A positive horizon exponent gives a square-integrable fixed radial majorant. -/
theorem horizonEnvelope_memLp (c : ℝ) (hc : c < 2) :
    MemLp (fun t : ℝ => Real.exp ((2-c)*t)) 2 radialMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := (integrableOn_exp_mul_Iic (by linarith : 0 < 2*(2-c)) 0).mono_set Iio_subset_Iic_self
  apply h.congr
  filter_upwards [] with t
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

/-- The actual radial time slice as a vector, with its original infinite-horizon measure. -/
def timeRadialSourceVector (s a : ℂ) (τ : ℝ) : Lp ℂ 2 radialMeasure :=
  (timeReducedCoefficient_memLp s a τ).toLp (timeReducedCoefficient s a τ)

theorem timeRadialSourceVector_ae (s a : ℂ) (τ : ℝ) :
    timeRadialSourceVector s a τ =ᵐ[radialMeasure] timeReducedCoefficient s a τ :=
  (timeReducedCoefficient_memLp s a τ).coeFn_toLp

/-- Quantitative Hilbert-space decay follows from the exact horizon cancellation. -/
theorem timeRadialSourceVector_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : c < 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ,
      ‖timeRadialSourceVector (physicalRate q branch) a τ‖ ≤ B*Real.exp (-c*τ) := by
  obtain ⟨C,hC,hb⟩ := timeReducedCoefficient_physical_bound q branch a c hc
  let E := (horizonEnvelope_memLp c hc).toLp (fun t : ℝ => Real.exp ((2-c)*t))
  refine ⟨C*‖E‖,mul_nonneg hC (norm_nonneg _),?_⟩
  intro τ
  have h : ‖timeRadialSourceVector (physicalRate q branch) a τ‖ ≤ C*Real.exp (-c*τ)*‖E‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [timeRadialSourceVector_ae (physicalRate q branch) a τ,
      (horizonEnvelope_memLp c hc).coeFn_toLp,ae_restrict_mem measurableSet_Iio] with t ht he ht₀
    rw [ht,he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact hb τ t ht₀
  nlinarith [Real.exp_pos (-c*τ)]

/-- The native source depends jointly continuously on static time and tortoise position. -/
theorem timeReducedCoefficient_joint_continuous (s a : ℂ) :
    Continuous (fun p : ℝ × ℝ => timeReducedCoefficient s a p.1 p.2) := by
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hA : Continuous (sourceAmplitude s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (sourceAmplitude_hasDerivAt s 0 a 1 t).continuousAt)
  have hB : Continuous (radialLiftFirst s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (radialLiftFirst_hasDerivAt s 0 a 1 t).continuousAt)
  have hH : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnset_hasDerivAt (2*s) u).continuousAt)
  have hH' : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt (2*s) u).continuousAt)
  unfold timeReducedCoefficient reducedCoefficient reducedPolynomial liftSecondPolynomial amplitudeRate
  fun_prop

/-- Fixed-position source values retain ordinary continuity in static time. -/
theorem timeReducedCoefficient_time_continuous (s a : ℂ) (t : ℝ) :
    Continuous (fun τ : ℝ => timeReducedCoefficient s a τ t) := by
  have hH : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnset_hasDerivAt (2*s) u).continuousAt)
  have hH' : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt (2*s) u).continuousAt)
  exact (continuous_const.mul (hH.comp (continuous_id.add continuous_const))).add
    (continuous_const.mul (hH'.comp (continuous_id.add continuous_const)))

/-- Actual radial source vectors form one strongly continuous causal family. -/
theorem timeRadialSourceVector_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (timeRadialSourceVector (physicalRate q branch) a) := by
  obtain ⟨C,hC,hb⟩ := timeReducedCoefficient_physical_bound q branch a 0 (by norm_num)
  apply continuous_toLp_two_of_dominated radialMeasure _ (timeReducedCoefficient_memLp _ _)
    (fun t => C*Real.exp ((2-0)*t)) ((horizonEnvelope_memLp 0 (by norm_num)).const_mul C)
  · intro τ
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    simpa using hb τ t ht
  · filter_upwards [] with t
    change Continuous (fun τ : ℝ => timeReducedCoefficient (physicalRate q branch) a τ t)
    exact timeReducedCoefficient_time_continuous (physicalRate q branch) a t

/-- The spatial source is the original radial vector tensored with the actual angular remainder. -/
theorem timeCuspMainVector_separated (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ) :
    timeCuspMainVector q branch a τ = l2SeparatedProduct
      (timeRadialSourceVector (physicalRate q branch) a τ) (squareResidualVector q) := by
  apply Lp.ext
  filter_upwards [timeCuspMainVector_ae q branch a τ,l2SeparatedProduct_ae
    (timeRadialSourceVector (physicalRate q branch) a τ) (squareResidualVector q),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (timeRadialSourceVector_ae (physicalRate q branch) a τ),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (squareResidual_memLp q).coeFn_toLp] with p hp hl hr ha
  rw [hp,hl]
  change timeReducedCoefficient (physicalRate q branch) a τ p.1*squareResidual q (coordinates p.2) =
    timeRadialSourceVector (physicalRate q branch) a τ p.1*squareResidualVector q p.2
  exact congrArg₂ (fun x y : ℂ => x*y) hr.symm ha.symm

/-- Continuity is in the full original spatial Hilbert norm. -/
theorem timeCuspMainVector_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (timeCuspMainVector q branch a) := by
  simp only [funext (timeCuspMainVector_separated q branch a)]
  exact (l2SeparatedProductContinuousBilinear.flip (squareResidualVector q)).continuous.comp
    (timeRadialSourceVector_continuous q branch a)

/-- Every time exponent below two controls the actual joint source norm. -/
theorem timeCuspMainVector_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : c < 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, ‖timeCuspMainVector q branch a τ‖ ≤ B*Real.exp (-c*τ) := by
  obtain ⟨C,hC,hb⟩ := timeRadialSourceVector_bound q branch a c hc
  refine ⟨C*‖squareResidualVector q‖,mul_nonneg hC (norm_nonneg _),?_⟩
  intro τ
  rw [timeCuspMainVector_separated,l2SeparatedProduct_norm]
  calc
    _ ≤ (C*Real.exp (-c*τ))*‖squareResidualVector q‖ := mul_le_mul_of_nonneg_right (hb τ) (norm_nonneg _)
    _ = _ := by ring

end
end RHTower.D4BMJointSource
