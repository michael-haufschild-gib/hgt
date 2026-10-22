import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceOnsetDerivativeBound
import GaloisForLFunctions.HTGeometry.L2DominatedDerivative
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceVectorDecay

/-! Norm differentiation of the literal radial forcing on its infinite horizon. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def timeReducedFirst (s a : ℂ) (τ t : ℝ) : ℂ :=
  reducedCoefficient s 0 a 1 t*timeOnsetFirst (2*s) (τ+t)+
    2*radialLiftFirst s 0 a 1 t*timeOnsetSecond (2*s) (τ+t)

/-- Both differentiated onset terms occur in the literal source derivative. -/
theorem timeReducedCoefficient_hasDerivAt (s a : ℂ) (τ t : ℝ) :
    HasDerivAt (fun r => timeReducedCoefficient s a r t) (timeReducedFirst s a τ t) τ := by
  have h₁ := (timeOnset_hasDerivAt (2*s) (τ+t)).scomp τ ((hasDerivAt_id τ).add_const t)
  have h₂ := (timeOnsetFirst_hasDerivAt (2*s) (τ+t)).scomp τ ((hasDerivAt_id τ).add_const t)
  convert (h₁.const_mul (reducedCoefficient s 0 a 1 t)).add
    (h₂.const_mul (2*radialLiftFirst s 0 a 1 t)) using 1 <;> first | rfl | simp [timeReducedFirst]

theorem timeReducedFirst_joint_continuous (s a : ℂ) :
    Continuous (fun p : ℝ × ℝ => timeReducedFirst s a p.1 p.2) := by
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hA : Continuous (sourceAmplitude s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (sourceAmplitude_hasDerivAt s 0 a 1 t).continuousAt)
  have hB : Continuous (radialLiftFirst s 0 a 1) := continuous_iff_continuousAt.mpr
    (fun t => (radialLiftFirst_hasDerivAt s 0 a 1 t).continuousAt)
  have hH : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt (2*s) u).continuousAt)
  have hH' := timeOnsetSecond_continuous (2*s)
  unfold timeReducedFirst reducedCoefficient reducedPolynomial liftSecondPolynomial amplitudeRate
  fun_prop

/-- The differentiated literal source retains both its original-time decay and
its two-power ingoing cancellation.  This is the exact majorant needed for
differentiating a future-delay convolution. -/
theorem timeReducedFirst_decay_bound (s a : ℂ) (c : ℝ)
    (hc : (2*s).re ≤ -c) (hc0 : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ t : ℝ, t < 0 →
      ‖timeReducedFirst s a τ t‖ ≤
        C*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
  obtain ⟨C₀,h₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (sourceHorizonProfile_continuousOn s a 0)
  obtain ⟨C₁,h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (sourceHorizonProfile_continuousOn s a 1)
  obtain ⟨B,hB,hb⟩ := timeOnset_derivative_pair_decay (2*s) c hc hc0
  let D := max (max C₀ C₁) 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D*B,mul_nonneg hD hB,fun τ t ht => ?_⟩
  have hu : radialUnit t ∈ Icc (0:ℝ) 1 :=
    ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩
  have hb₀ : ‖sourceHorizonProfile s a 0 (radialUnit t)‖ ≤ D :=
    (h₀ _ hu).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hb₁ : ‖sourceHorizonProfile s a 1 (radialUnit t)‖ ≤ D :=
    (h₁ _ hu).trans ((le_max_right _ _).trans (le_max_left _ _))
  have he : Real.exp (2*t)*Real.exp (-c*(τ+t)) =
      Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold timeReducedFirst
  rw [reducedCoefficient_horizon,radialLiftFirst_horizon]
  calc
    _ ≤ ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 0 (radialUnit t)*
        timeOnsetFirst (2*s) (τ+t)‖+
        ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 1 (radialUnit t)*
          timeOnsetSecond (2*s) (τ+t)‖ := norm_add_le _ _
    _ = Real.exp (2*t)*(‖sourceHorizonProfile s a 0 (radialUnit t)‖*
          ‖timeOnsetFirst (2*s) (τ+t)‖+
        ‖sourceHorizonProfile s a 1 (radialUnit t)‖*
          ‖timeOnsetSecond (2*s) (τ+t)‖) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ Real.exp (2*t)*(D*(‖timeOnsetFirst (2*s) (τ+t)‖+
        ‖timeOnsetSecond (2*s) (τ+t)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      nlinarith [norm_nonneg (timeOnsetFirst (2*s) (τ+t)),
        norm_nonneg (timeOnsetSecond (2*s) (τ+t))]
    _ ≤ Real.exp (2*t)*(D*(B*Real.exp (-c*(τ+t)))) := by
      gcongr
      exact hb (τ+t)
    _ = D*B*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
      calc
        _ = D*B*(Real.exp (2*t)*Real.exp (-c*(τ+t))) := by ring
        _ = _ := by rw [he]; ring

/-- The physical rate lies in every time-decay chamber required by the future
source integral. -/
theorem timeReducedFirst_physical_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ t : ℝ, t < 0 →
      ‖timeReducedFirst (physicalRate q branch) a τ t‖ ≤
        C*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
  apply timeReducedFirst_decay_bound
  have h := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at h
  linarith
  exact hc0

/-- The differentiated source retains the full two-power horizon cancellation uniformly in time. -/
theorem timeReducedFirst_bound (s a : ℂ) (hs : (2*s).re ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ t : ℝ, t < 0 → ‖timeReducedFirst s a τ t‖ ≤ C*Real.exp (2*t) := by
  obtain ⟨C₀,h₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (sourceHorizonProfile_continuousOn s a 0)
  obtain ⟨C₁,h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (sourceHorizonProfile_continuousOn s a 1)
  obtain ⟨B,hB,hb⟩ := timeOnset_derivative_pair_bound (2*s) hs
  let D := max (max C₀ C₁) 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D*B,mul_nonneg hD hB,fun τ t ht => ?_⟩
  have hu : radialUnit t ∈ Icc (0:ℝ) 1 :=
    ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩
  have hb₀ : ‖sourceHorizonProfile s a 0 (radialUnit t)‖ ≤ D :=
    (h₀ _ hu).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hb₁ : ‖sourceHorizonProfile s a 1 (radialUnit t)‖ ≤ D :=
    (h₁ _ hu).trans ((le_max_right _ _).trans (le_max_left _ _))
  unfold timeReducedFirst
  rw [reducedCoefficient_horizon,radialLiftFirst_horizon]
  calc
    _ ≤ ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 0 (radialUnit t)*timeOnsetFirst (2*s) (τ+t)‖+
        ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 1 (radialUnit t)*timeOnsetSecond (2*s) (τ+t)‖ := norm_add_le _ _
    _ = Real.exp (2*t)*(‖sourceHorizonProfile s a 0 (radialUnit t)‖*‖timeOnsetFirst (2*s) (τ+t)‖+
        ‖sourceHorizonProfile s a 1 (radialUnit t)‖*‖timeOnsetSecond (2*s) (τ+t)‖) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ Real.exp (2*t)*(D*(‖timeOnsetFirst (2*s) (τ+t)‖+‖timeOnsetSecond (2*s) (τ+t)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      nlinarith [norm_nonneg (timeOnsetFirst (2*s) (τ+t)),norm_nonneg (timeOnsetSecond (2*s) (τ+t))]
    _ ≤ Real.exp (2*t)*(D*B) := by gcongr; exact hb (τ+t)
    _ = _ := by ring

/-- The actual source derivative is square integrable without cutting off the horizon. -/
theorem timeReducedFirst_memLp (s a : ℂ) (hs : (2*s).re ≤ 0) (τ : ℝ) :
    MemLp (timeReducedFirst s a τ) 2 radialMeasure := by
  obtain ⟨C,hC,hb⟩ := timeReducedFirst_bound s a hs
  have hE : MemLp (fun t : ℝ => C*Real.exp (2*t)) 2 radialMeasure := by
    simpa using (horizonEnvelope_memLp 0 (by norm_num)).const_mul C
  apply hE.mono' ((timeReducedFirst_joint_continuous s a).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  exact hb τ t ht

def timeRadialSourceFirst (s a : ℂ) (hs : (2*s).re ≤ 0) (τ : ℝ) : Lp ℂ 2 radialMeasure :=
  (timeReducedFirst_memLp s a hs τ).toLp (timeReducedFirst s a τ)

/-- Differentiation holds in the original Hilbert norm, not only at fixed radial positions. -/
theorem timeRadialSourceVector_hasDerivAt (s a : ℂ) (hs : (2*s).re ≤ 0) (τ : ℝ) :
    HasDerivAt (timeRadialSourceVector s a) (timeRadialSourceFirst s a hs τ) τ := by
  obtain ⟨C,hC,hb⟩ := timeReducedFirst_bound s a hs
  apply hasDerivAt_toLp_two_of_dominated radialMeasure _ _ (timeReducedCoefficient_memLp s a)
    (timeReducedFirst_memLp s a hs) (fun t => C*Real.exp ((2-0)*t))
    ((horizonEnvelope_memLp 0 (by norm_num)).const_mul C)
  · exact Eventually.of_forall (fun t r => timeReducedCoefficient_hasDerivAt s a r t)
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    intro r
    simpa using hb r t ht

/-- The differentiated native forcing is strongly continuous through the onset. -/
theorem timeRadialSourceFirst_continuous (s a : ℂ) (hs : (2*s).re ≤ 0) :
    Continuous (timeRadialSourceFirst s a hs) := by
  obtain ⟨C,hC,hb⟩ := timeReducedFirst_bound s a hs
  apply continuous_toLp_two_of_dominated radialMeasure _ (timeReducedFirst_memLp s a hs)
    (fun t => C*Real.exp ((2-0)*t)) ((horizonEnvelope_memLp 0 (by norm_num)).const_mul C)
  · intro τ
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    simpa using hb τ t ht
  · filter_upwards [] with t
    change Continuous (fun τ : ℝ => timeReducedFirst s a τ t)
    have hH : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
      (fun u => (timeOnsetFirst_hasDerivAt (2*s) u).continuousAt)
    have hH' := timeOnsetSecond_continuous (2*s)
    exact (continuous_const.mul (hH.comp (continuous_id.add continuous_const))).add
      (continuous_const.mul (hH'.comp (continuous_id.add continuous_const)))

end
end RHTower.D4BMJointSource
