import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedGreenNumerator
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedUniformBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-! Uniform control of the original cleared reduced response at independent angular frequency. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual first jet retains the same two source moments and gradient lift. -/
def clearedReducedGreenFirst (w chi s a : ℂ) (t : ℝ) : ℂ :=
  let K := reducedGreenGradient chi s 1
  let b := horizonCoordinate t
  (coordinateFirst t:ℂ)*(normalizableFirst w chi b*firstEndpointMellin (horizonMellinCore s chi a 1 K) b w+
    horizonFirst w chi b*(∫ r in Ioc b (1:ℝ), normalizable w chi r*sourceProfile s w a 1 K 1 r))*clearedOnset s w+
      connection w chi*radialLiftFirst s w a (clearedOnset s w) t

private theorem clear_jet_scalar (p c d n h m o e l : ℂ) (hp : p ≠ 0) (hc : c ≠ 0) :
    d*(n*m+h*o)*(1+p*e)+c*l*(1+p*e) =
      -(p*c)*(d*(n*(m*(1/p+e)/(-c))+h*(o*(1/p+e)/(-c)))-l*(1/p+e)) := by
  field_simp [hp,hc]
  ring

theorem clearedReducedGreenFirst_eq (w chi s a : ℂ) (hs : w-2*s ≠ 0)
    (hc : connection w chi ≠ 0) (t : ℝ) :
    clearedReducedGreenFirst w chi s a t =
      reducedGreenClearingFactor w chi s*continuedReducedGreenFirst w chi s a 1 t := by
  have he := clear_jet_scalar (w-2*s) (connection w chi) (coordinateFirst t)
    (normalizableFirst w chi (horizonCoordinate t)) (horizonFirst w chi (horizonCoordinate t))
    (firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) (horizonCoordinate t) w)
    (∫ r in Ioc (horizonCoordinate t) (1:ℝ), normalizable w chi r*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 r)
    (onsetCorrection (2*s) w) (radialLiftFirst s w a 1 t) hs hc
  dsimp only [clearedReducedGreenFirst,reducedGreenClearingFactor,continuedReducedGreenFirst,
    continuedTortoiseGreenFirst,continuedResponseFirst,continuedHorizonMoment,continuedOuterMoment,
    radialLiftFirst,sourceAmplitude,clearedOnset,continuedOnset] at he ⊢
  linear_combination he

/-- The first spatial numerator jet is analytic, including at the source and connection zeros. -/
theorem clearedReducedGreenFirst_analyticAt (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun u => clearedReducedGreenFirst u chi s a t) w := by
  let K := reducedGreenGradient chi s 1
  have hb := horizonCoordinate_interior t ht
  have hM := horizonFirstMellin_analyticAt s chi a 1 K w hw hwr hb.1 hb.2
  have hO := (outerSourceIntegral_entire s chi a 1 K hb.1 hb.2).analyticAt w
  have hS := (clearedOnset_entire s).analyticAt w
  have hC := connection_frequency_analyticAt w chi hw
  have hL : AnalyticAt ℂ (fun u => radialLiftFirst s u a (clearedOnset s u) t) w := by
    unfold radialLiftFirst sourceAmplitude liftFirstPolynomial amplitudeRate
    fun_prop
  exact ((analyticAt_const.mul ((((normalizableFirst_frequency_entire chi hb).analyticAt w).mul hM).add
    ((horizonFirst_frequency_analyticAt w chi hw hb).mul hO))).mul hS).add (hC.mul hL)

/-- Original reduced forcing with the same denominator cleared as the response. -/
def clearedReducedForcing (w chi s a : ℂ) (t : ℝ) : ℂ :=
  -connection w chi*reducedCoefficient s w a (clearedOnset s w) t

private theorem clear_forcing_scalar (p c e x : ℂ) (hp : p ≠ 0) :
    -c*(x*(1+p*e)) = -(p*c)*(x*(1/p+e)) := by
  field_simp [hp]

theorem clearedReducedForcing_eq (w chi s a : ℂ) (hs : w-2*s ≠ 0) (t : ℝ) :
    clearedReducedForcing w chi s a t =
      reducedGreenClearingFactor w chi s*reducedCoefficient s w a (continuedOnset s w) t := by
  have he := clear_forcing_scalar (w-2*s) (connection w chi) (onsetCorrection (2*s) w)
    (reducedCoefficient s w a 1 t) hs
  dsimp only [clearedReducedForcing,reducedGreenClearingFactor,reducedCoefficient,
    sourceAmplitude,clearedOnset,continuedOnset] at he ⊢
  linear_combination he

/-- The actual cleared jets solve the original reduced-source ODE away from its denominator zeros. -/
theorem clearedReducedGreen_hasDerivAt (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (hs : w-2*s ≠ 0) (hc : connection w chi ≠ 0) (t : ℝ) (ht : t < 0) :
    HasDerivAt (clearedReducedGreen w chi s a) (clearedReducedGreenFirst w chi s a t) t ∧
      HasDerivAt (clearedReducedGreenFirst w chi s a)
        (w^(2 : ℕ)*clearedReducedGreen w chi s a t+
          (horizonCoordinate t:ℂ)*(1/4+chi^(2 : ℕ))*clearedReducedGreen w chi s a t-
          clearedReducedForcing w chi s a t) t := by
  have hU : clearedReducedGreen w chi s a =
      fun r => reducedGreenClearingFactor w chi s*continuedReducedGreen w chi s a 1 r :=
    funext (clearedReducedGreen_eq w chi s a hs hc)
  have hV : clearedReducedGreenFirst w chi s a =
      fun r => reducedGreenClearingFactor w chi s*continuedReducedGreenFirst w chi s a 1 r :=
    funext (clearedReducedGreenFirst_eq w chi s a hs hc)
  rw [hU,hV]
  have hd := continuedReducedGreen_hasDerivAt w chi s a 1 hw hwr t ht
  refine ⟨hd.1.const_mul _,?_⟩
  have he := continuedReducedGreen_equation w chi s a 1 hw hwr hc t ht
  apply (hd.2.const_mul (reducedGreenClearingFactor w chi s)).congr_deriv
  rw [clearedReducedForcing_eq w chi s a hs t]
  linear_combination -(reducedGreenClearingFactor w chi s)*he

/-- Every compact nonreal frequency family has one bound on the complete cleared reduced response. -/
theorem clearedReducedGreen_compact_bound (chi s a : ℂ) (Ω : Set ℂ) (hΩ : IsCompact Ω)
    (hstrip : ∀ w ∈ Ω, w.im ≠ 0 ∧ -2 < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ interior Ω, ∀ t < 0,
      ‖clearedReducedGreen w chi s a t‖ ≤ C*Real.exp (-|w.re| *t) := by
  let U (w : ℂ) := clearedReducedGreen w chi s a
  let V (w : ℂ) := clearedReducedGreenFirst w chi s a
  let A : ℝ := 4*‖(1/4:ℂ)+chi^(2 : ℕ)‖
  obtain ⟨B,hB,hf0⟩ := reducedCoefficient_family_norm_le_exp s a 1 (clearedOnset s)
    (fun w => -connection w chi) Ω hΩ (clearedOnset_entire s).continuous.continuousOn
    (fun w hw => (connection_frequency_analyticAt w chi (hstrip w hw).1).continuousAt.neg.continuousWithinAt)
  have hf (w : ℂ) (hw : w ∈ Ω) (t : ℝ) (ht : t < 0) :
      ‖clearedReducedForcing w chi s a t‖ ≤ B*Real.exp ((w.re+2)*t) := by
    simpa only [clearedReducedForcing,mul_one] using hf0 w hw t ht
  have hp (t : ℝ) (ht : t < 0) :
      ‖(horizonCoordinate t:ℂ)*((1/4:ℂ)+chi^(2 : ℕ))‖ ≤ A*Real.exp (2*t) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (horizonCoordinate_norm_le_exp t ht) (norm_nonneg _)).trans_eq (by ring)
  let D (w : ℂ) := symmetricHorizonGrowthCoefficient w (U w (-1)) (V w (-1)) A B
  have hD : ContinuousOn D Ω := by
    intro w hw
    have h := hstrip w hw
    have hu := clearedReducedGreen_analyticAt w chi s a h.1 h.2 (-1) (by norm_num)
    have hv := clearedReducedGreenFirst_analyticAt w chi s a h.1 h.2 (-1) (by norm_num)
    have hw0 : w ≠ 0 := by intro he; apply h.1; simp [he]
    exact ((symmetricHorizonGrowthCoefficient_continuousAt w (U w (-1)) (V w (-1)) A B hw0).comp_of_eq
      (continuousAt_id.prodMk (hu.continuousAt.prodMk (hv.continuousAt.prodMk
        (continuousAt_const.prodMk continuousAt_const)))) rfl).continuousWithinAt
  obtain ⟨C,hC⟩ := hΩ.exists_bound_of_continuousOn hD
  have hregular (w : ℂ) (hw : w ∈ Ω) (hs : w-2*s ≠ 0) (hc : connection w chi ≠ 0)
      (t : ℝ) (ht : t < 0) : ‖U w t‖ ≤ max C 0*Real.exp (-|w.re| *t) := by
    have h := hstrip w hw
    have hw0 : w ≠ 0 := by intro he; apply h.1; simp [he]
    have hd (r : ℝ) (hr : r < 0) := clearedReducedGreen_hasDerivAt w chi s a h.1 h.2 hs hc r hr
    have hbound := forcedSecondOrder_horizon_bound_symmetric w hw0 (U w) (V w)
      (fun r => (horizonCoordinate r:ℂ)*(1/4+chi^(2 : ℕ))) (clearedReducedForcing w chi s a) A B
      (by dsimp [A]; positivity) hB (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2) hp (hf w hw) t ht
    exact hbound.trans (mul_le_mul_of_nonneg_right ((le_abs_self (D w)).trans
      ((show |D w| ≤ C from hC w hw).trans (le_max_left _ _))) (Real.exp_pos _).le)
  refine ⟨max C 0,le_max_right _ _,fun w hw t ht => ?_⟩
  have h := hstrip w (interior_subset hw)
  have hlim := (clearedReducedGreen_analyticAt w chi s a h.1 h.2 t ht).continuousAt.norm
  have hlim' : ContinuousAt (fun u : ℂ => max C 0*Real.exp (-|u.re| *t)) w := by fun_prop
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] w)
    (hlim.mono_left nhdsWithin_le_nhds) (hlim'.mono_left nhdsWithin_le_nhds)
  have hmem0 : ∀ᶠ u in 𝓝 w, u ∈ Ω :=
    mem_of_superset (isOpen_interior.mem_nhds hw) interior_subset
  have hmem : ∀ᶠ u in 𝓝[≠] w, u ∈ Ω := hmem0.filter_mono nhdsWithin_le_nhds
  have hs : ∀ᶠ u in 𝓝[≠] w, u-2*s ≠ 0 := by
    by_cases he : w=2*s
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_ne_zero.mpr (by simpa [← he] using hu)
    · exact ((continuous_id.sub continuous_const).continuousAt.eventually_ne (sub_ne_zero.mpr he)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hmem,hs,connection_eventually_ne_zero w chi h.1] with u hu hsu hcu
  exact hregular u hu hsu hcu t ht


/-- One constant controls the complete numerator on a frequency neighborhood and a finite outer interval. -/
theorem clearedReducedGreen_outer_uniform_bound (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ u ∈ ball w R, ∀ t ∈ Ico T (0:ℝ),
      ‖clearedReducedGreen u chi s a t‖ ≤ C := by
  have hi : ∀ᶠ u : ℂ in 𝓝 w, u.im ≠ 0 := Complex.continuous_im.continuousAt.eventually_ne hw
  have hr : ∀ᶠ u : ℂ in 𝓝 w, -2 < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr
  have hb : ∀ᶠ u : ℂ in 𝓝 w, u ∈ ball w 1 := ball_mem_nhds w (by norm_num)
  obtain ⟨r,hr0,hrall⟩ := Metric.eventually_nhds_iff.mp (hi.and (hr.and hb))
  let R := r/2
  have hR : 0 < R := half_pos hr0
  have hRr : R < r := half_lt_self hr0
  have hstrip : ∀ u ∈ closedBall w R, u.im ≠ 0 ∧ -2 < u.re := by
    intro u hu
    have h := hrall ((mem_closedBall.mp hu).trans_lt hRr)
    exact ⟨h.1,h.2.1⟩
  obtain ⟨C,hC,hbound⟩ := clearedReducedGreen_compact_bound chi s a (closedBall w R)
    (isCompact_closedBall w R) hstrip
  refine ⟨R,C*Real.exp ((‖w‖+1)*|T|),hR,mul_nonneg hC (Real.exp_pos _).le,?_⟩
  intro u hu t ht
  have hui : u ∈ interior (closedBall w R) := ball_subset_interior_closedBall hu
  have hub := (hrall ((mem_ball.mp hu).trans hRr)).2.2
  have hun : |u.re| ≤ ‖w‖+1 := by
    have hn := norm_sub_norm_le u w
    have hd : ‖u-w‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hub
    exact (Complex.abs_re_le_norm u).trans (by linarith)
  have htT : -t ≤ |T| := (neg_le_neg ht.1).trans (neg_le_abs T)
  apply (hbound u hui t ht.2).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  calc
    -|u.re| *t = |u.re| *(-t) := by ring
    _ ≤ (‖w‖+1)*|T| := mul_le_mul hun htT (by linarith [ht.2]) (by positivity)

/-- Every actual physical fundamental frequency has a source-derived outer majorant, including at resonance. -/
theorem physicalClearedReducedGreen_outer_uniform_bound (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball (physicalFundamentalFrequency q side) R, ∀ t ∈ Ico T (0:ℝ),
        ‖clearedReducedGreen u (physicalRadialFrequency q) (physicalRate q branch) a t‖ ≤ C := by
  have hw := physicalFundamentalFrequency_strip q side
  exact clearedReducedGreen_outer_uniform_bound _ _ _ _ hw.1 (abs_lt.mp hw.2).1 T

end
end RHTower.D4BMJointSource
