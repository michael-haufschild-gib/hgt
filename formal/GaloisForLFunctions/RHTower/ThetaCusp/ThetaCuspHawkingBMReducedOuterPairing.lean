import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenUniformBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedRadialAdmission
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalSlope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalGreenFactor

/-! Frequency analyticity of the original cleared reduced response paired with its outer mode. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology Metric MeasureTheory GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original normalizable family has a common bound through its outer endpoint. -/
theorem normalizable_outer_uniform_bound (w chi : ℂ) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ ball w 1, ∀ z ∈ Icc b (1:ℝ), ‖normalizable u chi z‖ ≤ C := by
  let P (p : ℂ × ℝ) : ℂ := power (p.1/2) p.2*power (1/2) (1-p.2)
  have hp : ContinuousOn (fun p : ℂ × ℝ => power (p.1/2) p.2) (closedBall w 1 ×ˢ Icc b (1:ℝ)) := by
    intro p hp
    have ht : 0 < p.2 := hb.trans_le hp.2.1
    exact ((Complex.continuousAt_ofReal_cpow p.2 (p.1/2) (Or.inr (ne_of_gt ht))).comp_of_eq
      (show ContinuousAt (fun q : ℂ × ℝ => (q.2,q.1/2)) p by fun_prop) rfl).continuousWithinAt
  have ho : Continuous (fun p : ℂ × ℝ => power (1/2) (1-p.2)) :=
    (Complex.continuous_ofReal_cpow_const (y := (1/2:ℂ)) (by norm_num)).comp
      (show Continuous (fun p : ℂ × ℝ => 1-p.2) by fun_prop)
  obtain ⟨A,hA⟩ := ((isCompact_closedBall w 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn P (closedBall w 1 ×ˢ Icc b (1:ℝ)) from hp.mul ho.continuousOn)
  obtain ⟨G,hG,hg⟩ := outerGauss_uniform_bound w chi (by linarith : 0 < 1-b) (by linarith : 1-b < 1)
  refine ⟨max A 0*G,mul_nonneg (le_max_right _ _) hG,?_⟩
  intro u hu z hz
  have he : normalizable u chi z = P (u,z)*gaussFactor u chi true (1-z) := by
    unfold normalizable dress outerFactor P
    ring
  rw [he,norm_mul]
  have hn : ‖(1-(z:ℂ))‖ ≤ 1-b := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hz.2])]
    linarith [hz.1]
  exact mul_le_mul ((hA (u,z) ⟨ball_subset_closedBall hu,hz⟩).trans (le_max_left _ _))
    (hg u hu _ hn) (norm_nonneg _) (le_max_right _ _)
end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original outer mode has one frequency-uniform bound on each finite tortoise interval. -/
theorem tortoiseNormalizable_outer_uniform_bound (w chi : ℂ) {T : ℝ} (hT : T < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ ball w 1, ∀ t ∈ Ioo T (0:ℝ),
      ‖normalizable u chi (horizonCoordinate t)‖ ≤ C := by
  let b := Real.exp (2*T)/2
  have hb : 0 < b := half_pos (Real.exp_pos _)
  have heT : Real.exp (2*T) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show 2*T<0 by linarith)
  have hb1 : b < 1 := by dsimp [b]; linarith
  obtain ⟨C,hC,hbound⟩ := normalizable_outer_uniform_bound w chi hb hb1
  refine ⟨C,hC,fun u hu t ht => hbound u hu _ ⟨?_,(horizonCoordinate_interior t ht.2).2.le⟩⟩
  have het : Real.exp (2*T) ≤ Real.exp (2*t) := Real.exp_le_exp.mpr (by linarith [ht.1])
  have hzt : Real.exp (2*t) ≤ horizonCoordinate t := by
    rw [horizonCoordinate_factor,two_mul,Real.exp_add]
    have hh : Real.exp t ≤ Real.exp t*(1+radialUnit t) := by
      nlinarith [(Real.exp_pos t),(radialUnit_bounds t ht.2).1]
    simpa only [pow_two] using mul_self_le_mul_self (Real.exp_pos t).le hh
  exact (by dsimp [b]; linarith [Real.exp_pos (2*T)] : b ≤ Real.exp (2*T)).trans (het.trans hzt)

/-- Spatial continuity of the explicit numerator persists at both cleared denominator zeros. -/
theorem clearedReducedGreen_continuousAt_thetaCuspHawkingBMReducedOuterPairing (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    ContinuousAt (clearedReducedGreen w chi s a) t := by
  let K := reducedGreenGradient chi s 1
  have hb := horizonCoordinate_interior t ht
  have hM := (horizonFirstMoment_hasDerivAt s chi a 1 K w hw hwr hb).continuousAt
  have hO := (outerSourceIntegral_hasDerivAt s chi a 1 K w hb).continuousAt
  have hN := (normalizable_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have hH := (horizon_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have h := ((hN.mul hM).add (hH.mul hO)).comp_of_eq (horizonCoordinate_hasDerivAt t).continuousAt rfl
  exact (h.mul continuousAt_const).add
    (continuousAt_const.mul (radialLift_hasDerivAt s w a (clearedOnset s w) t).continuousAt)

/-- The original outer pairing with the reduced response's source and connection denominators cleared. -/
def clearedReducedOuterPairing (chi s a : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioo T (0:ℝ), clearedReducedGreen w chi s a t*normalizable w chi (horizonCoordinate t)

/-- The actual outer pairing is analytic through connection and source poles; the common majorant is derived. -/
theorem clearedReducedOuterPairing_analyticAt (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) {T : ℝ} (hT : T < 0) :
    AnalyticAt ℂ (clearedReducedOuterPairing chi s a T) w := by
  obtain ⟨RU,CU,hRU,hCU,hU⟩ := clearedReducedGreen_outer_uniform_bound w chi s a hw hwr T
  obtain ⟨CN,hCN,hN⟩ := tortoiseNormalizable_outer_uniform_bound w chi hT
  have hfreq : ∀ᶠ u : ℂ in 𝓝 w, u.im ≠ 0 ∧ -2 < u.re :=
    (Complex.continuous_im.continuousAt.eventually_ne hw).and
      (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr)
  obtain ⟨RF,hRF,hF⟩ := Metric.eventually_nhds_iff.mp hfreq
  let R := min RU (min RF 1)
  have hR : 0 < R := lt_min hRU (lt_min hRF (by norm_num))
  have hur (u : ℂ) (hu : u ∈ ball w R) : u ∈ ball w RU := ball_subset_ball (min_le_left _ _) hu
  have hun (u : ℂ) (hu : u ∈ ball w R) : u ∈ ball w 1 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  have huf (u : ℂ) (hu : u ∈ ball w R) : u.im ≠ 0 ∧ -2 < u.re :=
    hF (mem_ball.mp (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu))
  let F : ℂ → ℝ → ℂ := fun u t => clearedReducedGreen u chi s a t*normalizable u chi (horizonCoordinate t)
  let G := fun u : ℂ => (Ioo T (0:ℝ)).indicator (F u)
  let B := (Ioo T (0:ℝ)).indicator (fun _ : ℝ => CU*CN)
  have hcont (u : ℂ) (hu : u ∈ ball w R) : ContinuousOn (F u) (Ioo T (0:ℝ)) := by
    intro t ht
    have hn := ((normalizable_derivatives_continued (w := u) (chi := chi)
      (horizonCoordinate_interior t ht.2)).1.continuousAt).comp_of_eq
        (horizonCoordinate_hasDerivAt t).continuousAt rfl
    exact ((clearedReducedGreen_continuousAt_thetaCuspHawkingBMReducedOuterPairing u chi s a (huf u hu).1 (huf u hu).2 t ht.2).mul hn).continuousWithinAt
  have hmeas (u : ℂ) (hu : u ∈ ball w R) : AEStronglyMeasurable (G u) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
      ((hcont u hu).aestronglyMeasurable measurableSet_Ioo)
  have hdiff (t : ℝ) : DifferentiableOn ℂ (fun u => G u t) (ball w R) := by
    intro u hu
    by_cases ht : t ∈ Ioo T (0:ℝ)
    · have hA := (clearedReducedGreen_analyticAt u chi s a (huf u hu).1 (huf u hu).2 t ht.2).mul
        ((normalizable_frequency_entire chi (horizonCoordinate_interior t ht.2)).analyticAt u)
      simpa only [G,F,indicator_of_mem ht] using! hA.differentiableAt.differentiableWithinAt
    · simp only [G,indicator_of_notMem ht]
      fun_prop
  have hbound (t : ℝ) (u : ℂ) (hu : u ∈ ball w R) : ‖G u t‖ ≤ B t := by
    by_cases ht : t ∈ Ioo T (0:ℝ)
    · simp only [G,B,F,indicator_of_mem ht,norm_mul]
      exact mul_le_mul (hU u (hur u hu) t ⟨ht.1.le,ht.2⟩) (hN u (hun u hu) t ht) (norm_nonneg _) hCU
    · simp only [G,B,indicator_of_notMem ht,norm_zero,le_refl]
  have hBI : Integrable B volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrable_const (CU*CN))
  have hDI : DifferentiableOn ℂ (fun u => ∫ t, G u t) (ball w R) := by
    intro v hv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr
      (fun u hu => hmeas u (hsub hu)) (fun t => (hdiff t).mono hsub)
      (fun t u hu => hbound t u (hsub hu)) hBI).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball w (mem_ball_self hR)
  simpa only [G,F,integral_indicator measurableSet_Ioo,clearedReducedOuterPairing] using! hA

/-- Both physical fundamental resonances retain an analytic original outer pairing numerator. -/
theorem physicalClearedReducedOuterPairing_analyticAt (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) {T : ℝ} (hT : T < 0) :
    AnalyticAt ℂ (clearedReducedOuterPairing (physicalRadialFrequency q) (physicalRate q branch) a T)
      (physicalFundamentalFrequency q side) := by
  have hw := physicalFundamentalFrequency_strip q side
  exact clearedReducedOuterPairing_analyticAt _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hT

/-- The original cleared pairing density is absolutely integrable on its finite outer interval. -/
theorem clearedReducedOuterPairing_integrable (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) {T : ℝ} (hT : T < 0) :
    Integrable (fun t => clearedReducedGreen w chi s a t*normalizable w chi (horizonCoordinate t))
      (volume.restrict (Ioo T (0:ℝ))) := by
  obtain ⟨R,C,hR,hC,hU⟩ := clearedReducedGreen_outer_uniform_bound w chi s a hw hwr T
  obtain ⟨N,hN,hV⟩ := tortoiseNormalizable_outer_uniform_bound w chi hT
  have hc : ContinuousOn (fun t => clearedReducedGreen w chi s a t*normalizable w chi (horizonCoordinate t))
      (Ioo T (0:ℝ)) := by
    intro t ht
    have hn := ((normalizable_derivatives_continued (w := w) (chi := chi)
      (horizonCoordinate_interior t ht.2)).1.continuousAt).comp_of_eq
        (horizonCoordinate_hasDerivAt t).continuousAt rfl
    exact ((clearedReducedGreen_continuousAt_thetaCuspHawkingBMReducedOuterPairing w chi s a hw hwr t ht.2).mul hn).continuousWithinAt
  have hi : Integrable (fun _ : ℝ => C*N) (volume.restrict (Ioo T (0:ℝ))) := integrable_const _
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_mul]
  exact mul_le_mul (hU w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
    (hV w (mem_ball_self (by norm_num)) t ht) (norm_nonneg _) hC

/-- The literal outer pairing before its original scalar denominator is cleared. -/
def continuedReducedOuterPairing (chi s a : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioo T (0:ℝ), continuedReducedGreen w chi s a 1 t*normalizable w chi (horizonCoordinate t)

/-- The analytic outer numerator is the original outer integral times its exact clearing factor. -/
theorem clearedReducedOuterPairing_eq (w chi s a : ℂ) (T : ℝ)
    (hs : w-2*s ≠ 0) (hc : connection w chi ≠ 0) :
    clearedReducedOuterPairing chi s a T w =
      reducedGreenClearingFactor w chi s*continuedReducedOuterPairing chi s a T w := by
  unfold clearedReducedOuterPairing continuedReducedOuterPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [clearedReducedGreen_eq w chi s a hs hc t,mul_assoc])

/-- At a physical resonance the restored outer numerator retains the full source moment and the mode square. -/
theorem physicalClearedReducedOuterPairing_value (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (T : ℝ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    clearedReducedOuterPairing chi s a T w =
      (fundamentalSourceMoment w s a*clearedOnset s w)*
        ∫ t in Ioo T (0:ℝ), (normalizable w chi (horizonCoordinate t))^(2 : ℕ) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  have hw := physicalFundamentalFrequency_strip q side
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  unfold clearedReducedOuterPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change clearedReducedGreen w chi s a t*normalizable w chi (horizonCoordinate t)=_
  rw [clearedReducedGreen_fundamental_factor w chi s a hw.1 (abs_lt.mp hw.2).1 hf t ht.2,
    normalizable_fundamental_value w chi hf]
  ring

/-- The actual original outer integral has its physical residue after outer integration. -/
theorem physicalReducedOuterPairing_residue (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) {T : ℝ} (hT : T < 0) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    Tendsto (fun u => (u-w)*continuedReducedOuterPairing chi s a T u) (𝓝[≠] w)
      (𝓝 ((fundamentalSourceMoment w s a*clearedOnset s w)*
        (∫ t in Ioo T (0:ℝ), (normalizable w chi (horizonCoordinate t))^(2 : ℕ))/
          physicalFundamentalDenominatorSlope q branch side)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  have hN := physicalClearedReducedOuterPairing_analyticAt q branch side a hT
  have hD := physicalFundamental_clearingFactor_hasDerivAt q branch side
  have hd := physicalFundamental_denominatorSlope_ne_zero q branch side
  have hz := physicalFundamental_clearingFactor_zero q branch side
  have hlim := (hN.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div hD.tendsto_slope hd
  rw [physicalClearedReducedOuterPairing_value q branch side a T] at hlim
  apply hlim.congr'
  filter_upwards [hD.eventually_ne (c := 0) hd] with u hdu
  have hs : u-2*s ≠ 0 := by
    intro he
    apply hdu
    change -(u-2*s)*connection u chi=0
    rw [he,neg_zero,zero_mul]
  have hc : connection u chi ≠ 0 := by
    intro he
    apply hdu
    change -(u-2*s)*connection u chi=0
    rw [he,mul_zero]
  simp only [Pi.div_apply,slope_def_field,hz,sub_zero,div_div_eq_mul_div]
  rw [clearedReducedOuterPairing_eq u chi s a T hs hc]
  change (reducedGreenClearingFactor u chi s*continuedReducedOuterPairing chi s a T u)*(u-w)/
    reducedGreenClearingFactor u chi s=(u-w)*continuedReducedOuterPairing chi s a T u
  rw [mul_assoc,mul_div_cancel_left₀ _ (show reducedGreenClearingFactor u chi s ≠ 0 from hdu),mul_comm]

end
end RHTower.D4BMJointSource
