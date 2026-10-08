import GaloisForLFunctions.RHTower.WeilWorkPBAPJointFourier
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointNull
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalKernel
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketEnergy

/-!
Exact paired mass and full-mass logarithmic gamma coercivity.
The base logarithmic Fourier moment is integrable by actual gamma integrability.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Exact paired physical mass; disjoint clusters remove both shifted correlations. -/
theorem joint_pair_testMass (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    testMass (clusterDifference (cosineProfile f.1.1 T) L) +
      testMass (clusterDifference (sineProfile f.1.1 T) L) = 2*testMass f.1.1 := by
  have hp : EF.weilTest f.1.1 f.1.1 L = 0 :=
    weilTest_eq_zero_outside_interval hf (by simpa only [abs_of_nonneg hL] using hWL)
  have hm : EF.weilTest f.1.1 f.1.1 (-L) = 0 :=
    weilTest_eq_zero_outside_interval hf (by simpa only [abs_neg, abs_of_nonneg hL] using hWL)
  have hc := weilTest_clusterDifference (contDiff_cosineProfile f.2 T).continuous
    (hasCompactSupport_cosineProfile f.1.2.2 T) L 0
  have hs := weilTest_clusterDifference (contDiff_sineProfile f.2 T).continuous
    (hasCompactSupport_sineProfile f.1.2.2 T) L 0
  have h0 := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T 0
  have hminus := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T (-L)
  have hplus := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T L
  simp only [mul_zero, Real.cos_zero, Complex.ofReal_one, one_mul] at h0
  rw [hm, mul_zero] at hminus
  rw [hp, mul_zero] at hplus
  simp only [zero_sub, zero_add] at hc hs
  have he : EF.weilTest (clusterDifference (cosineProfile f.1.1 T) L)
      (clusterDifference (cosineProfile f.1.1 T) L) 0 +
      EF.weilTest (clusterDifference (sineProfile f.1.1 T) L)
        (clusterDifference (sineProfile f.1.1 T) L) 0 = 2*EF.weilTest f.1.1 f.1.1 0 := by
    linear_combination hc + hs + 2*h0 - hminus - hplus
  simp only [autocorr_zero_eq_testMass] at he
  exact_mod_cast he

/-- A nonzero smooth compact profile has strictly positive physical mass. -/
theorem joint_testMass_pos (f : JointSmoothTest) (hf : f.1.1 ≠ 0) : 0 < testMass f.1.1 := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra hn
    apply hf
    funext x
    exact not_ne_iff.mp fun h => hn ⟨x,h⟩
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f.2.continuous.norm.pow 2)
    (f.1.2.2.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp))
    (fun _ => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

/-- Literal sum of the two Fourier squares. -/
def jointPairDensity (f : JointSmoothTest) (L T ξ : ℝ) : ℝ :=
  ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 +
    ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2

private theorem joint_integrable_fourier_sq (g : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT g.1.1 (ξ:ℂ)‖^2) := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport g.1.2.2
  exact integrable_normSq_paperFT g.1.2.1 (tsupport_subset_of_vanish
    (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h)))

theorem jointPairDensity_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (jointPairDensity f L T) :=
  (joint_integrable_fourier_sq (clusterDifferenceTest (cosineProfileTest f T) L)).add
    (joint_integrable_fourier_sq (clusterDifferenceTest (sineProfileTest f T) L))

/-- Plancherel retains the exact mass independently of modulation frequency. -/
theorem jointPairDensity_mass (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    (1/(2*Real.pi))*(∫ ξ, jointPairDensity f L T ξ) = 2*testMass f.1.1 := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  change (1/(2*Real.pi))*(∫ ξ : ℝ,
    ‖paperFT gc.1.1 (ξ:ℂ)‖^2 + ‖paperFT gs.1.1 (ξ:ℂ)‖^2) = _
  rw [integral_add (joint_integrable_fourier_sq gc) (joint_integrable_fourier_sq gs),
    mul_add, LebesgueAtomWeil.integral_norm_sq_paperFT_eq gc.1.2.1 gc.1.2.2,
    LebesgueAtomWeil.integral_norm_sq_paperFT_eq gs.1.2.1 gs.1.2.2]
  exact joint_pair_testMass f hf hWL hL T

/-- Central spectral mass has a concrete inverse-cubic upper bound. -/
theorem jointPairDensity_low_mass (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (L T : ℝ) (hT : 0 < T) :
    (∫ ξ in Set.Ioc (-T/2) (T/2), jointPairDensity f L T ξ) ≤
      64*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)^2/T^3 := by
  let C : ℝ := 64*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)^2/T^4
  have hm : (volume : Measure ℝ) (Set.Ioc (-T/2) (T/2)) ≠ ⊤ :=
    measure_Ioc_lt_top.ne
  have hbound : (∫ ξ in Set.Ioc (-T/2) (T/2), jointPairDensity f L T ξ) ≤
      ∫ _ in Set.Ioc (-T/2) (T/2), C := by
    apply setIntegral_mono_on (jointPairDensity_integrable f L T).integrableOn
      (integrableOn_const hm) measurableSet_Ioc
    intro ξ hξ
    exact joint_pair_density_central_bound f hf L T hT ξ (abs_le.mpr ⟨by linarith [hξ.1], hξ.2⟩)
  calc _ ≤ ∫ _ in Set.Ioc (-T/2) (T/2), C := hbound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith)]
      dsimp [C]
      field_simp [ne_of_gt hT]
      ; ring

/-- Elementary logarithmic submultiplicativity, retaining both frequency translates. -/
theorem joint_log_triangle (a b : ℝ) :
    Real.log (2+|a+b|) ≤ Real.log (2+|a|)+Real.log (2+|b|) := by
  have hh : 2+|a+b| ≤ (2+|a|)*(2+|b|) := by
    nlinarith [abs_add_le a b, abs_nonneg a, abs_nonneg b,
      mul_nonneg (abs_nonneg a) (abs_nonneg b)]
  have h := Real.log_le_log (by positivity : 0<2+|a+b|) hh
  rwa [Real.log_mul (by positivity) (by positivity)] at h

theorem joint_gamma_lower_log (ξ : ℝ) :
    Real.log (2+|ξ|)-(10+Real.log 4) ≤ EF.gammaBracket ξ := by
  have h := Real.log_le_log (by positivity : 0<2+|ξ|)
    (show 2+|ξ| ≤ 4*(1+|ξ|/4) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  linarith [gammaBracket_lower ξ]

private theorem joint_integrable_gamma (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2 * EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.1.2.1 f.1.2.2 f.1.2.1 f.1.2.2
  refine h.re.congr (Filter.Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1.1 f.1.1) (ξ:ℂ) *
    (EF.gammaBracket ξ:ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The base logarithmic moment is finite by the corpus's actual gamma integrability. -/
theorem joint_fourier_log_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2 * Real.log (2+|ξ|)) := by
  have hd := joint_integrable_fourier_sq f
  have hg := joint_integrable_gamma f
  have harg : Continuous (fun ξ : ℝ => 2+|ξ|) := continuous_const.add continuous_abs
  have hl : Continuous (fun ξ : ℝ => Real.log (2+|ξ|)) :=
    harg.log (fun ξ => ne_of_gt (by linarith [abs_nonneg ξ]))
  apply (hg.add (hd.const_mul (10+Real.log 4))).mono'
    (hd.aestronglyMeasurable.mul hl.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖‖paperFT f.1.1 (ξ:ℂ)‖^2 * Real.log (2+|ξ|)‖ ≤
      ‖paperFT f.1.1 (ξ:ℂ)‖^2 * EF.gammaBracket ξ +
        (10+Real.log 4)*‖paperFT f.1.1 (ξ:ℂ)‖^2
    have hlog : 0 ≤ Real.log (2+|ξ|) := Real.log_nonneg (by linarith [abs_nonneg ξ])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hlog)]
    have hh := mul_le_mul_of_nonneg_left (joint_gamma_lower_log ξ)
      (sq_nonneg ‖paperFT f.1.1 (ξ:ℂ)‖)
    nlinarith

def jointLogMoment (f : JointSmoothTest) : ℝ :=
  (1/(2*Real.pi))*∫ ξ : ℝ, ‖paperFT f.1.1 (ξ:ℂ)‖^2 * Real.log (2+|ξ|)

theorem jointLogMoment_nonneg (f : JointSmoothTest) : 0 ≤ jointLogMoment f := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun ξ => mul_nonneg (sq_nonneg _)
    (Real.log_nonneg (by linarith [abs_nonneg ξ]))

/-- Pointwise logarithmic coercivity with the full translated Fourier mass. -/
theorem jointPairDensity_gamma_pointwise (f : JointSmoothTest) (L T ξ : ℝ) :
    jointPairDensity f L T ξ * (Real.log (2+|T|)-(10+Real.log 4)) -
      2*(‖paperFT f.1.1 (ξ+T:ℝ)‖^2 * Real.log (2+|ξ+T|) +
        ‖paperFT f.1.1 (ξ-T:ℝ)‖^2 * Real.log (2+|ξ-T|)) ≤
      jointPairDensity f L T ξ * EF.gammaBracket ξ := by
  let P := ‖1-Complex.exp (I*(ξ:ℂ)*L)‖^2
  let A := ‖paperFT f.1.1 (ξ+T:ℝ)‖^2
  let B := ‖paperFT f.1.1 (ξ-T:ℝ)‖^2
  have hP : 0 ≤ P := sq_nonneg _
  have hP4 : P ≤ 4 := by
    have he : ‖Complex.exp (I*(ξ:ℂ)*L)‖ = 1 := by
      rw [show I*(ξ:ℂ)*L = ((ξ*L:ℝ):ℂ)*I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hb : ‖1-Complex.exp (I*(ξ:ℂ)*L)‖ ≤ 2 := by
      calc _ ≤ ‖(1:ℂ)‖+‖Complex.exp (I*(ξ:ℂ)*L)‖ := norm_sub_le _ _
           _ = 2 := by rw [he, norm_one]; ring
    dsimp [P]
    nlinarith [norm_nonneg (1-Complex.exp (I*(ξ:ℂ)*L))]
  have hd : jointPairDensity f L T ξ = P*(A+B)/2 := by
    simpa only [jointPairDensity, P, A, B, Complex.ofReal_add, Complex.ofReal_sub]
      using normSq_paperFT_joint_pair f L T (ξ:ℂ)
  have hp : Real.log (2+|T|) ≤ Real.log (2+|ξ|)+Real.log (2+|ξ+T|) := by
    have h := joint_log_triangle ξ (-(ξ+T))
    simpa only [show ξ+ -(ξ+T) = -T by ring, abs_neg] using h
  have hm : Real.log (2+|T|) ≤ Real.log (2+|ξ|)+Real.log (2+|ξ-T|) := by
    have h := joint_log_triangle ξ (-(ξ-T))
    simpa only [show ξ+ -(ξ-T) = T by ring, abs_neg] using h
  have hpa : A*(Real.log (2+|T|)-(10+Real.log 4)-EF.gammaBracket ξ) ≤
      A*Real.log (2+|ξ+T|) :=
    mul_le_mul_of_nonneg_left (by linarith [joint_gamma_lower_log ξ]) (sq_nonneg _)
  have hmb : B*(Real.log (2+|T|)-(10+Real.log 4)-EF.gammaBracket ξ) ≤
      B*Real.log (2+|ξ-T|) :=
    mul_le_mul_of_nonneg_left (by linarith [joint_gamma_lower_log ξ]) (sq_nonneg _)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hpa hmb) hP
  have hweight : 0 ≤ A*Real.log (2+|ξ+T|)+B*Real.log (2+|ξ-T|) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg (ξ+T)])))
      (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg (ξ-T)])))
  have hbound := mul_le_mul_of_nonneg_right hP4 hweight
  change jointPairDensity f L T ξ * _ - 2*(A*_+B*_) ≤ _
  rw [hd]
  nlinarith

private theorem jointPairDensity_gamma_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (fun ξ => jointPairDensity f L T ξ * EF.gammaBracket ξ) := by
  have h := (joint_integrable_gamma (clusterDifferenceTest (cosineProfileTest f T) L)).add
    (joint_integrable_gamma (clusterDifferenceTest (sineProfileTest f T) L))
  exact h.congr (Filter.Eventually.of_forall fun ξ => by
    change ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ = jointPairDensity f L T ξ * EF.gammaBracket ξ
    dsimp [jointPairDensity]
    ring)

/-- Actual gamma energy retains coefficient twice the base physical mass. -/
theorem joint_pair_gamma_lower (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    2*testMass f.1.1*Real.log (2+|T|) -
      2*testMass f.1.1*(10+Real.log 4) - 4*jointLogMoment f ≤
      testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
      testGamma (clusterDifference (sineProfile f.1.1 T) L) := by
  let q : ℝ → ℝ := fun ξ => ‖paperFT f.1.1 (ξ:ℂ)‖^2 * Real.log (2+|ξ|)
  have hq : Integrable q := joint_fourier_log_integrable f
  have hp := hq.comp_add_right T
  have hm := hq.comp_sub_right T
  have hd := jointPairDensity_integrable f L T
  have hg := jointPairDensity_gamma_integrable f L T
  have hi := integral_mono
    ((hd.mul_const (Real.log (2+|T|)-(10+Real.log 4))).sub ((hp.add hm).const_mul 2))
    hg (jointPairDensity_gamma_pointwise f L T)
  change (∫ ξ, jointPairDensity f L T ξ*(Real.log (2+|T|)-(10+Real.log 4)) -
    2*(q (ξ+T)+q (ξ-T))) ≤ ∫ ξ, jointPairDensity f L T ξ*EF.gammaBracket ξ at hi
  have hsplit : (∫ ξ, jointPairDensity f L T ξ*(Real.log (2+|T|)-(10+Real.log 4)) -
      2*(q (ξ+T)+q (ξ-T))) =
      (∫ ξ, jointPairDensity f L T ξ*(Real.log (2+|T|)-(10+Real.log 4))) -
      ∫ ξ, 2*(q (ξ+T)+q (ξ-T)) :=
    integral_sub (hd.mul_const (Real.log (2+|T|)-(10+Real.log 4)))
      ((hp.add hm).const_mul 2)
  have hshift : (∫ ξ, q (ξ+T)+q (ξ-T)) = 2*∫ ξ, q ξ := by
    calc
      _ = (∫ ξ, q (ξ+T)) + ∫ ξ, q (ξ-T) := integral_add hp hm
      _ = _ := by rw [integral_add_right_eq_self q T, integral_sub_right_eq_self q T]; ring
  rw [hsplit, integral_mul_const, integral_const_mul, hshift] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))
  have hmass := jointPairDensity_mass f hf hWL hL T
  have he : testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
      testGamma (clusterDifference (sineProfile f.1.1 T) L) =
      (1/(2*Real.pi))*∫ ξ, jointPairDensity f L T ξ*EF.gammaBracket ξ := by
    unfold testGamma
    have hic := joint_integrable_gamma (clusterDifferenceTest (cosineProfileTest f T) L)
    have his := joint_integrable_gamma (clusterDifferenceTest (sineProfileTest f T) L)
    dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest] at hic his
    rw [← mul_add, ← integral_add hic his]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by dsimp [jointPairDensity]; ring
  rw [he]
  change 2*testMass f.1.1*Real.log (2+|T|) -
    2*testMass f.1.1*(10+Real.log 4) - 4*((1/(2*Real.pi))*∫ ξ, q ξ) ≤ _
  have hnormalize : (1/(2*Real.pi))*
      ((∫ ξ, jointPairDensity f L T ξ)*(Real.log (2+|T|)-(10+Real.log 4)) -
        2*(2*∫ ξ, q ξ)) =
      2*testMass f.1.1*Real.log (2+|T|) - 2*testMass f.1.1*(10+Real.log 4) -
        4*((1/(2*Real.pi))*∫ ξ, q ξ) := by
    calc
      _ = ((1/(2*Real.pi))*(∫ ξ, jointPairDensity f L T ξ))*
          (Real.log (2+|T|)-(10+Real.log 4)) - 4*((1/(2*Real.pi))*∫ ξ, q ξ) := by ring
      _ = _ := by rw [hmass]; ring
  rw [hnormalize] at hi'
  exact hi'

end RHTower.WeilWorkPBAP
