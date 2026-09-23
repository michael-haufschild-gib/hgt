import GaloisForLFunctions.RHTower.ThetaCuspCompletedProductFiberOddPtolemyNoGo
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms
import GaloisForLFunctions.HTGeometry.JuliaDefectLevyKhintchine

open Real Set Filter Topology MeasureTheory Polynomial

/-!
# Completed first-product-fibre Wigner no-go

Corpus proof chain under attack:

`nonnegative Wigner spectrum on every completed product fibre`
`→ fibrewise positive decomposition of the Hedenmalm/TCD current`
`→ positive TCD singular flux`
`→ global D1 positivity → S6F → Hankel/Bezoutian positivity → Weil positivity → RH`.

The first completed fibre at modular centre is the even extension of a positive-half profile
with strictly positive seam slope.  Two half-line integrations by parts show that its cosine
transform is eventually negative: the leading high-frequency term is the negative seam current,
while the integrable curvature transform vanishes by Riemann--Lebesgue.  The exact product-fibre
normal form then gives a positive frequency where the actual completed Wigner fibre is negative.
Thus the fibrewise-positive route is dead; a surviving TCD proof must cancel distinct product
fibres before reading a sign.
-/

namespace RHTower

noncomputable section

private def firstCompletedFiberJet (m : ℕ) (x : ℝ) : ℝ :=
  thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) 1 x

private theorem hasDerivAt_firstCompletedFiberJet (m : ℕ) (x : ℝ) :
    HasDerivAt (firstCompletedFiberJet m) (firstCompletedFiberJet (m + 1) x) x := by
  unfold firstCompletedFiberJet
  simpa [thetaCuspLogDerivativePolynomial] using
    hasDerivAt_thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) 1 x

private theorem firstCompletedFiberJet_zero :
    firstCompletedFiberJet 0 = fun x => thetaCuspSourceTerm x 1 := by
  change thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 =
    fun x => thetaCuspSourceTerm x 1
  exact (thetaCuspSourceTerm_eq_polynomialAtom 1).symm

private def firstCompletedFiberHalfAmplitude (x : ℝ) : ℝ :=
  firstCompletedFiberJet 0 x ^ (2 : ℕ)

private def firstCompletedFiberHalfSlope (x : ℝ) : ℝ :=
  2 * firstCompletedFiberJet 0 x * firstCompletedFiberJet 1 x

private def firstCompletedFiberHalfCurvature (x : ℝ) : ℝ :=
  2 * (firstCompletedFiberJet 1 x ^ (2 : ℕ) +
    firstCompletedFiberJet 0 x * firstCompletedFiberJet 2 x)

private theorem hasDerivAt_firstCompletedFiberHalfAmplitude (x : ℝ) :
    HasDerivAt firstCompletedFiberHalfAmplitude
      (firstCompletedFiberHalfSlope x) x := by
  have h := (hasDerivAt_firstCompletedFiberJet 0 x).mul
    (hasDerivAt_firstCompletedFiberJet 0 x)
  have hd :
      firstCompletedFiberJet (0 + 1) x * firstCompletedFiberJet 0 x +
          firstCompletedFiberJet 0 x * firstCompletedFiberJet (0 + 1) x =
        2 * firstCompletedFiberJet 0 x * firstCompletedFiberJet 1 x := by
    simp only [Nat.zero_add]
    ring
  have hfun : firstCompletedFiberHalfAmplitude =
      firstCompletedFiberJet 0 * firstCompletedFiberJet 0 := by
    funext y
    simp [firstCompletedFiberHalfAmplitude, pow_two]
  rw [hfun]
  exact h.congr_deriv hd

private theorem hasDerivAt_firstCompletedFiberHalfSlope (x : ℝ) :
    HasDerivAt firstCompletedFiberHalfSlope
      (firstCompletedFiberHalfCurvature x) x := by
  have h := ((hasDerivAt_firstCompletedFiberJet 0 x).mul
    (hasDerivAt_firstCompletedFiberJet 1 x)).const_mul 2
  have hd :
      2 * (firstCompletedFiberJet (0 + 1) x * firstCompletedFiberJet 1 x +
        firstCompletedFiberJet 0 x * firstCompletedFiberJet (1 + 1) x) =
      2 * (firstCompletedFiberJet 1 x ^ (2 : ℕ) +
        firstCompletedFiberJet 0 x * firstCompletedFiberJet 2 x) := by
    simp only [Nat.zero_add, Nat.one_add, pow_two]
  have hfun : firstCompletedFiberHalfSlope =
      fun y => 2 * (firstCompletedFiberJet 0 * firstCompletedFiberJet 1) y := by
    funext y
    simp [firstCompletedFiberHalfSlope]
    ring
  rw [hfun]
  exact h.congr_deriv hd

private theorem integrableOn_firstCompletedFiberJet_mul
    (m n : ℕ) :
    IntegrableOn (fun x : ℝ =>
      firstCompletedFiberJet m x * firstCompletedFiberJet n x) (Ioi 0) := by
  let C : ℝ := thetaCuspGaussianConstant (thetaCuspLogDerivativePolynomial m) *
    Real.exp (-(Real.pi / 2) * (1 : ℝ) ^ (2 : ℕ))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (thetaCuspGaussianConstant_nonneg _)
      (Real.exp_pos _).le
  have hnInt : IntegrableOn (firstCompletedFiberJet n) (Ioi 0) := by
    exact integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
      (thetaCuspLogDerivativePolynomial n) (by norm_num)
  apply Integrable.bdd_mul (c := C) hnInt
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_firstCompletedFiberJet m x).continuousAt).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    have hraw := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos
      (thetaCuspLogDerivativePolynomial m) hx.le (by norm_num : 0 < (1 : ℕ))
    have hexp : Real.exp (-x) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
    have hraw' : Real.exp x * |firstCompletedFiberJet m x| ≤ C := by
      simpa only [firstCompletedFiberJet, C, Nat.cast_one] using hraw
    change |firstCompletedFiberJet m x| ≤ C
    calc
      |firstCompletedFiberJet m x| =
          Real.exp (-x) * (Real.exp x * |firstCompletedFiberJet m x|) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
      _ ≤ Real.exp (-x) * C := by
        exact mul_le_mul_of_nonneg_left hraw' (Real.exp_pos _).le
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hexp hC
      _ = C := one_mul C

private theorem integrableOn_firstCompletedFiberHalfAmplitude :
    IntegrableOn firstCompletedFiberHalfAmplitude (Ioi 0) := by
  exact (integrableOn_firstCompletedFiberJet_mul 0 0).congr_fun
    (fun x _ => by simp [firstCompletedFiberHalfAmplitude, pow_two]) measurableSet_Ioi

private theorem integrableOn_firstCompletedFiberHalfSlope :
    IntegrableOn firstCompletedFiberHalfSlope (Ioi 0) := by
  refine ((integrableOn_firstCompletedFiberJet_mul 0 1).const_mul 2).congr ?_
  filter_upwards with x
  simp only [firstCompletedFiberHalfSlope]
  ring

private theorem integrableOn_firstCompletedFiberHalfCurvature :
    IntegrableOn firstCompletedFiberHalfCurvature (Ioi 0) := by
  have h11 := integrableOn_firstCompletedFiberJet_mul 1 1
  have h02 := integrableOn_firstCompletedFiberJet_mul 0 2
  refine ((h11.add h02).const_mul 2).congr ?_
  filter_upwards with x
  simp only [firstCompletedFiberHalfCurvature, Pi.add_apply, pow_two]

private theorem firstCompletedFiberHalfAmplitude_tendsto_atTop_zero :
    Tendsto firstCompletedFiberHalfAmplitude atTop (nhds 0) := by
  have h0 := thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (thetaCuspLogDerivativePolynomial 0) (by norm_num : 0 < (1 : ℕ))
  have hh : Tendsto (fun x =>
      thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 0) 1 x *
        thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 0) 1 x)
      atTop (nhds 0) := by simpa only [zero_mul] using h0.mul h0
  refine hh.congr' (Eventually.of_forall fun x => ?_)
  simp [firstCompletedFiberHalfAmplitude, firstCompletedFiberJet, pow_two]

private theorem firstCompletedFiberHalfSlope_tendsto_atTop_zero :
    Tendsto firstCompletedFiberHalfSlope atTop (nhds 0) := by
  have h0 := thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (thetaCuspLogDerivativePolynomial 0) (by norm_num : 0 < (1 : ℕ))
  have h1 := thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (thetaCuspLogDerivativePolynomial 1) (by norm_num : 0 < (1 : ℕ))
  have hh : Tendsto (fun x => 2 *
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 0) 1 x *
        thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1 x))
      atTop (nhds 0) := by simpa only [zero_mul, mul_zero] using (h0.mul h1).const_mul 2
  refine hh.congr' (Eventually.of_forall fun x => ?_)
  simp [firstCompletedFiberHalfSlope, firstCompletedFiberJet]
  ring

private theorem firstCompletedFiberHalfSlope_zero_pos :
    0 < firstCompletedFiberHalfSlope 0 := by
  have hjetSlope :
      firstCompletedFiberJet 1 0 =
        thetaCuspFirstAtomBoundaryLogSlope * thetaCuspSourceTerm 0 1 := by
    have h := hasDerivAt_firstCompletedFiberJet 0 0
    rw [firstCompletedFiberJet_zero] at h
    exact h.unique hasDerivAt_thetaCuspSourceTerm_one_zero
  rw [firstCompletedFiberHalfSlope, firstCompletedFiberJet_zero, hjetSlope]
  positivity [thetaCuspFirstAtomBoundaryLogSlope_pos,
    thetaCuspSourceTerm_one_zero_pos]

private theorem firstCompletedFiberHalfCosine_secondIntegrationByParts
    (b : ℝ) :
    b ^ (2 : ℕ) * (∫ x : ℝ in Ioi 0,
      firstCompletedFiberHalfAmplitude x * Real.cos (b * x)) =
      -firstCompletedFiberHalfSlope 0 -
        ∫ x : ℝ in Ioi 0,
          firstCompletedFiberHalfCurvature x * Real.cos (b * x) := by
  have hcos (x : ℝ) : HasDerivAt (fun y : ℝ => Real.cos (b * y))
      (-b * Real.sin (b * x)) x := by
    have h := (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b)
    convert h using 1
    all_goals try rfl
    ring
  have hsin (x : ℝ) : HasDerivAt (fun y : ℝ => -b * Real.sin (b * y))
      (-b ^ (2 : ℕ) * Real.cos (b * x)) x := by
    have h := ((Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b)).const_mul (-b)
    convert h using 1
    all_goals try rfl
    ring
  have hcosCurv : IntegrableOn (fun x : ℝ =>
      Real.cos (b * x) * firstCompletedFiberHalfCurvature x) (Ioi 0) := by
    apply Integrable.bdd_mul integrableOn_firstCompletedFiberHalfCurvature
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hsinSlope : IntegrableOn (fun x : ℝ =>
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfSlope x) (Ioi 0) := by
    apply Integrable.bdd_mul integrableOn_firstCompletedFiberHalfSlope
    · exact (by fun_prop : Continuous (fun x : ℝ => -b * Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
  have hcosSlopeZero : Tendsto (fun x : ℝ =>
      Real.cos (b * x) * firstCompletedFiberHalfSlope x)
      (𝓝[>] 0) (nhds (firstCompletedFiberHalfSlope 0)) := by
    have hright : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := inf_le_left
    have hc : Tendsto (fun x : ℝ => Real.cos (b * x)) (𝓝[>] 0) (nhds 1) := by
      have hcont : Continuous (fun x : ℝ => Real.cos (b * x)) := by fun_prop
      have hzero : Tendsto (fun x : ℝ => Real.cos (b * x))
          (𝓝 (0 : ℝ)) (nhds (Real.cos (b * 0))) := hcont.continuousAt
      simpa only [mul_zero, Real.cos_zero] using hzero.mono_left hright
    have hs : Tendsto firstCompletedFiberHalfSlope (𝓝[>] 0)
        (nhds (firstCompletedFiberHalfSlope 0)) :=
      (hasDerivAt_firstCompletedFiberHalfSlope 0).continuousAt.tendsto.mono_left hright
    simpa using hc.mul hs
  have hcosSlopeInf : Tendsto (fun x : ℝ =>
      Real.cos (b * x) * firstCompletedFiberHalfSlope x) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => ?_) (by simpa using firstCompletedFiberHalfSlope_tendsto_atTop_zero.norm)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have hsinAmpZero : Tendsto (fun x : ℝ =>
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfAmplitude x)
      (𝓝[>] 0) (nhds 0) := by
    have hright : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := inf_le_left
    have hs : Tendsto (fun x : ℝ => -b * Real.sin (b * x)) (𝓝[>] 0) (nhds 0) := by
      have hcont : Continuous (fun x : ℝ => -b * Real.sin (b * x)) := by fun_prop
      have hzero : Tendsto (fun x : ℝ => -b * Real.sin (b * x))
          (𝓝 (0 : ℝ)) (nhds (-b * Real.sin (b * 0))) := hcont.continuousAt
      simpa only [mul_zero, Real.sin_zero, mul_zero, neg_zero] using
        hzero.mono_left hright
    have ha : Tendsto firstCompletedFiberHalfAmplitude (𝓝[>] 0)
        (nhds (firstCompletedFiberHalfAmplitude 0)) :=
      (hasDerivAt_firstCompletedFiberHalfAmplitude 0).continuousAt.tendsto.mono_left hright
    simpa using hs.mul ha
  have hsinAmpInf : Tendsto (fun x : ℝ =>
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfAmplitude x) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => ?_)
      (by simpa using firstCompletedFiberHalfAmplitude_tendsto_atTop_zero.norm.const_mul |b|)
    rw [norm_mul]
    calc
      ‖-b * Real.sin (b * x)‖ * ‖firstCompletedFiberHalfAmplitude x‖
          ≤ |b| * ‖firstCompletedFiberHalfAmplitude x‖ := by
            gcongr
            rw [Real.norm_eq_abs, abs_mul, abs_neg]
            exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
      _ = _ := rfl
  have hsinAmp : IntegrableOn (fun x : ℝ =>
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfAmplitude x) (Ioi 0) := by
    apply Integrable.bdd_mul integrableOn_firstCompletedFiberHalfAmplitude
    · exact (by fun_prop : Continuous (fun x : ℝ => -b * Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
  have hcosAmp : IntegrableOn (fun x : ℝ =>
      (-b ^ (2 : ℕ) * Real.cos (b * x)) * firstCompletedFiberHalfAmplitude x) (Ioi 0) := by
    apply Integrable.bdd_mul integrableOn_firstCompletedFiberHalfAmplitude
    · exact (by fun_prop : Continuous (fun x : ℝ => -b ^ (2 : ℕ) * Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg (b ^ (2 : ℕ))) (abs_cos_le_one _)
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := fun x => Real.cos (b * x))
    (u' := fun x => -b * Real.sin (b * x))
    (v := firstCompletedFiberHalfSlope)
    (v' := firstCompletedFiberHalfCurvature)
    (fun x _ => hcos x) (fun x _ => hasDerivAt_firstCompletedFiberHalfSlope x)
    hcosCurv hsinSlope hcosSlopeZero hcosSlopeInf
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := fun x => -b * Real.sin (b * x))
    (u' := fun x => -b ^ (2 : ℕ) * Real.cos (b * x))
    (v := firstCompletedFiberHalfAmplitude)
    (v' := firstCompletedFiberHalfSlope)
    (fun x _ => hsin x) (fun x _ => hasDerivAt_firstCompletedFiberHalfAmplitude x)
    hsinSlope hcosAmp hsinAmpZero hsinAmpInf
  rw [show (∫ x : ℝ in Ioi 0,
      Real.cos (b * x) * firstCompletedFiberHalfCurvature x) =
      ∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfCurvature x * Real.cos (b * x) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hfirst
  rw [show (∫ x : ℝ in Ioi 0,
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfSlope x) =
      ∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfSlope x * (-b * Real.sin (b * x)) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hfirst
  rw [show (∫ x : ℝ in Ioi 0,
      (-b * Real.sin (b * x)) * firstCompletedFiberHalfSlope x) =
      ∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfSlope x * (-b * Real.sin (b * x)) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hsecond
  rw [show (∫ x : ℝ in Ioi 0,
      (-b ^ (2 : ℕ) * Real.cos (b * x)) * firstCompletedFiberHalfAmplitude x) =
      -b ^ (2 : ℕ) * ∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfAmplitude x * Real.cos (b * x) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring] at hsecond
  linarith

private theorem eventually_firstCompletedFiberHalfCosine_neg :
    ∀ᶠ b : ℝ in atTop,
      (∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfAmplitude x * Real.cos (b * x)) < 0 := by
  have hRLraw := HTGeometry.tendsto_setIntegral_mul_cos_atTop
    integrableOn_firstCompletedFiberHalfCurvature
  have hRL : Tendsto (fun b : ℝ => ∫ x : ℝ in Ioi 0,
      firstCompletedFiberHalfCurvature x * Real.cos (b * x)) atTop (nhds 0) := by
    convert hRLraw using 1
    funext b
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm x b, mul_comm]
  have hslope := firstCompletedFiberHalfSlope_zero_pos
  have hsmall : ∀ᶠ b : ℝ in atTop,
      |∫ x : ℝ in Ioi 0,
        firstCompletedFiberHalfCurvature x * Real.cos (b * x)| <
          firstCompletedFiberHalfSlope 0 := by
    simpa [Real.dist_eq] using hRL.eventually (Metric.ball_mem_nhds 0 hslope)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with b hb hbpos
  have hibp := firstCompletedFiberHalfCosine_secondIntegrationByParts b
  have hrem := (abs_lt.mp hb).1
  have hbsq : 0 < b ^ (2 : ℕ) := sq_pos_of_pos hbpos
  nlinarith

private theorem firstCompletedFiberHalfAmplitude_eq_sourceTerm_sq (x : ℝ) :
    firstCompletedFiberHalfAmplitude x = thetaCuspSourceTerm x 1 ^ (2 : ℕ) := by
  rw [firstCompletedFiberHalfAmplitude, firstCompletedFiberJet_zero]

private theorem thetaPositiveFactorPairs_one_wigner :
    thetaPositiveFactorPairs 1 = {(0, 0)} := by
  ext ⟨a, b⟩
  simp [thetaPositiveFactorPairs]

private theorem thetaCuspCompletedWignerProductFiber_one_zero_eq_integral
    (b : ℝ) :
    thetaCuspCompletedWignerProductFiber 1 0 b =
      ∫ t : ℝ, thetaCuspCompletedProductFiberWignerIntegrand 1 0 b t := by
  unfold thetaCuspCompletedWignerProductFiber
    thetaCuspCompletedProductFiberWignerIntegrand
  rw [thetaPositiveFactorPairs_one_wigner]
  simp [thetaCuspCompletedShellPairWigner,
    thetaCuspCompletedProductFiberAmplitude,
    thetaCuspCompletedPositiveShell,
    thetaPositiveFactorPairs_one_wigner]

private theorem thetaCuspCompletedProductFiberWignerIntegrand_one_zero
    (b t : ℝ) :
    thetaCuspCompletedProductFiberWignerIntegrand 1 0 b t =
      (firstCompletedFiberHalfAmplitude |t| : ℂ) *
        thetaWignerDifferencePhase b t := by
  rw [thetaCuspCompletedProductFiberWignerIntegrand,
    thetaCuspCompletedProductFiberAmplitude_one_zero,
    firstCompletedFiberHalfAmplitude_eq_sourceTerm_sq]

private theorem integrable_firstCompletedFiberHalfAmplitude_abs :
    Integrable (fun t : ℝ => firstCompletedFiberHalfAmplitude |t|) := by
  let g : ℝ → ℝ := Set.indicator (Ioi 0) firstCompletedFiberHalfAmplitude
  have hg : Integrable g :=
    integrableOn_firstCompletedFiberHalfAmplitude.integrable_indicator measurableSet_Ioi
  have hsum : Integrable (fun t : ℝ => g t + g (-t)) := hg.add hg.comp_neg
  refine hsum.congr ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hnotpos : ¬ 0 < t := not_lt_of_ge htneg.le
    simp [g, hnotpos, neg_pos.mpr htneg, abs_of_neg htneg]
  · have hnotneg : ¬ t < 0 := not_lt_of_ge htpos.le
    simp [g, htpos, hnotneg, abs_of_pos htpos]

private theorem integrable_thetaCuspCompletedProductFiberWignerIntegrand_one_zero
    (b : ℝ) :
    Integrable (thetaCuspCompletedProductFiberWignerIntegrand 1 0 b) := by
  have hamp : Integrable (fun t : ℝ =>
      (firstCompletedFiberHalfAmplitude |t| : ℂ)) :=
    integrable_firstCompletedFiberHalfAmplitude_abs.ofReal
  have hraw : Integrable (fun t : ℝ =>
      (firstCompletedFiberHalfAmplitude |t| : ℂ) *
        thetaWignerDifferencePhase b t) := by
    apply hamp.mul_bdd (c := 1)
    · exact (by
        unfold thetaWignerDifferencePhase
        fun_prop : Continuous fun t : ℝ => thetaWignerDifferencePhase b t)
        |>.aestronglyMeasurable
    · filter_upwards with t
      unfold thetaWignerDifferencePhase
      simpa [mul_assoc] using
        le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * b * t))
  exact hraw.congr (Eventually.of_forall fun t =>
    (thetaCuspCompletedProductFiberWignerIntegrand_one_zero b t).symm)

theorem thetaCuspCompletedWignerProductFiber_one_zero_re_eq_halfCosine
    (b : ℝ) :
    (thetaCuspCompletedWignerProductFiber 1 0 b).re =
      2 * ∫ t : ℝ in Ioi 0,
        firstCompletedFiberHalfAmplitude t * Real.cos (2 * b * t) := by
  let F : ℝ → ℂ := thetaCuspCompletedProductFiberWignerIntegrand 1 0 b
  have hF : Integrable F :=
    integrable_thetaCuspCompletedProductFiberWignerIntegrand_one_zero b
  have hsplit := integral_eq_integral_Ioi_add_reflect hF
  have hpair (t : ℝ) (ht : 0 ≤ t) :
      (F t + F (-t)).re =
        2 * firstCompletedFiberHalfAmplitude t * Real.cos (2 * b * t) := by
    dsimp only [F]
    rw [thetaCuspCompletedProductFiberWignerIntegrand_one_zero b t,
      thetaCuspCompletedProductFiberWignerIntegrand_one_zero b (-t),
      abs_neg, abs_of_nonneg ht]
    unfold thetaWignerDifferencePhase
    rw [show (2 * b * -t : ℝ) = -(2 * b * t) by ring]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero,
      Real.cos_neg]
    ring
  have hpairInt : IntegrableOn (fun t : ℝ => F t + F (-t)) (Ioi 0) :=
    hF.integrableOn.add hF.comp_neg.integrableOn
  have hre :
      (∫ t : ℝ in Ioi 0, F t + F (-t)).re =
        ∫ t : ℝ in Ioi 0,
          2 * firstCompletedFiberHalfAmplitude t * Real.cos (2 * b * t) := by
    calc
      (∫ t : ℝ in Ioi 0, F t + F (-t)).re =
          ∫ t : ℝ in Ioi 0, (F t + F (-t)).re :=
        (integral_re hpairInt).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpair t ht.le
  rw [thetaCuspCompletedWignerProductFiber_one_zero_eq_integral,
    hsplit, hre]
  rw [show (fun t : ℝ =>
      2 * firstCompletedFiberHalfAmplitude t * Real.cos (2 * b * t)) =
      fun t : ℝ => 2 *
        (firstCompletedFiberHalfAmplitude t * Real.cos (2 * b * t)) by
      funext t
      ring,
    integral_const_mul]

/-- The modularly completed first product fibre has negative Wigner spectrum at a positive
frequency.  Hence product-fibrewise Wigner positivity cannot prove the TCD/Hedenmalm sign;
any surviving proof must use cancellation between distinct product fibres. -/
theorem exists_pos_thetaCuspCompletedWignerProductFiber_one_zero_re_neg :
    ∃ b : ℝ, 0 < b ∧
      (thetaCuspCompletedWignerProductFiber 1 0 b).re < 0 := by
  obtain ⟨omega, hneg, hpos⟩ :=
    (eventually_firstCompletedFiberHalfCosine_neg.and
      (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨omega / 2, half_pos hpos, ?_⟩
  rw [thetaCuspCompletedWignerProductFiber_one_zero_re_eq_halfCosine]
  have hfreq :
      (∫ t : ℝ in Ioi 0,
        firstCompletedFiberHalfAmplitude t * Real.cos (2 * (omega / 2) * t)) =
      ∫ t : ℝ in Ioi 0,
        firstCompletedFiberHalfAmplitude t * Real.cos (omega * t) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [show 2 * (omega / 2) * t = omega * t by ring]
  rw [hfreq]
  exact mul_neg_of_pos_of_neg (by norm_num) hneg

/-- **Completed product-fibrewise Wigner positivity is false.** -/
theorem not_forall_thetaCuspCompletedWignerProductFiber_one_zero_re_nonneg :
    ¬ ∀ b : ℝ, 0 ≤ (thetaCuspCompletedWignerProductFiber 1 0 b).re := by
  obtain ⟨b, _hb, hneg⟩ :=
    exists_pos_thetaCuspCompletedWignerProductFiber_one_zero_re_neg
  exact fun h => (not_le_of_gt hneg) (h b)

end

end RHTower
