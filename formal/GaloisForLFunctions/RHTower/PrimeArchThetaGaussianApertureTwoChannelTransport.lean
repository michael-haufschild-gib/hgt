import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureHeightLocalizedContraction

/-!
# Two-channel score transport for the theta Gaussian aperture

The positive `p=4` first-atom channel and its signed `p=2` correction differ by the exact
likelihood `exp(-2x)`.  Combining that shift with the physical source score and its global
`3*pi*x^2` coercive residual gives a quantitative transport law between their adjacent moment
ratios.  The resulting RMS-height collar controls both the relative loss of the correction ratio
and the adjacent variation of the amplitude multiplier that enters second-degree curvature.

These are source-specific consequences of the completed theta atom.  They do not assert GABTC or
RH; the remaining curvature problem is to compare this explicit distortion with the positive
large-degree curvature of the leading channel.
-/

open Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Positive density of the aperture-tilted `p=2` correction channel. -/
def thetaCuspGaussianApertureCorrectionChannelWeight (lambda x : ℝ) : ℝ :=
  Real.exp (lambda * x ^ 2 + 5 * x / 2 - Real.pi * Real.exp (2 * x))

theorem thetaCuspGaussianApertureCorrectionChannelWeight_eq (lambda x : ℝ) :
    thetaCuspGaussianApertureCorrectionChannelWeight lambda x =
      Real.exp (lambda * x ^ 2) * thetaCuspPolynomialAtom (X ^ 2) 1 x := by
  simp only [thetaCuspGaussianApertureCorrectionChannelWeight, thetaCuspPolynomialAtom, Nat.cast_one,
    one_mul, eval_pow, eval_X]
  have hsq : Real.exp x ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem hasDerivAt_thetaCuspGaussianApertureCorrectionChannelWeight (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureCorrectionChannelWeight lambda)
      ((2 * lambda * x + 5 / 2 - 2 * Real.pi * Real.exp (2 * x)) *
        thetaCuspGaussianApertureCorrectionChannelWeight lambda x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have harg : HasDerivAt
      (fun y : ℝ => lambda * y ^ 2 + 5 * y / 2 - Real.pi * Real.exp (2 * y))
      (2 * lambda * x + 5 / 2 - 2 * Real.pi * Real.exp (2 * x)) x := by
    have hquad := ((hasDerivAt_id x).pow 2).const_mul lambda
    have hlin := ((hasDerivAt_id x).const_mul 5).div_const 2
    have htail := hexp.const_mul Real.pi
    convert (hquad.add hlin).sub htail using 1
    all_goals simp only [id_eq]
    all_goals ring
  change HasDerivAt
    (fun y : ℝ => Real.exp
      (lambda * y ^ 2 + 5 * y / 2 - Real.pi * Real.exp (2 * y)))
    ((2 * lambda * x + 5 / 2 - 2 * Real.pi * Real.exp (2 * x)) *
      Real.exp (lambda * x ^ 2 + 5 * x / 2 - Real.pi * Real.exp (2 * x))) x
  simpa only [Function.comp_apply, mul_comm] using
    (Real.hasDerivAt_exp _).comp x harg

private theorem exp_two_mul_thetaCuspPolynomialAtom_two_eq_four (x : ℝ) :
    Real.exp (2 * x) * thetaCuspPolynomialAtom (X ^ 2) 1 x =
      thetaCuspPolynomialAtom (X ^ 4) 1 x := by
  simp only [thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
  have hpow : Real.exp (2 * x) * Real.exp x ^ 2 = Real.exp x ^ 4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (2 * x) *
        (Real.exp (x / 2) * Real.exp x ^ 2 *
          Real.exp (-Real.pi * Real.exp x ^ 2)) =
      Real.exp (x / 2) *
        (Real.exp (2 * x) * Real.exp x ^ 2) *
          Real.exp (-Real.pi * Real.exp x ^ 2) by ring,
    hpow]

/-- Odd height numerator of one aperture-tilted polynomial channel. -/
def thetaCuspGaussianApertureTailChannelFirstHeightMoment (lambda : ℝ) (p j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j + 1) * Real.exp (lambda * x ^ 2) *
      thetaCuspPolynomialAtom (X ^ p) 1 x

theorem integrableOn_thetaCuspGaussianApertureTailChannelFirstHeightMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (p j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j + 1) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ p) 1 x) (Ioi 0) :=
  integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda (2 * j + 1) (X ^ p)

/-- Natural score moment of the correction channel. Its score is the leading score plus `x`. -/
def thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) *
      (thetaCuspGaussianApertureExactTailSaddleDegree lambda x + x) *
        thetaCuspGaussianApertureCorrectionChannelWeight lambda x

theorem integrableOn_thetaCuspGaussianApertureCorrectionChannelNaturalScoreMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) *
        (thetaCuspGaussianApertureExactTailSaddleDegree lambda x + x) *
          thetaCuspGaussianApertureCorrectionChannelWeight lambda x) (Ioi 0) := by
  have h4one := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda (2 * j + 1) (X ^ 4)
  have h2two := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda (2 * j + 2) (X ^ 2)
  have h2one := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda (2 * j + 1) (X ^ 2)
  have hcomb := ((h4one.const_mul Real.pi).sub (h2two.const_mul lambda)).sub
    (h2one.const_mul (5 / 4 : ℝ))
  apply hcomb.congr
  filter_upwards [] with x
  simp only [Pi.sub_apply, thetaCuspGaussianApertureCorrectionChannelWeight_eq]
  rw [← exp_two_mul_thetaCuspPolynomialAtom_two_eq_four]
  unfold thetaCuspGaussianApertureExactTailSaddleDegree
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega, pow_succ,
    show 2 * j + 1 = 2 * j + 1 by rfl, pow_succ]
  ring

theorem thetaCuspGaussianApertureCorrectionChannelCurrent_tendsto_zero
    {lambda : ℝ} (j : ℕ) :
    Tendsto (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureCorrectionChannelWeight lambda x)
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureCorrectionChannelWeight lambda x) := by
    exact (continuous_id.pow _).mul
      (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspGaussianApertureCorrectionChannelWeight lambda x).continuousAt)
  have h := (hcont.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa using h

theorem thetaCuspGaussianApertureCorrectionChannelCurrent_tendsto_atTop_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Tendsto (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureCorrectionChannelWeight lambda x)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase :=
    (pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      (2 * j + 1) (X ^ 2) (n := 1) (by norm_num)).norm
  have hupper : Tendsto (fun x : ℝ =>
      ‖x ^ (2 * j + 1) * thetaCuspPolynomialAtom (X ^ 2) 1 x‖)
      atTop (𝓝 0) := by simpa using hbase
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq,
    show x ^ (2 * j + 1) *
        (Real.exp (lambda * x ^ 2) * thetaCuspPolynomialAtom (X ^ 2) 1 x) =
      Real.exp (lambda * x ^ 2) *
        (x ^ (2 * j + 1) * thetaCuspPolynomialAtom (X ^ 2) 1 x) by ring,
    norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg hlambda (sq_nonneg x)))

/-- The `p=2` channel has the same centered response value as the leading channel after its
exact one-height score shift is retained. -/
theorem thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment_eq
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment lambda j =
      thetaCuspGaussianApertureGammaShape j *
        thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
  let u : ℝ → ℝ := fun x => x ^ (2 * j + 1)
  let u' : ℝ → ℝ := fun x => (2 * j + 1 : ℝ) * x ^ (2 * j)
  let v : ℝ → ℝ := thetaCuspGaussianApertureCorrectionChannelWeight lambda
  let v' : ℝ → ℝ := fun x =>
    (2 * lambda * x + 5 / 2 - 2 * Real.pi * Real.exp (2 * x)) * v x
  have huderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
    intro x _hx
    dsimp only [u, u']
    convert hasDerivAt_pow (2 * j + 1) x using 1
    norm_num
  have hvderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x _hx
    simpa only [v, v'] using hasDerivAt_thetaCuspGaussianApertureCorrectionChannelWeight lambda x
  have hscore :=
    integrableOn_thetaCuspGaussianApertureCorrectionChannelNaturalScoreMomentIntegrand hlambda j
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    apply (hscore.const_mul (-2 : ℝ)).congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, u, v', v]
    rw [pow_succ]
    unfold thetaCuspGaussianApertureExactTailSaddleDegree
    ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have hm := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
      hlambda (2 * j) (X ^ 2)
    apply (hm.const_mul (2 * j + 1 : ℝ)).congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, u', v]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := u) (u' := u') (v := v) (v' := v')
    huderiv hvderiv huv' hu'v
    (by simpa only [u, v, Pi.mul_apply] using
      (@thetaCuspGaussianApertureCorrectionChannelCurrent_tendsto_zero lambda j))
    (by simpa only [u, v, Pi.mul_apply] using
      (@thetaCuspGaussianApertureCorrectionChannelCurrent_tendsto_atTop_zero lambda hlambda j))
  have hleft : (∫ x : ℝ in Ioi 0, u x * v' x) =
      -2 * thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment lambda j := by
    rw [thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [u, v', v]
    rw [pow_succ]
    unfold thetaCuspGaussianApertureExactTailSaddleDegree
    ring
  have hright : (∫ x : ℝ in Ioi 0, u' x * v x) =
      (2 * j + 1 : ℝ) *
        thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [u', v]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  rw [hleft, hright] at hibp
  simp only [zero_sub] at hibp
  unfold thetaCuspGaussianApertureGammaShape
  linarith

/-- Exact score transport from the leading `p=4` channel to the signed `p=2` correction. -/
theorem thetaCuspGaussianApertureTwoChannel_scoreTransport
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (3 * Real.pi) *
        (thetaCuspGaussianApertureTailChannelMoment lambda 2 j *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) -
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
            thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1)) ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
        thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x
  let h : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureCorrectionChannelWeight lambda x
  let K : ℝ → ℝ := thetaCuspGaussianApertureLeadingChannelScoreResidual lambda
  let gf : ℝ → ℝ := fun x => K x * f x
  let gh : ℝ → ℝ := fun x => K x * h x
  have hf : Integrable f mu := by
    simpa only [f, mu] using
      integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
        hlambda (2 * j)
  have hh : Integrable h mu := by
    have hm := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
      hlambda (2 * j) (X ^ 2)
    apply hm.congr
    filter_upwards [] with x
    simp only [h, thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  have hgf : Integrable gf mu := by
    have hscore :=
      integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
        hlambda j
    have hm := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 1))
    have hd := hscore.sub (hm.const_mul (3 * Real.pi))
    apply hd.congr
    filter_upwards [] with x
    simp only [gf, K, f, thetaCuspGaussianApertureLeadingChannelScoreResidual,
      Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hgh : Integrable gh mu := by
    have hscore := integrableOn_thetaCuspGaussianApertureCorrectionChannelNaturalScoreMomentIntegrand
      hlambda j
    have hheight := integrableOn_thetaCuspGaussianApertureTailChannelFirstHeightMomentIntegrand
      hlambda 2 j
    have hnext := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
      hlambda (2 * (j + 1)) (X ^ 2)
    have hd := (hscore.sub hheight).sub (hnext.const_mul (3 * Real.pi))
    apply hd.congr
    filter_upwards [] with x
    simp only [gh, K, h, thetaCuspGaussianApertureLeadingChannelScoreResidual,
      thetaCuspGaussianApertureCorrectionChannelWeight_eq, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    simp only [pow_succ]
    ring
  have hmono :=
    thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn hlambda
  have hmem : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      z ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      0 ≤ (K z.2 - K z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1) := by
    filter_upwards [hmem] with z hz
    rcases hz with ⟨hx, hy⟩
    have fbase (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 ≤ f t := by
      dsimp only [f]
      exact mul_nonneg (pow_nonneg ht.le _) (Real.exp_nonneg _)
    have hlikelihood (t : ℝ) : h t = Real.exp (-2 * t) * f t := by
      dsimp only [h, f]
      rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq,
        thetaCuspGaussianApertureLeadingChannelWeight_eq,
        thetaCuspPolynomialAtom_two_eq_exp_neg_two_mul_four]
      ring
    rcases le_total z.1 z.2 with hxy | hyx
    · have hKdiff : 0 ≤ K z.2 - K z.1 :=
        sub_nonneg.mpr (hmono.monotoneOn hx hy hxy)
      have hediff : 0 ≤ Real.exp (-2 * z.1) - Real.exp (-2 * z.2) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
      have hbracket : 0 ≤ h z.1 * f z.2 - h z.2 * f z.1 := by
        rw [hlikelihood z.1, hlikelihood z.2]
        rw [show (Real.exp (-2 * z.1) * f z.1) * f z.2 -
              (Real.exp (-2 * z.2) * f z.2) * f z.1 =
            (f z.1 * f z.2) *
              (Real.exp (-2 * z.1) - Real.exp (-2 * z.2)) by
          ring]
        exact mul_nonneg (mul_nonneg (fbase z.1 hx) (fbase z.2 hy)) hediff
      exact mul_nonneg hKdiff hbracket
    · have hKdiff : 0 ≤ K z.1 - K z.2 :=
        sub_nonneg.mpr (hmono.monotoneOn hy hx hyx)
      have hediff : 0 ≤ Real.exp (-2 * z.2) - Real.exp (-2 * z.1) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
      have hbracket : 0 ≤ h z.2 * f z.1 - h z.1 * f z.2 := by
        rw [hlikelihood z.2, hlikelihood z.1]
        rw [show (Real.exp (-2 * z.2) * f z.2) * f z.1 -
              (Real.exp (-2 * z.1) * f z.1) * f z.2 =
            (f z.2 * f z.1) *
              (Real.exp (-2 * z.2) - Real.exp (-2 * z.1)) by
          ring]
        exact mul_nonneg (mul_nonneg (fbase z.2 hy) (fbase z.1 hx)) hediff
      nlinarith
  have hcross :=
    HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
      hf hh (by simpa only [gf] using hgf) (by simpa only [gh] using hgh) hkernel
  have hfval : (∫ x, f x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f]
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
    ring
  have hhval : (∫ x, h x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [h]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  have hgfval : (∫ x, gf x ∂mu) =
      thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
    simp only [gf, K]
    unfold thetaCuspGaussianApertureLeadingChannelScoreResidual
    rw [thetaCuspGaussianApertureLeadingChannelScoreMoment,
      thetaCuspGaussianApertureTailChannelMoment, ← integral_const_mul]
    rw [← integral_sub
      (integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
        hlambda j)
      ((integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
        hlambda (2 * (j + 1)) (X ^ 4)).const_mul (3 * Real.pi))]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f]
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq,
      show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hghval : (∫ x, gh x ∂mu) =
      thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment lambda j -
        thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1) := by
    let A : ℝ → ℝ := fun x =>
      x ^ (2 * j) *
        (thetaCuspGaussianApertureExactTailSaddleDegree lambda x + x) *
          thetaCuspGaussianApertureCorrectionChannelWeight lambda x
    let B : ℝ → ℝ := fun x =>
      x ^ (2 * j + 1) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ 2) 1 x
    let C : ℝ → ℝ := fun x =>
      (3 * Real.pi) *
        (x ^ (2 * (j + 1)) * Real.exp (lambda * x ^ 2) *
          thetaCuspPolynomialAtom (X ^ 2) 1 x)
    have hA : IntegrableOn A (Ioi 0) := by
      simpa only [A] using
        integrableOn_thetaCuspGaussianApertureCorrectionChannelNaturalScoreMomentIntegrand
          hlambda j
    have hB : IntegrableOn B (Ioi 0) := by
      simpa only [B] using
        integrableOn_thetaCuspGaussianApertureTailChannelFirstHeightMomentIntegrand
          hlambda 2 j
    have hC : IntegrableOn C (Ioi 0) := by
      exact (integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
        hlambda (2 * (j + 1)) (X ^ 2)).const_mul (3 * Real.pi)
    calc
      (∫ x, gh x ∂mu) = ∫ x : ℝ in Ioi 0, A x - B x - C x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [gh, K, h, A, B, C,
          thetaCuspGaussianApertureLeadingChannelScoreResidual]
        rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq,
          show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
        ring
      _ = (∫ x : ℝ in Ioi 0, A x - B x) -
          ∫ x : ℝ in Ioi 0, C x := by
        simpa only [Pi.sub_apply] using integral_sub (hA.sub hB) hC
      _ = (∫ x : ℝ in Ioi 0, A x) - (∫ x : ℝ in Ioi 0, B x) -
          ∫ x : ℝ in Ioi 0, C x := by
        rw [integral_sub hA hB]
      _ = thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment lambda j -
          thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j -
          (3 * Real.pi) *
            thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1) := by
        simp only [A, B, C,
          thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment,
          thetaCuspGaussianApertureTailChannelFirstHeightMoment,
          thetaCuspGaussianApertureTailChannelMoment, integral_const_mul]
  rw [hfval, hhval, hgfval, hghval,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda,
    thetaCuspGaussianApertureCorrectionChannelNaturalScoreMoment_eq hlambda] at hcross
  nlinarith

/-- Raw adjacent ratio of either positive polynomial channel. -/
def thetaCuspGaussianApertureTailChannelMomentRatio (lambda : ℝ) (p j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelMoment lambda p (j + 1) /
    thetaCuspGaussianApertureTailChannelMoment lambda p j

theorem thetaCuspGaussianApertureTailChannelMomentRatio_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (p j : ℕ) :
    0 < thetaCuspGaussianApertureTailChannelMomentRatio lambda p j := by
  rw [thetaCuspGaussianApertureTailChannelMomentRatio]
  exact div_pos
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda p (j + 1))
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda p j)

theorem thetaCuspGaussianApertureTailChannelFirstHeightMoment_nonneg
    {lambda : ℝ} (p j : ℕ) :
    0 ≤ thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda p j := by
  rw [thetaCuspGaussianApertureTailChannelFirstHeightMoment]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)) (by
      simp only [thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
      positivity)

/-- Cauchy pins the first-height numerator of the correction channel between its adjacent even
moments. -/
theorem thetaCuspGaussianApertureCorrectionChannelFirstHeightMoment_sq_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j ^ 2 ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 2 j *
        thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let base : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureCorrectionChannelWeight lambda x
  let f : ℝ → ℝ := fun x => Real.sqrt (base x)
  let g : ℝ → ℝ := fun x => x * Real.sqrt (base x)
  have hbase (x : ℝ) : 0 ≤ base x := by
    dsimp only [base]
    have hxpow : 0 ≤ x ^ (2 * j) := by
      rw [show 2 * j = j * 2 by omega, pow_mul]
      positivity
    exact mul_nonneg hxpow (Real.exp_nonneg _)
  have hfmeas : AEStronglyMeasurable f mu := by
    exact Continuous.aestronglyMeasurable
      (Real.continuous_sqrt.comp
        ((continuous_id.pow _).mul
          (continuous_iff_continuousAt.mpr fun x =>
            (hasDerivAt_thetaCuspGaussianApertureCorrectionChannelWeight lambda x).continuousAt)))
  have hgmeas : AEStronglyMeasurable g mu := by
    exact Continuous.aestronglyMeasurable
      (continuous_id.mul
        (Real.continuous_sqrt.comp
          ((continuous_id.pow _).mul
            (continuous_iff_continuousAt.mpr fun x =>
              (hasDerivAt_thetaCuspGaussianApertureCorrectionChannelWeight lambda x).continuousAt))))
  have hfint : Integrable (fun x => f x ^ 2) mu := by
    have hm := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
      hlambda (2 * j) (X ^ 2)
    apply hm.congr
    filter_upwards [] with x
    simp only [f]
    rw [Real.sq_sqrt (hbase x)]
    dsimp only [base]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  have hgint : Integrable (fun x => g x ^ 2) mu := by
    have hm := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
      hlambda (2 * (j + 1)) (X ^ 2)
    apply hm.congr
    filter_upwards [] with x
    simp only [g, mul_pow]
    rw [Real.sq_sqrt (hbase x)]
    dsimp only [base]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    hfmeas hgmeas hfint hgint
  have hfg : (∫ x, f x * g x ∂mu) =
      thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j := by
    rw [thetaCuspGaussianApertureTailChannelFirstHeightMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f, g]
    rw [show Real.sqrt (base x) * (x * Real.sqrt (base x)) = x * base x by
      calc
        Real.sqrt (base x) * (x * Real.sqrt (base x)) =
            x * Real.sqrt (base x) ^ 2 := by ring
        _ = x * base x := by rw [Real.sq_sqrt (hbase x)]]
    dsimp only [base]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    rw [pow_succ]
    ring
  have hf2 : (∫ x, f x ^ 2 ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f]
    rw [Real.sq_sqrt (hbase x)]
    dsimp only [base]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    ring
  have hg2 : (∫ x, g x ^ 2 ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1) := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, mul_pow]
    rw [Real.sq_sqrt (hbase x)]
    dsimp only [base]
    rw [thetaCuspGaussianApertureCorrectionChannelWeight_eq]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  rwa [hfg, hf2, hg2] at hcs

/-- The normalized first height of the correction channel is at most its RMS height. -/
theorem thetaCuspGaussianApertureCorrectionChannelMeanHeight_le_sqrt_ratio
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j /
        thetaCuspGaussianApertureTailChannelMoment lambda 2 j ≤
      Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j) := by
  let A0 := thetaCuspGaussianApertureTailChannelMoment lambda 2 j
  let A1 := thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1)
  let H := thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j
  let r := A1 / A0
  have hA0 : 0 < A0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 j
  have hA1 : 0 < A1 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 (j + 1)
  have hH : 0 ≤ H :=
    thetaCuspGaussianApertureTailChannelFirstHeightMoment_nonneg (lambda := lambda) 2 j
  have hsq : H ^ 2 ≤ A0 * A1 := by
    simpa only [A0, A1, H] using thetaCuspGaussianApertureCorrectionChannelFirstHeightMoment_sq_le hlambda j
  have hr : 0 ≤ r := (div_pos hA1 hA0).le
  have hdivsq : (H / A0) ^ 2 ≤ r := by
    dsimp only [r]
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hA0)).2 (by
      field_simp [hA0.ne']
      nlinarith)
  have hsqrt := Real.sq_sqrt hr
  have hroot : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hratio : 0 ≤ H / A0 := div_nonneg hH hA0.le
  rw [thetaCuspGaussianApertureTailChannelMomentRatio]
  dsimp only [A0, A1, H, r] at hdivsq hsqrt hroot hratio ⊢
  nlinarith

/-- Normalized score transport: the leading and correction channels have adjacent moment ratios
whose gap is controlled by the correction channel's literal mean height. -/
theorem thetaCuspGaussianApertureTwoChannel_ratioGap_le_meanHeight
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (3 * Real.pi) *
        (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j -
          thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j) ≤
      thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j /
        thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let A0 := thetaCuspGaussianApertureTailChannelMoment lambda 2 j
  let A1 := thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1)
  let H := thetaCuspGaussianApertureTailChannelFirstHeightMoment lambda 2 j
  have hC0 : 0 < C0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hA0 : 0 < A0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 j
  have hraw := thetaCuspGaussianApertureTwoChannel_scoreTransport hlambda j
  rw [thetaCuspGaussianApertureTailChannelMomentRatio, thetaCuspGaussianApertureTailChannelMomentRatio]
  change (3 * Real.pi) * (C1 / C0 - A1 / A0) ≤ H / A0
  change (3 * Real.pi) * (A0 * C1 - C0 * A1) ≤ C0 * H at hraw
  have hleft : (3 * Real.pi) * (C1 / C0 - A1 / A0) =
      ((3 * Real.pi) * (A0 * C1 - C0 * A1)) / (C0 * A0) := by
    field_simp [hC0.ne', hA0.ne']
  have hright : H / A0 = (C0 * H) / (C0 * A0) := by
    field_simp [hC0.ne', hA0.ne']
  rw [hleft, hright]
  exact (div_le_div_iff_of_pos_right (mul_pos hC0 hA0)).2 hraw

/-- The positive `p=4` saddle channel has no smaller RMS height than the signed `p=2`
correction channel. -/
theorem thetaCuspGaussianApertureTwoChannel_ratio_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j ≤
      thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j := by
  rw [thetaCuspGaussianApertureTailChannelMomentRatio, thetaCuspGaussianApertureTailChannelMomentRatio]
  exact (div_le_div_iff₀
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 j)
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j)).2 (by
      simpa only [mul_comm] using
        thetaCuspGaussianApertureTailChannel_two_succ_mul_four_le hlambda j)

/-- **Two-channel RMS transport collar.** The score shift `J₂-J₄=x` and the global `3*pi`
residual coercivity force the RMS heights of the signed correction and positive saddle channels
to stay within `1/(6*pi)` at every degree and every physical aperture. -/
theorem thetaCuspGaussianApertureTwoChannel_sqrtRatioGap_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j) -
        Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j) ≤
      1 / (6 * Real.pi) := by
  let a := Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j)
  let b := Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j)
  have hR4 : 0 < thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j :=
    thetaCuspGaussianApertureTailChannelMomentRatio_pos hlambda 4 j
  have hR2 : 0 < thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j :=
    thetaCuspGaussianApertureTailChannelMomentRatio_pos hlambda 2 j
  have hba : b ≤ a := Real.sqrt_le_sqrt (thetaCuspGaussianApertureTwoChannel_ratio_le hlambda j)
  have hb : 0 < b := Real.sqrt_pos.2 hR2
  have hapi : 0 < 3 * Real.pi := by positivity
  have hsqa : a ^ 2 = thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j :=
    Real.sq_sqrt hR4.le
  have hsqb : b ^ 2 = thetaCuspGaussianApertureTailChannelMomentRatio lambda 2 j :=
    Real.sq_sqrt hR2.le
  have hgap := thetaCuspGaussianApertureTwoChannel_ratioGap_le_meanHeight hlambda j
  have hmean := thetaCuspGaussianApertureCorrectionChannelMeanHeight_le_sqrt_ratio hlambda j
  have hcore : (3 * Real.pi) * (a ^ 2 - b ^ 2) ≤ b := by
    rw [hsqa, hsqb]
    exact hgap.trans hmean
  have hdiff : 0 ≤ a - b := sub_nonneg.mpr hba
  have hsum : 2 * b ≤ a + b := by linarith
  have hprod : (6 * Real.pi * (a - b)) * b ≤ 1 * b := by
    calc
      (6 * Real.pi * (a - b)) * b =
          (3 * Real.pi) * (a - b) * (2 * b) := by ring
      _ ≤ (3 * Real.pi) * (a - b) * (a + b) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hapi.le hdiff)
      _ = (3 * Real.pi) * (a ^ 2 - b ^ 2) := by ring
      _ ≤ b := hcore
      _ = 1 * b := by ring
  have hscaled : 6 * Real.pi * (a - b) ≤ 1 :=
    (mul_le_mul_iff_of_pos_right hb).mp hprod
  have htarget : a - b ≤ 1 / (6 * Real.pi) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Real.pi)).2 (by
      simpa only [one_div, mul_comm] using hscaled)
  simpa only [a, b] using htarget

/-- The signed correction ratio loses at most one inverse RMS-score unit per degree.  This is the
relative form of the two-channel transport law. -/
theorem thetaCuspGaussianApertureTailCorrectionRatio_relativeDecrement
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (3 * Real.pi) * Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j) *
        (thetaCuspGaussianApertureTailCorrectionRatio lambda j -
          thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)) ≤
      thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let A0 := thetaCuspGaussianApertureTailChannelMoment lambda 2 j
  let A1 := thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1)
  let r4 := C1 / C0
  let r2 := A1 / A0
  let rho := A0 / C0
  let rho' := A1 / C1
  let s := Real.sqrt r4
  have hC0 : 0 < C0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hC1 : 0 < C1 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1)
  have hA0 : 0 < A0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 j
  have hA1 : 0 < A1 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 (j + 1)
  have hr4 : 0 < r4 := div_pos hC1 hC0
  have hrho : 0 < rho := div_pos hA0 hC0
  have hs : 0 < s := Real.sqrt_pos.2 hr4
  have hs2 : s ^ 2 = r4 := Real.sq_sqrt hr4.le
  have hgap := thetaCuspGaussianApertureTwoChannel_ratioGap_le_meanHeight hlambda j
  have hmean := thetaCuspGaussianApertureCorrectionChannelMeanHeight_le_sqrt_ratio hlambda j
  have hroot := Real.sqrt_le_sqrt (thetaCuspGaussianApertureTwoChannel_ratio_le hlambda j)
  have hcore : (3 * Real.pi) * (r4 - r2) ≤ s := by
    dsimp only [r4, r2, s]
    exact hgap.trans (hmean.trans hroot)
  have hid : r4 * (rho - rho') = rho * (r4 - r2) := by
    dsimp only [r4, r2, rho, rho']
    field_simp [hC0.ne', hC1.ne', hA0.ne']
  have hmul : (3 * Real.pi) * (rho * (r4 - r2)) ≤ rho * s := by
    convert mul_le_mul_of_nonneg_left hcore hrho.le using 1
    all_goals ring
  rw [← hid] at hmul
  have hcancel : s * ((3 * Real.pi) * s * (rho - rho')) ≤ s * rho := by
    rw [show s * ((3 * Real.pi) * s * (rho - rho')) =
        (3 * Real.pi) * (s ^ 2 * (rho - rho')) by ring,
      hs2]
    simpa only [mul_assoc, mul_comm] using hmul
  have hfinal : (3 * Real.pi) * s * (rho - rho') ≤ rho :=
    (mul_le_mul_iff_of_pos_left hs).mp hcancel
  dsimp only [s, r4, rho, rho'] at hfinal
  simpa only [thetaCuspGaussianApertureTailChannelMomentRatio,
    thetaCuspGaussianApertureTailCorrectionRatio, C0, C1, A0, A1] using hfinal

/-- The monotone amplitude factor changes by at most its correction mass divided by the literal
RMS response scale. -/
theorem thetaCuspGaussianApertureTailAmplitudeFactor_scaledIncrement_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    2 * Real.pi ^ 2 * Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j) *
        (thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) -
          thetaCuspGaussianApertureTailAmplitudeFactor lambda j) ≤
      thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
  have hdelta := thetaCuspGaussianApertureTailCorrectionRatio_relativeDecrement hlambda j
  have hid :
      thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) -
          thetaCuspGaussianApertureTailAmplitudeFactor lambda j =
        (3 / (2 * Real.pi)) *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda j -
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)) := by
    rw [thetaCuspGaussianApertureTailAmplitudeFactor,
      thetaCuspGaussianApertureTailAmplitudeFactor]
    ring
  rw [hid]
  convert hdelta using 1
  field_simp [Real.pi_ne_zero]

/-- The multiplicative signed-amplitude correction differs from one by at most one inverse
RMS-score unit times the current correction mass. -/
theorem thetaCuspGaussianApertureTailAmplitudeMultiplier_scaledExcess_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Real.pi ^ 2 * Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j) *
        (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j - 1) ≤
      thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
  let d := thetaCuspGaussianApertureTailAmplitudeFactor lambda j
  let d' := thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1)
  let m := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j
  let s := Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j)
  have hd : 0 < d := thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j
  have hhalf : (1 / 2 : ℝ) < d := by
    simpa only [d] using one_half_lt_thetaCuspGaussianApertureTailAmplitudeFactor hlambda j
  have hinc : 0 ≤ d' - d := sub_nonneg.mpr
    (thetaCuspGaussianApertureTailAmplitudeFactor_le_succ hlambda j)
  have hm : m - 1 = (d' - d) / d := by
    change d' / d - 1 = (d' - d) / d
    field_simp [hd.ne']
  have hmle : m - 1 ≤ 2 * (d' - d) := by
    rw [hm, div_le_iff₀ hd]
    nlinarith [mul_nonneg hinc hd.le]
  have hscale : 0 ≤ Real.pi ^ 2 * s := by positivity
  have hbound := thetaCuspGaussianApertureTailAmplitudeFactor_scaledIncrement_le hlambda j
  calc
    Real.pi ^ 2 * s * (m - 1) ≤
        Real.pi ^ 2 * s * (2 * (d' - d)) :=
      mul_le_mul_of_nonneg_left hmle hscale
    _ = 2 * Real.pi ^ 2 * s * (d' - d) := by ring
    _ ≤ thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
      simpa only [s, d, d'] using hbound

/-- **Second-degree signed-channel distortion bound.**  The adjacent motion of the amplitude
multiplier is controlled by the two neighboring correction masses, at the smaller of their
literal RMS response scales. -/
theorem thetaCuspGaussianApertureTailAmplitudeMultiplier_adjacentVariation
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Real.pi ^ 2 *
        min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
        |thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) -
          thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j| ≤
      thetaCuspGaussianApertureTailCorrectionRatio lambda j +
        thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) := by
  let s0 := Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j)
  let s1 := Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))
  let m0 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j
  let m1 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)
  let rho0 := thetaCuspGaussianApertureTailCorrectionRatio lambda j
  let rho1 := thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)
  have hs0 : 0 ≤ s0 := Real.sqrt_nonneg _
  have hs1 : 0 ≤ s1 := Real.sqrt_nonneg _
  have hm0 : 1 ≤ m0 := one_le_thetaCuspGaussianApertureTailAmplitudeMultiplier hlambda j
  have hm1 : 1 ≤ m1 :=
    one_le_thetaCuspGaussianApertureTailAmplitudeMultiplier hlambda (j + 1)
  have habs : |m1 - m0| ≤ (m0 - 1) + (m1 - 1) := by
    calc
      |m1 - m0| = |(m1 - 1) - (m0 - 1)| := by ring_nf
      _ ≤ |m1 - 1| + |m0 - 1| := abs_sub _ _
      _ = (m0 - 1) + (m1 - 1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hm1),
          abs_of_nonneg (sub_nonneg.mpr hm0)]
        ring
  have hmin : 0 ≤ min s0 s1 := le_min hs0 hs1
  have hscale : 0 ≤ Real.pi ^ 2 * min s0 s1 := mul_nonneg (sq_nonneg _) hmin
  have h0 := thetaCuspGaussianApertureTailAmplitudeMultiplier_scaledExcess_le hlambda j
  have h1 := thetaCuspGaussianApertureTailAmplitudeMultiplier_scaledExcess_le hlambda (j + 1)
  have h0' : Real.pi ^ 2 * min s0 s1 * (m0 - 1) ≤ rho0 := by
    calc
      Real.pi ^ 2 * min s0 s1 * (m0 - 1) ≤
          Real.pi ^ 2 * s0 * (m0 - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (min_le_left s0 s1) (sq_nonneg Real.pi))
          (sub_nonneg.mpr hm0)
      _ ≤ rho0 := by simpa only [s0, m0, rho0] using h0
  have h1' : Real.pi ^ 2 * min s0 s1 * (m1 - 1) ≤ rho1 := by
    calc
      Real.pi ^ 2 * min s0 s1 * (m1 - 1) ≤
          Real.pi ^ 2 * s1 * (m1 - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (min_le_right s0 s1) (sq_nonneg Real.pi))
          (sub_nonneg.mpr hm1)
      _ ≤ rho1 := by simpa only [s1, m1, rho1] using h1
  calc
    Real.pi ^ 2 * min s0 s1 * |m1 - m0| ≤
        Real.pi ^ 2 * min s0 s1 * ((m0 - 1) + (m1 - 1)) :=
      mul_le_mul_of_nonneg_left habs hscale
    _ = Real.pi ^ 2 * min s0 s1 * (m0 - 1) +
        Real.pi ^ 2 * min s0 s1 * (m1 - 1) := by ring
    _ ≤ rho0 + rho1 := add_le_add h0' h1'

/-! ### Exact Gaussian reference collar -/

/-- The global residual score is strictly increasing already on the closed positive ray. -/
theorem thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn_Ici_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictMonoOn (thetaCuspGaussianApertureLeadingChannelScoreResidual lambda) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x _hx
    exact (hasDerivAt_thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    rw [(hasDerivAt_thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x).deriv]
    exact thetaCuspGaussianApertureLeadingChannelScoreResidualSlope_pos hlambda hx

/-- The exact source score lies strictly above its `3*pi*x^2` Gaussian reference at every
positive height. -/
theorem thetaCuspGaussianApertureLeadingChannelScoreResidual_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 0 < x) :
    0 < thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x := by
  have hmono :=
    thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn_Ici_zero hlambda
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx.le) hx
  have hzero :
      thetaCuspGaussianApertureLeadingChannelScoreResidual lambda 0 = 0 := by
    simp [thetaCuspGaussianApertureLeadingChannelScoreResidual,
      thetaCuspGaussianApertureExactTailSaddleDegree]
  rwa [hzero] at h

/-- Unnormalized mass of the positive residual above the exact Gaussian reference. -/
def thetaCuspGaussianApertureLeadingChannelScoreResidualMoment
    (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x *
      thetaCuspGaussianApertureLeadingChannelWeight lambda x

theorem integrableOn_thetaCuspGaussianApertureLeadingChannelScoreResidualMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x *
        thetaCuspGaussianApertureLeadingChannelWeight lambda x) (Ioi 0) := by
  have hscore :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand hlambda j
  have hnext := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
    hlambda (2 * (j + 1))
  apply (hscore.sub (hnext.const_mul (3 * Real.pi))).congr
  filter_upwards [] with x
  simp only [thetaCuspGaussianApertureLeadingChannelScoreResidual, Pi.sub_apply]
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
  ring

theorem thetaCuspGaussianApertureLeadingChannelScoreResidualMoment_eq
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureLeadingChannelScoreResidualMoment lambda j =
      thetaCuspGaussianApertureGammaShape j *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
  calc
    thetaCuspGaussianApertureLeadingChannelScoreResidualMoment lambda j =
        thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j -
          (3 * Real.pi) *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
      rw [thetaCuspGaussianApertureLeadingChannelScoreResidualMoment,
        thetaCuspGaussianApertureLeadingChannelScoreMoment,
        thetaCuspGaussianApertureTailChannelMoment, ← integral_const_mul]
      rw [← integral_sub
        (integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand hlambda j)
        ((integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
          hlambda (2 * (j + 1)) (X ^ 4)).const_mul (3 * Real.pi))]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [thetaCuspGaussianApertureLeadingChannelWeight_eq,
        show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      simp only [thetaCuspGaussianApertureLeadingChannelScoreResidual]
      ring
    _ = thetaCuspGaussianApertureGammaShape j *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
      rw [thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda]

theorem thetaCuspGaussianApertureLeadingChannelScoreResidualMoment_nonneg
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 ≤ thetaCuspGaussianApertureLeadingChannelScoreResidualMoment lambda j := by
  rw [thetaCuspGaussianApertureLeadingChannelScoreResidualMoment]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hx.le _) (thetaCuspGaussianApertureLeadingChannelScoreResidual_pos
      hlambda hx).le)
    (by
      unfold thetaCuspGaussianApertureLeadingChannelWeight
      exact (Real.exp_pos _).le)

/-- **Gaussian reference collar.**  Every positive leading-channel gamma-normalized ratio lies
below the aperture-independent Gaussian value `1/(3*pi)`. -/
theorem thetaCuspGaussianApertureTailChannelGammaRatio_four_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j /
        thetaCuspGaussianApertureGammaShape j ≤
      1 / (3 * Real.pi) := by
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let a := thetaCuspGaussianApertureGammaShape j
  have hC0 : 0 < C0 := thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have ha : 0 < a := thetaCuspGaussianApertureGammaShape_pos j
  have hpi : 0 < 3 * Real.pi := by positivity
  have hres := thetaCuspGaussianApertureLeadingChannelScoreResidualMoment_nonneg hlambda j
  rw [thetaCuspGaussianApertureLeadingChannelScoreResidualMoment_eq hlambda] at hres
  have hraw : (3 * Real.pi) * C1 ≤ a * C0 := by
    dsimp only [C0, C1, a]
    linarith
  rw [thetaCuspGaussianApertureTailChannelMomentRatio]
  change (C1 / C0) / a ≤ 1 / (3 * Real.pi)
  rw [div_le_iff₀ ha, div_le_iff₀ hC0]
  calc
    C1 ≤ (a * C0) / (3 * Real.pi) :=
      (le_div_iff₀ hpi).2 (by simpa only [mul_comm] using hraw)
    _ = (1 / (3 * Real.pi) * a) * C0 := by
      field_simp [Real.pi_ne_zero]

/-! ### Exact second-degree transport into the signed first atom -/

/-- Gamma-normalized adjacent ratio of one positive polynomial channel. -/
def thetaCuspGaussianApertureTailChannelGammaRatio
    (lambda : ℝ) (p j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelMomentRatio lambda p j /
    thetaCuspGaussianApertureGammaShape j

/-- Boundary second difference of one positive channel's gamma-normalized ratios. -/
def thetaCuspGaussianApertureTailChannelRatioCurvature
    (lambda : ℝ) (p j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelGammaRatio lambda p j -
    2 * thetaCuspGaussianApertureTailChannelGammaRatio lambda p (j + 1) +
    thetaCuspGaussianApertureTailChannelGammaRatio lambda p (j + 2)

/-- Gamma-normalized adjacent ratio of the literal signed first theta atom. -/
def thetaCuspGaussianApertureFirstAtomGammaRatio
    (lambda : ℝ) (j : ℕ) : ℝ :=
  (thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) /
      thetaCuspGaussianApertureFirstAtomHalfMoment lambda j) /
    thetaCuspGaussianApertureGammaShape j

/-- Boundary second difference of the literal signed first-atom gamma ratios. -/
def thetaCuspGaussianApertureFirstAtomRatioCurvature
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureFirstAtomGammaRatio lambda j -
    2 * thetaCuspGaussianApertureFirstAtomGammaRatio lambda (j + 1) +
    thetaCuspGaussianApertureFirstAtomGammaRatio lambda (j + 2)

theorem thetaCuspGaussianApertureFirstAtomGammaRatio_eq_leading_mul_multiplier
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureFirstAtomGammaRatio lambda j =
      thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
        thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomGammaRatio,
    thetaCuspGaussianApertureTailChannelGammaRatio,
    thetaCuspGaussianApertureFirstAtomMomentRatio_eq_leading_mul_amplitudeMultiplier
      hlambda]
  rw [thetaCuspGaussianApertureTailChannelMomentRatio]
  ring

/-- Exact second-degree product rule for the signed first atom.  Its curvature is the leading
channel curvature transported by the middle amplitude multiplier, plus exactly two adjacent
projective displacement terms. -/
theorem thetaCuspGaussianApertureFirstAtomRatioCurvature_eq_transport
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureFirstAtomRatioCurvature lambda j =
      thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) *
          thetaCuspGaussianApertureTailChannelRatioCurvature lambda 4 j +
        (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)) *
          thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j +
        (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2) -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)) *
          thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) := by
  rw [thetaCuspGaussianApertureFirstAtomRatioCurvature,
    thetaCuspGaussianApertureFirstAtomGammaRatio_eq_leading_mul_multiplier hlambda,
    thetaCuspGaussianApertureFirstAtomGammaRatio_eq_leading_mul_multiplier hlambda,
    thetaCuspGaussianApertureFirstAtomGammaRatio_eq_leading_mul_multiplier hlambda]
  unfold thetaCuspGaussianApertureTailChannelRatioCurvature
  ring

theorem thetaCuspGaussianApertureTailChannelGammaRatio_nonneg
    {lambda : ℝ} (hlambda : lambda ≤ 0) (p j : ℕ) :
    0 ≤ thetaCuspGaussianApertureTailChannelGammaRatio lambda p j := by
  exact div_nonneg
    (thetaCuspGaussianApertureTailChannelMomentRatio_pos hlambda p j).le
    (thetaCuspGaussianApertureGammaShape_pos j).le

/-- The two adjacent displacement terms form the exact amplitude-curvature leakage budget. -/
def thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
      |thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) -
        thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j| +
    thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
      |thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2) -
        thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)|

/-- The signed first-atom curvature can lose no more than the two explicit adjacent amplitude
displacements from the multiplier-transported positive-channel curvature. -/
theorem thetaCuspGaussianApertureFirstAtomRatioCurvature_transport_sub_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) *
          thetaCuspGaussianApertureTailChannelRatioCurvature lambda 4 j -
        thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage lambda j ≤
      thetaCuspGaussianApertureFirstAtomRatioCurvature lambda j := by
  let q0 := thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j
  let q2 := thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2)
  let m0 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j
  let m1 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)
  let m2 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2)
  have hq0 : 0 ≤ q0 :=
    thetaCuspGaussianApertureTailChannelGammaRatio_nonneg hlambda 4 j
  have hq2 : 0 ≤ q2 :=
    thetaCuspGaussianApertureTailChannelGammaRatio_nonneg hlambda 4 (j + 2)
  have h0 := mul_le_mul_of_nonneg_right (neg_abs_le (m0 - m1)) hq0
  have h2 := mul_le_mul_of_nonneg_right (neg_abs_le (m2 - m1)) hq2
  rw [thetaCuspGaussianApertureFirstAtomRatioCurvature_eq_transport hlambda]
  unfold thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage
  dsimp only [q0, q2, m0, m1, m2] at h0 h2 ⊢
  rw [abs_sub_comm m1 m0]
  linarith

/-- **Two-scale curvature leakage law.**  After multiplication by the two neighboring literal
RMS response scales, the complete second-degree distortion of the signed first atom is controlled
by the three neighboring correction masses.  This is denominator-free and uniform in aperture
and degree. -/
theorem thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage_scaled_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Real.pi ^ 2 *
        min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
        min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2))) *
        thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage lambda j ≤
      min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2))) *
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda j +
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)) +
      min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) +
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 2)) := by
  let s01 := min
    (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
    (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
  let s12 := min
    (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
    (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2)))
  let q0 := thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j
  let q2 := thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2)
  let m0 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j
  let m1 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)
  let m2 := thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2)
  let rho0 := thetaCuspGaussianApertureTailCorrectionRatio lambda j
  let rho1 := thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)
  let rho2 := thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 2)
  have hs01 : 0 ≤ s01 := le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs12 : 0 ≤ s12 := le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hq0 : 0 ≤ q0 :=
    thetaCuspGaussianApertureTailChannelGammaRatio_nonneg hlambda 4 j
  have hq2 : 0 ≤ q2 :=
    thetaCuspGaussianApertureTailChannelGammaRatio_nonneg hlambda 4 (j + 2)
  have hvar0 := thetaCuspGaussianApertureTailAmplitudeMultiplier_adjacentVariation hlambda j
  have hvar1 :=
    thetaCuspGaussianApertureTailAmplitudeMultiplier_adjacentVariation hlambda (j + 1)
  have h0 := mul_le_mul_of_nonneg_left hvar0 (mul_nonneg hs12 hq0)
  have h1 := mul_le_mul_of_nonneg_left hvar1 (mul_nonneg hs01 hq2)
  unfold thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage
  dsimp only [s01, s12, q0, q2, m0, m1, m2, rho0, rho1, rho2] at h0 h1 ⊢
  nlinarith

/-- The previous leakage law inserted into the exact second-degree product rule.  It isolates the
literal source margin still required from the positive `p=4` channel without leaving an unnamed
signed-amplitude error. -/
theorem thetaCuspGaussianApertureFirstAtomRatioCurvature_scaledDeficit_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Real.pi ^ 2 *
        min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
        min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2))) *
        (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) *
            thetaCuspGaussianApertureTailChannelRatioCurvature lambda 4 j -
          thetaCuspGaussianApertureFirstAtomRatioCurvature lambda j) ≤
      min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2))) *
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda j +
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1)) +
      min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
          (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) +
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 2)) := by
  let scale := Real.pi ^ 2 *
    min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 j))
      (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1))) *
    min (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 1)))
      (Real.sqrt (thetaCuspGaussianApertureTailChannelMomentRatio lambda 4 (j + 2)))
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  have htransport :=
    thetaCuspGaussianApertureFirstAtomRatioCurvature_transport_sub_le hlambda j
  have hdeficit :
      thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) *
            thetaCuspGaussianApertureTailChannelRatioCurvature lambda 4 j -
          thetaCuspGaussianApertureFirstAtomRatioCurvature lambda j ≤
        thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage lambda j := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hdeficit hscale
  have hleakage :=
    thetaCuspGaussianApertureTailAmplitudeCurvatureLeakage_scaled_le hlambda j
  dsimp only [scale] at hscaled
  exact hscaled.trans hleakage

end

end RHTower
