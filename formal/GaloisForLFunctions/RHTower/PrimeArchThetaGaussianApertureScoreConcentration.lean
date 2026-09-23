import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow

open Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower


noncomputable section

/-- Positive density of the aperture-tilted `p=4` first-atom channel. -/
def thetaCuspGaussianApertureLeadingChannelWeight (lambda x : ℝ) : ℝ :=
  Real.exp (lambda * x ^ 2 + 9 * x / 2 - Real.pi * Real.exp (2 * x))

theorem thetaCuspGaussianApertureLeadingChannelWeight_eq
    (lambda x : ℝ) :
    thetaCuspGaussianApertureLeadingChannelWeight lambda x =
      Real.exp (lambda * x ^ 2) * thetaCuspPolynomialAtom (X ^ 4) 1 x := by
  simp only [thetaCuspGaussianApertureLeadingChannelWeight,
    thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
  rw [← Real.exp_nat_mul]
  have hsq : Real.exp x ^ 2 = Real.exp (2 * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem hasDerivAt_thetaCuspGaussianApertureLeadingChannelWeight
    (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureLeadingChannelWeight lambda)
      ((2 * lambda * x + 9 / 2 - 2 * Real.pi * Real.exp (2 * x)) *
        thetaCuspGaussianApertureLeadingChannelWeight lambda x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    exact ((Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)).congr_deriv (by ring)
  have harg : HasDerivAt
      (fun y : ℝ => lambda * y ^ 2 + 9 * y / 2 - Real.pi * Real.exp (2 * y))
      (2 * lambda * x + 9 / 2 - 2 * Real.pi * Real.exp (2 * x)) x := by
    have hquad := ((hasDerivAt_id x).pow 2).const_mul lambda
    have hlin := ((hasDerivAt_id x).const_mul 9).div_const 2
    have htail := hexp.const_mul Real.pi
    exact ((hquad.add hlin).sub htail).congr_deriv (by
      simp only [id_eq]
      ring)
  change HasDerivAt
    (fun y : ℝ => Real.exp
      (lambda * y ^ 2 + 9 * y / 2 - Real.pi * Real.exp (2 * y)))
    ((2 * lambda * x + 9 / 2 - 2 * Real.pi * Real.exp (2 * x)) *
      Real.exp (lambda * x ^ 2 + 9 * x / 2 - Real.pi * Real.exp (2 * x))) x
  exact ((Real.hasDerivAt_exp _).comp x harg).congr_deriv (by ring)

theorem integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    {lambda : ℝ} (hlambda : lambda ≤ 0) (m : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * Real.exp (lambda * x ^ 2) * thetaCuspPolynomialAtom P 1 x)
      (Ioi 0) := by
  have hbase := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    m P (n := 1) (by norm_num)
  apply MeasureTheory.Integrable.mono hbase
  · exact Continuous.aestronglyMeasurable
      (((continuous_id.pow m).mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.pow 2)))).mul
        (continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_thetaCuspPolynomialAtom P 1 x).continuousAt))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hexpLe : Real.exp (lambda * x ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg hlambda (sq_nonneg x))
    rw [show x ^ m * Real.exp (lambda * x ^ 2) *
          thetaCuspPolynomialAtom P 1 x =
        Real.exp (lambda * x ^ 2) *
          (x ^ m * thetaCuspPolynomialAtom P 1 x) by ring,
      norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) hexpLe

theorem integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
    {lambda : ℝ} (hlambda : lambda ≤ 0) (m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspGaussianApertureLeadingChannelWeight lambda x) (Ioi 0) := by
  apply (integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda m (X ^ 4)).congr
  filter_upwards [] with x
  simp only [thetaCuspGaussianApertureLeadingChannelWeight_eq]
  ring

private theorem exp_two_mul_thetaCuspPolynomialAtom_four_eq_six (x : ℝ) :
    Real.exp (2 * x) * thetaCuspPolynomialAtom (X ^ 4) 1 x =
      thetaCuspPolynomialAtom (X ^ 6) 1 x := by
  simp only [thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
  have hpow : Real.exp (2 * x) * Real.exp x ^ 4 = Real.exp x ^ 6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (2 * x) *
        (Real.exp (x / 2) * Real.exp x ^ 4 *
          Real.exp (-Real.pi * Real.exp x ^ 2)) =
      Real.exp (x / 2) *
        (Real.exp (2 * x) * Real.exp x ^ 4) *
          Real.exp (-Real.pi * Real.exp x ^ 2) by ring,
    hpow]

/-- Unnormalized moment of the exact physical score under the leading channel. -/
def thetaCuspGaussianApertureLeadingChannelScoreMoment
    (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
      thetaCuspGaussianApertureLeadingChannelWeight lambda x

theorem integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
        thetaCuspGaussianApertureLeadingChannelWeight lambda x) (Ioi 0) := by
  have h6 := integrableOn_pow_mul_exp_aperture_mul_thetaCuspPolynomialAtom
    hlambda (2 * j + 1) (X ^ 6)
  have h4two :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j + 2)
  have h4one :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j + 1)
  have hcomb := ((h6.const_mul Real.pi).sub (h4two.const_mul lambda)).sub
    (h4one.const_mul (9 / 4 : ℝ))
  simp only [thetaCuspGaussianApertureLeadingChannelWeight_eq] at hcomb ⊢
  apply hcomb.congr
  filter_upwards [] with x
  simp only [Pi.sub_apply]
  rw [← exp_two_mul_thetaCuspPolynomialAtom_four_eq_six]
  unfold thetaCuspGaussianApertureExactTailSaddleDegree
  ring

theorem thetaCuspGaussianApertureLeadingChannelCurrent_tendsto_zero
    {lambda : ℝ} (j : ℕ) :
    Tendsto (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureLeadingChannelWeight lambda x)
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureLeadingChannelWeight lambda x) := by
    exact (continuous_id.pow _).mul
      (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspGaussianApertureLeadingChannelWeight lambda x).continuousAt)
  have h := (hcont.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have h2 : Tendsto (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureLeadingChannelWeight lambda x)
      (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0) := by
    simpa using h
  exact h2

theorem thetaCuspGaussianApertureLeadingChannelCurrent_tendsto_atTop_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Tendsto (fun x : ℝ =>
      x ^ (2 * j + 1) * thetaCuspGaussianApertureLeadingChannelWeight lambda x)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase :=
    (pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      (2 * j + 1) (X ^ 4) (n := 1) (by norm_num)).norm
  have hupper : Tendsto (fun x : ℝ =>
      ‖x ^ (2 * j + 1) * thetaCuspPolynomialAtom (X ^ 4) 1 x‖)
      atTop (𝓝 0) := by simpa using hbase
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [thetaCuspGaussianApertureLeadingChannelWeight_eq,
    show x ^ (2 * j + 1) *
        (Real.exp (lambda * x ^ 2) * thetaCuspPolynomialAtom (X ^ 4) 1 x) =
      Real.exp (lambda * x ^ 2) *
        (x ^ (2 * j + 1) * thetaCuspPolynomialAtom (X ^ 4) 1 x) by ring,
    norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg hlambda (sq_nonneg x)))

/-- Exact score-centering law. The physical saddle coordinate has mean `j+1/2` under the
`j`-th aperture-tilted leading-channel moment measure. -/
theorem thetaCuspGaussianApertureLeadingChannelScoreMoment_eq
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j =
      thetaCuspGaussianApertureGammaShape j *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
  let u : ℝ → ℝ := fun x => x ^ (2 * j + 1)
  let u' : ℝ → ℝ := fun x => (2 * j + 1 : ℝ) * x ^ (2 * j)
  let v : ℝ → ℝ := thetaCuspGaussianApertureLeadingChannelWeight lambda
  let v' : ℝ → ℝ := fun x =>
    (2 * lambda * x + 9 / 2 - 2 * Real.pi * Real.exp (2 * x)) * v x
  have huderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
    intro x _hx
    dsimp only [u, u']
    exact (hasDerivAt_pow (2 * j + 1) x).congr_deriv (by
      simp only [Nat.add_sub_cancel]
      push_cast
      ring)
  have hvderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x _hx
    simpa only [v, v'] using
      hasDerivAt_thetaCuspGaussianApertureLeadingChannelWeight lambda x
  have hscore :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      hlambda j
  have hub'int : IntegrableOn (u * v') (Ioi 0) := by
    apply (hscore.const_mul (-2 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.mul_apply, u, v', v]
    rw [show 2 * j + 1 = 2 * j + 1 by rfl, pow_succ]
    unfold thetaCuspGaussianApertureExactTailSaddleDegree
    ring
  have hu'bint : IntegrableOn (u' * v) (Ioi 0) := by
    have hm := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j)
    apply (hm.const_mul (2 * j + 1 : ℝ)).congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, u', v]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := u) (u' := u') (v := v) (v' := v')
    huderiv hvderiv hub'int hu'bint
    (by
      have hz := @thetaCuspGaussianApertureLeadingChannelCurrent_tendsto_zero
        lambda j
      exact hz)
    (by
      have hz := @thetaCuspGaussianApertureLeadingChannelCurrent_tendsto_atTop_zero
        lambda hlambda j
      exact hz)
  have hleft : (∫ x : ℝ in Ioi 0, u x * v' x) =
      -2 * thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j := by
    rw [thetaCuspGaussianApertureLeadingChannelScoreMoment,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [u, v', v]
    rw [pow_succ]
    unfold thetaCuspGaussianApertureExactTailSaddleDegree
    ring
  have hright : (∫ x : ℝ in Ioi 0, u' x * v x) =
      (2 * j + 1 : ℝ) *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [u', v]
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
    ring
  rw [hleft, hright] at hibp
  simp only [zero_sub] at hibp
  unfold thetaCuspGaussianApertureGammaShape
  linarith

/-- The physical score response correlation between degrees `j` and `j+k`. -/
def thetaCuspGaussianApertureLeadingChannelScoreCorrelation
    (lambda : ℝ) (j k : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
      thetaCuspGaussianApertureLeadingChannelScoreMoment lambda (j + k) -
    thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + k) *
      thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j

/-- Exact all-degree response-correlation cancellation: the centered physical score has no
independent signed mass. Its correlation with `x^(2k)` is exactly `k` times the positive product
of the two channel masses. -/
theorem thetaCuspGaussianApertureLeadingChannelScoreCorrelation_eq
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j k : ℕ) :
    thetaCuspGaussianApertureLeadingChannelScoreCorrelation lambda j k =
      (k : ℝ) *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + k) := by
  rw [thetaCuspGaussianApertureLeadingChannelScoreCorrelation,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda]
  unfold thetaCuspGaussianApertureGammaShape
  push_cast
  ring

theorem thetaCuspGaussianApertureLeadingChannelScoreCorrelation_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < thetaCuspGaussianApertureLeadingChannelScoreCorrelation lambda j k := by
  rw [thetaCuspGaussianApertureLeadingChannelScoreCorrelation_eq hlambda]
  exact mul_pos
    (mul_pos (by exact_mod_cast hk)
      (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j))
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + k))

/-- Residual score after subtracting the global triple-Gaussian curvature floor `3*pi*x^(2 : ℕ)`. -/
def thetaCuspGaussianApertureLeadingChannelScoreResidual
    (lambda x : ℝ) : ℝ :=
  thetaCuspGaussianApertureExactTailSaddleDegree lambda x - 3 * Real.pi * x ^ 2

theorem hasDerivAt_thetaCuspGaussianApertureLeadingChannelScoreResidual
    (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureLeadingChannelScoreResidual lambda)
      (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x -
        6 * Real.pi * x) x := by
  exact ((hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).sub
    (((hasDerivAt_id x).pow 2).const_mul (3 * Real.pi))).congr_deriv (by
      simp only [id_eq]
      ring)

theorem thetaCuspGaussianApertureLeadingChannelScoreResidualSlope_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 0 < x) :
    0 < thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x -
      6 * Real.pi * x := by
  have hexpFloor : 1 + 2 * x + 2 * x ^ 2 ≤ Real.exp (2 * x) := by
    have h := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 2 * x) 3
    norm_num [Finset.sum_range_succ] at h
    nlinarith
  have hone : 0 ≤ 1 + 2 * x := by linarith
  have hproduct :
      (1 + 2 * x + 2 * x ^ 2) * (1 + 2 * x) ≤
        Real.exp (2 * x) * (1 + 2 * x) :=
    mul_le_mul_of_nonneg_right hexpFloor hone
  have hpoly : 5 / 6 ≤ 1 - 2 * x + 6 * x ^ 2 + 4 * x ^ 3 := by
    have hsq := sq_nonneg (x - 1 / 6)
    have hcube : 0 ≤ x ^ 3 := by positivity
    nlinarith
  have hpolyPi : 9 / 4 <
      Real.pi * (1 - 2 * x + 6 * x ^ 2 + 4 * x ^ 3) := by
    have hscale := mul_le_mul_of_nonneg_left hpoly Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have hmain : 9 / 4 <
      Real.pi * Real.exp (2 * x) * (1 + 2 * x) - 6 * Real.pi * x := by
    have hscale := mul_le_mul_of_nonneg_left hproduct Real.pi_pos.le
    nlinarith
  have haperture : 0 ≤ -2 * lambda * x := by
    exact mul_nonneg (by nlinarith : 0 ≤ -2 * lambda) hx.le
  unfold thetaCuspGaussianApertureExactTailSaddleDegreeSlope
  nlinarith

/-- After removal of the Gaussian floor, the exact score is still strictly increasing on the
whole positive half-line. -/
theorem thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictMonoOn (thetaCuspGaussianApertureLeadingChannelScoreResidual lambda) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x _hx
    exact (hasDerivAt_thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(hasDerivAt_thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x).deriv]
    exact thetaCuspGaussianApertureLeadingChannelScoreResidualSlope_pos hlambda hx

/-- Exact score coercivity. The source score correlation controls the ordinary moment variance
with the sharp global Gaussian floor `pi`. -/
theorem thetaCuspGaussianApertureLeadingChannelMoment_variance_le_score
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (3 * Real.pi) *
        (thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 2) -
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) ^ 2) ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let h : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x
  let K : ℝ → ℝ := thetaCuspGaussianApertureLeadingChannelScoreResidual lambda
  let f : ℝ → ℝ := fun x => K x * h x
  let g : ℝ → ℝ := fun x => x ^ 2
  have hh : Integrable h mu := by
    simpa only [MeasureTheory.IntegrableOn, h, mu] using
      integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
        hlambda (2 * j)
  have hscorej :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      hlambda j
  have hmj1 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 1))
  have hf : Integrable f mu := by
    have hdiff := hscorej.sub (hmj1.const_mul (3 * Real.pi))
    apply hdiff.congr
    filter_upwards [] with x
    simp only [f, K, h, thetaCuspGaussianApertureLeadingChannelScoreResidual,
      Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hgh : Integrable (fun x => g x * h x) mu := by
    apply hmj1.congr
    filter_upwards [] with x
    simp only [g, h]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hscorej1 :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      hlambda (j + 1)
  have hmj2 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 2))
  have hgf : Integrable (fun x => g x * f x) mu := by
    have hdiff := hscorej1.sub (hmj2.const_mul (3 * Real.pi))
    apply hdiff.congr
    filter_upwards [] with x
    simp only [g, f, K, h,
      thetaCuspGaussianApertureLeadingChannelScoreResidual,
      Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
      show 2 * (j + 2) = 2 * j + 4 by omega, pow_add, pow_add]
    ring
  have hmono :=
    thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn hlambda
  have hmem : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu, z ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      0 ≤ (g z.2 - g z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1) := by
    filter_upwards [hmem] with z hz
    rcases hz with ⟨hx, hy⟩
    have hbase (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 ≤ h t := by
      dsimp only [h]
      exact mul_nonneg (pow_nonneg ht.le _)
        (Real.exp_nonneg _)
    rcases le_total z.1 z.2 with hxy | hyx
    · have hgdiff : 0 ≤ g z.2 - g z.1 := by
        dsimp only [g]
        exact sub_nonneg.mpr ((sq_le_sq₀ hx.le hy.le).2 hxy)
      have hKdiff : 0 ≤ K z.2 - K z.1 := by
        exact sub_nonneg.mpr
          (hmono.monotoneOn hx hy hxy)
      have hbracket : 0 ≤ h z.1 * f z.2 - h z.2 * f z.1 := by
        rw [show h z.1 * f z.2 - h z.2 * f z.1 =
          (h z.1 * h z.2) * (K z.2 - K z.1) by
            dsimp only [f]
            ring]
        exact mul_nonneg (mul_nonneg (hbase z.1 hx) (hbase z.2 hy)) hKdiff
      exact mul_nonneg hgdiff hbracket
    · have hswap := hmono.monotoneOn hy hx hyx
      have hgdiff : 0 ≤ g z.1 - g z.2 := by
        dsimp only [g]
        exact sub_nonneg.mpr ((sq_le_sq₀ hy.le hx.le).2 hyx)
      have hKdiff : 0 ≤ K z.1 - K z.2 := sub_nonneg.mpr hswap
      have hbracket : 0 ≤ h z.2 * f z.1 - h z.1 * f z.2 := by
        rw [show h z.2 * f z.1 - h z.1 * f z.2 =
          (h z.2 * h z.1) * (K z.1 - K z.2) by
            dsimp only [f]
            ring]
        exact mul_nonneg (mul_nonneg (hbase z.2 hy) (hbase z.1 hx)) hKdiff
      nlinarith
  have hcross :=
    HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
      hf hh hgf hgh hkernel
  have hmass : (∫ x, h x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [h]
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
    ring
  have hgbase : (∫ x, g x * h x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, h]
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq,
      show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hmom2 : (∫ x,
      x ^ (2 * (j + 2)) *
        thetaCuspGaussianApertureLeadingChannelWeight lambda x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 2) := by
    rw [thetaCuspGaussianApertureTailChannelMoment]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
    ring
  have hfvalue : (∫ x, f x ∂mu) =
      thetaCuspGaussianApertureLeadingChannelScoreMoment lambda j -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
    have hfexpand : f = fun x : ℝ =>
        x ^ (2 * j) * thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
            thetaCuspGaussianApertureLeadingChannelWeight lambda x -
          (3 * Real.pi) * (g x * h x) := by
      funext x
      simp only [f, K, g, h,
        thetaCuspGaussianApertureLeadingChannelScoreResidual]
      ring
    rw [hfexpand, integral_sub hscorej (hgh.const_mul (3 * Real.pi)),
      integral_const_mul,
      thetaCuspGaussianApertureLeadingChannelScoreMoment, hgbase]
  have hgfvalue : (∫ x, g x * f x ∂mu) =
      thetaCuspGaussianApertureLeadingChannelScoreMoment lambda (j + 1) -
        (3 * Real.pi) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 2) := by
    have hgfexpand : (fun x => g x * f x) = fun x : ℝ =>
        x ^ (2 * (j + 1)) *
            thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
              thetaCuspGaussianApertureLeadingChannelWeight lambda x -
          (3 * Real.pi) * (x ^ (2 * (j + 2)) *
            thetaCuspGaussianApertureLeadingChannelWeight lambda x) := by
      funext x
      simp only [g, f, K, h,
        thetaCuspGaussianApertureLeadingChannelScoreResidual]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega,
        show 2 * (j + 2) = 2 * j + 4 by omega, pow_add, pow_add]
      ring
    rw [hgfexpand, integral_sub hscorej1 (hmj2.const_mul (3 * Real.pi)),
      integral_const_mul,
      thetaCuspGaussianApertureLeadingChannelScoreMoment, hmom2]
  rw [hmass, hgbase, hfvalue, hgfvalue,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda,
    thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda] at hcross
  unfold thetaCuspGaussianApertureGammaShape at hcross
  norm_num only [Nat.cast_add, Nat.cast_one] at hcross
  nlinarith

/-- Raw adjacent ratio of the positive leading channel. -/
def thetaCuspGaussianApertureLeadingChannelMomentRatio
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) /
    thetaCuspGaussianApertureTailChannelMoment lambda 4 j

/-- **Uniform response-Lipschitz law.** One degree of size bias changes the raw leading-channel
mean by at most `1/(3*pi)`, uniformly over every cold aperture and every degree. -/
theorem thetaCuspGaussianApertureLeadingChannelMomentRatio_succ_sub_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureLeadingChannelMomentRatio lambda (j + 1) -
        thetaCuspGaussianApertureLeadingChannelMomentRatio lambda j ≤
      (3 * Real.pi)⁻¹ := by
  let a := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let b := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let c := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 2)
  have ha : 0 < a := thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hb : 0 < b :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1)
  have hthreePi : 0 < 3 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hvariance :=
    thetaCuspGaussianApertureLeadingChannelMoment_variance_le_score hlambda j
  have hfrac : c / b - b / a = (a * c - b ^ 2) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [thetaCuspGaussianApertureLeadingChannelMomentRatio,
    thetaCuspGaussianApertureLeadingChannelMomentRatio, hfrac]
  rw [inv_eq_one_div,
    div_le_div_iff₀ (mul_pos ha hb) hthreePi]
  dsimp only [a, b, c]
  nlinarith

/-- The exact physical score is a strictly increasing coordinate on the closed positive ray. -/
theorem thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictMonoOn (thetaCuspGaussianApertureExactTailSaddleDegree lambda) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x _hx
    exact (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    rw [(hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).deriv]
    have hres :=
      thetaCuspGaussianApertureLeadingChannelScoreResidualSlope_pos hlambda hx
    have hpositive : 0 < 6 * Real.pi * x := by positivity
    nlinarith

theorem tendsto_thetaCuspGaussianApertureExactTailSaddleDegree_atTop
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    Tendsto (thetaCuspGaussianApertureExactTailSaddleDegree lambda) atTop atTop := by
  have hlinear : Tendsto (fun x : ℝ => (3 / 4 : ℝ) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hexp : 1 ≤ Real.exp (2 * x) :=
    Real.one_le_exp (by linarith)
  have hA : 3 < Real.pi * Real.exp (2 * x) := by
    have hscale : Real.pi ≤ Real.pi * Real.exp (2 * x) :=
      by simpa using mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
    exact Real.pi_gt_three.trans_le hscale
  have haperture : 0 ≤ -lambda * x ^ 2 :=
    mul_nonneg (neg_nonneg.mpr hlambda) (sq_nonneg x)
  have hmain : (3 / 4 : ℝ) * x ≤
      (Real.pi * Real.exp (2 * x) - 9 / 4) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx
  unfold thetaCuspGaussianApertureExactTailSaddleDegree
  nlinarith

/-- The physical score coordinate is a bijection of the positive ray. -/
theorem thetaCuspGaussianApertureExactTailSaddleDegree_bijOn_Ici_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    Set.BijOn (thetaCuspGaussianApertureExactTailSaddleDegree lambda)
      (Ici 0) (Ici 0) := by
  have hmono :=
    thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero hlambda
  have hzero : thetaCuspGaussianApertureExactTailSaddleDegree lambda 0 = 0 := by
    simp [thetaCuspGaussianApertureExactTailSaddleDegree]
  refine ⟨?_, hmono.injOn, ?_⟩
  · intro x hx
    rw [mem_Ici, ← hzero]
    exact hmono.monotoneOn (mem_Ici.mpr le_rfl) hx (mem_Ici.mp hx)
  · intro y hy
    have hlarge : ∀ᶠ x : ℝ in atTop,
        y ≤ thetaCuspGaussianApertureExactTailSaddleDegree lambda x :=
      (tendsto_atTop.1
        (tendsto_thetaCuspGaussianApertureExactTailSaddleDegree_atTop hlambda)) y
    obtain ⟨x, hx0, hyx⟩ := ((eventually_ge_atTop (0 : ℝ)).and hlarge).exists
    obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hx0
      (fun _ _ =>
        (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda _).continuousAt.continuousWithinAt)
      (mem_Icc.mpr ⟨by simp only [hzero]; exact hy, hyx⟩)
    exact ⟨z, hz.1, hzy⟩

/-- Every gamma-shape degree has one unique positive response-centered physical saddle. -/
theorem existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    ∃! x : ℝ, 0 < x ∧
      thetaCuspGaussianApertureExactTailSaddleDegree lambda x =
        thetaCuspGaussianApertureGammaShape j := by
  have hshape : 0 < thetaCuspGaussianApertureGammaShape j := by
    unfold thetaCuspGaussianApertureGammaShape
    positivity
  have hbij :=
    thetaCuspGaussianApertureExactTailSaddleDegree_bijOn_Ici_zero hlambda
  obtain ⟨x, hx0, hxshape⟩ := hbij.2.2 (mem_Ici.mpr hshape.le)
  have hx : 0 < x := by
    have hx0' : 0 ≤ x := mem_Ici.mp hx0
    rcases hx0'.eq_or_lt with rfl | hx
    · simp [thetaCuspGaussianApertureExactTailSaddleDegree] at hxshape
      linarith
    · exact hx
  refine ⟨x, ⟨hx, hxshape⟩, ?_⟩
  intro y hy
  exact (hbij.2.1 hx.le hy.1.le (hxshape.trans hy.2.symm)).symm

/-- The canonical response-centered saddle height. -/
noncomputable def thetaCuspGaussianApertureResponseCenteredSaddleHeight
    (lambda : ℝ) (hlambda : lambda ≤ 0) (j : ℕ) : ℝ :=
  Classical.choose
    (existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle hlambda j)

theorem thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 < thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j :=
  (Classical.choose_spec
    (existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle hlambda j)).1.1

theorem thetaCuspGaussianApertureResponseCenteredSaddleHeight_score
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureExactTailSaddleDegree lambda
        (thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j) =
      thetaCuspGaussianApertureGammaShape j :=
  (Classical.choose_spec
    (existsUnique_thetaCuspGaussianApertureResponseCenteredSaddle hlambda j)).1.2

/-- Pointwise strong monotonicity of the physical score in squared height. -/
theorem thetaCuspGaussianApertureExactTailSaddleDegree_sq_cocoercive
    {lambda x y : ℝ} (hlambda : lambda ≤ 0) (hx : 0 < x) (hy : 0 < y) :
    (3 * Real.pi) * (x ^ 2 - y ^ 2) ^ 2 ≤
      (x ^ 2 - y ^ 2) *
        (thetaCuspGaussianApertureExactTailSaddleDegree lambda x -
          thetaCuspGaussianApertureExactTailSaddleDegree lambda y) := by
  have hmono :=
    thetaCuspGaussianApertureLeadingChannelScoreResidual_strictMonoOn hlambda
  have hres : 0 ≤
      (x ^ 2 - y ^ 2) *
        (thetaCuspGaussianApertureLeadingChannelScoreResidual lambda x -
          thetaCuspGaussianApertureLeadingChannelScoreResidual lambda y) := by
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((sq_le_sq₀ hx.le hy.le).2 hxy))
        (sub_nonpos.mpr (hmono.monotoneOn hx hy hxy))
    · exact mul_nonneg
        (sub_nonneg.mpr ((sq_le_sq₀ hy.le hx.le).2 hyx))
        (sub_nonneg.mpr (hmono.monotoneOn hy hx hyx))
  unfold thetaCuspGaussianApertureLeadingChannelScoreResidual at hres
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

theorem integral_pow_leadingChannelWeight_eq_moment
    (lambda : ℝ) (j : ℕ) :
    (∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
  rw [thetaCuspGaussianApertureTailChannelMoment]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
  ring

/-- **Response-centered saddle localization.** The exact score correlation gives a uniform
mean-square window around the response-centered physical saddle, without a Laplace asymptotic:
the unnormalized squared-height error costs at most one adjacent leading-channel moment. -/
theorem thetaCuspGaussianApertureLeadingChannel_centeredSaddleError_le
    {lambda s : ℝ} (hlambda : lambda ≤ 0) {j : ℕ} (hspos : 0 < s)
    (hs : thetaCuspGaussianApertureExactTailSaddleDegree lambda s =
      thetaCuspGaussianApertureGammaShape j) :
    (3 * Real.pi) *
        (∫ x : ℝ in Ioi 0,
          (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
            thetaCuspGaussianApertureLeadingChannelWeight lambda x) ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let base : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x
  let lhs : ℝ → ℝ := fun x =>
    (3 * Real.pi) * (x ^ 2 - s ^ 2) ^ 2 * base x
  let rhs : ℝ → ℝ := fun x =>
    (x ^ 2 - s ^ 2) *
      (thetaCuspGaussianApertureExactTailSaddleDegree lambda x -
        thetaCuspGaussianApertureExactTailSaddleDegree lambda s) * base x
  have hm0 := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
    hlambda (2 * j)
  have hm1 := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
    hlambda (2 * (j + 1))
  have hm2 := integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
    hlambda (2 * (j + 2))
  have herror : Integrable (fun x : ℝ =>
      (x ^ 2 - s ^ 2) ^ 2 * base x) mu := by
    have hcomb := (hm2.sub (hm1.const_mul (2 * s ^ 2))).add
      (hm0.const_mul (s ^ 4))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [base, Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
      show 2 * (j + 2) = 2 * j + 4 by omega, pow_add, pow_add]
    ring
  have hlhs : Integrable lhs mu := by
    apply (herror.const_mul (3 * Real.pi)).congr
    filter_upwards [] with x
    simp only [lhs]
    ring
  have hscore0 :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      hlambda j
  have hscore1 :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelScoreMomentIntegrand
      hlambda (j + 1)
  have hrhs : Integrable rhs mu := by
    have hcomb :=
      ((hscore1.sub (hm1.const_mul
          (thetaCuspGaussianApertureExactTailSaddleDegree lambda s))).sub
        (hscore0.const_mul (s ^ 2))).add
      (hm0.const_mul
        (s ^ 2 * thetaCuspGaussianApertureExactTailSaddleDegree lambda s))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [rhs, base, Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hpoint : ∀ᵐ x : ℝ ∂mu, lhs x ≤ rhs x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hbase : 0 ≤ base x := by
      dsimp only [base]
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (thetaCuspGaussianApertureExactTailSaddleDegree_sq_cocoercive
        hlambda hx hspos) hbase
  have hinterior := integral_mono_ae hlhs hrhs hpoint
  have hrhsValue : (∫ x, rhs x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
    change (∫ x : ℝ in Ioi 0, rhs x) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
    let A : ℝ → ℝ := fun x =>
      x ^ (2 * (j + 1)) *
        thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x
    let B : ℝ → ℝ := fun x =>
      thetaCuspGaussianApertureExactTailSaddleDegree lambda s *
        (x ^ (2 * (j + 1)) *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x)
    let C : ℝ → ℝ := fun x => s ^ 2 *
      (x ^ (2 * j) *
        thetaCuspGaussianApertureExactTailSaddleDegree lambda x *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x)
    let D : ℝ → ℝ := fun x =>
      (s ^ 2 * thetaCuspGaussianApertureExactTailSaddleDegree lambda s) *
        (x ^ (2 * j) *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x)
    have hA : IntegrableOn A (Ioi 0) := by simpa only [A] using hscore1
    have hB : IntegrableOn B (Ioi 0) := by
      simpa only [MeasureTheory.IntegrableOn, B] using hm1.const_mul
        (thetaCuspGaussianApertureExactTailSaddleDegree lambda s)
    have hC : IntegrableOn C (Ioi 0) := by
      simpa only [MeasureTheory.IntegrableOn, C] using hscore0.const_mul (s ^ 2)
    have hD : IntegrableOn D (Ioi 0) := by
      simpa only [MeasureTheory.IntegrableOn, D] using hm0.const_mul
        (s ^ 2 * thetaCuspGaussianApertureExactTailSaddleDegree lambda s)
    have hdecomp : rhs = (A - B - C) + D := by
      funext x
      simp only [rhs, base, A, B, C, D, Pi.add_apply, Pi.sub_apply]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      ring
    rw [hdecomp]
    rw [integral_add' ((hA.sub hB).sub hC) hD,
      integral_sub' (hA.sub hB) hC, integral_sub' hA hB,
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [A]
    rw [← thetaCuspGaussianApertureLeadingChannelScoreMoment,
      integral_pow_leadingChannelWeight_eq_moment,
      ← thetaCuspGaussianApertureLeadingChannelScoreMoment,
      integral_pow_leadingChannelWeight_eq_moment]
    rw [thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda,
      thetaCuspGaussianApertureLeadingChannelScoreMoment_eq hlambda, hs]
    unfold thetaCuspGaussianApertureGammaShape
    push_cast
    ring
  rw [hrhsValue] at hinterior
  change (3 * Real.pi) *
      (∫ x : ℝ in Ioi 0,
        (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x) ≤
    thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  rw [← integral_const_mul]
  simpa only [lhs, base, mu, mul_assoc] using hinterior

theorem thetaCuspGaussianApertureLeadingChannel_canonicalSaddleError_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (3 * Real.pi) *
        (∫ x : ℝ in Ioi 0,
          (x ^ 2 -
              thetaCuspGaussianApertureResponseCenteredSaddleHeight
                lambda hlambda j ^ 2) ^ 2 *
            x ^ (2 * j) *
              thetaCuspGaussianApertureLeadingChannelWeight lambda x) ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
  exact thetaCuspGaussianApertureLeadingChannel_centeredSaddleError_le
    hlambda
    (thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos hlambda j)
    (thetaCuspGaussianApertureResponseCenteredSaddleHeight_score hlambda j)

end

end RHTower
