import GaloisForLFunctions.RHTower.ThetaFiniteShellFourierBoundary
import GaloisForLFunctions.RHTower.ThetaFiniteShellSubquadraticSourceBound
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticTwoRayDecay
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeEntireTransform
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination

/-!
# Infinitely many nonreal zeros of every fixed theta-shell prefix

The literal canonical prefix has a cubic exponential source envelope. Its complex
cosine transform is entire with growth bounded by exp(C (1 + norm z)^(3/2)).
Two-ray Fourier decay therefore forces infinitely many complex zeros. The exact
nonzero boundary slope gives an eventually negative real transform, so only
finitely many zeros are real. Consequently every nonempty fixed shell prefix has
infinitely many nonreal zeros.

This closes the concrete analytic transfer in the existing paper argument in
`docs/drafts/pipeline/1-in-progress/k-rvm-finite-sixth-moment-bracket.md`.
No numerical moment, zero, or spectral estimate is used. This result concerns
fixed shell prefixes; it does not settle the complete theta source or RH.
-/

open Real Complex MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

private def prefixEnvelopeConstant (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, thetaCuspSourceAtomDominationWeight (n+1)) *
    (4 * Real.pi ^ (2 : ℕ))

private theorem prefixEnvelopeConstant_nonneg (N : ℕ) :
    0 ≤ prefixEnvelopeConstant N := by
  unfold prefixEnvelopeConstant
  exact mul_nonneg (Finset.sum_nonneg fun n _ =>
    thetaCuspSourceAtomDominationWeight_nonneg (n+1)) (by positivity)

private theorem prefix_nonneg (N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ thetaCuspFiniteShellPrefix N x := by
  unfold thetaCuspFiniteShellPrefix
  exact Finset.sum_nonneg fun n _ => thetaCuspSourceTerm_nonneg_of_pos hx n

private theorem prefix_le_cubicEnvelope (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFiniteShellPrefix N x ≤
      prefixEnvelopeConstant N * Real.exp (-x^3-x) := by
  have he := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2*x) 4
  norm_num [Finset.sum_range_succ] at he
  have hpi := Real.pi_gt_three
  have hexp0 := Real.exp_pos (2*x)
  have hcube : 9*x/2-Real.pi*Real.exp (2*x) ≤ -x^3-x := by
    nlinarith [sq_nonneg x, pow_nonneg hx 3]
  have hfirst := (thetaCuspFirstAtom_le_doubleExponentialEnvelope x).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcube) (by positivity))
  rw [thetaCuspFiniteShellPrefix, Finset.sum_range_succ']
  simp only [thetaCuspSourceTerm, thetaCuspSeed, Nat.cast_zero, zero_mul,
    zero_pow (by omega : 2 ≠ 0), zero_pow (by omega : 4 ≠ 0), sub_zero,
    mul_zero, add_zero]
  change (∑ n ∈ Finset.range N, thetaCuspSourceTerm x (n+1)) ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        thetaCuspSourceAtomDominationWeight (n+1) *
          ((4 * Real.pi^2) * Real.exp (-x^3-x)) := by
      apply Finset.sum_le_sum
      intro n _
      exact (thetaCuspSourceTerm_le_first (Nat.succ_pos n) hx).trans
        (mul_le_mul_of_nonneg_left hfirst
          (thetaCuspSourceAtomDominationWeight_nonneg (n+1)))
    _ = _ := by rw [← Finset.sum_mul]; simp only [prefixEnvelopeConstant, mul_assoc]

private theorem linear_sub_cube_le {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    t*x-x^3 ≤ (1+t) ^ (3/2 : ℝ) := by
  have hs0 := Real.sqrt_nonneg (1+t)
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ 1+t)
  have hpow : (1+t) ^ (3/2 : ℝ) = (1+t)*Real.sqrt (1+t) := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num,
      Real.rpow_add (by linarith : 0 < 1+t), Real.rpow_one]
  rw [hpow]
  by_cases hxs : x ≤ Real.sqrt (1+t)
  · nlinarith [mul_nonneg ht (sub_nonneg.mpr hxs), pow_nonneg hx 3]
  · have hsq : 1+t ≤ x^2 := by nlinarith
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsq)]

/-- Positive-half-line restriction of a literal canonical theta-shell prefix. -/
def thetaFiniteShellHalfSource (N : ℕ) : ℝ → ℂ :=
  (Ioi 0).indicator fun x => (thetaCuspFiniteShellPrefix N x : ℂ)

private theorem halfSource_measurable (N : ℕ) :
    AEStronglyMeasurable (thetaFiniteShellHalfSource N) volume := by
  apply AEStronglyMeasurable.indicator _ measurableSet_Ioi
  apply Continuous.aestronglyMeasurable
  apply Complex.continuous_ofReal.comp
  rw [← thetaFiniteShellJet_zero_eq]
  exact continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaFiniteShellJet N 0 x).continuousAt

private theorem halfSource_weight_bound (N : ℕ) (A x : ℝ) :
    ‖thetaFiniteShellHalfSource N x‖ * Real.exp (A * |x|) ≤
      (Ioi 0).indicator (fun x =>
        (prefixEnvelopeConstant N * Real.exp ((1+|A|) ^ (3/2 : ℝ))) *
          Real.exp (-x)) x := by
  by_cases hx : 0 < x
  · have hxmem : x ∈ Ioi (0 : ℝ) := hx
    simp only [thetaFiniteShellHalfSource, indicator_of_mem hxmem,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (prefix_nonneg N hx),
      abs_of_pos hx]
    calc
      _ ≤ (prefixEnvelopeConstant N * Real.exp (-x^3-x)) * Real.exp (A*x) :=
        mul_le_mul_of_nonneg_right (prefix_le_cubicEnvelope N hx.le)
          (Real.exp_pos _).le
      _ = prefixEnvelopeConstant N * Real.exp (A*x-x^3) * Real.exp (-x) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (prefixEnvelopeConstant_nonneg N)
        apply Real.exp_le_exp.mpr
        exact (sub_le_sub_right (mul_le_mul_of_nonneg_right (le_abs_self A) hx.le) _).trans
          (linear_sub_cube_le (abs_nonneg A) hx.le)
  · simp [thetaFiniteShellHalfSource, hx]

theorem allExpWeightIntegrable_thetaFiniteShellHalfSource (N : ℕ) :
    AllExpWeightIntegrable (thetaFiniteShellHalfSource N) := by
  intro A
  apply Integrable.mono' ((integrable_indicator_iff measurableSet_Ioi).mpr
    ((integrableOn_exp_neg_Ioi 0).const_mul
      (prefixEnvelopeConstant N * Real.exp ((1+|A|) ^ (3/2 : ℝ)))))
    ((halfSource_measurable N).norm.mul (by fun_prop))
  filter_upwards with x
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  exact halfSource_weight_bound N A x

/-- Entire cosine transform of the finite theta-shell prefix. -/
def thetaFiniteShellEntire (N : ℕ) (z : ℂ) : ℂ :=
  (expFourier (thetaFiniteShellHalfSource N) z +
    expFourier (thetaFiniteShellHalfSource N) (-z))/2

theorem differentiable_thetaFiniteShellEntire (N : ℕ) :
    Differentiable ℂ (thetaFiniteShellEntire N) := by
  have hd := differentiable_expFourier_of_allExpWeightIntegrable
    (halfSource_measurable N) (allExpWeightIntegrable_thetaFiniteShellHalfSource N)
  exact (hd.add (hd.comp differentiable_neg)).div_const _

theorem thetaFiniteShellEntire_neg (N : ℕ) (z : ℂ) :
    thetaFiniteShellEntire N (-z) = thetaFiniteShellEntire N z := by
  simp only [thetaFiniteShellEntire, neg_neg]
  ring


private theorem halfSource_kernel_integrable (N : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => thetaFiniteShellHalfSource N x *
      Complex.exp (-(I*z*x))) :=
  integrable_expFourier_kernel' (halfSource_measurable N)
    ((allExpWeightIntegrable_thetaFiniteShellHalfSource N).expWeightIntegrable
      (|z.im|+1)) (by linarith)

/-- The entire construction is exactly the source cosine integral. -/
theorem thetaFiniteShellEntire_eq_integral (N : ℕ) (z : ℂ) :
    thetaFiniteShellEntire N z = ∫ x : ℝ in Ioi 0,
      (thetaCuspFiniteShellPrefix N x : ℂ) * Complex.cos (z*x) := by
  unfold thetaFiniteShellEntire expFourier
  rw [← integral_add (halfSource_kernel_integrable N z)
    (halfSource_kernel_integrable N (-z)), ← integral_div]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [thetaFiniteShellHalfSource, indicator_of_mem hx, Complex.cos]
    rw [show -(I*z*(x : ℂ)) = -(z*x)*I by ring,
      show -(I*(-z)*(x : ℂ)) = (z*x)*I by ring]
    ring
  · simp [thetaFiniteShellHalfSource, hx]

theorem thetaFiniteShellEntire_real (N : ℕ) (b : ℝ) :
    thetaFiniteShellEntire N (b : ℂ) =
      ((∫ x : ℝ in Ioi 0, thetaCuspFiniteShellPrefix N x * Real.cos (b*x)) : ℝ) := by
  rw [thetaFiniteShellEntire_eq_integral]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  simp

private theorem norm_halfSource_expFourier_le (N : ℕ) (z : ℂ) :
    ‖expFourier (thetaFiniteShellHalfSource N) z‖ ≤
      prefixEnvelopeConstant N * Real.exp ((1+‖z‖) ^ (3/2 : ℝ)) := by
  let K := prefixEnvelopeConstant N * Real.exp ((1+‖z‖) ^ (3/2 : ℝ))
  have hbound (x : ℝ) : ‖thetaFiniteShellHalfSource N x *
      Complex.exp (-(I*z*x))‖ ≤
        (Ioi 0).indicator (fun x => K * Real.exp (-x)) x := by
    rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    have harg : z.im*x ≤ ‖z‖*|x| :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg x))
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg _)).trans
      (by simpa only [abs_of_nonneg (norm_nonneg z)] using
        halfSource_weight_bound N ‖z‖ x)
  calc
    _ ≤ ∫ x : ℝ, ‖thetaFiniteShellHalfSource N x *
        Complex.exp (-(I*z*x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (Ioi 0).indicator (fun x => K * Real.exp (-x)) x := by
      apply integral_mono_ae (halfSource_kernel_integrable N z).norm
        ((integrable_indicator_iff measurableSet_Ioi).mpr
          ((integrableOn_exp_neg_Ioi 0).const_mul K))
      exact Eventually.of_forall hbound
    _ = _ := by
      rw [integral_indicator measurableSet_Ioi, integral_const_mul,
        integral_exp_neg_Ioi_zero, mul_one]

theorem thetaFiniteShellEntire_subquadratic (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaFiniteShellEntire N z‖ ≤ Real.exp (C*(1+‖z‖) ^ (3/2 : ℝ)) := by
  refine ⟨prefixEnvelopeConstant N+1, by linarith [prefixEnvelopeConstant_nonneg N], ?_⟩
  intro z
  let r := (1+‖z‖) ^ (3/2 : ℝ)
  have hr : 1 ≤ r := by
    dsimp [r]
    exact Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  have hK := prefixEnvelopeConstant_nonneg N
  have hraw : ‖thetaFiniteShellEntire N z‖ ≤ prefixEnvelopeConstant N * Real.exp r := by
    rw [thetaFiniteShellEntire, norm_div, Complex.norm_ofNat]
    have hp := norm_halfSource_expFourier_le N z
    have hm := norm_halfSource_expFourier_le N (-z)
    rw [norm_neg] at hm
    have hs := norm_add_le (expFourier (thetaFiniteShellHalfSource N) z)
      (expFourier (thetaFiniteShellHalfSource N) (-z))
    change _ ≤ prefixEnvelopeConstant N * Real.exp r
    change _ ≤ prefixEnvelopeConstant N * Real.exp r at hp hm
    linarith
  apply hraw.trans
  calc
    _ ≤ Real.exp (prefixEnvelopeConstant N) * Real.exp r := by
      gcongr
      linarith [Real.add_one_le_exp (prefixEnvelopeConstant N)]
    _ ≤ Real.exp ((prefixEnvelopeConstant N+1)*r) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

theorem thetaFiniteShellEntire_real_tendsto_zero (N : ℕ) :
    Tendsto (fun b : ℝ => ‖thetaFiniteShellEntire N (b : ℂ)‖) atTop (𝓝 0) := by
  have h := HTGeometry.tendsto_setIntegral_mul_cos_atTop
    (integrableOn_thetaFiniteShellJet N 0)
  rw [thetaFiniteShellJet_zero_eq] at h
  have heq (b : ℝ) : ‖thetaFiniteShellEntire N (b : ℂ)‖ =
      ‖∫ x : ℝ in Ioi 0, Real.cos (x*b) * thetaCuspFiniteShellPrefix N x‖ := by
    rw [thetaFiniteShellEntire_real, Complex.norm_real]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm x b, mul_comm]
  simpa only [heq, norm_zero] using h.norm

theorem thetaFiniteShellEntire_zeroSet_infinite (N : ℕ) :
    {z : ℂ | thetaFiniteShellEntire N z = 0}.Infinite := by
  obtain ⟨C, hC, hg⟩ := thetaFiniteShellEntire_subquadratic N
  apply zeroSet_infinite_of_subquadratic_twoRayDecay
    (differentiable_thetaFiniteShellEntire N) (by norm_num : (0:ℝ) ≤ 3/2)
    (by norm_num : (3/2:ℝ) < 2) hC hg
    (thetaFiniteShellEntire_real_tendsto_zero N)
  simpa only [Complex.ofReal_neg, thetaFiniteShellEntire_neg] using
    thetaFiniteShellEntire_real_tendsto_zero N

/-- Every nonempty fixed prefix has only finitely many real zeros. -/
theorem thetaFiniteShellEntire_real_zeroSet_finite (N : ℕ) :
    {z : ℂ | thetaFiniteShellEntire (N+1) z = 0 ∧ z.im = 0}.Finite := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_thetaFiniteShellCosine_neg N)
  have hne (b : ℝ) (hb : B ≤ b) : thetaFiniteShellEntire (N+1) (b : ℂ) ≠ 0 := by
    rw [thetaFiniteShellEntire_real]
    exact Complex.ofReal_ne_zero.mpr (ne_of_lt (hB b hb))
  have hf := differentiable_thetaFiniteShellEntire (N+1)
  have han := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hiso : ∀ z ∈ (univ : Set ℂ),
      ¬ (∀ᶠ w in 𝓝 z, thetaFiniteShellEntire (N+1) w = 0) := by
    intro z _ hz
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) hz
    exact hne B le_rfl (hzero (mem_univ (B : ℂ)))
  have hfinite := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact
    isOpen_univ hf.differentiableOn hiso
    (isCompact_closedBall (0 : ℂ) (|B|+1)) (subset_univ _)
  apply hfinite.subset
  intro z hz
  refine ⟨?_, hz.1⟩
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2
  have habs : thetaFiniteShellEntire (N+1) ((|z.re| : ℝ) : ℂ) =
      thetaFiniteShellEntire (N+1) z := by
    conv_rhs => rw [hzreal]
    rcases le_total 0 z.re with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, Complex.ofReal_neg, thetaFiniteShellEntire_neg]
  have hr : |z.re| < B := by
    by_contra hr
    exact hne |z.re| (le_of_not_gt hr) (habs.trans hz.1)
  rw [Metric.mem_closedBall, dist_zero_right, hzreal, Complex.norm_real,
    Real.norm_eq_abs]
  linarith [le_abs_self B]

/-- Every nonempty canonical theta-shell prefix has infinitely many nonreal
zeros. This does not make a claim about the complete theta source. -/
theorem thetaFiniteShellEntire_nonreal_zeroSet_infinite (N : ℕ) :
    {z : ℂ | thetaFiniteShellEntire (N+1) z = 0 ∧ z.im ≠ 0}.Infinite := by
  intro hfinite
  apply thetaFiniteShellEntire_zeroSet_infinite (N+1)
  apply (hfinite.union (thetaFiniteShellEntire_real_zeroSet_finite N)).subset
  intro z hz
  by_cases him : z.im = 0
  · exact Or.inr ⟨hz, him⟩
  · exact Or.inl ⟨hz, him⟩

end RHTower
