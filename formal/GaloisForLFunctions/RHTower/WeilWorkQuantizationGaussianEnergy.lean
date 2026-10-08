import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianCoefficientLimit

/-!
# Actual centered Gaussian energy detects every nonrigid source

The literal critical trace is measurable, respects conjugation, and has
integrable Gaussian energy. Each normalized Fourier moment is bounded by
that physical energy. Exact coefficient recovery then yields arithmetic
rigidity/RH or a positive linear lower bound at every sufficiently large scale.
No boundary Dirichlet expansion or limiting-energy premise is assumed.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

theorem measurable_quantizationCenteredTrace (hW : WeilPositiveFull lam) :
    Measurable (quantizationCenteredTrace hW) := by
  have hz : Continuous (fun t : ℝ => riemannZeta (tracePoint 0 t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hn : tracePoint 0 t ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num [tracePoint] at this
    exact (differentiableAt_riemannZeta hn).continuousAt.comp (by unfold tracePoint; fun_prop)
  exact (measurable_quantizationTraceF hW).sub (hz.measurable.const_mul _)

theorem quantizationCenteredTrace_neg (hW : WeilPositiveFull lam) (t : ℝ) :
    quantizationCenteredTrace hW (-t) = conj (quantizationCenteredTrace hW t) := by
  have hb := sourceCompletion_conj hW (s := 1) (by norm_num)
  simp only [map_one] at hb
  have ht : tracePoint 0 (-t) = conj (tracePoint 0 t) := by
    apply Complex.ext <;> simp [tracePoint]
  simp only [quantizationCenteredTrace, quantizationTraceF_neg, ht, riemannZeta_conj,
    map_sub, map_mul, ← hb]

private theorem gaussian_measurable (T : ℝ) : Measurable (quantizationGaussianWeight T) := by
  unfold quantizationGaussianWeight
  fun_prop

private theorem gaussian_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (quantizationGaussianWeight T) :=
  integrable_exp_neg_mul_sq (by positivity : 0 < 1 / T ^ 2)

theorem integral_quantizationGaussianWeight {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, quantizationGaussianWeight T t) = T * Real.sqrt Real.pi := by
  unfold quantizationGaussianWeight
  rw [integral_gaussian]
  rw [div_div_eq_mul_div, div_one, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hT.le]
  ring

theorem integrable_quantizationCenteredTrace_gaussian_square (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => ‖quantizationCenteredTrace hW t‖ ^ 2 *
      quantizationGaussianWeight T t) := by
  obtain ⟨C, hC, hb⟩ := exists_quantizationCenteredTrace_bound hW
  have hg := gaussian_integrable hT
  have hg2 : Integrable (fun t : ℝ => t ^ 2 * quantizationGaussianWeight T t) := by
    simpa only [Real.rpow_two, quantizationGaussianWeight] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / T ^ 2)
        (by positivity) (s := 2) (by norm_num))
  have hm : Integrable (fun t : ℝ => 2 * C ^ 2 *
      (quantizationGaussianWeight T t + t ^ 2 * quantizationGaussianWeight T t)) :=
    (hg.add hg2).const_mul _
  refine hm.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (((measurable_quantizationCenteredTrace hW).norm.pow_const 2).mul
      (gaussian_measurable T)).aestronglyMeasurable
  · have hg0 : 0 ≤ quantizationGaussianWeight T t := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hg0)]
    have hsq : ‖quantizationCenteredTrace hW t‖ ^ 2 ≤ (C * (1 + |t|)) ^ 2 := by
      nlinarith [hb t, norm_nonneg (quantizationCenteredTrace hW t)]
    have hp : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    have hbound : ‖quantizationCenteredTrace hW t‖ ^ 2 ≤ 2 * C ^ 2 * (1 + t ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg C)]
    nlinarith [mul_le_mul_of_nonneg_right hbound hg0]

/-- Positive-height energy of the literal pole-centered critical trace. -/
def quantizationCenteredGaussianEnergy (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t

theorem quantizationCenteredGaussianEnergy_nonneg (hW : WeilPositiveFull lam) (T : ℝ) :
    0 ≤ quantizationCenteredGaussianEnergy hW T := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem integral_quantizationCenteredTrace_gaussian_square (hW : WeilPositiveFull lam) (T : ℝ) :
    (∫ t : ℝ, ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t) =
      2 * quantizationCenteredGaussianEnergy hW T := by
  have he (t : ℝ) : ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t =
      ‖quantizationCenteredTrace hW |t|‖ ^ 2 * quantizationGaussianWeight T |t| := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, quantizationCenteredTrace_neg, Complex.norm_conj]
      simp [quantizationGaussianWeight]
  calc
    _ = ∫ t : ℝ, ‖quantizationCenteredTrace hW |t|‖ ^ 2 * quantizationGaussianWeight T |t| :=
      integral_congr_ae (Eventually.of_forall he)
    _ = _ := integral_comp_abs (f := fun t =>
      ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t)

private theorem norm_centeredGaussianTrace (hW : WeilPositiveFull lam) (T ℓ t : ℝ) :
    ‖quantizationCenteredGaussianTrace hW T ℓ t‖ =
      ‖quantizationCenteredTrace hW t‖ * quantizationGaussianWeight T t := by
  rw [quantizationCenteredGaussianTrace, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < quantizationGaussianWeight T t from Real.exp_pos _),
    Complex.norm_exp]
  simp

theorem integrable_quantizationCenteredGaussianTrace (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) (ℓ : ℝ) : Integrable (quantizationCenteredGaussianTrace hW T ℓ) := by
  have hmaj := (integrable_quantizationCenteredTrace_gaussian_square hW hT).add
    (gaussian_integrable hT)
  refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have he : Continuous (fun t : ℝ => Complex.exp ((ℓ : ℂ) * ((t : ℂ) * I))) := by fun_prop
    exact ((he.measurable.mul (measurable_quantizationCenteredTrace hW)).mul
      (Complex.continuous_ofReal.measurable.comp (gaussian_measurable T))).aestronglyMeasurable
  · rw [norm_centeredGaussianTrace]
    have hg : 0 ≤ quantizationGaussianWeight T t := (Real.exp_pos _).le
    have h : ‖quantizationCenteredTrace hW t‖ ≤ ‖quantizationCenteredTrace hW t‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖quantizationCenteredTrace hW t‖ - 1)]
    simpa only [Pi.add_apply, add_mul, one_mul] using mul_le_mul_of_nonneg_right h hg

/-- Each actual Gaussian Fourier moment is bounded by the normalized physical energy. -/
theorem norm_quantizationCenteredGaussianMoment_sq_le (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    ‖quantizationCenteredGaussianMoment hW T ℓ‖ ^ 2 ≤
      2 * quantizationCenteredGaussianEnergy hW T / (T * Real.sqrt Real.pi) := by
  let c := quantizationCenteredGaussianMoment hW T ℓ
  let M := T * Real.sqrt Real.pi
  have hM : 0 < M := mul_pos hT (Real.sqrt_pos.mpr Real.pi_pos)
  have hJ := integrable_quantizationCenteredGaussianTrace hW hT ℓ
  have hleft := (hJ.const_mul (conj c)).re.const_mul 2
  have hright := (integrable_quantizationCenteredTrace_gaussian_square hW hT).add
    ((gaussian_integrable hT).const_mul (‖c‖ ^ 2))
  have hp (t : ℝ) : 2 * (conj c * quantizationCenteredGaussianTrace hW T ℓ t).re ≤
      ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t +
        ‖c‖ ^ 2 * quantizationGaussianWeight T t := by
    have hr := Complex.re_le_norm (conj c * quantizationCenteredGaussianTrace hW T ℓ t)
    rw [norm_mul, Complex.norm_conj, norm_centeredGaussianTrace] at hr
    have hg : 0 ≤ quantizationGaussianWeight T t := (Real.exp_pos _).le
    nlinarith [mul_nonneg (sq_nonneg (‖quantizationCenteredTrace hW t‖ - ‖c‖)) hg]
  have hi := integral_mono hleft hright hp
  change (∫ t : ℝ, 2 * (conj c * quantizationCenteredGaussianTrace hW T ℓ t).re) ≤
    ∫ t : ℝ, ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t +
      ‖c‖ ^ 2 * quantizationGaussianWeight T t at hi
  have hir : (∫ t : ℝ, (conj c * quantizationCenteredGaussianTrace hW T ℓ t).re) =
      (∫ t : ℝ, conj c * quantizationCenteredGaussianTrace hW T ℓ t).re :=
    integral_re (hJ.const_mul (conj c))
  rw [integral_const_mul, hir, integral_const_mul,
    integral_add (integrable_quantizationCenteredTrace_gaussian_square hW hT)
      ((gaussian_integrable hT).const_mul (‖c‖ ^ 2)),
    integral_const_mul, integral_quantizationGaussianWeight hT,
    integral_quantizationCenteredTrace_gaussian_square] at hi
  have hc : (∫ t : ℝ, quantizationCenteredGaussianTrace hW T ℓ t) = (M : ℂ) * c := by
    dsimp [c, M, quantizationCenteredGaussianMoment]
    have hm : ((T * Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]
  have hr : (conj c * ((M : ℂ) * c)).re = M * ‖c‖ ^ 2 := by
    rw [show conj c * ((M : ℂ) * c) = (M : ℂ) * (c * conj c) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hc, hr] at hi
  apply (le_div_iff₀ hM).mpr
  dsimp only [M] at hi ⊢
  nlinarith

/-- A nonzero literal coefficient forces positive linear physical energy at all large scales. -/
theorem eventually_quantizationCenteredGaussianEnergy_lower (hW : WeilPositiveFull lam)
    {n : ℕ} (hn : 0 < n) (hu : quantizationCenteredCoeff hW n ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      κ * T ≤ quantizationCenteredGaussianEnergy hW T := by
  let q : ℝ := ‖quantizationCenteredCoeff hW n / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hq : 0 < q := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact div_ne_zero hu (by exact_mod_cast (Real.sqrt_pos.mpr hnR).ne')
  have ht := (tendsto_quantizationCenteredGaussianMoment hW hn).norm.pow 2
  have he : ∀ᶠ T : ℝ in atTop, q / 2 <
      ‖quantizationCenteredGaussianMoment hW T (Real.log (n : ℝ))‖ ^ 2 :=
    ht.eventually (lt_mem_nhds (by dsimp [q] at hq ⊢; linarith))
  refine ⟨Real.sqrt Real.pi * q / 4, by positivity, ?_⟩
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  have hb := norm_quantizationCenteredGaussianMoment_sq_le hW hT0 (Real.log (n : ℝ))
  have hh := (le_div_iff₀ (mul_pos hT0 (Real.sqrt_pos.mpr Real.pi_pos))).mp hb
  have hprod := mul_le_mul_of_nonneg_right hT.le
    (mul_pos hT0 (Real.sqrt_pos.mpr Real.pi_pos)).le
  nlinarith

/-- Full positivity gives arithmetic rigidity/RH or an eventual positive linear centered energy. -/
theorem quantization_rigidity_or_centeredGaussianEnergy_lower (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
        κ * T ≤ quantizationCenteredGaussianEnergy hW T := by
  classical
  by_cases hu : ∃ n : ℕ, 0 < n ∧ quantizationCenteredCoeff hW n ≠ 0
  · obtain ⟨n, hn, hne⟩ := hu
    exact Or.inr (eventually_quantizationCenteredGaussianEnergy_lower hW hn hne)
  left
  have hz (n : ℕ) (hn : n ≠ 0) : sourceCoeff lam n = sourceCompletion hW 1 := by
    have hh : quantizationCenteredCoeff hW n = 0 := by
      by_contra hh
      exact hu ⟨n, Nat.pos_of_ne_zero hn, hh⟩
    simpa only [quantizationCenteredCoeff, if_neg hn, sub_eq_zero] using hh
  have hb : sourceCompletion hW 1 = 1 := by
    rw [← hz 1 (by decide)]
    exact GaloisForLFunctions.HTGeometry.dirichletExp_one
      (IntegerMassRigidity.lamLog_zero lam) (IntegerMassRigidity.lamLog_one lam)
  have hone (n : ℕ) (hn : n ≠ 0) :
      GaloisForLFunctions.HTGeometry.dirichletExp (IntegerMassRigidity.lamLog lam) n = 1 :=
    (hz n hn).trans hb
  exact AbelianTwist.vonMangoldt_and_RH_of_coeff_eq_one
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (differentiableOn_weilContinuation hW) (fun _ hs => quantizationContinuation_eq_arch hW hs)
    (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW) hone

end RHTower.WeilSpectral
