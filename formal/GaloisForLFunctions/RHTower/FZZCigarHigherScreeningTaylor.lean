import GaloisForLFunctions.RHTower.FZZCigarScreeningCollisionFinitePart
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Original higher screening subtraction and parameter analyticity

The full fifth Taylor polynomial of the regular position factor is subtracted
before plane integration. A fixed interval expansion of `(1+q*t)^(β/2)`, with
`q = ‖z‖² - 2*z.re`, keeps the base uniformly positive on the half-radius disk.
The sixth derivative gives a remainder bounded by `C*‖z‖⁶`, uniformly in a
neighborhood of every regular exponent. The original subtracted source is
therefore integrable for every singular exponent above `-8`.

The integral Taylor remainder retains a nonnegative product-measure weight and
the complete sixth descending factorial in `β/2`. Joint integrability precedes
Fubini. Its admitted exponential representation proves real analyticity in the
regular exponent; the original open exponential-moment interval proves real
analyticity in the singular exponent. Reflection admits the second puncture.

This is the local subtracted source. Restoring the complete integrated Taylor
polynomial, retaining the exterior and all collision pole values, and matching
the resulting higher finite part to the continued Gamma source remain separate
obligations. Positivity of the auxiliary weight is not positivity of that finite
part. No physical Ward identity, phase normalization, or RH assertion is assumed.
-/


open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

theorem affine_rpow_iteratedDeriv (n : ℕ) (s q t : ℝ)
    (ht : 0 < 1+q*t) :
    iteratedDeriv n (fun x : ℝ => (1+q*x)^s) t =
      q^n * (descPochhammer ℝ n).eval s * (1+q*t)^(s-n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hpos : ∀ᶠ x in 𝓝 t, 0 < 1+q*x :=
      (show ContinuousAt (fun x : ℝ => 1+q*x) t by fun_prop).eventually
        (eventually_gt_nhds ht)
    have heq : iteratedDeriv n (fun x : ℝ => (1+q*x)^s) =ᶠ[𝓝 t]
        (fun x : ℝ => q^n * (descPochhammer ℝ n).eval s * (1+q*x)^(s-n)) := by
      filter_upwards [hpos] with x hx
      exact ih x hx
    rw [heq.deriv_eq]
    have ha : HasDerivAt (fun x : ℝ => 1+q*x) q t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul q).const_add 1
    rw [((ha.rpow_const (p := s-n) (Or.inl ht.ne')).const_mul
      (q^n * (descPochhammer ℝ n).eval s)).deriv]
    rw [descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : s - (n : ℝ) - 1 = s - ((n : ℝ)+1) := by ring
    rw [he]
    ring

theorem affine_rpow_contDiffAt (s q t : ℝ) (ht : 0 < 1+q*t)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (fun x : ℝ => (1+q*x)^s) t :=
  (Real.contDiffAt_rpow_const_of_ne ht.ne').comp t
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))

theorem affine_base_bounds (q t : ℝ) (hq : q ∈ Icc (-3/4 : ℝ) (5/4))
    (ht : t ∈ Icc (0 : ℝ) 1) : 1+q*t ∈ Icc (1/4 : ℝ) (9/4) := by
  constructor
  · have h := mul_le_mul_of_nonneg_right hq.1 ht.1
    nlinarith [ht.2]
  · have h := mul_le_mul_of_nonneg_right hq.2 ht.1
    nlinarith [ht.2]

theorem affine_rpow_within (n : ℕ) (s q t : ℝ)
    (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (fun x : ℝ => (1+q*x)^s) (Icc 0 1) t =
      q^n * (descPochhammer ℝ n).eval s * (1+q*t)^(s-n) := by
  have hp : 0 < 1+q*t := lt_of_lt_of_le (by norm_num) (affine_base_bounds q t hq ht).1
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (affine_rpow_contDiffAt s q t hp n) ht]
  exact affine_rpow_iteratedDeriv n s q t hp

private theorem sixth_derivative_uniform_bound (s₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (s₀-1) (s₀+1),
      ∀ x ∈ Icc (1/4 : ℝ) (9/4),
        ‖(descPochhammer ℝ 6).eval s * x^(s-6)‖ ≤ C := by
  let K := Icc (s₀-1) (s₀+1) ×ˢ Icc (1/4 : ℝ) (9/4)
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      (descPochhammer ℝ 6).eval p.1 * p.2^(p.1-6)) K := by
    apply ((descPochhammer ℝ 6).continuous.comp continuous_fst).continuousOn.mul
    apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
    intro p hp
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hp.2.1))
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs x hx
  exact (hC (s,x) ⟨hs,hx⟩).trans (le_max_left _ _)

private theorem scalar_fifth_remainder_bound (s₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (s₀-1) (s₀+1),
      ∀ q ∈ Icc (-3/4 : ℝ) (5/4),
        ‖(1+q)^s - ∑ j ∈ Finset.range 6,
          (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j‖ ≤ C*|q|^(6 : ℕ) := by
  obtain ⟨C,hC0,hC⟩ := sixth_derivative_uniform_bound s₀
  refine ⟨C / ((5:ℕ).factorial : ℝ), by positivity, ?_⟩
  intro s hs q hq
  have hcont : ContDiffOn ℝ (5+1) (fun t : ℝ => (1+q*t)^s) (Icc 0 1) := by
    intro t ht
    exact (affine_rpow_contDiffAt s q t
      (lt_of_lt_of_le (by norm_num) (affine_base_bounds q t hq ht).1) _).contDiffWithinAt
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (5+1) (fun t : ℝ => (1+q*t)^s) (Icc 0 1) t‖ ≤ C*|q|^(6 : ℕ) := by
    intro t ht
    rw [affine_rpow_within 6 s q t hq ht, mul_assoc, norm_mul, norm_pow, Real.norm_eq_abs]
    simpa only [Nat.cast_ofNat, mul_comm] using mul_le_mul_of_nonneg_left
      (hC s hs (1+q*t) (affine_base_bounds q t hq ht)) (by positivity : 0 ≤ |q|^(6 : ℕ))
  have h := taylor_mean_remainder_bound (n := 5) (by norm_num : (0:ℝ) ≤ 1) hcont
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hb
  have ht : taylorWithinEval (fun t : ℝ => (1+q*t)^s) 5 (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range 6, (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [affine_rpow_within j s q 0 hq (by norm_num)]
    simp only [mul_zero, add_zero, Real.one_rpow, mul_one, sub_zero, one_pow, smul_eq_mul]
    ring
  rw [ht] at h
  simpa only [mul_one, sub_zero, one_pow, div_mul_eq_mul_div] using h

/-- The complete fifth Taylor polynomial of the original regular collision factor. -/
def fzzScreeningFifthTaylor (β : ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    (descPochhammer ℝ j).eval (β/2) / (j.factorial : ℝ) * (‖z‖^(2 : ℕ)-2*z.re)^j

/-- Pointwise subtraction is performed before the singular plane integral. -/
def fzzScreeningFifthSubtracted (α β : ℝ) (z : ℂ) : ℝ :=
  ‖z‖^α * (‖z-1‖^β - fzzScreeningFifthTaylor β z)

theorem plane_q_bounds (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    (‖z‖^(2 : ℕ)-2*z.re) ∈ Icc (-3/4 : ℝ) (5/4) ∧
      |‖z‖^(2 : ℕ)-2*z.re| ≤ (5/2)*‖z‖ := by
  have hr : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hr0 := norm_nonneg z
  have hre := abs_le.mp (Complex.abs_re_le_norm z)
  have hsq := mul_nonneg hr0 (show 0 ≤ 1/2-‖z‖ by linarith)
  have hlow := mul_nonneg (show 0 ≤ 1/2-‖z‖ by linarith)
    (show 0 ≤ 3/2-‖z‖ by linarith)
  constructor
  · constructor <;> nlinarith [hre.1,hre.2]
  · rw [abs_le]
    constructor <;> nlinarith [hre.1,hre.2]

private theorem plane_q_identity (z : ℂ) :
    1+(‖z‖^(2 : ℕ)-2*z.re) = ‖z-1‖^(2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring

/-- A uniform sixth-order bound in a full neighborhood of every regular exponent. -/
theorem fzzScreeningFifthTaylor_uniform_remainder (β₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Icc (β₀-2) (β₀+2),
      ∀ z ∈ closedBall (0 : ℂ) (1/2),
        ‖‖z-1‖^β - fzzScreeningFifthTaylor β z‖ ≤ C*‖z‖^(6 : ℕ) := by
  obtain ⟨C,hC0,hC⟩ := scalar_fifth_remainder_bound (β₀/2)
  refine ⟨C*(5/2)^(6 : ℕ), by positivity, ?_⟩
  intro β hβ z hz
  obtain ⟨hq,hqn⟩ := plane_q_bounds z hz
  have hβ' : β/2 ∈ Icc (β₀/2-1) (β₀/2+1) := by
    constructor <;> linarith [hβ.1,hβ.2]
  have h := hC (β/2) hβ' (‖z‖^(2 : ℕ)-2*z.re) hq
  rw [plane_q_identity, ← Real.rpow_natCast_mul (norm_nonneg (z-1))] at h
  simp only [Nat.cast_ofNat, show (2:ℝ)*(β/2)=β by ring] at h
  change ‖‖z-1‖^β - fzzScreeningFifthTaylor β z‖ ≤ _ at h
  exact h.trans (by
    calc
      C*|‖z‖^(2 : ℕ)-2*z.re|^(6 : ℕ) ≤ C*((5/2)*‖z‖)^(6 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hqn 6) hC0
      _ = (C*(5/2)^(6 : ℕ))*‖z‖^(6 : ℕ) := by rw [mul_pow]; ring)


private theorem fifth_subtracted_integrable (α β : ℝ) (hα : -8 < α) :
    IntegrableOn (fzzScreeningFifthSubtracted α β) (ball 0 (1/2)) := by
  obtain ⟨C,hC0,hC⟩ := fzzScreeningFifthTaylor_uniform_remainder β
  have hi : IntegrableOn (fun z : ℂ => ‖z‖^(α+6)) (ball 0 (1/2)) := by
    have h := (fzzScreeningPlaneKernel_integrable_zero_iff (α+6) 0).mpr (by linarith)
    change IntegrableOn (fun z : ℂ => ‖z‖^(α+6) * ‖z-1‖^(0:ℝ)) (ball 0 (1/2)) at h
    simpa only [Real.rpow_zero, mul_one] using h
  apply (hi.const_mul C).mono' (by
    unfold fzzScreeningFifthSubtracted fzzScreeningFifthTaylor
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz hz0
  have hn := norm_pos_iff.mpr hz0
  change ‖‖z‖^α * (‖z-1‖^β - fzzScreeningFifthTaylor β z)‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) α)]
  calc
    ‖z‖^α * ‖‖z-1‖^β - fzzScreeningFifthTaylor β z‖ ≤ ‖z‖^α * (C*‖z‖^(6 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (hC β (by constructor <;> linarith) z (ball_subset_closedBall hz))
        (Real.rpow_nonneg (norm_nonneg z) α)
    _ = C*‖z‖^(α+6) := by
      rw [Real.rpow_add hn]
      norm_num only [Real.rpow_ofNat]
      ring

/-- Subtracting the full fifth polynomial admits the original local source through
all three poles at exponents `-2`, `-4`, and `-6`. -/
theorem fzzScreeningFifthSubtracted_integrable (u β : ℝ) :
    IntegrableOn (fzzScreeningFifthSubtracted (-8+Real.exp u) β) (ball 0 (1/2)) :=
  fifth_subtracted_integrable _ β (by linarith [Real.exp_pos u])

/-- The reflected original subtraction has the same admission at the second puncture. -/
theorem fzzScreeningFifthSubtracted_reflected_integrable (u α : ℝ) :
    IntegrableOn (fun z : ℂ => fzzScreeningFifthSubtracted (-8+Real.exp u) α (1-z))
      (ball 1 (1/2)) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integrableOn_comp_preimage
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding
    (f := fzzScreeningFifthSubtracted (-8+Real.exp u) α) (s := ball 0 (1/2))
  have he : (fun z : ℂ => 1-z) ⁻¹' ball 0 (1/2) = ball 1 (1/2) := by
    ext z
    simp [mem_ball, dist_eq_norm, norm_sub_rev]
  rw [he] at h
  exact h.mpr (fzzScreeningFifthSubtracted_integrable u α)


private def higherPositiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))

theorem higherPositiveWeight_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : Integrable (fun z => f z*Real.exp (t*X z)) μ) :
    Integrable (fun z => Real.exp (t*X z)) (higherPositiveWeightMeasure μ f) := by
  rw [higherPositiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]
  apply hi.norm.mono' (by fun_prop)
  filter_upwards with z
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_max_right _ _),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem higherPositiveWeight_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    mgf X (higherPositiveWeightMeasure μ f) t = ∫ z, max (f z) 0*Real.exp (t*X z) ∂μ := by
  rw [mgf, higherPositiveWeightMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

theorem higher_signed_exp_analyticAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    AnalyticAt ℝ (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ) t := by
  have hn : ∀ᶠ s in 𝓝 t, Integrable (fun z => (-f z)*Real.exp (s*X z)) μ := by
    filter_upwards [hi] with s hs
    convert! hs.neg using 1
    ext z
    dsimp
    ring
  have hp : t ∈ interior (integrableExpSet X (higherPositiveWeightMeasure μ f)) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hi] with s hs
    exact higherPositiveWeight_integrable μ f X hf hX s hs
  have hm : t ∈ interior (integrableExpSet X (higherPositiveWeightMeasure μ (fun z => -f z))) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hn] with s hs
    exact higherPositiveWeight_integrable μ (fun z => -f z) X hf.neg hX s hs
  apply ((analyticAt_mgf hp).sub (analyticAt_mgf hm)).congr
  filter_upwards [hi, hn] with s hs ht
  simp only [Pi.sub_apply]
  rw [higherPositiveWeight_integral μ f X hf, higherPositiveWeight_integral μ (fun z => -f z) X hf.neg]
  have hip : Integrable (fun z => max (f z) 0*Real.exp (s*X z)) μ := by
    have h := higherPositiveWeight_integrable μ f X hf hX s hs
    rw [higherPositiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  have him : Integrable (fun z => max (-f z) 0*Real.exp (s*X z)) μ := by
    have h := higherPositiveWeight_integrable μ (fun z => -f z) X hf.neg hX s ht
    rw [higherPositiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  rw [← integral_sub hip him]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : 0 ≤ f z
  · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    ring
  · have hz' := le_of_not_ge hz
    rw [max_eq_right hz', max_eq_left (neg_nonneg.mpr hz')]
    ring

theorem fifth_subtracted_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningFifthSubtracted α β z * Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningFifthSubtracted (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖) = ‖z‖^δ by rw [Real.rpow_def_of_pos hn, mul_comm]]
  unfold fzzScreeningFifthSubtracted
  rw [Real.rpow_add hn]
  ring

private theorem fifth_subtracted_shift_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (α+δ) β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, -8 < α+δ :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa using ha)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningFifthSubtracted α β z * Real.exp (δ*Real.log ‖z‖))
        (volume.restrict (ball 0 (1/2))) := by
    filter_upwards [hshift] with δ hδ
    apply (fifth_subtracted_integrable (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (fifth_subtracted_shift α β δ hz).symm
  have han := higher_signed_exp_analyticAt (volume.restrict (ball (0 : ℂ) (1/2)))
    (fzzScreeningFifthSubtracted α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningFifthSubtracted fzzScreeningFifthTaylor; fun_prop)
    (by fun_prop) 0 hi
  apply han.congr
  filter_upwards with δ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  exact fifth_subtracted_shift α β δ hz

/-- The original subtracted source is analytic in its singular exponent throughout
the half-line above `-8`; no continued Gamma identity is used. -/
theorem fzzScreeningFifthSubtracted_singular_analytic (u β : ℝ) :
    AnalyticAt ℝ (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u+δ) β z) 0 :=
  fifth_subtracted_shift_analytic _ β (by linarith [Real.exp_pos u])

theorem affine_rpow_taylor (s q : ℝ) (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) :
    taylorWithinEval (fun t : ℝ => (1+q*t)^s) 5 (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range 6, (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [affine_rpow_within j s q 0 hq (by norm_num)]
  simp only [mul_zero, add_zero, Real.one_rpow, mul_one, sub_zero, one_pow, smul_eq_mul]
  ring

theorem scalar_fifth_integral_remainder (s q : ℝ)
    (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) :
    (1+q)^s - ∑ j ∈ Finset.range 6,
      (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j =
      ∫ t : ℝ in Ioc 0 1,
        ((1-t)^(5 : ℕ) / ((5:ℕ).factorial : ℝ)) *
          (q^(6 : ℕ) * (descPochhammer ℝ 6).eval s * (1+q*t)^(s-6)) := by
  have hf : ContDiffOn ℝ (5+1 : ℕ) (fun t : ℝ => (1+q*t)^s) (Icc 0 1) := by
    intro t ht
    exact (affine_rpow_contDiffAt s q t
      (lt_of_lt_of_le (by norm_num) (affine_base_bounds q t hq ht).1) _).contDiffWithinAt
  have h := taylor_integral_remainder (n := 5) (x := 1) (x₀ := 0)
    (by simpa only [uIcc_of_le zero_le_one] using hf)
  rw [uIcc_of_le zero_le_one, affine_rpow_taylor s q hq,
    intervalIntegral.integral_of_le zero_le_one] at h
  simp only [mul_one] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [affine_rpow_within 6 s q t hq ⟨ht.1.le,ht.2⟩, smul_eq_mul]
  simp only [Nat.cast_ofNat]

/-- The auxiliary measure retains the original plane position and a Taylor interval. -/
def fzzScreeningFifthLiftMeasure : Measure (ℂ × ℝ) :=
  (volume.restrict (ball (0 : ℂ) (1/2))).prod (volume.restrict (Ioc (0 : ℝ) 1))

/-- Original Taylor remainder weight; it is nonnegative on the integration domain. -/
def fzzScreeningFifthLiftWeight (α : ℝ) (p : ℂ × ℝ) : ℝ :=
  ‖p.1‖^α * (‖p.1‖^(2 : ℕ)-2*p.1.re)^(6 : ℕ) *
    ((1-p.2)^(5 : ℕ) / ((5:ℕ).factorial : ℝ)) *
    (1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2)^(-6 : ℝ)

/-- The bounded logarithmic variable for the regular source exponent. -/
def fzzScreeningFifthLiftLog (p : ℂ × ℝ) : ℝ :=
  Real.log (1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2)/2

theorem fifth_subtracted_lift_pointwise (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    fzzScreeningFifthSubtracted α β z =
      (descPochhammer ℝ 6).eval (β/2) *
        ∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t) *
          Real.exp (β*fzzScreeningFifthLiftLog (z,t)) := by
  have hq := (plane_q_bounds z hz).1
  have h := scalar_fifth_integral_remainder (β/2) (‖z‖^(2 : ℕ)-2*z.re) hq
  rw [plane_q_identity, ← Real.rpow_natCast_mul (norm_nonneg (z-1))] at h
  simp only [Nat.cast_ofNat, show (2:ℝ)*(β/2)=β by ring] at h
  change ‖z-1‖^β - fzzScreeningFifthTaylor β z = _ at h
  rw [fzzScreeningFifthSubtracted, h, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : 0 < 1+(‖z‖^(2 : ℕ)-2*z.re)*t :=
    lt_of_lt_of_le (by norm_num) (affine_base_bounds _ t hq ⟨ht.1.le,ht.2⟩).1
  have he : (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(β/2-6) =
      (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(-6 : ℝ) *
        Real.exp (β*(Real.log (1+(‖z‖^(2 : ℕ)-2*z.re)*t)/2)) := by
    rw [show β/2-6 = β/2+(-6) by ring, Real.rpow_add hp]
    rw [Real.rpow_def_of_pos hp]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  rw [he]
  dsimp [fzzScreeningFifthLiftWeight, fzzScreeningFifthLiftLog]
  ring


private def fifthLiftCompact : Set (ℂ × ℝ) :=
  closedBall (0 : ℂ) (1/2) ×ˢ Icc (0 : ℝ) 1

private theorem fifth_lift_base_pos (p : ℂ × ℝ) (hp : p ∈ fifthLiftCompact) :
    0 < 1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2 :=
  lt_of_lt_of_le (by norm_num)
    (affine_base_bounds _ _ (plane_q_bounds p.1 hp.1).1 hp.2).1

private theorem fifth_lift_log_continuous :
    ContinuousOn fzzScreeningFifthLiftLog fifthLiftCompact := by
  unfold fzzScreeningFifthLiftLog
  exact ((show ContinuousOn (fun p : ℂ × ℝ => 1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2)
      fifthLiftCompact by fun_prop).log (fun p hp => (fifth_lift_base_pos p hp).ne')).div_const 2

private def fifthLiftFactor (β : ℝ) (p : ℂ × ℝ) : ℝ :=
  ((1-p.2)^(5 : ℕ) / ((5:ℕ).factorial : ℝ)) *
    (1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2)^(-6 : ℝ) *
    Real.exp (β*fzzScreeningFifthLiftLog p)

private theorem fifth_lift_factor_continuous (β : ℝ) :
    ContinuousOn (fifthLiftFactor β) fifthLiftCompact := by
  have hp : ContinuousOn (fun p : ℂ × ℝ =>
      (1+(‖p.1‖^(2 : ℕ)-2*p.1.re)*p.2)^(-6 : ℝ)) fifthLiftCompact := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro p hp
    exact Or.inl (fifth_lift_base_pos p hp).ne'
  exact ((show ContinuousOn (fun p : ℂ × ℝ =>
      (1-p.2)^(5 : ℕ) / ((5:ℕ).factorial : ℝ)) fifthLiftCompact by fun_prop).mul hp).mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul fifth_lift_log_continuous))

theorem fifth_lift_exp_integrable (α β : ℝ) (ha : -8 < α) :
    Integrable (fun p => fzzScreeningFifthLiftWeight α p * Real.exp (β*fzzScreeningFifthLiftLog p))
      fzzScreeningFifthLiftMeasure := by
  have hr : IntegrableOn (fun z : ℂ => ‖z‖^(α+6)) (ball 0 (1/2)) := by
    have h := (fzzScreeningPlaneKernel_integrable_zero_iff (α+6) 0).mpr (by linarith)
    change IntegrableOn (fun z : ℂ => ‖z‖^(α+6) * ‖z-1‖^(0:ℝ)) (ball 0 (1/2)) at h
    simpa only [Real.rpow_zero, mul_one] using h
  have hi : Integrable (fun p : ℂ × ℝ => ‖p.1‖^(α+6)) fzzScreeningFifthLiftMeasure := by
    have h := hr.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)))
    simpa only [fzzScreeningFifthLiftMeasure, mul_one] using h
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : ℂ) (1/2)).prod isCompact_Icc).exists_bound_of_continuousOn
    (fifth_lift_factor_continuous β)
  apply (hi.const_mul ((5/2)^(6 : ℕ) * max C 0)).mono' (by
    unfold fzzScreeningFifthLiftWeight fzzScreeningFifthLiftLog
    fun_prop)
  rw [fzzScreeningFifthLiftMeasure, Measure.ae_prod_iff_ae_ae (measurableSet_le
    (by unfold fzzScreeningFifthLiftWeight fzzScreeningFifthLiftLog; fun_prop) (by fun_prop))]
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz hz0
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hn := norm_pos_iff.mpr hz0
  have hq := (plane_q_bounds z (ball_subset_closedBall hz)).2
  have hcp : ‖fifthLiftFactor β (z,t)‖ ≤ max C 0 :=
    (hC (z,t) ⟨ball_subset_closedBall hz, ht.1.le, ht.2⟩).trans (le_max_left _ _)
  have he : fzzScreeningFifthLiftWeight α (z,t) * Real.exp (β*fzzScreeningFifthLiftLog (z,t)) =
      ‖z‖^α * (‖z‖^(2 : ℕ)-2*z.re)^(6 : ℕ) * fifthLiftFactor β (z,t) := by
    dsimp [fzzScreeningFifthLiftWeight, fifthLiftFactor]
    ring
  change ‖fzzScreeningFifthLiftWeight α (z,t) * Real.exp (β*fzzScreeningFifthLiftLog (z,t))‖ ≤ _
  rw [he, norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) α),
    norm_pow, Real.norm_eq_abs]
  calc
    ‖z‖^α * |‖z‖^(2 : ℕ)-2*z.re|^(6 : ℕ) * ‖fifthLiftFactor β (z,t)‖ ≤
        ‖z‖^α * |‖z‖^(2 : ℕ)-2*z.re|^(6 : ℕ) * max C 0 :=
      mul_le_mul_of_nonneg_left hcp (by positivity)
    _ ≤ ‖z‖^α * ((5/2)*‖z‖)^(6 : ℕ) * max C 0 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hq 6) (by positivity))
        (le_max_right _ _)
    _ = ((5/2)^(6 : ℕ) * max C 0) * ‖z‖^(α+6) := by
      rw [mul_pow, Real.rpow_add hn]
      norm_num only [Real.rpow_ofNat]
      ring

private theorem fifth_lift_identity (α β : ℝ) (ha : -8 < α) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted α β z) =
      (descPochhammer ℝ 6).eval (β/2) *
        ∫ p : ℂ × ℝ, fzzScreeningFifthLiftWeight α p * Real.exp (β*fzzScreeningFifthLiftLog p)
          ∂fzzScreeningFifthLiftMeasure := by
  rw [fzzScreeningFifthLiftMeasure, integral_prod _ (fifth_lift_exp_integrable α β ha),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact fifth_subtracted_lift_pointwise α β z (ball_subset_closedBall hz)

/-- The original local source factors through an admitted exponential integral;
the descending factorial, including its sign and zeros, is retained exactly. -/
theorem fzzScreeningFifthSubtracted_lift_identity (u β : ℝ) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (-8+Real.exp u) β z) =
      (descPochhammer ℝ 6).eval (β/2) *
        ∫ p : ℂ × ℝ, fzzScreeningFifthLiftWeight (-8+Real.exp u) p *
          Real.exp (β*fzzScreeningFifthLiftLog p) ∂fzzScreeningFifthLiftMeasure :=
  fifth_lift_identity _ β (by linarith [Real.exp_pos u])

/-- Every real regular exponent is admitted in the original lifted source. -/
theorem fzzScreeningFifthLift_exp_integrable (u β : ℝ) :
    Integrable (fun p => fzzScreeningFifthLiftWeight (-8+Real.exp u) p *
      Real.exp (β*fzzScreeningFifthLiftLog p)) fzzScreeningFifthLiftMeasure :=
  fifth_lift_exp_integrable _ β (by linarith [Real.exp_pos u])

/-- The Taylor weight is nonnegative on its original product measure. -/
theorem fzzScreeningFifthLiftWeight_nonneg (α : ℝ) :
    ∀ᵐ p ∂fzzScreeningFifthLiftMeasure, 0 ≤ fzzScreeningFifthLiftWeight α p := by
  rw [fzzScreeningFifthLiftMeasure, Measure.ae_prod_iff_ae_ae (measurableSet_le
    measurable_const (by unfold fzzScreeningFifthLiftWeight; fun_prop))]
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' : 0 ≤ 1-t := by linarith [ht.2]
  have hp := fifth_lift_base_pos (z,t) ⟨ball_subset_closedBall hz, ht.1.le, ht.2⟩
  unfold fzzScreeningFifthLiftWeight
  positivity

/-- The complete pointwise subtraction has analytic dependence on its regular
exponent, with the singular-domain assumption discharged from the parameter. -/
theorem fzzScreeningFifthSubtracted_regular_analytic (u β : ℝ) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u) s z) β := by
  have h := higher_signed_exp_analyticAt fzzScreeningFifthLiftMeasure
    (fzzScreeningFifthLiftWeight (-8+Real.exp u)) fzzScreeningFifthLiftLog
    (by unfold fzzScreeningFifthLiftWeight; fun_prop)
    (by unfold fzzScreeningFifthLiftLog; fun_prop) β
    (Eventually.of_forall (fun s => fzzScreeningFifthLift_exp_integrable u s))
  have hp : AnalyticAt ℝ (fun s : ℝ => (descPochhammer ℝ 6).eval (s/2)) β :=
    ((analyticAt_id (𝕜 := ℝ) (z := β)).div_const).aeval_polynomial (descPochhammer ℝ 6)
  apply (hp.mul h).congr
  filter_upwards with s
  exact (fzzScreeningFifthSubtracted_lift_identity u s).symm


end GaloisForLFunctions.RHTower
