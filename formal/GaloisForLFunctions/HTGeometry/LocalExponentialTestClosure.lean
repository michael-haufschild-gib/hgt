import Mathlib

/-!
# Local-exponential test closure

A finite measure on `ℝ` that integrates one exponential window `e^{a|x|}` is determined by its
moments: the complex moment-generating functions of two such measures are analytic on the common
vertical strip, their jets at the origin are the moment sequences, and the identity theorem
propagates the vanishing difference to the imaginary axis, where it is the characteristic function.

This is the local-exponential replacement for entire-moment determinacy, and it is the closure
mechanism behind polynomial density in `L²` of such a measure.
-/

namespace HTGeometry

open MeasureTheory ProbabilityTheory Complex Filter Set

/-! ## Vanishing jets -/

/-- A vanishing jet forces a vanishing analytic germ. -/
theorem eventuallyEq_zero_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (h : ∀ n, iteratedDeriv n f z = 0) :
    ∀ᶠ w in nhds z, f w = 0 := by
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f z :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr fun i _ => h i
  rw [← hm] at hle
  simp only [Nat.cast_add, Nat.cast_one] at hle
  rw [ENat.add_one_le_iff (by simp)] at hle
  exact lt_irrefl _ hle

/-! ## The exponential window strip -/

/-- The open vertical strip of half-width `a`. -/
def momentStrip (a : ℝ) : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo (-a) a}

theorem momentStrip_convex (a : ℝ) : Convex ℝ (momentStrip a) :=
  (convex_Ioo (-a) a).linear_preimage Complex.reLm

theorem zero_mem_momentStrip {a : ℝ} (ha : 0 < a) : (0 : ℂ) ∈ momentStrip a := by
  refine ⟨by simpa using by linarith, by simpa using ha⟩

theorem mul_I_mem_momentStrip {a : ℝ} (ha : 0 < a) (t : ℝ) : ((t : ℂ) * I) ∈ momentStrip a := by
  have hre : ((t : ℂ) * I).re = 0 := by simp
  refine ⟨?_, ?_⟩ <;> rw [hre] <;> linarith

theorem momentStrip_subset_interior {a : ℝ} {μ : Measure ℝ}
    (hμ : Set.Ioo (-a) a ⊆ integrableExpSet id μ) :
    momentStrip a ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet id μ)} :=
  fun _ hz => interior_maximal hμ isOpen_Ioo hz

/-! ## Local-exponential moment determinacy -/

/-- **Local-exponential moment determinacy.**  Two finite measures on `ℝ` sharing one exponential
window and all moments coincide. -/
theorem measure_eq_of_forall_moment_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : ℝ} (ha : 0 < a)
    (hμ : Set.Ioo (-a) a ⊆ integrableExpSet id μ)
    (hν : Set.Ioo (-a) a ⊆ integrableExpSet id ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n ∂μ = ∫ x : ℝ, (x : ℂ) ^ n ∂ν) :
    μ = ν := by
  have hsubμ := momentStrip_subset_interior hμ
  have hsubν := momentStrip_subset_interior hν
  have hzero := zero_mem_momentStrip ha
  have hanμ : AnalyticOnNhd ℂ (complexMGF id μ) (momentStrip a) :=
    analyticOnNhd_complexMGF.mono hsubμ
  have hanν : AnalyticOnNhd ℂ (complexMGF id ν) (momentStrip a) :=
    analyticOnNhd_complexMGF.mono hsubν
  have hdiff : AnalyticOnNhd ℂ (complexMGF id μ - complexMGF id ν) (momentStrip a) :=
    hanμ.sub hanν
  have hjet : ∀ n, iteratedDeriv n (complexMGF id μ - complexMGF id ν) 0 = 0 := by
    intro n
    rw [iteratedDeriv_sub (hanμ 0 hzero).contDiffAt (hanν 0 hzero).contDiffAt,
      iteratedDeriv_complexMGF (hsubμ hzero) n, iteratedDeriv_complexMGF (hsubν hzero) n]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    rw [hmom n, sub_self]
  have hgerm : (complexMGF id μ - complexMGF id ν) =ᶠ[nhds 0] 0 :=
    eventuallyEq_zero_of_iteratedDeriv_eq_zero (hdiff 0 hzero) hjet
  have heq : Set.EqOn (complexMGF id μ - complexMGF id ν) 0 (momentStrip a) :=
    hdiff.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (momentStrip_convex a).isPreconnected hzero hgerm
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hmem := heq (mul_I_mem_momentStrip ha t)
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hmem
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I, hmem]

/-- **Local-exponential moment determinacy, real form.** -/
theorem measure_eq_of_forall_real_moment_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμ : Set.Ioo (-a) a ⊆ integrableExpSet id μ)
    (hν : Set.Ioo (-a) a ⊆ integrableExpSet id ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂μ = ∫ x : ℝ, x ^ n ∂ν) :
    μ = ν := by
  refine measure_eq_of_forall_moment_eq ha hμ hν fun n => ?_
  have hcast : ∀ ρ : Measure ℝ, ∫ x : ℝ, (x : ℂ) ^ n ∂ρ = ((∫ x : ℝ, x ^ n ∂ρ : ℝ) : ℂ) := by
    intro ρ
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (Complex.ofReal_pow x n).symm)
  rw [hcast, hcast, hmom n]

/-! ## Exponential domination of monomials -/

theorem pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx (n + 1))
  refine Finset.single_le_sum (f := fun i : ℕ => x ^ i / (i.factorial : ℝ)) (fun i _ => ?_)
    (Finset.self_mem_range_succ n)
  positivity

/-- Every monomial is dominated by the exponential window. -/
theorem abs_pow_le_const_mul_exp {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    |x| ^ n ≤ (n.factorial : ℝ) / a ^ n * Real.exp (a * |x|) := by
  have hax : (0 : ℝ) ≤ a * |x| := mul_nonneg ha.le (abs_nonneg x)
  have h := pow_div_factorial_le_exp hax n
  have hfa : (n.factorial : ℝ) ≠ 0 := by positivity
  have han : (a : ℝ) ^ n ≠ 0 := by positivity
  have key : |x| ^ n = ((n.factorial : ℝ) / a ^ n) * ((a * |x|) ^ n / (n.factorial : ℝ)) := by
    rw [mul_pow]
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ## Square integrability in the exponential window -/

section Window

variable {μ : Measure ℝ}

/-- The half window lies in `L²`. -/
theorem memLp_two_exp_half {a : ℝ} (hexp : Integrable (fun x => Real.exp (a * |x|)) μ) :
    MemLp (fun x : ℝ => Real.exp (a * |x| / 2)) 2 μ := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).mpr (hexp.congr ?_)
  filter_upwards with x
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- Every monomial lies in `L²` of a measure with an exponential window. -/
theorem memLp_two_pow {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 μ := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).mpr ?_
  refine Integrable.mono (hexp.const_mul (((2 * n).factorial : ℝ) / a ^ (2 * n)))
    (by fun_prop) ?_
  filter_upwards with x
  have hb := abs_pow_le_const_mul_exp ha (2 * n) x
  have hsq : ((x : ℝ) ^ n) ^ 2 = x ^ (2 * n) := by
    rw [← pow_mul, mul_comm]
  have hnn : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) / a ^ (2 * n) * Real.exp (a * |x|) := by
    have := (Real.exp_pos (a * |x|)).le
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, hsq, abs_pow]
  exact hb

/-- **Cauchy--Schwarz window pairing.**  A weight dominated by the half window pairs integrably
with any `L²` density. -/
theorem integrable_mul_of_le_exp_half {a : ℝ}
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ)
    {h : ℝ → ℝ} (hmeas : AEStronglyMeasurable h μ)
    (hbound : ∀ᵐ x ∂μ, |h x| ≤ Real.exp (a * |x| / 2)) :
    Integrable (fun x => h x * f x) μ := by
  have hhL2 : MemLp h 2 μ := by
    refine MemLp.of_le (memLp_two_exp_half hexp) hmeas ?_
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hx
  exact hhL2.integrable_mul hf

end Window

/-! ## Theorem 2.1: the orthogonal complement of the polynomials is trivial -/

section Density

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The positive part of a density, as a nonnegative-real weight. -/
noncomputable def posWeight (f : ℝ → ℝ) (x : ℝ) : NNReal := Real.toNNReal (f x)

/-- The negative part of a density, as a nonnegative-real weight. -/
noncomputable def negWeight (f : ℝ → ℝ) (x : ℝ) : NNReal := Real.toNNReal (-f x)

theorem coe_posWeight (f : ℝ → ℝ) (x : ℝ) : ((posWeight f x : NNReal) : ℝ) = max (f x) 0 :=
  Real.coe_toNNReal' _

theorem coe_negWeight (f : ℝ → ℝ) (x : ℝ) : ((negWeight f x : NNReal) : ℝ) = max (-f x) 0 :=
  Real.coe_toNNReal' _

theorem coe_posWeight_sub_coe_negWeight (f : ℝ → ℝ) (x : ℝ) :
    ((posWeight f x : NNReal) : ℝ) - ((negWeight f x : NNReal) : ℝ) = f x := by
  rw [coe_posWeight, coe_negWeight]
  rcases le_or_gt 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right h.le, max_eq_left (by linarith), zero_sub, neg_neg]

theorem abs_coe_posWeight_le (f : ℝ → ℝ) (x : ℝ) :
    |((posWeight f x : NNReal) : ℝ)| ≤ |f x| := by
  rw [coe_posWeight, abs_of_nonneg (le_max_right _ _ |>.trans_eq rfl : (0:ℝ) ≤ max (f x) 0)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem abs_coe_negWeight_le (f : ℝ → ℝ) (x : ℝ) :
    |((negWeight f x : NNReal) : ℝ)| ≤ |f x| := by
  rw [coe_negWeight, abs_of_nonneg (le_max_right _ _ |>.trans_eq rfl : (0:ℝ) ≤ max (-f x) 0)]
  exact max_le ((neg_le_abs _).trans (le_of_eq rfl)) (abs_nonneg _)

omit [IsFiniteMeasure μ] in
theorem lintegral_toNNReal_ne_top {g : ℝ → ℝ} (hg : Integrable g μ) :
    ∫⁻ x, ((Real.toNNReal (g x) : NNReal) : ENNReal) ∂μ ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt ?_ hg.hasFiniteIntegral)
  exact lintegral_ofReal_le_lintegral_enorm g

omit [IsFiniteMeasure μ] in
/-- A nonnegative weight bounded by an `L²` density lies in `L²`. -/
theorem memLp_two_coe_weight {f : ℝ → ℝ} (hf : MemLp f 2 μ) {ρ : ℝ → NNReal}
    (hρ : AEMeasurable ρ μ) (hle : ∀ x, ((ρ x : NNReal) : ℝ) ≤ |f x|) :
    MemLp (fun x => ((ρ x : NNReal) : ℝ)) 2 μ := by
  refine MemLp.of_le hf hρ.coe_nnreal_real.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (ρ x).coe_nonneg]
  exact hle x

omit [IsFiniteMeasure μ] in
/-- A tilted weight inherits the exponential window of the base measure. -/
theorem window_subset_integrableExpSet {a : ℝ}
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) {ρ : ℝ → NNReal} (hρ : AEMeasurable ρ μ)
    (hle : ∀ x, ((ρ x : NNReal) : ℝ) ≤ |f x|) :
    Set.Ioo (-(a / 2)) (a / 2)
      ⊆ integrableExpSet id (μ.withDensity fun x => ((ρ x : NNReal) : ENNReal)) := by
  intro t ht
  have hρL2 : MemLp (fun x => ((ρ x : NNReal) : ℝ)) 2 μ := memLp_two_coe_weight hf hρ hle
  have hbound : ∀ᵐ x ∂μ, |Real.exp (t * x)| ≤ Real.exp (a * |x| / 2) := by
    filter_upwards with x
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have h1 : t * x ≤ |t| * |x| := (le_abs_self _).trans_eq (abs_mul t x)
    have h2 : |t| ≤ a / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc t * x ≤ |t| * |x| := h1
      _ ≤ (a / 2) * |x| := mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
      _ = a * |x| / 2 := by ring
  have hint : Integrable (fun x => Real.exp (t * x) * ((ρ x : NNReal) : ℝ)) μ :=
    integrable_mul_of_le_exp_half hexp hρL2 (by fun_prop) hbound
  show Integrable (fun x => Real.exp (t * id x)) _
  refine (integrable_withDensity_iff_integrable_smul₀ hρ).mpr ?_
  refine hint.congr ?_
  filter_upwards with x
  rw [NNReal.smul_def, smul_eq_mul, id_eq]
  ring

/-- **Theorem 2.1.**  A square-integrable density orthogonal to every monomial vanishes, as soon
as the measure has one exponential window. -/
theorem ae_eq_zero_of_forall_moment_eq_zero {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hfm : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hpm : AEMeasurable (posWeight f) μ := hfm.real_toNNReal
  have hnm : AEMeasurable (negWeight f) μ := hfm.neg.real_toNNReal
  have hplep : ∀ x, ((posWeight f x : NNReal) : ℝ) ≤ |f x| := fun x => by
    rw [coe_posWeight]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnlep : ∀ x, ((negWeight f x : NNReal) : ℝ) ≤ |f x| := fun x => by
    rw [coe_negWeight]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  set νp : Measure ℝ := μ.withDensity (fun x => ((posWeight f x : NNReal) : ENNReal)) with hνp
  set νn : Measure ℝ := μ.withDensity (fun x => ((negWeight f x : NNReal) : ENNReal)) with hνn
  have hfinp : IsFiniteMeasure νp := isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hfint)
  have hfinn : IsFiniteMeasure νn :=
    isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hfint.neg)
  have hpL2 : MemLp (fun x => ((posWeight f x : NNReal) : ℝ)) 2 μ :=
    memLp_two_coe_weight hf hpm hplep
  have hnL2 : MemLp (fun x => ((negWeight f x : NNReal) : ℝ)) 2 μ :=
    memLp_two_coe_weight hf hnm hnlep
  have hmoments : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂νp = ∫ x : ℝ, x ^ n ∂νn := by
    intro n
    have hxn : MemLp (fun x : ℝ => x ^ n) 2 μ := memLp_two_pow ha hexp n
    have hip : Integrable (fun x => ((posWeight f x : NNReal) : ℝ) * x ^ n) μ :=
      hpL2.integrable_mul hxn
    have hin : Integrable (fun x => ((negWeight f x : NNReal) : ℝ) * x ^ n) μ :=
      hnL2.integrable_mul hxn
    have hp : ∫ x : ℝ, x ^ n ∂νp = ∫ x : ℝ, ((posWeight f x : NNReal) : ℝ) * x ^ n ∂μ := by
      rw [hνp, integral_withDensity_eq_integral_smul₀ hpm]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp [NNReal.smul_def])
    have hn : ∫ x : ℝ, x ^ n ∂νn = ∫ x : ℝ, ((negWeight f x : NNReal) : ℝ) * x ^ n ∂μ := by
      rw [hνn, integral_withDensity_eq_integral_smul₀ hnm]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp [NNReal.smul_def])
    rw [hp, hn, ← sub_eq_zero, ← integral_sub hip hin]
    rw [← hmom n]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ((posWeight f x : NNReal) : ℝ) * x ^ n - ((negWeight f x : NNReal) : ℝ) * x ^ n
      = x ^ n * f x
    rw [← sub_mul, coe_posWeight_sub_coe_negWeight]
    ring
  have hwp := window_subset_integrableExpSet hexp hf hpm hplep
  have hwn := window_subset_integrableExpSet hexp hf hnm hnlep
  have hEq : νp = νn :=
    measure_eq_of_forall_real_moment_eq (by linarith) hwp hwn hmoments
  have hdens : (fun x => ((posWeight f x : NNReal) : ENNReal))
      =ᵐ[μ] fun x => ((negWeight f x : NNReal) : ENNReal) :=
    (withDensity_eq_iff hpm.coe_nnreal_ennreal hnm.coe_nnreal_ennreal
      (lintegral_toNNReal_ne_top hfint)).mp hEq
  filter_upwards [hdens] with x hx
  have hxr : ((posWeight f x : NNReal) : ℝ) = ((negWeight f x : NNReal) : ℝ) := by
    exact_mod_cast congrArg ENNReal.toNNReal hx
  have := coe_posWeight_sub_coe_negWeight f x
  rw [hxr, sub_self] at this
  simpa using this.symm

omit [IsFiniteMeasure μ] in
theorem memLp_two_complex_pow {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ) (n : ℕ) :
    MemLp (fun x : ℝ => (x : ℂ) ^ n) 2 μ := by
  refine MemLp.of_le (memLp_two_pow ha hexp n) (by fun_prop) ?_
  filter_upwards with x
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]

/-- **Theorem 2.1, complex form.**  The orthogonal complement of the polynomials in `L²(μ;ℂ)` is
trivial. -/
theorem ae_eq_zero_of_forall_complex_moment_eq_zero {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {f : ℝ → ℂ} (hf : MemLp f 2 μ)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (x : ℂ) ^ n * f x) μ := fun n =>
    (memLp_two_complex_pow ha hexp n).integrable_mul hf
  have hre : ∀ n : ℕ, ∫ x : ℝ, x ^ n * (f x).re ∂μ = 0 := by
    intro n
    have h1 : (fun x : ℝ => x ^ n * (f x).re)
        = fun x : ℝ => RCLike.re ((x : ℂ) ^ n * f x) := by
      funext x
      simp [RCLike.re_to_complex, ← Complex.ofReal_pow]
    rw [h1, integral_re (hint n), hmom n]
    simp
  have him : ∀ n : ℕ, ∫ x : ℝ, x ^ n * (f x).im ∂μ = 0 := by
    intro n
    have h1 : (fun x : ℝ => x ^ n * (f x).im)
        = fun x : ℝ => RCLike.im ((x : ℂ) ^ n * f x) := by
      funext x
      simp [RCLike.im_to_complex, ← Complex.ofReal_pow]
    rw [h1, integral_im (hint n), hmom n]
    simp
  have hrez := ae_eq_zero_of_forall_moment_eq_zero ha hexp hf.re hre
  have himz := ae_eq_zero_of_forall_moment_eq_zero ha hexp hf.im him
  filter_upwards [hrez, himz] with x hx hy
  exact Complex.ext hx hy

end Density

/-! ## Polynomial density in `L²(μ;ℂ)` -/

section L2Density

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a)
  (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)

/-- The `n`-th monomial as an element of `L²(μ;ℂ)`. -/
noncomputable def monomialLp (n : ℕ) : Lp ℂ 2 μ :=
  MemLp.toLp _ (memLp_two_complex_pow ha hexp n)

omit [IsFiniteMeasure μ] in
theorem coeFn_monomialLp (n : ℕ) :
    (monomialLp ha hexp n : ℝ → ℂ) =ᵐ[μ] fun x => (x : ℂ) ^ n :=
  MemLp.coeFn_toLp _

/-- The polynomial submodule of `L²(μ;ℂ)`. -/
noncomputable def polySubmodule : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ (Set.range (monomialLp ha hexp))

omit [IsFiniteMeasure μ] in
theorem monomialLp_mem (n : ℕ) : monomialLp ha hexp n ∈ polySubmodule ha hexp :=
  Submodule.subset_span ⟨n, rfl⟩

/-- **Theorem 2.1 in Hilbert form.**  The polynomials have trivial orthogonal complement. -/
theorem polySubmodule_orthogonal : (polySubmodule ha hexp)ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf => ?_
  have hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * (f : ℝ → ℂ) x ∂μ = 0 := by
    intro n
    have h := (Submodule.mem_orthogonal _ f).mp hf (monomialLp ha hexp n)
      (monomialLp_mem ha hexp n)
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_monomialLp ha hexp n] with x hx
    rw [hx, RCLike.inner_apply, ← Complex.ofReal_pow, Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_complex_moment_eq_zero ha hexp (Lp.memLp f) hmom)

omit [IsFiniteMeasure μ] in
/-- Every element of the polynomial submodule is almost everywhere an actual polynomial
function. -/
theorem exists_polynomial_of_mem_polySubmodule {f : Lp ℂ 2 μ} (hf : f ∈ polySubmodule ha hexp) :
    ∃ P : Polynomial ℂ, (f : ℝ → ℂ) =ᵐ[μ] fun x => Polynomial.eval (x : ℂ) P := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      refine ⟨Polynomial.X ^ n, ?_⟩
      filter_upwards [coeFn_monomialLp ha hexp n] with x hx
      rw [hx]
      simp
  | zero =>
      refine ⟨0, ?_⟩
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
      rw [hx]
      simp
  | add g h _ _ ihg ihh =>
      obtain ⟨P, hP⟩ := ihg
      obtain ⟨Q, hQ⟩ := ihh
      refine ⟨P + Q, ?_⟩
      filter_upwards [Lp.coeFn_add g h, hP, hQ] with x hx hp hq
      rw [hx]
      simp [hp, hq]
  | smul c g _ ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨c • P, ?_⟩
      filter_upwards [Lp.coeFn_smul c g, hP] with x hx hp
      rw [hx]
      simp [hp]

/-- **Polynomial density.**  The polynomials are dense in `L²(μ;ℂ)` as soon as `μ` has one
exponential window. -/
theorem dense_polySubmodule :
    Dense ((polySubmodule ha hexp : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr (polySubmodule_orthogonal ha hexp))

end L2Density

/-! ## The bounded weight multiplier on `L²(μ;ℂ)` -/

section WeightMultiplier

variable {μ : Measure ℝ} {g : ℝ → ℝ} {C : ℝ}

theorem memLp_weight_mul (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℂ 2 μ) :
    MemLp (fun x => ((g x : ℂ)) * (f : ℝ → ℂ) x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp f).const_mul (C : ℂ)) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg).mul (Lp.aestronglyMeasurable f)
  · filter_upwards [hbdd] with x hx
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Multiplication by a bounded real weight, as an operator on `L²(μ;ℂ)`. -/
noncomputable def weightMul (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_weight_mul hC hg hbdd f).toLp _

theorem coeFn_weightMul (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℂ 2 μ) :
    (weightMul hC hg hbdd f : ℝ → ℂ) =ᵐ[μ] fun x => (g x : ℂ) * (f : ℝ → ℂ) x :=
  MemLp.coeFn_toLp _

theorem weightMul_sub (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f h : Lp ℂ 2 μ) :
    weightMul hC hg hbdd (f - h) = weightMul hC hg hbdd f - weightMul hC hg hbdd h := by
  refine Lp.ext ?_
  filter_upwards [coeFn_weightMul hC hg hbdd (f - h), Lp.coeFn_sub f h,
    Lp.coeFn_sub (weightMul hC hg hbdd f) (weightMul hC hg hbdd h),
    coeFn_weightMul hC hg hbdd f, coeFn_weightMul hC hg hbdd h] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.sub_apply, mul_sub]

theorem norm_weightMul_le (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℂ 2 μ) :
    ‖weightMul hC hg hbdd f‖ ≤ C * ‖f‖ := by
  have hle : ‖weightMul hC hg hbdd f‖ ≤ ‖(C : ℂ) • f‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_weightMul hC hg hbdd f, Lp.coeFn_smul (C : ℂ) f, hbdd] with x h1 h2 hx
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  refine hle.trans (le_of_eq ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- The weighted quadratic functional of a bounded real weight. -/
noncomputable def weightedSq (μ : Measure ℝ) (g : ℝ → ℝ) (f : Lp ℂ 2 μ) : ℝ :=
  ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 * g x ∂μ

/-- The weighted quadratic functional is the real part of the multiplier form. -/
theorem weightedSq_eq_re_inner (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℂ 2 μ) :
    weightedSq μ g f = RCLike.re (inner ℂ f (weightMul hC hg hbdd f)) := by
  rw [L2.inner_def, weightedSq]
  have hint : Integrable (fun x : ℝ =>
      inner ℂ ((f : ℝ → ℂ) x) ((weightMul hC hg hbdd f : ℝ → ℂ) x)) μ :=
    L2.integrable_inner f (weightMul hC hg hbdd f)
  rw [← integral_re hint]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_weightMul hC hg hbdd f] with x hx
  rw [hx, RCLike.inner_apply, RCLike.re_to_complex]
  simp [Complex.mul_re]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem lipschitzWith_weightMul (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) :
    LipschitzWith (Real.toNNReal C) (weightMul hC hg hbdd) := by
  refine LipschitzWith.of_dist_le_mul fun f h => ?_
  rw [dist_eq_norm, dist_eq_norm, ← weightMul_sub, Real.coe_toNNReal C hC]
  exact norm_weightMul_le hC hg hbdd (f - h)

theorem continuous_weightedSq (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) : Continuous (weightedSq μ g) := by
  have hcont : Continuous fun f : Lp ℂ 2 μ => inner ℂ f (weightMul hC hg hbdd f) :=
    continuous_inner.comp
      (continuous_id.prodMk (lipschitzWith_weightMul hC hg hbdd).continuous)
  have heq : weightedSq μ g = fun f : Lp ℂ 2 μ =>
      (inner ℂ f (weightMul hC hg hbdd f)).re := by
    funext f
    rw [weightedSq_eq_re_inner hC hg hbdd f, RCLike.re_to_complex]
  rw [heq]
  exact Complex.continuous_re.comp hcont

end WeightMultiplier

/-! ## The scalar endgame -/

section ScalarEndgame

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a : ℝ} {g : ℝ → ℝ} {C : ℝ}

/-- Nonnegativity of the weighted quadratic functional propagates from the polynomials to all of
`L²(μ;ℂ)` by density and continuity. -/
theorem weightedSq_nonneg (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ) (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C)
    (hpos : ∀ P : Polynomial ℂ, 0 ≤ ∫ x : ℝ, ‖Polynomial.eval (x : ℂ) P‖ ^ 2 * g x ∂μ)
    (f : Lp ℂ 2 μ) : 0 ≤ weightedSq μ g f := by
  have hclosed : IsClosed {u : Lp ℂ 2 μ | 0 ≤ weightedSq μ g u} :=
    isClosed_le continuous_const (continuous_weightedSq hC hg hbdd)
  have hsub : ((polySubmodule ha hexp : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ))
      ⊆ {u : Lp ℂ 2 μ | 0 ≤ weightedSq μ g u} := by
    intro u hu
    obtain ⟨P, hP⟩ := exists_polynomial_of_mem_polySubmodule ha hexp hu
    show 0 ≤ weightedSq μ g u
    rw [weightedSq, integral_congr_ae (by filter_upwards [hP] with x hx; rw [hx])]
    exact hpos P
  have huniv := hclosed.closure_subset_iff.mpr hsub
  rw [(dense_polySubmodule ha hexp).closure_eq] at huniv
  exact huniv (Set.mem_univ f)

/-- **The scalar endgame.**  A bounded real density pairing nonnegatively with every squared
polynomial modulus is nonnegative almost everywhere. -/
theorem ae_nonneg_of_forall_sq_poly_integral_nonneg (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ) (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C)
    (hpos : ∀ P : Polynomial ℂ, 0 ≤ ∫ x : ℝ, ‖Polynomial.eval (x : ℂ) P‖ ^ 2 * g x ∂μ) :
    0 ≤ᵐ[μ] g := by
  classical
  set g' : ℝ → ℝ := hg.mk g with hg'def
  have hg'meas : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hgg' : g =ᵐ[μ] g' := hg.ae_eq_mk
  set E : Set ℝ := {x : ℝ | g' x < 0} with hEdef
  have hE : MeasurableSet E := hg'meas.measurable measurableSet_Iio
  have hμE : μ E ≠ ⊤ := (measure_lt_top μ E).ne
  have hgint : Integrable g μ := by
    refine Integrable.mono (integrable_const C) hg ?_
    filter_upwards [hbdd] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
    exact hx
  set fE : Lp ℂ 2 μ := indicatorConstLp 2 hE hμE (1 : ℂ) with hfE
  have hval : weightedSq μ g fE = ∫ x : ℝ in E, g x ∂μ := by
    rw [weightedSq, ← integral_indicator hE]
    refine integral_congr_ae ?_
    have hind := indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := hE) (hμs := hμE)
      (c := (1 : ℂ))
    filter_upwards [hind] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [hxE]
  have hge : 0 ≤ ∫ x : ℝ in E, g x ∂μ := by
    rw [← hval]
    exact weightedSq_nonneg ha hexp hC hg hbdd hpos fE
  have hneg : ∀ᵐ x ∂(μ.restrict E), g x < 0 := by
    rw [ae_restrict_iff' hE]
    filter_upwards [hgg'] with x hx hxE
    rw [hx]
    exact hxE
  have hle : ∫ x : ℝ in E, g x ∂μ ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [hneg] with x hx
    exact hx.le
  have hzero : ∫ x : ℝ in E, (-g x) ∂μ = 0 := by
    rw [integral_neg]
    have : ∫ x : ℝ in E, g x ∂μ = 0 := le_antisymm hle hge
    rw [this, neg_zero]
  have hnonneg : 0 ≤ᵐ[μ.restrict E] fun x => -g x := by
    filter_upwards [hneg] with x hx
    show (0 : ℝ) ≤ -g x
    linarith
  have haezero := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (hgint.restrict.neg)).mp hzero
  have hcontra : ∀ᵐ _x ∂(μ.restrict E), False := by
    filter_upwards [haezero, hneg] with x h1 h2
    have : -g x = 0 := h1
    linarith
  have hEzero : μ E = 0 := by
    have hbot : μ.restrict E = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      have := (Filter.eventually_false_iff_eq_bot (f := ae (μ.restrict E))).mp hcontra
      simpa [MeasureTheory.ae_eq_bot] using this
    rwa [Measure.restrict_eq_zero] at hbot
  have hnot : ∀ᵐ x ∂μ, x ∉ E := by
    rw [MeasureTheory.ae_iff]
    simpa using hEzero
  filter_upwards [hgg', hnot] with x h1 h2
  show (0 : ℝ) ≤ g x
  rw [h1]
  exact not_lt.mp h2

end ScalarEndgame

end HTGeometry
