import GaloisForLFunctions.RHTower.ThetaZeroDivisionCausalKernel

/-!
# Blaschke factors act isometrically on decaying quasi-polynomials

A quasi-polynomial `E(s) = Σ_μ p_μ(s) e^{μs}` is *decaying* when every exponent has negative real
part; it then lies in `L²(0,∞)`.  For `λ > 0` the Blaschke step
`B_λ E = −E + 2λ (e^{−λ·} * E)` has Laplace multiplier `(λ − q)/(λ + q)` and is an isometry:
with `y = e^{−λ·} * E` one has `y' = E − λy`, `B_λ E = λy − y'`, `E = λy + y'`, and
`‖λy − y'‖² − ‖λy + y'‖² = −2λ (‖y‖²)'`, so the energies agree because `y(0) = 0` and `y → 0`.

Multiplication by the variable, `E ↦ sE`, gives the derivative of the Laplace transform:
`(ℒE)' = −ℒ(sE)` off the exponents.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry (QuasiPolynomial)

namespace RHTower

noncomputable section

/-! ## Decaying quasi-polynomials -/

/-- Every exponent has negative real part. -/
def IsDecayingQP (E : QuasiPolynomial) : Prop := ∀ μ ∈ E.support, μ.re < 0

theorem IsDecayingQP.exists_rate {E : QuasiPolynomial} (hE : IsDecayingQP E) :
    ∃ A : ℝ, A < 0 ∧ ∀ μ ∈ E.support, μ.re < A := by
  classical
  rcases E.support.eq_empty_or_nonempty with h | h
  · exact ⟨-1, by norm_num, by simp [h]⟩
  · obtain ⟨μ₁, hμ₁, hmax⟩ := Finset.exists_max_image E.support Complex.re h
    have h1 := hE μ₁ hμ₁
    exact ⟨μ₁.re / 2, by linarith, fun μ hμ => by linarith [hmax μ hμ]⟩

theorem IsDecayingQP.exists_bound {E : QuasiPolynomial} (hE : IsDecayingQP E) :
    ∃ A C : ℝ, A < 0 ∧ 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ‖E.eval s‖ ≤ C * Real.exp (A * s) := by
  obtain ⟨A, hA, hlt⟩ := hE.exists_rate
  obtain ⟨C, hC, hb⟩ := QuasiPolynomial.exists_norm_eval_le E hlt
  exact ⟨A, C, hA, hC, hb⟩

theorem IsDecayingQP.integrableOn_norm_sq {E : QuasiPolynomial} (hE : IsDecayingQP E) :
    IntegrableOn (fun s : ℝ => ‖E.eval s‖ ^ 2) (Ioi 0) := by
  obtain ⟨A, C, hA, hC, hb⟩ := hE.exists_bound
  have hI : IntegrableOn (fun s : ℝ => C ^ 2 * Real.exp (-(-2 * A) * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine Integrable.mono' hI ((QuasiPolynomial.continuous_eval E).norm.pow 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := hb s (le_of_lt hs)
  calc ‖E.eval s‖ ^ 2 ≤ (C * Real.exp (A * s)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 * Real.exp (-(-2 * A) * s) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf

theorem IsDecayingQP.tendsto_eval {E : QuasiPolynomial} (hE : IsDecayingQP E) :
    Tendsto (fun s : ℝ => E.eval s) atTop (𝓝 0) := by
  obtain ⟨A, C, hA, hC, hb⟩ := hE.exists_bound
  have hlim : Tendsto (fun s : ℝ => C * Real.exp (A * s)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hA)).const_mul C
    rw [mul_zero] at this
    exact this
  refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hlim)
  filter_upwards [eventually_ge_atTop 0] with s hs
  exact hb s hs

theorem IsDecayingQP.convExp {E : QuasiPolynomial} (hE : IsDecayingQP E) {μ : ℂ} (hμ : μ.re < 0) :
    IsDecayingQP (QuasiPolynomial.convExp μ E) := fun ν hν => by
  rcases Finset.mem_insert.1 (QuasiPolynomial.support_convExp_subset μ E hν) with h | h
  · rw [h]; exact hμ
  · exact hE ν h

/-! ## The Blaschke step -/

/-- The Blaschke step `E ↦ −E + 2λ ∫₀^s e^{−λ(s−u)} E(u) du`, with Laplace multiplier
`(λ − q)/(λ + q)`. -/
def blaschkeStep (lam : ℝ) (E : QuasiPolynomial) : QuasiPolynomial :=
  -E + ((2 * lam : ℝ) : ℂ) • QuasiPolynomial.convExp (-(lam : ℂ)) E

theorem eval_blaschkeStep (lam : ℝ) (E : QuasiPolynomial) (s : ℝ) :
    (blaschkeStep lam E).eval s =
      -E.eval s + ((2 * lam : ℝ) : ℂ) * (QuasiPolynomial.convExp (-(lam : ℂ)) E).eval s := by
  rw [blaschkeStep, QuasiPolynomial.eval_add, QuasiPolynomial.eval_neg, QuasiPolynomial.eval_smul]

theorem IsDecayingQP.blaschkeStep {E : QuasiPolynomial} (hE : IsDecayingQP E) {lam : ℝ}
    (hlam : 0 < lam) : IsDecayingQP (blaschkeStep lam E) := by
  classical
  have hC := hE.convExp (μ := -(lam : ℂ)) (by simp [hlam])
  intro ν hν
  rw [RHTower.blaschkeStep] at hν
  rcases Finset.mem_union.1 (Finsupp.support_add hν) with h | h
  · rw [Finsupp.support_neg] at h; exact hE ν h
  · exact hC ν (Finsupp.support_smul h)

theorem laplace_blaschkeStep {E : QuasiPolynomial} (hE : IsDecayingQP E) {lam : ℝ} (hlam : 0 < lam)
    {q : ℂ} (hq : 0 < q.re) :
    (blaschkeStep lam E).laplace q = (lam - q) / (lam + q) * E.laplace q := by
  have hlq : (lam : ℂ) + q ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hconv := laplace_convExp (-(lam : ℂ)) E (q := q) (by simp; linarith)
    (fun ν hν => (hE ν hν).trans hq)
  rw [blaschkeStep, QuasiPolynomial.laplace_add, QuasiPolynomial.laplace_neg,
    QuasiPolynomial.laplace_smul, hconv, show q - -(lam : ℂ) = lam + q by ring]
  field_simp
  push_cast
  ring

/-- Derivative of the exponential convolution: `y' = E + μ y`. -/
theorem hasDerivAt_eval_convExp (μ : ℂ) (E : QuasiPolynomial) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (QuasiPolynomial.convExp μ E).eval t)
      (E.eval s + μ * (QuasiPolynomial.convExp μ E).eval s) s := by
  have hrepr : (fun t : ℝ => (QuasiPolynomial.convExp μ E).eval t) = fun t : ℝ =>
      Complex.exp (μ * t) * ∫ u in (0 : ℝ)..t, Complex.exp (-(μ * u)) * E.eval u := by
    funext t
    rw [QuasiPolynomial.eval_convExp, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [← mul_assoc, ← Complex.exp_add]
    ring_nf
  have hcont : Continuous fun u : ℝ => Complex.exp (-(μ * u)) * E.eval u :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
      (QuasiPolynomial.continuous_eval E)
  have hI := (hcont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (μ * t)) (Complex.exp (μ * s) * μ) s := by
    have := ((hasDerivAt_id (s : ℂ)).const_mul μ).cexp
    simpa using this.comp_ofReal
  have hval := congrFun hrepr s
  rw [hrepr]
  refine (hexp.mul hI).congr_deriv ?_
  rw [hval]
  have : Complex.exp (μ * s) * (Complex.exp (-(μ * s)) * E.eval s) = E.eval s := by
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [this]
  ring

theorem eval_convExp_zero (μ : ℂ) (E : QuasiPolynomial) :
    (QuasiPolynomial.convExp μ E).eval 0 = 0 := by
  rw [QuasiPolynomial.eval_convExp, intervalIntegral.integral_same]

/-- **Energy identity.**  The Blaschke step is an isometry of `L²(0,∞)` on decaying
quasi-polynomials: with `y = e^{−λ·} * E`, `‖λy − y'‖² − ‖λy + y'‖² = −2λ (‖y‖²)'`. -/
theorem integral_norm_sq_blaschkeStep {E : QuasiPolynomial} (hE : IsDecayingQP E) {lam : ℝ}
    (hlam : 0 < lam) :
    ∫ s in Ioi (0 : ℝ), ‖(blaschkeStep lam E).eval s‖ ^ 2 = ∫ s in Ioi (0 : ℝ), ‖E.eval s‖ ^ 2 := by
  set y : ℝ → ℂ := fun t => (QuasiPolynomial.convExp (-(lam : ℂ)) E).eval t with hydef
  set F : ℝ → ℂ := fun t => E.eval t with hFdef
  have hy : ∀ t, HasDerivAt y (F t - (lam : ℂ) * y t) t := fun t => by
    have := hasDerivAt_eval_convExp (-(lam : ℂ)) E t
    simpa [y, F, sub_eq_add_neg, neg_mul] using this
  have hJ : ∀ t, (blaschkeStep lam E).eval t = (lam : ℂ) * y t - (F t - (lam : ℂ) * y t) := fun t => by
    rw [eval_blaschkeStep]
    simp only [y, F]
    push_cast
    ring
  have hFsplit : ∀ t, F t = (lam : ℂ) * y t + (F t - (lam : ℂ) * y t) := fun t => by ring
  -- pointwise identity
  have hpt : ∀ t, ‖(blaschkeStep lam E).eval t‖ ^ 2 =
      ‖F t‖ ^ 2 - lam * (2 * inner ℝ (y t) (F t - (lam : ℂ) * y t)) * 2 := fun t => by
    rw [hJ t]
    conv_rhs => rw [hFsplit t]
    rw [norm_sub_sq_real, norm_add_sq_real]
    have : (lam : ℂ) * y t = lam • y t := by rw [Complex.real_smul]
    rw [this, real_inner_smul_left]
    ring_nf
  -- finite-horizon identity
  have hcontD : Continuous fun t => 2 * inner ℝ (y t) (F t - (lam : ℂ) * y t) := by
    have hyc : Continuous y := QuasiPolynomial.continuous_eval _
    have hFc : Continuous F := QuasiPolynomial.continuous_eval _
    exact continuous_const.mul ((hyc.inner (hFc.sub (continuous_const.mul hyc))))
  have hfin : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, ‖(blaschkeStep lam E).eval t‖ ^ 2 =
      (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) - 2 * lam * ‖y T‖ ^ 2 := by
    intro T hT
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := T)
      (f := fun t => ‖y t‖ ^ 2) (fun t _ => (hy t).norm_sq) (hcontD.intervalIntegrable 0 T)
    have hy0 : y 0 = 0 := eval_convExp_zero _ _
    simp only [hy0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
      at hFTC
    simp_rw [hpt]
    have hFi : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume 0 T :=
      ((QuasiPolynomial.continuous_eval E).norm.pow 2).intervalIntegrable 0 T
    have hGi : IntervalIntegrable (fun t => lam * (2 * inner ℝ (y t) (F t - (lam : ℂ) * y t)) * 2)
        volume 0 T := ((hcontD.const_mul lam).mul continuous_const).intervalIntegrable 0 T
    rw [intervalIntegral.integral_sub (f := fun t => ‖F t‖ ^ 2)
      (g := fun t => lam * (2 * inner ℝ (y t) (F t - (lam : ℂ) * y t)) * 2) hFi hGi,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hFTC]
    ring
  -- limits
  have hJdec := hE.blaschkeStep hlam
  have hydec : IsDecayingQP (QuasiPolynomial.convExp (-(lam : ℂ)) E) :=
    hE.convExp (by simp [hlam])
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hJdec.integrableOn_norm_sq tendsto_id
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 hE.integrableOn_norm_sq tendsto_id
  have h3 : Tendsto (fun T => ‖y T‖ ^ 2) atTop (𝓝 0) := by
    have := (hydec.tendsto_eval.norm).pow 2
    simpa using this
  have h4 := h2.sub (h3.const_mul (2 * lam))
  rw [mul_zero, sub_zero] at h4
  refine tendsto_nhds_unique h1 (h4.congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with T hT
  exact (hfin T hT).symm

/-! ## Multiplication by the variable and the derivative of the Laplace transform -/

/-- `E ↦ s E(s)`. -/
def qpMulX (E : QuasiPolynomial) : QuasiPolynomial :=
  Finsupp.mapRange (fun p => Polynomial.X * p) (by simp) E

theorem eval_qpMulX (E : QuasiPolynomial) (s : ℝ) : (qpMulX E).eval s = s * E.eval s := by
  unfold qpMulX QuasiPolynomial.eval
  rw [Finsupp.sum_mapRange_index (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun μ _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_X]
  ring

theorem support_qpMulX_subset (E : QuasiPolynomial) : (qpMulX E).support ⊆ E.support :=
  Finsupp.support_mapRange

theorem laplace_qpMulX (E : QuasiPolynomial) (q : ℂ) :
    (qpMulX E).laplace q = ∑ μ ∈ E.support, ∑ j ∈ Finset.range ((E μ).natDegree + 1),
      (E μ).coeff j * ((j + 1).factorial : ℂ) / (q - μ) ^ (j + 2) := by
  unfold qpMulX QuasiPolynomial.laplace
  rw [Finsupp.sum_mapRange_index (by simp)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hN : (Polynomial.X * E μ).natDegree < (E μ).natDegree + 2 := by
    have := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := E μ)
    rw [Polynomial.natDegree_X] at this
    omega
  have h := QuasiPolynomial.laplaceTerm_eq_range μ hN q
  rw [QuasiPolynomial.laplaceTerm] at h
  beta_reduce
  rw [h, Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
    zero_div, add_zero]

/-- **`(ℒE)' = −ℒ(sE)`** off the exponents. -/
theorem hasDerivAt_laplace (E : QuasiPolynomial) {q : ℂ} (hq : q ∉ E.support) :
    HasDerivAt E.laplace (-(qpMulX E).laplace q) q := by
  classical
  rw [laplace_qpMulX, ← Finset.sum_neg_distrib]
  have hfun : E.laplace = fun z => ∑ μ ∈ E.support, ∑ j ∈ Finset.range ((E μ).natDegree + 1),
      (E μ).coeff j * (j.factorial : ℂ) * ((z - μ) ^ (j + 1))⁻¹ := by
    funext z
    rw [QuasiPolynomial.laplace_eq_sum]
    simp only [div_eq_mul_inv]
  rw [hfun]
  refine HasDerivAt.fun_sum fun μ hμ => ?_
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun j _ => ?_
  have hne : q - μ ≠ 0 := sub_ne_zero.2 fun h => hq (h ▸ hμ)
  have hpow : (q - μ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hne
  have hd := ((((hasDerivAt_id q).sub_const μ).pow (j + 1)).inv hpow).const_mul
    ((E μ).coeff j * (j.factorial : ℂ))
  refine hd.congr_deriv ?_
  simp only [id, Pi.pow_apply, Nat.add_sub_cancel, mul_one]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem integral_eval_qpMulX_mul_cexp (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) * E.eval s * Complex.exp (-(q * s)) = (qpMulX E).laplace q := by
  have h := (QuasiPolynomial.integral_eval_mul_cexp (qpMulX E)
    (fun μ hμ => hq μ (support_qpMulX_subset E hμ))).2
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [eval_qpMulX]

theorem integrableOn_eval_qpMulX_mul_cexp (E : QuasiPolynomial) {q : ℂ}
    (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) * E.eval s * Complex.exp (-(q * s))) (Ioi 0) := by
  have h := (QuasiPolynomial.integral_eval_mul_cexp (qpMulX E)
    (fun μ hμ => hq μ (support_qpMulX_subset E hμ))).1
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [eval_qpMulX]

end

end RHTower
