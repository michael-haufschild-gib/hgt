import GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus

/-!
# Derivatives, exponential shifts and differential operators on quasi-polynomials

The derivative of `Σ_μ p_μ(s) e^{μs}` is the quasi-polynomial `Σ_μ (p_μ' + μ p_μ)(s) e^{μs}`, so
every quasi-polynomial is smooth with quasi-polynomial iterated derivatives.  For `Re q` beyond
every exponent, the Laplace transform obeys
* `𝓛(E')(q) = q 𝓛E(q) - E(0)` (integration by parts on the half-line),
* `𝓛(e^{c·} E)(q) = 𝓛E(q - c)`,
* `𝓛(∫₀^· e^{μ(·-u)} E(u) du)(q) = 𝓛E(q)/(q - μ)` (the convolution solves `G' = μG + E`,
  `G(0) = 0`),
* `𝓛(P(∂)E)(q) = P(q) 𝓛E(q)` when `E` vanishes at `0` to order `deg P`.
A real-valued quasi-polynomial has real iterated derivatives, which identifies the iterated
derivatives of a real function represented by a quasi-polynomial.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace QuasiPolynomial

/-! ## The derivative -/

/-- The derivative `Σ_μ (p_μ' + μ p_μ) e^{μs}` as a linear map. -/
def derivativeLM : QuasiPolynomial →ₗ[ℂ] QuasiPolynomial :=
  Finsupp.lsum ℂ fun μ =>
    (Finsupp.lsingle μ) ∘ₗ (Polynomial.derivative + LinearMap.mulLeft ℂ (Polynomial.C μ))

theorem derivativeLM_single (μ : ℂ) (p : Polynomial ℂ) :
    derivativeLM (Finsupp.single μ p) =
      Finsupp.single μ (Polynomial.derivative p + Polynomial.C μ * p) := by
  simp [derivativeLM]

theorem hasDerivAt_eval (E : QuasiPolynomial) (s : ℝ) :
    HasDerivAt E.eval ((derivativeLM E).eval s) s := by
  induction E using Finsupp.induction_linear generalizing s with
  | zero =>
    rw [map_zero, eval_zero]
    have : (eval 0 : ℝ → ℂ) = fun _ => 0 := funext eval_zero
    rw [this]
    exact hasDerivAt_const s 0
  | add E F hE hF =>
    rw [map_add, eval_add, show eval (E + F) = fun s => eval E s + eval F s from
      funext (eval_add E F)]
    exact (hE s).add (hF s)
  | single μ p =>
    rw [derivativeLM_single, eval_single, show eval (Finsupp.single μ p) =
      fun s : ℝ => p.eval (s : ℂ) * Complex.exp (μ * s) from funext (eval_single μ p)]
    have h1 := hasDerivAt_polynomial_ofReal p s
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (μ * s)) (Complex.exp (μ * s) * μ) s := by
      have := ((hasDerivAt_id (s : ℂ)).const_mul μ).cexp.comp_ofReal
      simpa using this
    refine (h1.mul h2).congr_deriv ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring

theorem deriv_eval (E : QuasiPolynomial) : deriv E.eval = (derivativeLM E).eval :=
  funext fun s => (hasDerivAt_eval E s).deriv

theorem support_derivativeLM_subset (E : QuasiPolynomial) :
    (derivativeLM E).support ⊆ E.support := by
  classical
  intro ν hν
  rw [derivativeLM, Finsupp.lsum_apply, Finsupp.sum] at hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hν)
  have := Finsupp.support_single_subset hν'
  rw [Finset.mem_singleton] at this
  exact this ▸ hμ

/-- The `k`-th derivative. -/
def iterDeriv (k : ℕ) : QuasiPolynomial →ₗ[ℂ] QuasiPolynomial := derivativeLM ^ k

theorem iterDeriv_zero (E : QuasiPolynomial) : iterDeriv 0 E = E := by
  simp [iterDeriv]

theorem iterDeriv_succ (k : ℕ) (E : QuasiPolynomial) :
    iterDeriv (k + 1) E = iterDeriv k (derivativeLM E) := by
  simp only [iterDeriv, pow_succ, Module.End.mul_apply]

theorem iterDeriv_succ' (k : ℕ) (E : QuasiPolynomial) :
    iterDeriv (k + 1) E = derivativeLM (iterDeriv k E) := by
  simp only [iterDeriv, pow_succ', Module.End.mul_apply]

theorem iteratedDeriv_eval (k : ℕ) (E : QuasiPolynomial) :
    iteratedDeriv k E.eval = (iterDeriv k E).eval := by
  induction k generalizing E with
  | zero => rw [iteratedDeriv_zero, iterDeriv_zero]
  | succ k ih => rw [iteratedDeriv_succ', deriv_eval, ih, iterDeriv_succ]

theorem support_iterDeriv_subset (k : ℕ) (E : QuasiPolynomial) :
    (iterDeriv k E).support ⊆ E.support := by
  induction k with
  | zero => rw [iterDeriv_zero]
  | succ k ih => rw [iterDeriv_succ']; exact (support_derivativeLM_subset _).trans ih

/-! ## Laplace transform of the derivative -/

theorem exists_re_lt_between (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    ∃ A < q.re, ∀ μ ∈ E.support, μ.re < A := by
  rcases E.support.eq_empty_or_nonempty with h | h
  · exact ⟨q.re - 1, by linarith, fun μ hμ => by simp [h] at hμ⟩
  · obtain ⟨μ₀, hμ₀, hmax⟩ := E.support.exists_max_image (fun μ => μ.re) h
    have := hq μ₀ hμ₀
    exact ⟨(μ₀.re + q.re) / 2, by linarith, fun μ hμ => by linarith [hmax μ hμ]⟩

theorem tendsto_eval_mul_cexp (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    Tendsto (fun s : ℝ => E.eval s * Complex.exp (-(q * s))) atTop (𝓝 0) := by
  obtain ⟨A, hAq, hA⟩ := E.exists_re_lt_between hq
  obtain ⟨C, hC0, hC⟩ := E.exists_norm_eval_le hA
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun s : ℝ => C * Real.exp ((A - q.re) * s)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : A - q.re < 0)))
    simpa using this.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(q * (s : ℂ))).re = -(q.re * s) := by simp [Complex.mul_re]
  rw [hre]
  calc ‖E.eval s‖ * Real.exp (-(q.re * s)) ≤ C * Real.exp (A * s) * Real.exp (-(q.re * s)) :=
        mul_le_mul_of_nonneg_right (hC s hs) (Real.exp_pos _).le
    _ = C * Real.exp ((A - q.re) * s) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **`𝓛(E')(q) = q 𝓛E(q) - E(0)`.** -/
theorem laplace_derivativeLM (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    (derivativeLM E).laplace q = q * E.laplace q - E.eval 0 := by
  have hq' : ∀ μ ∈ (derivativeLM E).support, μ.re < q.re := fun μ hμ =>
    hq μ (support_derivativeLM_subset E hμ)
  obtain ⟨i1, e1⟩ := integral_eval_mul_cexp (derivativeLM E) hq'
  obtain ⟨i2, e2⟩ := integral_eval_mul_cexp E hq
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => E.eval s * Complex.exp (-(q * s)))
      ((derivativeLM E).eval s * Complex.exp (-(q * s)) -
        q * (E.eval s * Complex.exp (-(q * s)))) s := fun s => by
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-(q * s)))
        (Complex.exp (-(q * s)) * (-q)) s := by
      have := (((hasDerivAt_id (s : ℂ)).const_mul q).neg).cexp.comp_ofReal
      simpa using this
    refine ((hasDerivAt_eval E s).mul h2).congr_deriv ?_
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuous_eval E).mul (by fun_prop)).continuousWithinAt
    (fun s _ => hderiv s) (i1.sub (i2.const_mul q)) (tendsto_eval_mul_cexp E hq)
  rw [integral_sub i1 (i2.const_mul q), MeasureTheory.integral_const_mul, e1, e2] at h
  simp only [Pi.mul_apply, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one,
    zero_sub] at h
  linear_combination h

/-- `𝓛(E^{(k)})(q) = q^k 𝓛E(q)` when `E^{(j)}(0) = 0` for `j < k`. -/
theorem laplace_iterDeriv (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re)
    (k : ℕ) (h0 : ∀ j < k, (iterDeriv j E).eval 0 = 0) :
    (iterDeriv k E).laplace q = q ^ k * E.laplace q := by
  induction k with
  | zero => rw [iterDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [iterDeriv_succ', laplace_derivativeLM _ fun μ hμ => hq μ (support_iterDeriv_subset k E hμ),
      ih fun j hj => h0 j (by omega), h0 k (by omega), sub_zero, pow_succ]
    ring

/-! ## Polynomial differential operators -/

/-- The differential operator `P(∂)E = Σ_k P_k E^{(k)}`. -/
def applyPoly (P : Polynomial ℂ) (E : QuasiPolynomial) : QuasiPolynomial :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • iterDeriv k E

theorem eval_applyPoly (P : Polynomial ℂ) (E : QuasiPolynomial) (s : ℝ) :
    (applyPoly P E).eval s =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * iteratedDeriv k E.eval s := by
  rw [applyPoly, eval_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_smul, iteratedDeriv_eval]

/-- **`𝓛(P(∂)E)(q) = P(q) 𝓛E(q)`** when `E` vanishes to order `deg P` at `0`. -/
theorem laplace_applyPoly (P : Polynomial ℂ) (E : QuasiPolynomial) {q : ℂ}
    (hq : ∀ μ ∈ E.support, μ.re < q.re) (h0 : ∀ j < P.natDegree, (iterDeriv j E).eval 0 = 0) :
    (applyPoly P E).laplace q = P.eval q * E.laplace q := by
  rw [applyPoly, laplace_sum, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [laplace_smul, laplace_iterDeriv E hq k fun j hj => h0 j (by
    rw [Finset.mem_range] at hk; omega)]
  ring

/-! ## Exponential shifts -/

/-- The exponential shift `s ↦ e^{cs} E(s)`. -/
def shift (c : ℂ) (E : QuasiPolynomial) : QuasiPolynomial := Finsupp.mapDomain (· + c) E

theorem shift_add (c : ℂ) (E F : QuasiPolynomial) : shift c (E + F) = shift c E + shift c F :=
  Finsupp.mapDomain_add

theorem shift_single (c μ : ℂ) (p : Polynomial ℂ) :
    shift c (Finsupp.single μ p) = Finsupp.single (μ + c) p :=
  Finsupp.mapDomain_single

theorem eval_shift (c : ℂ) (E : QuasiPolynomial) (s : ℝ) :
    (shift c E).eval s = Complex.exp (c * s) * E.eval s := by
  induction E using Finsupp.induction_linear with
  | zero => simp [shift]
  | add E F hE hF => rw [shift_add, eval_add, eval_add, hE, hF, mul_add]
  | single μ p =>
    rw [shift_single, eval_single, eval_single, add_mul, Complex.exp_add]
    ring

theorem laplace_shift (c : ℂ) (E : QuasiPolynomial) (q : ℂ) :
    (shift c E).laplace q = E.laplace (q - c) := by
  induction E using Finsupp.induction_linear with
  | zero => simp [shift, laplace]
  | add E F hE hF => rw [shift_add, laplace_add, laplace_add, hE, hF]
  | single μ p =>
    rw [shift_single, laplace_single, laplace_single, laplaceTerm, laplaceTerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show q - (μ + c) = q - c - μ by ring]

theorem support_shift_subset (c : ℂ) (E : QuasiPolynomial) :
    (shift c E).support ⊆ E.support.image (· + c) :=
  Finsupp.mapDomain_support

/-! ## The causal exponential convolution -/

theorem eval_convExp_zero (μ : ℂ) (E : QuasiPolynomial) : (convExp μ E).eval 0 = 0 := by
  rw [eval_convExp, intervalIntegral.integral_same]

theorem hasDerivAt_eval_convExp (μ : ℂ) (E : QuasiPolynomial) (s : ℝ) :
    HasDerivAt (convExp μ E).eval (μ * (convExp μ E).eval s + E.eval s) s := by
  have hfun : (convExp μ E).eval = fun s : ℝ =>
      Complex.exp (μ * s) * ∫ u in (0 : ℝ)..s, Complex.exp (-(μ * u)) * E.eval u := by
    funext s
    rw [eval_convExp, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show Complex.exp (μ * (s - u)) * E.eval u =
      Complex.exp (μ * s) * (Complex.exp (-(μ * u)) * E.eval u)
    rw [← mul_assoc, ← Complex.exp_add]
    ring_nf
  have hc : Continuous fun u : ℝ => Complex.exp (-(μ * u)) * E.eval u :=
    (by fun_prop : Continuous fun u : ℝ => Complex.exp (-(μ * u))).mul (continuous_eval E)
  have h1 : HasDerivAt (fun s : ℝ => Complex.exp (μ * s)) (Complex.exp (μ * s) * μ) s := by
    have := ((hasDerivAt_id (s : ℂ)).const_mul μ).cexp.comp_ofReal
    simpa using this
  have h2 := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [hfun]
  refine (h1.mul h2).congr_deriv ?_
  rw [← mul_assoc, ← Complex.exp_add, show μ * (s : ℂ) + -(μ * s) = 0 by ring, Complex.exp_zero,
    one_mul]
  ring

theorem derivativeLM_convExp (μ : ℂ) (E : QuasiPolynomial) :
    derivativeLM (convExp μ E) = μ • convExp μ E + E := by
  refine sub_eq_zero.mp (eq_zero_of_eval_eq_zero _ fun s _ => ?_)
  rw [eval_sub, eval_add, eval_smul, sub_eq_zero]
  exact (hasDerivAt_eval (convExp μ E) s).unique (hasDerivAt_eval_convExp μ E s)

/-- **`𝓛(∫₀^· e^{μ(·-u)} E(u) du)(q) = 𝓛E(q)/(q - μ)`.** -/
theorem laplace_convExp (μ : ℂ) (E : QuasiPolynomial) {q : ℂ}
    (hq : ∀ ν ∈ E.support, ν.re < q.re) (hμ : μ.re < q.re) :
    (convExp μ E).laplace q = E.laplace q / (q - μ) := by
  have hG : ∀ ν ∈ (convExp μ E).support, ν.re < q.re := fun ν hν => by
    rcases Finset.mem_insert.1 (support_convExp_subset μ E hν) with h | h
    · exact h ▸ hμ
    · exact hq ν h
  have h := laplace_derivativeLM (convExp μ E) hG
  rw [derivativeLM_convExp, laplace_add, laplace_smul, eval_convExp_zero, sub_zero] at h
  have hqμ : q - μ ≠ 0 := fun h' => by
    rw [sub_eq_zero] at h'; rw [h'] at hμ; exact lt_irrefl _ hμ
  field_simp
  linear_combination -h

/-- Convolution with `e^{μ·}` raises the vanishing order at `0` by one. -/
theorem iterDeriv_convExp_eval_zero (μ : ℂ) (E : QuasiPolynomial) {n : ℕ}
    (hE : ∀ j < n, (iterDeriv j E).eval 0 = 0) :
    ∀ j < n + 1, (iterDeriv j (convExp μ E)).eval 0 = 0 := by
  intro j hj
  induction j with
  | zero => rw [iterDeriv_zero, eval_convExp_zero]
  | succ j ih =>
    rw [iterDeriv_succ, derivativeLM_convExp, map_add, map_smul, eval_add, eval_smul,
      ih (by omega), hE j (by omega), mul_zero, add_zero]

/-! ## Real-valued quasi-polynomials -/

theorem im_eval_derivativeLM (E : QuasiPolynomial) (h : ∀ s : ℝ, (E.eval s).im = 0) (s : ℝ) :
    ((derivativeLM E).eval s).im = 0 := by
  have h1 : HasDerivAt (fun s => (E.eval s).im) ((derivativeLM E).eval s).im s :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_eval E s))
  have h2 : (fun s => (E.eval s).im) = fun _ => (0 : ℝ) := funext h
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const s 0)

/-- If a real function agrees with a quasi-polynomial, so do all its iterated derivatives. -/
theorem iteratedDeriv_ofReal_eq {f : ℝ → ℝ} {E : QuasiPolynomial} (hf : ∀ s, (f s : ℂ) = E.eval s)
    (k : ℕ) (s : ℝ) : ((iteratedDeriv k f s : ℝ) : ℂ) = (iterDeriv k E).eval s := by
  induction k generalizing f E s with
  | zero => rw [iteratedDeriv_zero, iterDeriv_zero, hf]
  | succ k ih =>
    have hreal : ∀ s, ((derivativeLM E).eval s).im = 0 :=
      im_eval_derivativeLM E fun s => by rw [← hf]; exact Complex.ofReal_im _
    have hd : ∀ s, HasDerivAt f ((derivativeLM E).eval s).re s := fun s => by
      have h1 : HasDerivAt (fun s => (E.eval s).re) ((derivativeLM E).eval s).re s :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_eval E s)
      have h2 : (fun s => (E.eval s).re) = f :=
        funext fun s => by rw [← hf]; exact Complex.ofReal_re _
      rw [h2] at h1
      exact h1
    have hderiv : deriv f = fun s => ((derivativeLM E).eval s).re := funext fun s => (hd s).deriv
    rw [iteratedDeriv_succ', hderiv, iterDeriv_succ]
    refine ih (fun s => ?_) s
    exact Complex.ext (by simp) (by simp [hreal s])

end QuasiPolynomial

end

end GaloisForLFunctions.HTGeometry
