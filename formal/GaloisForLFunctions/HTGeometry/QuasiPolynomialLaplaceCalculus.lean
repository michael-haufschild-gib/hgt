import GaloisForLFunctions.HTGeometry.ComplexScaledGammaIntegral
import Mathlib

/-!
# Quasi-polynomials and their Laplace transforms

A quasi-polynomial `E(s) = Σ_μ p_μ(s) e^{μs}` is recorded by its finitely supported family of
polynomial coefficients `p_μ`, indexed by the exponents `μ ∈ ℂ`.

* **Convolution with an exponential.**  `∫₀^s e^{μ(s−u)} E(u) du` is again a quasi-polynomial:
  on the exponent `μ` the coefficient is integrated, and off it the equation `Q' + (λ − μ)Q = p` is
  solved by `Q = Σ_k (−1)^k p^{(k)}/(λ − μ)^{k+1}`.
* **Laplace transform.**  For `Re q` beyond every exponent,
  `∫₀^∞ E(s) e^{-qs} ds = Σ_μ Σ_j p_{μ,j} j!/(q − μ)^{j+1}`; this rational function has a pole of
  order exactly `deg p_μ + 1` at each exponent and is analytic elsewhere.
* **Uniqueness and reality.**  A quasi-polynomial whose transform vanishes on a real ray is zero;
  one whose transform is real on a real ray is real-valued.
* **Growth.**  With `a` the largest real part of an exponent and `m` the largest degree on the line
  `Re μ = a`, `E(s) = s^m e^{as} (Σ_{top} lead(p_μ) e^{i Im μ s} + o(1))`; a nonzero trigonometric
  polynomial does not tend to zero (Cesàro means), so `limsup log‖E(s)‖/s = a`.  A real-valued
  quasi-polynomial is fixed by conjugation, its top exponents pair up conjugately and the leading
  term is the real trigonometric polynomial `Σ_{top} Re(lead(p_μ) e^{i Im μ s})`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Quasi-polynomials `s ↦ Σ_μ p_μ(s) e^{μ s}`, indexed by their exponents. -/
abbrev QuasiPolynomial := ℂ →₀ Polynomial ℂ

namespace QuasiPolynomial

/-- The value `Σ_μ p_μ(s) e^{μ s}`. -/
def eval (E : QuasiPolynomial) (s : ℝ) : ℂ :=
  E.sum fun μ p => p.eval (s : ℂ) * Complex.exp (μ * s)

theorem eval_eq_sum (E : QuasiPolynomial) (s : ℝ) :
    E.eval s = ∑ μ ∈ E.support, (E μ).eval (s : ℂ) * Complex.exp (μ * s) := rfl

@[simp] theorem eval_zero (s : ℝ) : eval 0 s = 0 := by simp [eval]

theorem eval_add (E F : QuasiPolynomial) (s : ℝ) : eval (E + F) s = eval E s + eval F s := by
  unfold eval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ p q => by simp [add_mul])

theorem eval_single (μ : ℂ) (p : Polynomial ℂ) (s : ℝ) :
    eval (Finsupp.single μ p) s = p.eval (s : ℂ) * Complex.exp (μ * s) := by
  unfold eval
  exact Finsupp.sum_single_index (by simp)

theorem eval_smul (c : ℂ) (E : QuasiPolynomial) (s : ℝ) : eval (c • E) s = c * eval E s := by
  induction E using Finsupp.induction_linear with
  | zero => simp
  | add E F hE hF => rw [smul_add, eval_add, eval_add, hE, hF, mul_add]
  | single μ p =>
    rw [Finsupp.smul_single, eval_single, eval_single, Polynomial.eval_smul, smul_eq_mul, mul_assoc]

theorem eval_neg (E : QuasiPolynomial) (s : ℝ) : eval (-E) s = -eval E s := by
  rw [← neg_one_smul ℂ E, eval_smul]; ring

theorem eval_sub (E F : QuasiPolynomial) (s : ℝ) : eval (E - F) s = eval E s - eval F s := by
  rw [sub_eq_add_neg, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_sum {ι : Type*} (t : Finset ι) (E : ι → QuasiPolynomial) (s : ℝ) :
    eval (∑ i ∈ t, E i) s = ∑ i ∈ t, eval (E i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, eval_add, ih]

theorem eval_finsuppSum (E : QuasiPolynomial) (G : ℂ → Polynomial ℂ → QuasiPolynomial) (s : ℝ) :
    eval (E.sum G) s = E.sum fun μ p => eval (G μ p) s :=
  eval_sum _ _ s

theorem continuous_eval (E : QuasiPolynomial) : Continuous E.eval := by
  rw [show E.eval = fun s : ℝ => ∑ μ ∈ E.support, (E μ).eval (s : ℂ) * Complex.exp (μ * s) from
    funext (eval_eq_sum E)]
  refine continuous_finsetSum _ fun μ _ => ?_
  exact ((E μ).continuous.comp Complex.continuous_ofReal).mul (by fun_prop)

/-! ## Antiderivatives and the equation `Q' + νQ = p` -/

/-- The antiderivative `Σ_i p_i X^{i+1}/(i+1)`, vanishing at `0`. -/
def antideriv (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff i / (i + 1)) * Polynomial.X ^ (i + 1)

theorem derivative_antideriv (p : Polynomial ℂ) : Polynomial.derivative (antideriv p) = p := by
  rw [antideriv, map_sum]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 2
  push_cast
  field_simp

theorem eval_antideriv_zero (p : Polynomial ℂ) : (antideriv p).eval 0 = 0 := by
  simp [antideriv, Polynomial.eval_finsetSum]

/-- The solution `Q = Σ_k (−1)^k p^{(k)}/ν^{k+1}` of `Q' + νQ = p`. -/
def expSolve (ν : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    Polynomial.C ((-1) ^ k / ν ^ (k + 1)) * Polynomial.derivative^[k] p

theorem derivative_expSolve_add {ν : ℂ} (hν : ν ≠ 0) (p : Polynomial ℂ) :
    Polynomial.derivative (expSolve ν p) + Polynomial.C ν * expSolve ν p = p := by
  unfold expSolve
  set n := p.natDegree
  rw [map_sum, Finset.mul_sum]
  simp only [Polynomial.derivative_C_mul, ← Function.iterate_succ_apply' Polynomial.derivative]
  have h1 : ∑ k ∈ Finset.range (n + 1), Polynomial.C ((-1) ^ k / ν ^ (k + 1)) *
      Polynomial.derivative^[k + 1] p =
      -∑ k ∈ Finset.range (n + 1), Polynomial.C ((-1) ^ (k + 1) / ν ^ (k + 1)) *
        Polynomial.derivative^[k + 1] p := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_mul, ← map_neg]
    congr 2
    rw [pow_succ]; ring
  have h2 : ∑ k ∈ Finset.range (n + 1), Polynomial.C ν *
      (Polynomial.C ((-1) ^ k / ν ^ (k + 1)) * Polynomial.derivative^[k] p) =
      ∑ k ∈ Finset.range (n + 1), Polynomial.C ((-1) ^ k / ν ^ k) * Polynomial.derivative^[k] p := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← map_mul]
    congr 2
    rw [pow_succ]; field_simp
  rw [h1, h2, Finset.sum_range_succ' (fun k => Polynomial.C ((-1) ^ k / ν ^ k) *
    Polynomial.derivative^[k] p), Finset.sum_range_succ (fun k => Polynomial.C ((-1) ^ (k + 1) /
      ν ^ (k + 1)) * Polynomial.derivative^[k + 1] p),
    Polynomial.iterate_derivative_eq_zero (show p.natDegree < n + 1 by omega)]
  simp

/-! ## Convolution with an exponential -/

/-- The convolution `∫₀^s e^{μ(s−u)} p(u) e^{λu} du` of one term, as an exponential polynomial. -/
def convExpTerm (μ lam : ℂ) (p : Polynomial ℂ) : QuasiPolynomial :=
  if lam = μ then Finsupp.single lam (antideriv p)
  else Finsupp.single lam (expSolve (lam - μ) p) -
    Finsupp.single μ (Polynomial.C ((expSolve (lam - μ) p).eval 0))

/-- The convolution `∫₀^s e^{μ(s−u)} E(u) du`. -/
def convExp (μ : ℂ) (E : QuasiPolynomial) : QuasiPolynomial := E.sum fun lam p => convExpTerm μ lam p

theorem hasDerivAt_polynomial_ofReal (p : Polynomial ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => p.eval (u : ℂ)) ((Polynomial.derivative p).eval (u : ℂ)) u :=
  (p.hasDerivAt (u : ℂ)).comp_ofReal

theorem eval_convExpTerm (μ lam : ℂ) (p : Polynomial ℂ) (s : ℝ) :
    (convExpTerm μ lam p).eval s =
      ∫ u in (0 : ℝ)..s, Complex.exp (μ * (s - u)) * (p.eval (u : ℂ) * Complex.exp (lam * u)) := by
  have hcont : Continuous fun u : ℝ =>
      Complex.exp (μ * (s - u)) * (p.eval (u : ℂ) * Complex.exp (lam * u)) :=
    (by fun_prop : Continuous fun u : ℝ => Complex.exp (μ * (s - u))).mul
      ((p.continuous.comp Complex.continuous_ofReal).mul (by fun_prop))
  unfold convExpTerm
  split_ifs with h
  · subst h
    rw [eval_single]
    have hd : ∀ u ∈ uIcc (0 : ℝ) s, HasDerivAt (fun u : ℝ => Complex.exp (lam * s) *
        (antideriv p).eval (u : ℂ))
        (Complex.exp (lam * (s - u)) * (p.eval (u : ℂ) * Complex.exp (lam * u))) u := by
      intro u _
      have := (hasDerivAt_polynomial_ofReal (antideriv p) u).const_mul (Complex.exp (lam * s))
      rw [derivative_antideriv] at this
      refine this.congr_deriv ?_
      rw [show Complex.exp (lam * (s - u)) * (p.eval (u : ℂ) * Complex.exp (lam * u)) =
        p.eval (u : ℂ) * (Complex.exp (lam * (s - u)) * Complex.exp (lam * u)) by ring,
        ← Complex.exp_add]
      ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    simp [eval_antideriv_zero]
    ring
  · have hν : lam - μ ≠ 0 := sub_ne_zero.2 h
    set Q := expSolve (lam - μ) p
    rw [eval_sub, eval_single, eval_single, Polynomial.eval_C]
    have hd : ∀ u ∈ uIcc (0 : ℝ) s, HasDerivAt (fun u : ℝ => Complex.exp (μ * s) *
        (Q.eval (u : ℂ) * Complex.exp ((lam - μ) * u)))
        (Complex.exp (μ * (s - u)) * (p.eval (u : ℂ) * Complex.exp (lam * u))) u := by
      intro u _
      have he : HasDerivAt (fun u : ℝ => Complex.exp ((lam - μ) * u))
          ((lam - μ) * Complex.exp ((lam - μ) * u)) u := by
        have := ((hasDerivAt_id (u : ℂ)).const_mul (lam - μ)).cexp.comp_ofReal
        simpa [mul_comm] using this
      have := ((hasDerivAt_polynomial_ofReal Q u).mul he).const_mul (Complex.exp (μ * s))
      refine this.congr_deriv ?_
      have hQ := congrArg (fun P : Polynomial ℂ => P.eval (u : ℂ)) (derivative_expSolve_add hν p)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hQ
      have e1 : Complex.exp (μ * (s - u)) * Complex.exp (lam * u) =
          Complex.exp (μ * s) * Complex.exp ((lam - μ) * u) := by
        rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
      calc Complex.exp (μ * s) * ((Polynomial.derivative Q).eval (u : ℂ) *
            Complex.exp ((lam - μ) * u) + Q.eval (u : ℂ) * ((lam - μ) *
              Complex.exp ((lam - μ) * u)))
          = Complex.exp (μ * s) * Complex.exp ((lam - μ) * u) *
            ((Polynomial.derivative Q).eval (u : ℂ) + (lam - μ) * Q.eval (u : ℂ)) := by ring
        _ = _ := by rw [hQ, ← e1]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [mul_left_comm, ← Complex.exp_add]
    ring_nf

theorem eval_convExp (μ : ℂ) (E : QuasiPolynomial) (s : ℝ) :
    (convExp μ E).eval s = ∫ u in (0 : ℝ)..s, Complex.exp (μ * (s - u)) * E.eval u := by
  rw [convExp, eval_finsuppSum, Finsupp.sum]
  simp only [eval_convExpTerm]
  have hsum : (fun u : ℝ => Complex.exp (μ * (s - u)) * E.eval u) = fun u : ℝ =>
      ∑ lam ∈ E.support, Complex.exp (μ * (s - u)) * ((E lam).eval (u : ℂ) * Complex.exp (lam * u)) :=
    funext fun u => by rw [eval_eq_sum, Finset.mul_sum]
  rw [hsum, intervalIntegral.integral_finsetSum (f := fun lam (u : ℝ) =>
    Complex.exp (μ * (s - u)) * ((E lam).eval (u : ℂ) * Complex.exp (lam * u))) fun lam _ => by
      exact ((by fun_prop : Continuous fun u : ℝ => Complex.exp (μ * (s - u))).mul
        (((E lam).continuous.comp Complex.continuous_ofReal).mul (by fun_prop))).intervalIntegrable _ _]

/-! ## Exponential bounds and the Laplace transform -/

theorem norm_eval_polynomial_le (p : Polynomial ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ‖p.eval (s : ℂ)‖ ≤ C * Real.exp (δ * s) := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * (i.factorial / δ ^ i),
    Finset.sum_nonneg fun i _ => by positivity, fun s hs => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := Real.pow_div_factorial_le_exp (δ * s) (by positivity) i
  rw [mul_pow, div_le_iff₀ (by positivity)] at h
  have hδi : 0 < δ ^ i := pow_pos hδ i
  calc ‖p.coeff i‖ * s ^ i = ‖p.coeff i‖ * (δ ^ i * s ^ i) / δ ^ i := by field_simp
    _ ≤ ‖p.coeff i‖ * (Real.exp (δ * s) * i.factorial) / δ ^ i := by gcongr
    _ = _ := by ring

/-- Exponential polynomials grow at most like `e^{As}` for every `A` exceeding the real parts of
their exponents. -/
theorem exists_norm_eval_le (E : QuasiPolynomial) {A : ℝ} (hA : ∀ μ ∈ E.support, μ.re < A) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ‖E.eval s‖ ≤ C * Real.exp (A * s) := by
  classical
  have hC : ∀ μ ∈ E.support, ∃ C, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖(E μ).eval (s : ℂ)‖ ≤ C * Real.exp ((A - μ.re) * s) := fun μ hμ =>
    norm_eval_polynomial_le (E μ) (by linarith [hA μ hμ])
  choose! C hC0 hCb using hC
  refine ⟨∑ μ ∈ E.support, C μ, Finset.sum_nonneg hC0, fun s hs => ?_⟩
  rw [eval_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : (μ * (s : ℂ)).re = μ.re * s := by simp [Complex.mul_re]
  rw [hre]
  calc ‖(E μ).eval (s : ℂ)‖ * Real.exp (μ.re * s) ≤
        C μ * Real.exp ((A - μ.re) * s) * Real.exp (μ.re * s) :=
        mul_le_mul_of_nonneg_right (hCb μ hμ s hs) (Real.exp_pos _).le
    _ = C μ * Real.exp (A * s) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The Laplace transform `Σ_μ Σ_j p_{μ,j} j!/(q − μ)^{j+1}`, a rational function of `q`. -/
def laplace (E : QuasiPolynomial) (q : ℂ) : ℂ :=
  E.sum fun μ p => ∑ j ∈ Finset.range (p.natDegree + 1),
    p.coeff j * (j.factorial : ℂ) / (q - μ) ^ (j + 1)

theorem laplace_eq_sum (E : QuasiPolynomial) (q : ℂ) :
    E.laplace q = ∑ μ ∈ E.support, ∑ j ∈ Finset.range ((E μ).natDegree + 1),
      (E μ).coeff j * (j.factorial : ℂ) / (q - μ) ^ (j + 1) := rfl

theorem integrableOn_pow_mul_cexp (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ j * Complex.exp (-(z * t))) (Ioi 0) := by
  have h := integrableOn_cpow_mul_cexp (a := (j : ℂ) + 1) (c := z) (by simp; positivity) hz
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Complex.cpow_natCast]

theorem integral_pow_mul_cexp (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ j * Complex.exp (-(z * t)) = (j.factorial : ℂ) / z ^ (j + 1) := by
  have h := gammaScaledIntegral_eq (a := (j : ℂ) + 1) (by simp; positivity) hz
  unfold gammaScaledIntegral at h
  simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial] at h
  rw [h, show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]

theorem eval_mul_cexp_eq_sum (E : QuasiPolynomial) (q : ℂ) (s : ℝ) :
    E.eval s * Complex.exp (-(q * s)) = ∑ μ ∈ E.support, ∑ j ∈ Finset.range ((E μ).natDegree + 1),
      (E μ).coeff j * ((s : ℂ) ^ j * Complex.exp (-((q - μ) * s))) := by
  rw [eval_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Complex.exp (-((q - μ) * s)) = Complex.exp (μ * s) * Complex.exp (-(q * s)) by
    rw [← Complex.exp_add]; ring_nf]
  ring

/-- **Laplace transform of an exponential polynomial.** -/
theorem integral_eval_mul_cexp (E : QuasiPolynomial) {q : ℂ} (hq : ∀ μ ∈ E.support, μ.re < q.re) :
    IntegrableOn (fun s : ℝ => E.eval s * Complex.exp (-(q * s))) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), E.eval s * Complex.exp (-(q * s)) = E.laplace q := by
  have hz : ∀ μ ∈ E.support, 0 < (q - μ).re := fun μ hμ => by
    rw [Complex.sub_re]; linarith [hq μ hμ]
  have hint : ∀ μ ∈ E.support, ∀ j ∈ Finset.range ((E μ).natDegree + 1),
      IntegrableOn (fun s : ℝ => (E μ).coeff j * ((s : ℂ) ^ j * Complex.exp (-((q - μ) * s))))
        (Ioi 0) := fun μ hμ j _ => (integrableOn_pow_mul_cexp j (hz μ hμ)).const_mul _
  have heq : (fun s : ℝ => E.eval s * Complex.exp (-(q * s))) = fun s : ℝ =>
      ∑ μ ∈ E.support, ∑ j ∈ Finset.range ((E μ).natDegree + 1),
        (E μ).coeff j * ((s : ℂ) ^ j * Complex.exp (-((q - μ) * s))) :=
    funext (eval_mul_cexp_eq_sum E q)
  rw [heq]
  refine ⟨integrable_finsetSum _ fun μ hμ => integrable_finsetSum _ (hint μ hμ), ?_⟩
  rw [integral_finsetSum _ fun μ hμ => integrable_finsetSum _ (hint μ hμ), laplace_eq_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [integral_finsetSum _ (hint μ hμ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_cexp j (hz μ hμ), mul_div_assoc]

/-! ## Poles of the Laplace transform, uniqueness and conjugation -/

/-- The contribution `Σ_{j ≤ deg p} p_j j!/(q − μ)^{j+1}` of one exponent. -/
def laplaceTerm (μ : ℂ) (p : Polynomial ℂ) (q : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * (j.factorial : ℂ) / (q - μ) ^ (j + 1)

theorem laplace_eq_sum_term (E : QuasiPolynomial) (q : ℂ) :
    E.laplace q = ∑ μ ∈ E.support, laplaceTerm μ (E μ) q := rfl

theorem laplaceTerm_eq_range (μ : ℂ) {p : Polynomial ℂ} {N : ℕ} (hN : p.natDegree < N) (q : ℂ) :
    laplaceTerm μ p q =
      ∑ j ∈ Finset.range N, p.coeff j * (j.factorial : ℂ) / (q - μ) ^ (j + 1) := by
  unfold laplaceTerm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hj; omega)]
  simp

theorem laplaceTerm_zero (μ q : ℂ) : laplaceTerm μ 0 q = 0 := by simp [laplaceTerm]

theorem laplaceTerm_add (μ : ℂ) (p p' : Polynomial ℂ) (q : ℂ) :
    laplaceTerm μ (p + p') q = laplaceTerm μ p q + laplaceTerm μ p' q := by
  set N := p.natDegree + p'.natDegree + 1
  rw [laplaceTerm_eq_range μ (N := N) ((Polynomial.natDegree_add_le _ _).trans_lt (by omega)),
    laplaceTerm_eq_range μ (N := N) (by omega), laplaceTerm_eq_range μ (N := N) (by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_add]; ring

theorem laplaceTerm_neg (μ : ℂ) (p : Polynomial ℂ) (q : ℂ) :
    laplaceTerm μ (-p) q = -laplaceTerm μ p q := by
  unfold laplaceTerm
  rw [Polynomial.natDegree_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_neg]; ring

theorem laplace_add (E F : QuasiPolynomial) (q : ℂ) : laplace (E + F) q = laplace E q + laplace F q := by
  unfold laplace
  exact Finsupp.sum_add_index' (fun μ => laplaceTerm_zero μ q) fun μ p p' => laplaceTerm_add μ p p' q

theorem laplace_single (μ : ℂ) (p : Polynomial ℂ) (q : ℂ) :
    laplace (Finsupp.single μ p) q = laplaceTerm μ p q := by
  unfold laplace
  exact Finsupp.sum_single_index (laplaceTerm_zero μ q)

theorem laplace_neg (E : QuasiPolynomial) (q : ℂ) : laplace (-E) q = -laplace E q := by
  induction E using Finsupp.induction_linear with
  | zero => simp [laplace]
  | add E F hE hF => rw [neg_add, laplace_add, laplace_add, hE, hF, neg_add]
  | single μ p => rw [← Finsupp.single_neg, laplace_single, laplace_single, laplaceTerm_neg]

theorem laplace_sub (E F : QuasiPolynomial) (q : ℂ) : laplace (E - F) q = laplace E q - laplace F q := by
  rw [sub_eq_add_neg, laplace_add, laplace_neg, sub_eq_add_neg]

theorem laplace_sum {ι : Type*} (t : Finset ι) (E : ι → QuasiPolynomial) (q : ℂ) :
    laplace (∑ i ∈ t, E i) q = ∑ i ∈ t, laplace (E i) q := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [laplace]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, laplace_add, ih]

theorem laplaceTerm_smul (μ c : ℂ) (p : Polynomial ℂ) (q : ℂ) :
    laplaceTerm μ (c • p) q = c * laplaceTerm μ p q := by
  rw [laplaceTerm_eq_range μ (N := p.natDegree + 1)
    ((Polynomial.natDegree_smul_le c p).trans_lt (by omega)), laplaceTerm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_smul, smul_eq_mul]; ring

theorem laplace_smul (c : ℂ) (E : QuasiPolynomial) (q : ℂ) :
    laplace (c • E) q = c * laplace E q := by
  induction E using Finsupp.induction_linear with
  | zero => simp [laplace]
  | add E F hE hF => rw [smul_add, laplace_add, laplace_add, hE, hF, mul_add]
  | single μ p =>
    rw [Finsupp.smul_single, laplace_single, laplace_single, laplaceTerm_smul]

theorem support_convExp_subset (μ : ℂ) (E : QuasiPolynomial) :
    (convExp μ E).support ⊆ insert μ E.support := by
  classical
  intro ν hν
  unfold convExp Finsupp.sum at hν
  obtain ⟨lam, hlam, hν'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hν)
  beta_reduce at hν'
  unfold convExpTerm at hν'
  split_ifs at hν' with h
  · have := Finsupp.support_single_subset hν'
    rw [Finset.mem_singleton] at this
    exact Finset.mem_insert_of_mem (this ▸ hlam)
  · have hsub := Finsupp.support_sub (f := Finsupp.single lam (expSolve (lam - μ) (E lam)))
      (g := Finsupp.single μ (Polynomial.C ((expSolve (lam - μ) (E lam)).eval 0))) hν'
    rcases Finset.mem_union.1 hsub with h1 | h1
    · have := Finsupp.support_single_subset h1
      rw [Finset.mem_singleton] at this
      exact Finset.mem_insert_of_mem (this ▸ hlam)
    · have := Finsupp.support_single_subset h1
      rw [Finset.mem_singleton] at this
      rw [this]
      exact Finset.mem_insert_self μ _

theorem analyticAt_laplaceTerm (μ : ℂ) (p : Polynomial ℂ) {q : ℂ} (hq : q ≠ μ) :
    AnalyticAt ℂ (laplaceTerm μ p) q := by
  have : laplaceTerm μ p = fun q => ∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * (j.factorial : ℂ) / (q - μ) ^ (j + 1) := rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.div
    ((analyticAt_id.sub analyticAt_const).pow _) (pow_ne_zero _ (sub_ne_zero.2 hq))

theorem analyticAt_laplace (E : QuasiPolynomial) {q : ℂ} (hq : q ∉ E.support) :
    AnalyticAt ℂ E.laplace q := by
  rw [show E.laplace = fun q => ∑ μ ∈ E.support, laplaceTerm μ (E μ) q from
    funext (laplace_eq_sum_term E)]
  exact Finset.analyticAt_fun_sum _ fun μ hμ =>
    analyticAt_laplaceTerm μ _ fun h => hq (h ▸ hμ)

/-- **Pole order.**  At an exponent `μ` the transform has a pole of order exactly `deg p_μ + 1`. -/
theorem meromorphicOrderAt_laplace (E : QuasiPolynomial) {μ : ℂ} (hμ : μ ∈ E.support) :
    meromorphicOrderAt E.laplace μ = ((-(((E μ).natDegree : ℤ) + 1) : ℤ) : WithTop ℤ) := by
  classical
  set p := E μ with hp
  set d := p.natDegree
  have hp0 : p ≠ 0 := Finsupp.mem_support_iff.1 hμ
  set G : ℂ → ℂ := fun q => ∑ μ' ∈ E.support.erase μ, laplaceTerm μ' (E μ') q
  have hG : AnalyticAt ℂ G μ := Finset.analyticAt_fun_sum _ fun μ' hμ' =>
    analyticAt_laplaceTerm μ' _ fun h => (Finset.ne_of_mem_erase hμ') h.symm
  set g : ℂ → ℂ := fun q => (∑ j ∈ Finset.range (d + 1), p.coeff j * (j.factorial : ℂ) *
    (q - μ) ^ (d - j)) + (q - μ) ^ (d + 1) * G q
  have hg : AnalyticAt ℂ g μ := by
    refine (Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).pow _)).add
      (((analyticAt_id.sub analyticAt_const).pow _).mul hG)
  have hg0 : g μ ≠ 0 := by
    simp only [g, sub_self, zero_pow (Nat.succ_ne_zero d), zero_mul, add_zero]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => by
      rw [zero_pow (by simp at hj; omega), mul_zero], zero_add, Nat.sub_self, pow_zero, mul_one]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hp0) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d))
  have hrep : ∀ q, q ≠ μ → E.laplace q = (q - μ) ^ (-((d : ℤ) + 1)) • g q := by
    intro q hq
    have hq' : q - μ ≠ 0 := sub_ne_zero.2 hq
    rw [laplace_eq_sum_term, ← Finset.add_sum_erase _ _ hμ, smul_eq_mul, zpow_neg,
      show (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    simp only [g, mul_add, Finset.mul_sum]
    congr 1
    · unfold laplaceTerm
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjd : j ≤ d := by simp at hj; omega
      rw [show (q - μ) ^ (d + 1) = (q - μ) ^ (j + 1) * (q - μ) ^ (d - j) by
        rw [← pow_add]; congr 1; omega]
      have h1 : (q - μ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hq'
      have h2 : (q - μ) ^ (d - j) ≠ 0 := pow_ne_zero _ hq'
      field_simp
      rw [hp]; ring
    · rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq'), one_mul]
  have hmer : MeromorphicAt E.laplace μ := by
    have h1 : MeromorphicAt (fun q => (q - μ) ^ (-((d : ℤ) + 1)) • g q) μ :=
      (((MeromorphicAt.id μ).sub (MeromorphicAt.const μ μ)).zpow _).smul hg.meromorphicAt
    exact h1.congr (eventually_nhdsWithin_of_forall fun q hq => (hrep q hq).symm)
  rw [meromorphicOrderAt_eq_int_iff hmer]
  exact ⟨g, hg, hg0, eventually_nhdsWithin_of_forall fun q hq => hrep q hq⟩

theorem tendsto_ofReal_nhdsNE (a : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨(Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fun h => ht (Complex.ofReal_inj.mp h)

/-- **Uniqueness.**  An exponential polynomial whose Laplace transform vanishes on a real ray is
zero. -/
theorem eq_zero_of_laplace_eq_zero (E : QuasiPolynomial) {A : ℝ}
    (h : ∀ σ : ℝ, A < σ → E.laplace σ = 0) : E = 0 := by
  classical
  by_contra hE
  obtain ⟨μ, hμ⟩ : E.support.Nonempty := Finsupp.support_nonempty_iff.2 hE
  set U : Set ℂ := (↑E.support : Set ℂ)ᶜ
  have hU : IsPreconnected U :=
    ((E.support.countable_toSet).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have han : AnalyticOnNhd ℂ E.laplace U := fun q hq => analyticAt_laplace E hq
  obtain ⟨μ₁, hμ₁, hmax⟩ := Finset.exists_max_image E.support Complex.re ⟨μ, hμ⟩
  set σ₀ : ℝ := max A μ₁.re + 1
  have hσA : A < σ₀ := by have := le_max_left A μ₁.re; linarith
  have hσU : (σ₀ : ℂ) ∈ U := fun hmem => by
    have h1 := hmax _ hmem
    have h2 := le_max_right A μ₁.re
    simp only [Complex.ofReal_re] at h1
    linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (σ₀ : ℂ), E.laplace z = 0 := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] σ₀, E.laplace t = 0 := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hσA)] with t ht using h t ht
    exact (tendsto_ofReal_nhdsNE σ₀).frequently hev.frequently
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hσU hfreq
  have hev : ∀ᶠ z in 𝓝[≠] μ, E.laplace z = 0 := by
    have hcl : IsClosed (↑(E.support.erase μ) : Set ℂ) := (E.support.erase μ).finite_toSet.isClosed
    have hnot : μ ∉ (↑(E.support.erase μ) : Set ℂ) := by simp
    filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
      with z hz hzμ
    refine hzero fun hmem => hz ?_
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hzμ, hmem⟩)
  have := meromorphicOrderAt_eq_top_iff.2 hev
  rw [meromorphicOrderAt_laplace E hμ] at this
  exact WithTop.coe_ne_top this

/-- Complex conjugation `Σ \bar p_μ(s) e^{\bar μ s}`. -/
def conj (E : QuasiPolynomial) : QuasiPolynomial :=
  E.sum fun μ p => Finsupp.single (starRingEnd ℂ μ) (p.map (starRingEnd ℂ))

theorem eval_conj (E : QuasiPolynomial) (s : ℝ) : (conj E).eval s = starRingEnd ℂ (E.eval s) := by
  rw [conj, eval_finsuppSum, Finsupp.sum, eval_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [eval_single, map_mul, Polynomial.eval_map, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    ← Polynomial.eval₂_at_apply (starRingEnd ℂ), Complex.conj_ofReal]

theorem laplace_conj (E : QuasiPolynomial) (q : ℂ) :
    (conj E).laplace q = starRingEnd ℂ (E.laplace (starRingEnd ℂ q)) := by
  rw [conj, Finsupp.sum, laplace_sum, laplace_eq_sum_term, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [laplace_single, laplaceTerm, laplaceTerm, map_sum,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map, map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj, map_natCast]

/-- **Real exponential polynomials.**  If the Laplace transform is real on a real ray, the
exponential polynomial is real-valued. -/
theorem im_eval_eq_zero (E : QuasiPolynomial) {A : ℝ} (h : ∀ σ : ℝ, A < σ → (E.laplace σ).im = 0)
    (s : ℝ) : (E.eval s).im = 0 := by
  have hF : E - conj E = 0 := by
    refine eq_zero_of_laplace_eq_zero _ (A := A) fun σ hσ => ?_
    rw [laplace_sub, laplace_conj, Complex.conj_ofReal, sub_eq_zero]
    exact (Complex.conj_eq_iff_im.2 (h σ hσ)).symm
  have := congrArg (fun F => eval F s) hF
  simp only [eval_sub, eval_zero, eval_conj, sub_eq_zero] at this
  exact Complex.conj_eq_iff_im.1 this.symm

theorem conj_apply (E : QuasiPolynomial) (μ : ℂ) :
    conj E μ = (E (starRingEnd ℂ μ)).map (starRingEnd ℂ) := by
  classical
  rw [conj, Finsupp.sum, Finsupp.finsetSum_apply]
  simp_rw [Finsupp.single_apply]
  rw [Finset.sum_eq_single (starRingEnd ℂ μ)]
  · simp
  · intro ν _ hν
    rw [if_neg]
    rintro rfl
    exact hν (by simp)
  · intro h
    rw [Finsupp.notMem_support_iff.1 h]
    simp

/-- A quasi-polynomial vanishing on the positive half-line is zero. -/
theorem eq_zero_of_eval_eq_zero (E : QuasiPolynomial) (h : ∀ s : ℝ, 0 < s → E.eval s = 0) :
    E = 0 := by
  refine eq_zero_of_laplace_eq_zero E (A := ∑ μ ∈ E.support, |μ.re|) fun σ hσ => ?_
  have hq : ∀ μ ∈ E.support, μ.re < (σ : ℂ).re := fun μ hμ => by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun ν : ℂ => |ν.re|) (fun ν _ => abs_nonneg ν.re) hμ)) hσ
  rw [← (integral_eval_mul_cexp E hq).2,
    setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) fun s hs => by
      simp [h s hs]]
  simp

/-- A quasi-polynomial that is real on the positive half-line is fixed by conjugation. -/
theorem conj_eq_self_of_im_eval (E : QuasiPolynomial) (h : ∀ s : ℝ, 0 < s → (E.eval s).im = 0) :
    conj E = E := by
  refine sub_eq_zero.1 (eq_zero_of_eval_eq_zero _ fun s hs => ?_)
  rw [eval_sub, eval_conj, sub_eq_zero]
  exact Complex.conj_eq_iff_im.2 (h s hs)

/-! ## Trigonometric polynomials do not decay -/

/-- **Cesàro means.**  If `f → 0` then `S⁻¹ ∫₀^S f → 0`. -/
theorem tendsto_average_of_tendsto_zero {f : ℝ → ℂ} (hf : Continuous f)
    (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun S : ℝ => (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, f s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨S₀, hS₀⟩ := h (ε / 2) (by positivity)
  set T₀ := max S₀ 0
  set M := ∫ s in (0 : ℝ)..T₀, ‖f s‖
  refine ⟨max (T₀ + 1) (4 * (M + 1) / ε), fun S hS => ?_⟩
  have hT : T₀ + 1 ≤ S := (le_max_left _ _).trans hS
  have hSpos : 0 < S := by have := le_max_right S₀ 0; linarith
  have hM : 4 * (M + 1) / ε ≤ S := (le_max_right _ _).trans hS
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg (le_max_right _ _) fun _ _ => norm_nonneg _
  rw [dist_zero_right, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hSpos.le]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := f)
    (a := 0) (b := T₀) (c := S) (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have h1 : ‖∫ s in (0 : ℝ)..T₀, f s‖ ≤ M :=
    intervalIntegral.norm_integral_le_integral_norm (le_max_right _ _)
  have h2 : ‖∫ s in T₀..S, f s‖ ≤ ε / 2 * |S - T₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      have hs' : T₀ < s := by
        rw [Set.uIoc_of_le (by linarith)] at hs
        exact hs.1
      have := hS₀ s ((le_max_left S₀ 0).trans hs'.le)
      rw [dist_zero_right] at this
      exact this.le
  rw [← hsplit]
  have habs : |S - T₀| ≤ S := by
    rw [abs_of_nonneg (by linarith)]; linarith [le_max_right S₀ 0]
  have htot : ‖(∫ s in (0 : ℝ)..T₀, f s) + ∫ s in T₀..S, f s‖ ≤ M + ε / 2 * S :=
    (norm_add_le _ _).trans (add_le_add h1 (h2.trans (by gcongr)))
  rw [inv_mul_lt_iff₀ hSpos]
  have : M < ε / 2 * S := by
    rw [div_le_iff₀ hε] at hM
    nlinarith
  linarith

theorem tendsto_average_cexp {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun S : ℝ => (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, Complex.exp (ω * s * Complex.I)) atTop
      (𝓝 0) := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have heq : ∀ S : ℝ, ∫ s in (0 : ℝ)..S, Complex.exp (ω * s * Complex.I) =
      (Complex.exp (ω * Complex.I * S) - 1) / (ω * Complex.I) := fun S => by
    have := integral_exp_mul_complex (a := 0) (b := S) hc
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [← this]
    congr 1; funext s; ring_nf
  simp_rw [heq]
  have hb : ∀ S : ℝ, ‖(Complex.exp (ω * Complex.I * S) - 1) / (ω * Complex.I)‖ ≤ 2 / ‖(ω : ℂ) * Complex.I‖ :=
    fun S => by
      rw [norm_div]
      refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
      rw [show (ω : ℂ) * Complex.I * S = ((ω * S : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  refine squeeze_zero_norm' (Eventually.of_forall fun S => ?_) (?_ : Tendsto (fun S : ℝ =>
    ‖(S : ℂ)⁻¹‖ * (2 / ‖(ω : ℂ) * Complex.I‖)) atTop (𝓝 0))
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb S) (norm_nonneg _)
  · have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (2 / ‖(ω : ℂ) * Complex.I‖)
    rw [zero_mul] at this
    refine this.congr' (eventually_ge_atTop 0 |>.mono fun S hS => ?_)
    show S⁻¹ * _ = ‖(S : ℂ)⁻¹‖ * _
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hS]

/-- **A nonzero trigonometric polynomial does not tend to zero.** -/
theorem not_tendsto_zero_trig {ι : Type*} (t : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    (hω : Set.InjOn ω t) {i₀ : ι} (hi₀ : i₀ ∈ t) (hc : c i₀ ≠ 0) :
    ¬ Tendsto (fun s : ℝ => ∑ i ∈ t, c i * Complex.exp (ω i * s * Complex.I)) atTop (𝓝 0) := by
  classical
  intro hT
  set f : ℝ → ℂ := fun s => (∑ i ∈ t, c i * Complex.exp (ω i * s * Complex.I)) *
    Complex.exp (-(ω i₀ * s * Complex.I))
  have hfc : Continuous f := by simp only [f]; fun_prop
  have hf0 : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ s : ℝ, ‖Complex.exp (-(ω i₀ * s * Complex.I))‖ ≤ 1 := fun s => by
      rw [show -((ω i₀ : ℂ) * s * Complex.I) = ((-(ω i₀ * s) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hTn : Tendsto (fun s : ℝ => ‖∑ i ∈ t, c i * Complex.exp (ω i * s * Complex.I)‖) atTop
        (𝓝 0) := by
      have := hT.norm
      rwa [norm_zero] at this
    refine squeeze_zero_norm (fun s => ?_) hTn
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb s)
  have havg := tendsto_average_of_tendsto_zero hfc hf0
  have hsum : ∀ S : ℝ, (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, f s = ∑ i ∈ t, c i *
      ((S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, Complex.exp ((ω i - ω i₀ : ℝ) * s * Complex.I)) := fun S => by
    have hfe : f = fun s : ℝ => ∑ i ∈ t, c i * Complex.exp ((ω i - ω i₀ : ℝ) * s * Complex.I) :=
      funext fun s => by
        simp only [f, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, ← Complex.exp_add]; push_cast; ring_nf
    rw [hfe, intervalIntegral.integral_finsetSum (f := fun i (s : ℝ) =>
      c i * Complex.exp ((ω i - ω i₀ : ℝ) * s * Complex.I)) fun i _ => by
        exact (by fun_prop : Continuous fun s : ℝ =>
          c i * Complex.exp ((ω i - ω i₀ : ℝ) * s * Complex.I)).intervalIntegrable _ _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]; ring
  have hlim : Tendsto (fun S : ℝ => (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, f s) atTop (𝓝 (c i₀)) := by
    simp_rw [hsum]
    rw [show c i₀ = ∑ i ∈ t, if i = i₀ then c i else 0 by
      rw [Finset.sum_ite_eq' t i₀ c, if_pos hi₀]]
    refine tendsto_finsetSum _ fun i hi => ?_
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl]
      have : ∀ᶠ S : ℝ in atTop, c i * ((S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S,
          Complex.exp ((ω i - ω i : ℝ) * s * Complex.I)) = c i := by
        filter_upwards [eventually_gt_atTop 0] with S hS
        simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
          intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
        rw [inv_mul_cancel₀ (by exact_mod_cast hS.ne'), mul_one]
      exact tendsto_const_nhds.congr' (this.mono fun S h => h.symm)
    · rw [if_neg h]
      have hne : ω i - ω i₀ ≠ 0 := sub_ne_zero.2 fun he => h (hω hi hi₀ he)
      have := (tendsto_average_cexp hne).const_mul (c i)
      rwa [mul_zero] at this
  exact hc (tendsto_nhds_unique hlim havg)

/-! ## Top-term asymptotics and exponential type -/

theorem tendsto_eval_div_pow {p : Polynomial ℂ} {m : ℕ} (hp : p.natDegree ≤ m) :
    Tendsto (fun s : ℝ => p.eval (s : ℂ) / (s : ℂ) ^ m) atTop (𝓝 (p.coeff m)) := by
  have heq : ∀ᶠ s : ℝ in atTop, p.eval (s : ℂ) / (s : ℂ) ^ m =
      ∑ j ∈ Finset.range (m + 1), p.coeff j * ((s : ℂ) ^ (m - j))⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by omega), Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := by simp at hj; omega
    rw [show (s : ℂ) ^ m = (s : ℂ) ^ j * (s : ℂ) ^ (m - j) by rw [← pow_add]; congr 1; omega]
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  rw [show p.coeff m = ∑ j ∈ Finset.range (m + 1), if j = m then p.coeff j else 0 by
    rw [Finset.sum_ite_eq' _ m, if_pos (Finset.mem_range.2 (by omega))]]
  refine tendsto_finsetSum _ fun j hj => ?_
  by_cases h : j = m
  · subst h
    simp only [Nat.sub_self, pow_zero, inv_one, mul_one, if_pos]
    exact tendsto_const_nhds
  · rw [if_neg h]
    have hjm : 0 < m - j := by simp at hj; omega
    have hinv : Tendsto (fun s : ℝ => ((s : ℂ) ^ (m - j))⁻¹) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_atTop (α := ℝ) hjm.ne').comp tendsto_id
      have h2 := (tendsto_inv_atTop_zero.comp h1)
      have h3 := (Complex.continuous_ofReal.tendsto 0).comp h2
      rw [Complex.ofReal_zero] at h3
      refine h3.congr fun s => ?_
      simp
    have := hinv.const_mul (p.coeff j)
    rwa [mul_zero] at this

/-- **Top-term asymptotics.**  For `E ≠ 0` let `a` be the largest real part of an exponent and `m`
the largest degree among the exponents on the line `Re μ = a`; `top` collects the exponents on that
line of degree `m`.  Then `E(s)/(s^m e^{as}) − Σ_{μ ∈ top} lead(p_μ) e^{i Im μ s} → 0`. -/
theorem exists_top_asymptotics (E : QuasiPolynomial) (hE : E ≠ 0) :
    ∃ (a : ℝ) (m : ℕ) (top : Finset ℂ), top.Nonempty ∧
      (∀ μ, μ ∈ top ↔ μ ∈ E.support ∧ μ.re = a ∧ (E μ).natDegree = m) ∧
      (∀ μ ∈ E.support, μ.re ≤ a) ∧ (∀ μ ∈ E.support, μ.re = a → (E μ).natDegree ≤ m) ∧
      Tendsto (fun s : ℝ => E.eval s / ((s : ℂ) ^ m * (Real.exp (a * s) : ℂ)) -
        ∑ μ ∈ top, (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)) atTop (𝓝 0) := by
  classical
  obtain ⟨μ₀, hμ₀⟩ : E.support.Nonempty := Finsupp.support_nonempty_iff.2 hE
  obtain ⟨μ₁, hμ₁, hmax⟩ := Finset.exists_max_image E.support Complex.re ⟨μ₀, hμ₀⟩
  set a := μ₁.re
  set Sa := E.support.filter fun μ => μ.re = a
  obtain ⟨μ₂, hμ₂, hmaxd⟩ := Finset.exists_max_image Sa (fun μ => (E μ).natDegree)
    ⟨μ₁, Finset.mem_filter.2 ⟨hμ₁, rfl⟩⟩
  set m := (E μ₂).natDegree
  set top := Sa.filter fun μ => (E μ).natDegree = m
  have hSa : ∀ μ, μ ∈ Sa ↔ μ ∈ E.support ∧ μ.re = a := fun μ => Finset.mem_filter
  have htop : ∀ μ, μ ∈ top ↔ (μ ∈ E.support ∧ μ.re = a) ∧ (E μ).natDegree = m := fun μ => by
    rw [Finset.mem_filter, hSa]
  refine ⟨a, m, top, ⟨μ₂, (htop μ₂).2 ⟨(hSa μ₂).1 hμ₂, rfl⟩⟩, fun μ => (htop μ).trans and_assoc,
    hmax, fun μ hμ hre => hmaxd μ ((hSa μ).2 ⟨hμ, hre⟩), ?_⟩
  -- termwise limits
  have hsum_top : ∀ s : ℝ, ∑ μ ∈ top, (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I) =
      ∑ μ ∈ E.support, if μ ∈ top then (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)
        else 0 := fun s => by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 fun μ hμ => ((htop μ).1 hμ).1.1]
  have hsplit : ∀ᶠ s : ℝ in atTop, E.eval s / ((s : ℂ) ^ m * (Real.exp (a * s) : ℂ)) -
      ∑ μ ∈ top, (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I) =
      ∑ μ ∈ E.support, ((E μ).eval (s : ℂ) / (s : ℂ) ^ m * Complex.exp ((μ - a) * s) -
        if μ ∈ top then (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I) else 0) := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [hsum_top, eval_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    have he : Complex.exp ((μ - a) * s) = Complex.exp (μ * s) / (Real.exp (a * s) : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_sub]; push_cast; ring_nf
    rw [he]
    have hea : (Real.exp (a * s) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
  have key : ∀ μ ∈ E.support, Tendsto (fun s : ℝ => (E μ).eval (s : ℂ) / (s : ℂ) ^ m *
      Complex.exp ((μ - a) * s) - if μ ∈ top then (E μ).leadingCoeff *
        Complex.exp (μ.im * s * Complex.I) else 0) atTop (𝓝 0) := by
    intro μ hμ
    by_cases hre : μ.re = a
    · have hdeg : (E μ).natDegree ≤ m := hmaxd μ ((hSa μ).2 ⟨hμ, hre⟩)
      have hexp : ∀ s : ℝ, Complex.exp ((μ - a) * s) = Complex.exp (μ.im * s * Complex.I) := fun s => by
        congr 1
        conv_lhs => rw [← Complex.re_add_im μ]
        rw [hre]; ring
      have hcoeff : (if μ ∈ top then (E μ).leadingCoeff else 0) = (E μ).coeff m := by
        split_ifs with h
        · rw [Polynomial.leadingCoeff, ((htop μ).1 h).2]
        · have hlt : (E μ).natDegree < m := lt_of_le_of_ne hdeg fun he =>
            h ((htop μ).2 ⟨⟨hμ, hre⟩, he⟩)
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      have hb : ∀ s : ℝ, ‖Complex.exp (μ.im * s * Complex.I)‖ ≤ 1 := fun s => by
        rw [show (μ.im : ℂ) * s * Complex.I = ((μ.im * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      have hd : Tendsto (fun s : ℝ => ‖(E μ).eval (s : ℂ) / (s : ℂ) ^ m - (E μ).coeff m‖) atTop
          (𝓝 0) := by
        have := (tendsto_eval_div_pow (p := E μ) hdeg).sub_const ((E μ).coeff m)
        rw [sub_self] at this
        have := this.norm
        rwa [norm_zero] at this
      refine squeeze_zero_norm (fun s => ?_) hd
      have hite : (if μ ∈ top then (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I) else 0) =
          (E μ).coeff m * Complex.exp (μ.im * s * Complex.I) := by
        rw [← hcoeff]; split_ifs <;> simp
      rw [hite, hexp, ← sub_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb s)
    · have hlt : μ.re < a := lt_of_le_of_ne (hmax μ hμ) hre
      have hnot : μ ∉ top := fun h => hre ((htop μ).1 h).1.2
      simp only [hnot, if_false, sub_zero]
      set δ := (a - μ.re) / 2
      have hδ : 0 < δ := by simp only [δ]; linarith
      obtain ⟨C, hC0, hC⟩ := norm_eval_polynomial_le (E μ) hδ
      have hlim : Tendsto (fun s : ℝ => C * Real.exp (-(δ * s))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop hδ)).const_mul C
        rw [mul_zero] at this
        exact this.congr fun s => by simp only [Function.comp, id]
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_ge_atTop 1] with s hs
      have hs0 : 0 ≤ s := by linarith
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0, Complex.norm_exp]
      have hre' : ((μ - a) * (s : ℂ)).re = (μ.re - a) * s := by simp [Complex.mul_re]
      rw [hre']
      have hsm : 1 ≤ s ^ m := one_le_pow₀ hs
      calc ‖(E μ).eval (s : ℂ)‖ / s ^ m * Real.exp ((μ.re - a) * s)
          ≤ C * Real.exp (δ * s) * Real.exp ((μ.re - a) * s) := by
            gcongr
            exact (div_le_self (norm_nonneg _) hsm).trans (hC s hs0)
        _ = C * Real.exp (-(δ * s)) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; simp only [δ]; ring
  simpa using tendsto_finsetSum E.support key

/-- **Growth of a real quasi-polynomial.**  If `E` is fixed by conjugation, its coefficients satisfy
`p_{μ̄} = p̄_μ`, so the top exponents come in conjugate pairs and
`Re E(s) = s^m e^{as} (Σ_top Re(lead(p_μ) e^{i Im μ s}) + o(1))`; the real trigonometric polynomial
on the right does not tend to zero. -/
theorem exists_real_top_asymptotics (E : QuasiPolynomial) (hE : E ≠ 0) (hc : conj E = E) :
    ∃ (a : ℝ) (m : ℕ) (top : Finset ℂ), top.Nonempty ∧
      (∀ μ, μ ∈ top ↔ μ ∈ E.support ∧ μ.re = a ∧ (E μ).natDegree = m) ∧
      (∀ μ ∈ E.support, μ.re ≤ a) ∧ (∀ μ ∈ E.support, μ.re = a → (E μ).natDegree ≤ m) ∧
      (∀ μ, E (starRingEnd ℂ μ) = (E μ).map (starRingEnd ℂ)) ∧
      Tendsto (fun s : ℝ => (E.eval s).re / (s ^ m * Real.exp (a * s)) -
        ∑ μ ∈ top, ((E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)).re) atTop (𝓝 0) ∧
      ¬ Tendsto (fun s : ℝ => ∑ μ ∈ top,
        ((E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)).re) atTop (𝓝 0) := by
  obtain ⟨a, m, top, hne, htop, hmax, hdeg, hlim⟩ := exists_top_asymptotics E hE
  have hsym : ∀ μ, E (starRingEnd ℂ μ) = (E μ).map (starRingEnd ℂ) := fun μ => by
    conv_lhs => rw [← hc]
    rw [conj_apply, Complex.conj_conj]
  have hmemc : ∀ μ, μ ∈ E.support → starRingEnd ℂ μ ∈ E.support := fun μ hμ => by
    rw [Finsupp.mem_support_iff, hsym, Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
    exact Finsupp.mem_support_iff.1 hμ
  have hdegc : ∀ μ, (E (starRingEnd ℂ μ)).natDegree = (E μ).natDegree := fun μ => by
    rw [hsym, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _)]
  have htopc : ∀ μ ∈ top, starRingEnd ℂ μ ∈ top := fun μ hμ => by
    obtain ⟨h1, h2, h3⟩ := (htop μ).1 hμ
    exact (htop _).2 ⟨hmemc μ h1, by rw [Complex.conj_re, h2], by rw [hdegc, h3]⟩
  set T : ℝ → ℂ := fun s => ∑ μ ∈ top, (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)
  have hTreal : ∀ s : ℝ, starRingEnd ℂ (T s) = T s := fun s => by
    simp only [T, map_sum]
    refine Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) htopc htopc
      (fun μ _ => Complex.conj_conj μ) (fun μ _ => Complex.conj_conj μ) fun μ _ => ?_
    rw [hsym, Polynomial.leadingCoeff_map_of_injective (RingHom.injective _), map_mul,
      ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_im, Complex.ofReal_neg]
    ring
  have hre : ∀ s : ℝ, ∑ μ ∈ top, ((E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)).re =
      (T s).re := fun s => by simp only [T, Complex.re_sum]
  refine ⟨a, m, top, hne, htop, hmax, hdeg, hsym, ?_, fun h => ?_⟩
  · have := (Complex.continuous_re.tendsto 0).comp hlim
    rw [Complex.zero_re] at this
    refine this.congr fun s => ?_
    simp only [Function.comp, Complex.sub_re, hre]
    rw [show (s : ℂ) ^ m * (Real.exp (a * s) : ℂ) = ((s ^ m * Real.exp (a * s) : ℝ) : ℂ) by
      push_cast; ring, Complex.div_ofReal_re]
  · have hT : Tendsto T atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp h
      rw [Complex.ofReal_zero] at this
      refine this.congr fun s => ?_
      simp only [Function.comp, hre]
      exact Complex.conj_eq_iff_re.1 (hTreal s)
    obtain ⟨μ₀, hμ₀⟩ := hne
    refine not_tendsto_zero_trig top (fun μ => (E μ).leadingCoeff) (fun μ => μ.im)
      (fun μ hμ ν hν hμν => ?_) hμ₀
      (Polynomial.leadingCoeff_ne_zero.2 (Finsupp.mem_support_iff.1 ((htop μ₀).1 hμ₀).1)) hT
    exact Complex.ext (by rw [((htop μ).1 hμ).2.1, ((htop ν).1 hν).2.1]) hμν

theorem eventually_norm_eval_le_exp (E : QuasiPolynomial) {A : ℝ} (hA : ∀ μ ∈ E.support, μ.re < A) :
    ∀ᶠ s in atTop, ‖E.eval s‖ ≤ Real.exp (A * s) := by
  classical
  rcases E.support.eq_empty_or_nonempty with h | h
  · refine Eventually.of_forall fun s => ?_
    rw [eval_eq_sum, h, Finset.sum_empty, norm_zero]
    exact (Real.exp_pos _).le
  obtain ⟨μ₁, hμ₁, hmax⟩ := Finset.exists_max_image E.support Complex.re h
  set A' := (μ₁.re + A) / 2
  have hA' : ∀ μ ∈ E.support, μ.re < A' := fun μ hμ => by
    have := hmax μ hμ; have := hA μ₁ hμ₁; simp only [A']; linarith
  obtain ⟨C, hC0, hC⟩ := exists_norm_eval_le E hA'
  have hδ : 0 < A - A' := by have := hA μ₁ hμ₁; simp only [A']; linarith
  have hgrow : Tendsto (fun s : ℝ => Real.exp ((A - A') * s)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hδ)
  filter_upwards [hgrow.eventually_ge_atTop C, eventually_ge_atTop 0] with s hs hs0
  calc ‖E.eval s‖ ≤ C * Real.exp (A' * s) := hC s hs0
    _ ≤ Real.exp ((A - A') * s) * Real.exp (A' * s) :=
        mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = Real.exp (A * s) := by rw [← Real.exp_add]; ring_nf

/-- **Lower growth.**  An exponential polynomial exceeds `e^{Bs}` for arbitrarily large `s`,
for every `B` below the largest real part of its exponents. -/
theorem frequently_exp_le_norm_eval (E : QuasiPolynomial) {a : ℝ} (ha : ∃ μ ∈ E.support, μ.re = a)
    (ha' : ∀ μ ∈ E.support, μ.re ≤ a) {B : ℝ} (hB : B < a) :
    ∃ᶠ s in atTop, Real.exp (B * s) ≤ ‖E.eval s‖ := by
  classical
  obtain ⟨μa, hμa, hμare⟩ := ha
  have hE : E ≠ 0 := fun h => by rw [h] at hμa; simp at hμa
  obtain ⟨a', m, top, htopne, htopiff, hle, -, hlim⟩ := exists_top_asymptotics E hE
  have htopsub : ∀ μ ∈ top, μ ∈ E.support := fun μ hμ => ((htopiff μ).1 hμ).1
  have htop : ∀ μ ∈ top, μ.re = a' ∧ (E μ).natDegree = m := fun μ hμ =>
    ((htopiff μ).1 hμ).2
  have haa : a' = a := by
    obtain ⟨μ, hμ⟩ := htopne
    have h1 := (htop μ hμ).1
    have h2 := ha' μ (htopsub μ hμ)
    have h3 := hle μa hμa
    linarith
  subst haa
  set T : ℝ → ℂ := fun s => ∑ μ ∈ top, (E μ).leadingCoeff * Complex.exp (μ.im * s * Complex.I)
  have hT : ¬ Tendsto T atTop (𝓝 0) := by
    obtain ⟨μ, hμ⟩ := htopne
    refine not_tendsto_zero_trig top (fun μ => (E μ).leadingCoeff) Complex.im (fun μ hμ ν hν he => ?_)
      hμ (Polynomial.leadingCoeff_ne_zero.2 (Finsupp.mem_support_iff.1 (htopsub μ hμ)))
    exact Complex.ext (by rw [(htop μ hμ).1, (htop ν hν).1]) he
  obtain ⟨η, hη, hfreq⟩ : ∃ η > 0, ∃ᶠ s in atTop, η ≤ ‖T s‖ := by
    by_contra hcon
    simp only [gt_iff_lt, not_exists, not_and, Filter.not_frequently, not_le] at hcon
    refine hT (Metric.tendsto_nhds.2 fun ε hε => ?_)
    filter_upwards [hcon ε hε] with s hs
    rwa [dist_zero_right]
  have hclose := (Metric.tendsto_nhds.1 hlim) (η / 2) (by positivity)
  have hgrow : Tendsto (fun s : ℝ => η / 2 * Real.exp ((a' - B) * s)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
      (by positivity)
  refine (hfreq.and_eventually ((hclose.and (hgrow.eventually_ge_atTop 1)).and
    (eventually_ge_atTop 1))).mono fun s ⟨hs1, ⟨hs2, hs3⟩, hs4⟩ => ?_
  rw [dist_zero_right] at hs2
  have hs0 : 0 < s := by linarith
  set r := E.eval s / ((s : ℂ) ^ m * (Real.exp (a' * s) : ℂ))
  have hr : η / 2 ≤ ‖r‖ := by
    have := norm_sub_norm_le (T s) (T s - r)
    rw [show T s - (T s - r) = r by ring, norm_sub_rev] at this
    linarith
  have hden : (s : ℂ) ^ m * (Real.exp (a' * s) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hs0.ne')) (by exact_mod_cast (Real.exp_pos _).ne')
  have hEr : E.eval s = r * ((s : ℂ) ^ m * (Real.exp (a' * s) : ℂ)) := by
    simp only [r]; rw [div_mul_cancel₀ _ hden]
  have hnorm : ‖(s : ℂ) ^ m * (Real.exp (a' * s) : ℂ)‖ = s ^ m * Real.exp (a' * s) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs0.le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hEr, norm_mul, hnorm]
  have hsm : 1 ≤ s ^ m := one_le_pow₀ hs4
  have he : Real.exp (B * s) * (η / 2 * Real.exp ((a' - B) * s)) = η / 2 * Real.exp (a' * s) := by
    rw [mul_left_comm, ← Real.exp_add]; ring_nf
  calc Real.exp (B * s) ≤ Real.exp (B * s) * (η / 2 * Real.exp ((a' - B) * s)) :=
        le_mul_of_one_le_right (Real.exp_pos _).le hs3
    _ = η / 2 * Real.exp (a' * s) := he
    _ ≤ ‖r‖ * (s ^ m * Real.exp (a' * s)) := by
        have := Real.exp_pos (a' * s)
        nlinarith [mul_le_mul hr (le_mul_of_one_le_left this.le hsm) this.le (norm_nonneg r)]

/-- **Exponential type.**  If `a ≥ 0` is the largest real part of an exponent of `E`,
`limsup_{s→∞} log‖E(s)‖/s = a`. -/
theorem limsup_log_norm_eval (E : QuasiPolynomial) {a : ℝ} (ha : ∃ μ ∈ E.support, μ.re = a)
    (ha' : ∀ μ ∈ E.support, μ.re ≤ a) (ha0 : 0 ≤ a) :
    Filter.limsup (fun s : ℝ => Real.log ‖E.eval s‖ / s) atTop = a := by
  have hup : ∀ ε > 0, ∀ᶠ s in atTop, Real.log ‖E.eval s‖ / s ≤ a + ε := fun ε hε => by
    filter_upwards [eventually_norm_eval_le_exp E (A := a + ε) fun μ hμ => by
      linarith [ha' μ hμ], eventually_gt_atTop 0] with s hs hs0
    rw [div_le_iff₀ hs0]
    rcases (norm_nonneg (E.eval s)).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; positivity
    · calc Real.log ‖E.eval s‖ ≤ Real.log (Real.exp ((a + ε) * s)) := Real.log_le_log h hs
        _ = (a + ε) * s := Real.log_exp _
  have hlow : ∀ ε > 0, ∃ᶠ s in atTop, a - ε ≤ Real.log ‖E.eval s‖ / s := fun ε hε => by
    refine ((frequently_exp_le_norm_eval E ha ha' (B := a - ε) (by linarith)).and_eventually
      (eventually_gt_atTop 0)).mono fun s ⟨hs, hs0⟩ => ?_
    rw [le_div_iff₀ hs0]
    calc (a - ε) * s = Real.log (Real.exp ((a - ε) * s)) := (Real.log_exp _).symm
      _ ≤ Real.log ‖E.eval s‖ := Real.log_le_log (Real.exp_pos _) hs
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun s : ℝ => Real.log ‖E.eval s‖ / s :=
    isBoundedUnder_of_eventually_le (hup 1 one_pos)
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop fun s : ℝ => Real.log ‖E.eval s‖ / s :=
    ⟨a - 1, fun b hb => by
      obtain ⟨s, hs1, hs2⟩ := ((hlow 1 one_pos).and_eventually hb).exists
      exact hs1.trans hs2⟩
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => limsup_le_of_le hcobdd (hup ε hε))
    (le_of_forall_pos_le_add fun ε hε => ?_)
  have := le_limsup_of_frequently_le (hlow ε hε) hbdd
  linarith

end QuasiPolynomial

end

end GaloisForLFunctions.HTGeometry
