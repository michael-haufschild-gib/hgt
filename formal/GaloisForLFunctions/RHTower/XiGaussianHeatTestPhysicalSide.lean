import GaloisForLFunctions.RHTower.XiGaussianHeatHankelIndex

/-!
# The heat test on the physical side

The heat Hankel form only sees the even entire functions `G(z) = e^{-az²/2} p(z²)` at the
spectral points.  Each one is the Fourier–Laplace transform of an explicit polynomial–Gaussian.

**Theorem** (`integral_heatPhysical_mul_cexp`).  For `a > 0`, `p ∈ ℂ[X]` and every complex `z`,

`∫ g(x) e^{ixz} dx = e^{-az²/2} p(z²)`,   `g = (2πa)^{-1/2} Σ_k p_k (−1)^k ∂^{2k} e^{-x²/(2a)}`.

Proof.  `∫ e^{ixt} e^{-bx²} dx = (π/b)^{1/2} e^{-t²/(4b)}` holds for complex `t`
(`fourierIntegral_gaussian`).  Integration by parts gives
`∫ ∂^m e^{-bx²} · e^{ixt} dx = (−it)^m ∫ e^{-bx²} e^{ixt} dx`.  The boundary terms vanish because
every derivative is a polynomial times `e^{-bx²}`, which beats `|e^{ixt}| = e^{-x Im t}`.  Take
`b = 1/(2a)` and use `(−it)^{2k} = (−1)^k t^{2k}`.
-/

open scoped Real
open Complex Polynomial MeasureTheory

namespace RHTower

noncomputable section

/-! ## Derivatives of the Gaussian -/

/-- The polynomial factor of the `m`-th derivative of `e^{-bx²}`. -/
def gaussDerivPoly (b : ℝ) : ℕ → ℂ[X]
  | 0 => 1
  | m + 1 => derivative (gaussDerivPoly b m) - C (2 * (b : ℂ)) * X * gaussDerivPoly b m

/-- The `m`-th derivative of `e^{-bx²}`. -/
def gaussDeriv (b : ℝ) (m : ℕ) (x : ℝ) : ℂ :=
  (gaussDerivPoly b m).eval (x : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)

theorem hasDerivAt_gaussDeriv (b : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (gaussDeriv b m) (gaussDeriv b (m + 1) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (gaussDerivPoly b m).eval (y : ℂ))
      ((derivative (gaussDerivPoly b m)).eval (x : ℂ)) x :=
    ((gaussDerivPoly b m).hasDerivAt (x : ℂ)).comp_ofReal
  have h3 : HasDerivAt (fun y : ℂ => -(b : ℂ) * y ^ 2) (-(b : ℂ) * (2 * (x : ℂ))) (x : ℂ) := by
    exact ((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(b : ℂ))).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2))
      (Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) * (-(b : ℂ) * (2 * (x : ℂ)))) x :=
    h3.cexp.comp_ofReal
  have key : gaussDeriv b (m + 1) x =
      (derivative (gaussDerivPoly b m)).eval (x : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) +
        (gaussDerivPoly b m).eval (x : ℂ) *
          (Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) * (-(b : ℂ) * (2 * (x : ℂ)))) := by
    rw [gaussDeriv, gaussDerivPoly]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring
  exact (h1.mul h2).congr_deriv key.symm

/-! ## Integrability -/

/-- `(1 + |x|)^d ≤ d! (4/b)^d e^{b/2} e^{(b/2)x²}`. -/
theorem one_add_abs_pow_le_exp {b : ℝ} (hb : 0 < b) (d : ℕ) (x : ℝ) :
    (1 + |x|) ^ d ≤ d.factorial * (4 / b) ^ d * Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2) := by
  have h0 : 0 ≤ b / 4 * (1 + |x|) ^ 2 := by positivity
  have hfac := Real.pow_div_factorial_le_exp _ h0 d
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  rw [div_le_iff₀ hf] at hfac
  have hsq : (1 + |x|) ^ 2 ≤ 2 + 2 * x ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have hexp : Real.exp (b / 4 * (1 + |x|) ^ 2) ≤ Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h1 : (1 + |x|) ^ d ≤ (1 + |x|) ^ (2 * d) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by omega)
  have hb4 : 0 ≤ (4 / b) ^ d := by positivity
  calc (1 + |x|) ^ d ≤ (1 + |x|) ^ (2 * d) := h1
    _ = (4 / b) ^ d * (b / 4 * (1 + |x|) ^ 2) ^ d := by
        rw [mul_pow, ← mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm 4 b,
          div_self (by positivity), one_pow, one_mul, ← pow_mul]
    _ ≤ (4 / b) ^ d * (Real.exp (b / 4 * (1 + |x|) ^ 2) * d.factorial) :=
        mul_le_mul_of_nonneg_left hfac hb4
    _ ≤ (4 / b) ^ d * ((Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2)) * d.factorial) := by
        gcongr
    _ = d.factorial * (4 / b) ^ d * Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2) := by ring

/-- A polynomial times `e^{-bx²}` is integrable against every complex exponential `e^{itx}`. -/
theorem integrable_poly_gauss_cexp {b : ℝ} (hb : 0 < b) (q : ℂ[X]) (t : ℂ) :
    Integrable (fun x : ℝ => q.eval (x : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) *
      Complex.exp (I * t * x)) := by
  set d := q.natDegree
  have hg : Integrable (fun x : ℝ =>
      Complex.exp (-(((b / 2 : ℝ)) : ℂ) * (x : ℂ) ^ 2 + (I * t) * x + 0)) :=
    integrable_cexp_quadratic (by simp; linarith) _ _
  set C := polyMass q * (d.factorial * (4 / b) ^ d * Real.exp (b / 2)) with hC
  refine (hg.norm.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((q.differentiable.continuous.comp Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.pow 2)))).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        Complex.continuous_ofReal))).aestronglyMeasurable
  · have hP := norm_eval_le_polyMass q (x : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hP
    have hpow := one_add_abs_pow_le_exp hb d x
    have hmass := polyMass_nonneg q
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    have e1 : (-(b : ℂ) * (x : ℂ) ^ 2).re = -(b * x ^ 2) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
    have e2 : (I * t * x).re = -(t.im * x) := by simp
    have e3 : (-(((b / 2 : ℝ)) : ℂ) * (x : ℂ) ^ 2 + (I * t) * x + 0).re =
        -(b / 2 * x ^ 2) - t.im * x := by
      rw [Complex.add_re, Complex.add_re, Complex.zero_re, add_zero, e2, ← Complex.ofReal_pow,
        ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    rw [e1, e2, e3]
    have hE : Real.exp (-(b * x ^ 2)) = Real.exp (-(b / 2 * x ^ 2)) * Real.exp (-(b / 2 * x ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    have hkey : polyMass q * (1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2)) ≤ C := by
      have h1 : (1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2)) ≤
          d.factorial * (4 / b) ^ d * Real.exp (b / 2) := by
        have he := Real.exp_pos (b / 2 * x ^ 2)
        calc (1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2))
            ≤ (d.factorial * (4 / b) ^ d * Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2)) *
                Real.exp (-(b / 2 * x ^ 2)) :=
              mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ = d.factorial * (4 / b) ^ d * Real.exp (b / 2) := by
              rw [mul_assoc, ← Real.exp_add]; simp
      calc polyMass q * (1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2))
          = polyMass q * ((1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2))) := by ring
        _ ≤ C := mul_le_mul_of_nonneg_left h1 hmass
    calc ‖q.eval (x : ℂ)‖ * Real.exp (-(b * x ^ 2)) * Real.exp (-(t.im * x))
        ≤ (polyMass q * (1 + |x|) ^ d) * Real.exp (-(b * x ^ 2)) * Real.exp (-(t.im * x)) := by
          gcongr
      _ = (polyMass q * (1 + |x|) ^ d * Real.exp (-(b / 2 * x ^ 2))) *
            Real.exp (-(b / 2 * x ^ 2) - t.im * x) := by
          rw [hE, sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ C * Real.exp (-(b / 2 * x ^ 2) - t.im * x) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

theorem integrable_gaussDeriv_mul_cexp {b : ℝ} (hb : 0 < b) (m : ℕ) (t : ℂ) :
    Integrable (fun x : ℝ => gaussDeriv b m x * Complex.exp (I * t * x)) :=
  integrable_poly_gauss_cexp hb _ t

/-! ## Integration by parts -/

theorem integral_gaussDeriv_succ_mul_cexp {b : ℝ} (hb : 0 < b) (m : ℕ) (t : ℂ) :
    ∫ x : ℝ, gaussDeriv b (m + 1) x * Complex.exp (I * t * x) =
      -(I * t) * ∫ x : ℝ, gaussDeriv b m x * Complex.exp (I * t * x) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * t * y))
      (Complex.exp (I * t * x) * (I * t)) x := by
    intro x
    have h : HasDerivAt (fun y : ℂ => I * t * y) (I * t) (x : ℂ) := by
      simpa using (hasDerivAt_id (x : ℂ)).const_mul (I * t)
    exact h.cexp.comp_ofReal
  have hint1 : Integrable ((fun y : ℝ => Complex.exp (I * t * y)) * gaussDeriv b (m + 1)) := by
    refine (integrable_gaussDeriv_mul_cexp hb (m + 1) t).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have hint2 : Integrable ((fun x : ℝ => Complex.exp (I * t * x) * (I * t)) * gaussDeriv b m) := by
    refine ((integrable_gaussDeriv_mul_cexp hb m t).mul_const (I * t)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have hint3 : Integrable ((fun y : ℝ => Complex.exp (I * t * y)) * gaussDeriv b m) := by
    refine (integrable_gaussDeriv_mul_cexp hb m t).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x)
    (fun x _ => hasDerivAt_gaussDeriv b m x) hint1 hint2 hint3
  have e1 : ∫ x : ℝ, gaussDeriv b (m + 1) x * Complex.exp (I * t * x) =
      ∫ x : ℝ, Complex.exp (I * t * x) * gaussDeriv b (m + 1) x := by
    congr 1; funext x; ring
  have e2 : ∫ x : ℝ, Complex.exp (I * t * x) * (I * t) * gaussDeriv b m x =
      (I * t) * ∫ x : ℝ, gaussDeriv b m x * Complex.exp (I * t * x) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, h, e2]
  ring

/-- `∫ ∂^m e^{-bx²} · e^{ixt} dx = (−it)^m (π/b)^{1/2} e^{-t²/(4b)}` for complex `t`. -/
theorem integral_gaussDeriv_mul_cexp {b : ℝ} (hb : 0 < b) (m : ℕ) (t : ℂ) :
    ∫ x : ℝ, gaussDeriv b m x * Complex.exp (I * t * x) =
      (-(I * t)) ^ m * ((π / (b : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (-t ^ 2 / (4 * b))) := by
  induction m with
  | zero =>
    have hb' : 0 < (b : ℂ).re := by simpa using hb
    rw [pow_zero, one_mul, ← fourierIntegral_gaussian hb' t]
    congr 1
    funext x
    simp only [gaussDeriv, gaussDerivPoly, eval_one, one_mul]
    ring
  | succ m ih =>
    rw [integral_gaussDeriv_succ_mul_cexp hb, ih]
    ring

/-! ## The physical heat test -/

/-- The physical heat test `g = (2πa)^{-1/2} Σ_k p_k (−1)^k ∂^{2k} e^{-x²/(2a)}`. -/
def heatPhysical (a : ℝ) (p : ℂ[X]) (x : ℝ) : ℂ :=
  ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
    ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (-1) ^ k * gaussDeriv (1 / (2 * a)) (2 * k) x

/-- **The heat test is the Fourier–Laplace transform of a polynomial–Gaussian.** -/
theorem integral_heatPhysical_mul_cexp {a : ℝ} (ha : 0 < a) (p : ℂ[X]) (z : ℂ) :
    ∫ x : ℝ, heatPhysical a p x * Complex.exp (I * z * x) =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) * p.eval (z ^ 2) := by
  have hb : 0 < 1 / (2 * a) := by positivity
  have hpi : (π : ℂ) / ((1 / (2 * a) : ℝ) : ℂ) = ((2 * π * a : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hA : 0 < 2 * π * a := by positivity
  have hcp : ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * ((2 * π * a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hA.ne')]
    norm_num
  have hexp : Complex.exp (-z ^ 2 / (4 * ((1 / (2 * a) : ℝ) : ℂ))) =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) := by
    congr 1
    push_cast
    field_simp
    ring
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      Integrable (fun x : ℝ => p.coeff k * (-1) ^ k * gaussDeriv (1 / (2 * a)) (2 * k) x *
        Complex.exp (I * z * x)) := fun k _ => by
    refine ((integrable_gaussDeriv_mul_cexp hb (2 * k) z).const_mul (p.coeff k * (-1) ^ k)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hsplit : (fun x : ℝ => heatPhysical a p x * Complex.exp (I * z * x)) =
      fun x => ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑ k ∈ Finset.range (p.natDegree + 1),
          p.coeff k * (-1) ^ k * gaussDeriv (1 / (2 * a)) (2 * k) x * Complex.exp (I * z * x) := by
    funext x
    rw [heatPhysical, mul_assoc, Finset.sum_mul]
  rw [hsplit, integral_const_mul, integral_finsetSum _ hterm]
  have hk : ∀ k ∈ Finset.range (p.natDegree + 1),
      ∫ x : ℝ, p.coeff k * (-1) ^ k * gaussDeriv (1 / (2 * a)) (2 * k) x *
        Complex.exp (I * z * x) =
      p.coeff k * (z ^ 2) ^ k * (((2 * π * a : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-(a : ℂ) * z ^ 2 / 2)) := fun k _ => by
    have e : (fun x : ℝ => p.coeff k * (-1) ^ k * gaussDeriv (1 / (2 * a)) (2 * k) x *
        Complex.exp (I * z * x)) = fun x => (p.coeff k * (-1) ^ k) *
          (gaussDeriv (1 / (2 * a)) (2 * k) x * Complex.exp (I * z * x)) := by
      funext x; ring
    rw [e, integral_const_mul, integral_gaussDeriv_mul_cexp hb, hpi, hexp, pow_mul]
    have : (-(I * z)) ^ 2 = -z ^ 2 := by ring_nf; rw [I_sq]; ring
    rw [this, neg_pow]
    have h11 : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    linear_combination (p.coeff k * (z ^ 2) ^ k * (((2 * π * a : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      Complex.exp (-(a : ℂ) * z ^ 2 / 2))) * h11
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul, ← mul_assoc, mul_comm _ (∑ k ∈ _, _),
    mul_assoc, ← mul_assoc (((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))), hcp, one_mul, mul_comm,
    eval_eq_sum_range]

end

end RHTower
