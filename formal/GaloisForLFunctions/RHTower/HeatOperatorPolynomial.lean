import GaloisForLFunctions.RHTower.GaussianMomentFourier

/-!
# The Gaussian heat operator on polynomials

Completing the Gaussian square in the transform of `R(ix)e^{-tx²}` produces the finite operator

`e^{-(4t)^{-1}∂_u²}R = ∑_j ((-1/(4t))^j / j!) R^{(2j)}`,

evaluated at `u = ξ/(2t)`.  The operator is characterized by the commutator

`H(Xp) = X H(p) - (H p)'/(2t)`,

which is the recursion defining the rescaled Hermite polynomials `A_n`; and `A_n` in turn is the
jet polynomial of the Gaussian in the rescaled variable, `q_n(ξ) = (-1)^n A_n(ξ/(2t))`.  Combining
these with the moment formula gives the exact Fourier factorization.
-/

open Polynomial

namespace RHTower

noncomputable section

/-! ## The rescaled Hermite polynomials -/

/-- The rescaled Hermite polynomials `A_0 = 1`, `A_{n+1} = X A_n - A_n'/(2t)`. -/
noncomputable def heatShiftPoly (t : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | (n + 1) => Polynomial.X * heatShiftPoly t n
      - Polynomial.C (1 / (2 * t)) * (heatShiftPoly t n).derivative

@[simp]
theorem heatShiftPoly_zero (t : ℝ) : heatShiftPoly t 0 = 1 := rfl

theorem heatShiftPoly_succ (t : ℝ) (n : ℕ) :
    heatShiftPoly t (n + 1) = Polynomial.X * heatShiftPoly t n
      - Polynomial.C (1 / (2 * t)) * (heatShiftPoly t n).derivative := rfl

/-- The rescaling substitution `u = ξ/(2t)`. -/
noncomputable def heatScale (t : ℝ) : Polynomial ℝ := Polynomial.C (1 / (2 * t)) * Polynomial.X

theorem derivative_heatScale (t : ℝ) :
    (heatScale t).derivative = Polynomial.C (1 / (2 * t)) := by
  rw [heatScale, Polynomial.derivative_mul]
  simp

theorem eval_heatScale (t ξ : ℝ) : (heatScale t).eval ξ = ξ / (2 * t) := by
  rw [heatScale]
  simp [div_eq_inv_mul, mul_comm]

/-- **The Gaussian jet polynomial is the rescaled Hermite polynomial in `ξ/(2t)`.** -/
theorem gaussJetPoly_eq_heatShift (t : ℝ) : ∀ n : ℕ,
    gaussJetPoly t n = (-1 : ℝ) ^ n • (heatShiftPoly t n).comp (heatScale t)
  | 0 => by simp [gaussJetPoly, heatShiftPoly]
  | (n + 1) => by
    have ih := gaussJetPoly_eq_heatShift t n
    have hBd : ((heatShiftPoly t n).comp (heatScale t)).derivative
        = Polynomial.C (1 / (2 * t)) * ((heatShiftPoly t n).derivative.comp (heatScale t)) := by
      rw [Polynomial.derivative_comp, derivative_heatScale]
    have hBs : (heatShiftPoly t (n + 1)).comp (heatScale t)
        = Polynomial.C (1 / (2 * t)) * Polynomial.X * ((heatShiftPoly t n).comp (heatScale t))
          - ((heatShiftPoly t n).comp (heatScale t)).derivative := by
      rw [heatShiftPoly_succ, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.mul_comp,
        Polynomial.X_comp, Polynomial.C_comp, hBd, heatScale]
    rw [gaussJetPoly_succ, ih, hBs, Polynomial.derivative_smul, mul_smul_comm, pow_succ,
      mul_neg_one, neg_smul, smul_sub, neg_sub]

/-- The evaluation form of the rescaling. -/
theorem gaussJetPoly_eval_eq (t ξ : ℝ) (n : ℕ) :
    (gaussJetPoly t n).eval ξ = (-1 : ℝ) ^ n * (heatShiftPoly t n).eval (ξ / (2 * t)) := by
  rw [gaussJetPoly_eq_heatShift t n, Polynomial.eval_smul, Polynomial.eval_comp, eval_heatScale,
    smul_eq_mul]

/-! ## The iterated Leibniz rule for multiplication by `X` -/

theorem iterate_derivative_X_mul_succ (p : Polynomial ℝ) : ∀ k : ℕ,
    Polynomial.derivative^[k + 1] (Polynomial.X * p)
      = Polynomial.X * Polynomial.derivative^[k + 1] p
        + Polynomial.C ((k : ℝ) + 1) * Polynomial.derivative^[k] p
  | 0 => by
    simp only [zero_add, Function.iterate_one, Polynomial.derivative_mul, Polynomial.derivative_X,
      one_mul, Function.iterate_zero, id_eq, Nat.cast_zero, Polynomial.C_1]
    abel
  | (k + 1) => by
    have ih := iterate_derivative_X_mul_succ p k
    show Polynomial.derivative^[k + 2] (Polynomial.X * p)
        = Polynomial.X * Polynomial.derivative^[k + 2] p
          + Polynomial.C (((k + 1 : ℕ) : ℝ) + 1) * Polynomial.derivative^[k + 1] p
    have hL : Polynomial.derivative^[k + 2] (Polynomial.X * p)
        = Polynomial.derivative (Polynomial.derivative^[k + 1] (Polynomial.X * p)) :=
      Function.iterate_succ_apply' Polynomial.derivative (k + 1) _
    have hR1 : Polynomial.derivative (Polynomial.derivative^[k + 1] p)
        = Polynomial.derivative^[k + 2] p :=
      (Function.iterate_succ_apply' Polynomial.derivative (k + 1) p).symm
    have hR2 : Polynomial.derivative (Polynomial.derivative^[k] p)
        = Polynomial.derivative^[k + 1] p :=
      (Function.iterate_succ_apply' Polynomial.derivative k p).symm
    rw [hL, ih, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_mul,
      Polynomial.derivative_X, Polynomial.derivative_C, one_mul, zero_mul, zero_add, hR1, hR2]
    push_cast
    simp only [Polynomial.C_add, Polynomial.C_1]
    ring

theorem iterate_derivative_X_mul (p : Polynomial ℝ) (k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.X * p)
      = Polynomial.X * Polynomial.derivative^[k] p
        + Polynomial.C ((k : ℝ)) * Polynomial.derivative^[k - 1] p := by
  cases k with
  | zero => simp
  | succ k =>
    rw [iterate_derivative_X_mul_succ p k]
    push_cast
    simp

/-! ## The truncated heat operator -/

/-- The heat operator `∑_{j≤m} ((-1/(4t))^j/j!) R^{(2j)}`, truncated at order `m`. -/
noncomputable def heatOpTo (t : ℝ) (m : ℕ) (R : Polynomial ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
      * Polynomial.derivative^[2 * j] R

theorem heatOpTo_sum {ι : Type*} (t : ℝ) (m : ℕ) (s : Finset ι) (f : ι → Polynomial ℝ) :
    heatOpTo t m (∑ i ∈ s, f i) = ∑ i ∈ s, heatOpTo t m (f i) := by
  simp only [heatOpTo, Polynomial.iterate_derivative_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem heatOpTo_C_mul (t : ℝ) (m : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    heatOpTo t m (Polynomial.C a * p) = Polynomial.C a * heatOpTo t m p := by
  simp only [heatOpTo, Polynomial.iterate_derivative_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem heatOpTo_one (t : ℝ) (m : ℕ) : heatOpTo t m 1 = 1 := by
  rw [heatOpTo]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    have h2j : (1 : Polynomial ℝ).natDegree < 2 * j := by
      simp only [Polynomial.natDegree_one]
      omega
    rw [Polynomial.iterate_derivative_eq_zero h2j, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) h

theorem derivative_heatOpTo (t : ℝ) (m : ℕ) (p : Polynomial ℝ) :
    (heatOpTo t m p).derivative
      = ∑ j ∈ Finset.range (m + 1),
          Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
            * Polynomial.derivative^[2 * j + 1] p := by
  rw [heatOpTo, Polynomial.derivative_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.derivative_C_mul, ← Function.iterate_succ_apply' Polynomial.derivative (2 * j)]

/-- **The commutator law.**  On polynomials of degree at most the truncation order the heat
operator satisfies `H(Xp) = X H(p) - (Hp)'/(2t)`. -/
theorem heatOpTo_X_mul {t : ℝ} {m : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ m) :
    heatOpTo t m (Polynomial.X * p)
      = Polynomial.X * heatOpTo t m p
        - Polynomial.C (1 / (2 * t)) * (heatOpTo t m p).derivative := by
  have hsplit : heatOpTo t m (Polynomial.X * p)
      = (∑ j ∈ Finset.range (m + 1),
          Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
            * (Polynomial.X * Polynomial.derivative^[2 * j] p))
        + ∑ j ∈ Finset.range (m + 1),
          Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
            * (Polynomial.C ((2 * j : ℕ) : ℝ) * Polynomial.derivative^[2 * j - 1] p) := by
    rw [heatOpTo, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iterate_derivative_X_mul p (2 * j), mul_add]
  have hfirst : (∑ j ∈ Finset.range (m + 1),
      Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
        * (Polynomial.X * Polynomial.derivative^[2 * j] p))
      = Polynomial.X * heatOpTo t m p := by
    rw [heatOpTo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hshift : (∑ j ∈ Finset.range (m + 1),
      Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
        * (Polynomial.C ((2 * j : ℕ) : ℝ) * Polynomial.derivative^[2 * j - 1] p))
      = ∑ j ∈ Finset.range m,
          Polynomial.C (-1 / (2 * t)) * (Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
            * Polynomial.derivative^[2 * j + 1] p) := by
    rw [Finset.sum_range_succ']
    have hzero : Polynomial.C ((-1 / (4 * t)) ^ (0 : ℕ) / (Nat.factorial 0 : ℝ))
        * (Polynomial.C ((2 * 0 : ℕ) : ℝ) * Polynomial.derivative^[2 * 0 - 1] p) = 0 := by
      simp
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hidx : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [hidx]
    rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 2
    have hfac : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    rw [hfac]
    push_cast
    field_simp
    ring
  have htail : (∑ j ∈ Finset.range (m + 1),
      Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
        * Polynomial.derivative^[2 * j + 1] p)
      = ∑ j ∈ Finset.range m,
          Polynomial.C ((-1 / (4 * t)) ^ j / (Nat.factorial j : ℝ))
            * Polynomial.derivative^[2 * j + 1] p := by
    rw [Finset.sum_range_succ]
    have hdeg : p.natDegree < 2 * m + 1 := by omega
    rw [Polynomial.iterate_derivative_eq_zero hdeg, mul_zero, add_zero]
  have hCneg : Polynomial.C (-1 / (2 * t)) = -Polynomial.C (1 / (2 * t)) := by
    rw [← Polynomial.C_neg]
    congr 1
    ring
  rw [hsplit, hfirst, hshift, ← Finset.mul_sum, ← htail, derivative_heatOpTo, hCneg]
  ring

/-! ## The heat operator on monomials -/

theorem heatOpTo_X_pow (t : ℝ) {m : ℕ} : ∀ n : ℕ, n ≤ m →
    heatOpTo t m ((Polynomial.X : Polynomial ℝ) ^ n) = heatShiftPoly t n
  | 0, _ => by simpa using heatOpTo_one t m
  | (n + 1), hn => by
    have hle : n ≤ m := by omega
    have ih := heatOpTo_X_pow t n hle
    have hdeg : ((Polynomial.X : Polynomial ℝ) ^ n).natDegree ≤ m := by
      rw [Polynomial.natDegree_X_pow]
      exact hle
    have hstep : ((Polynomial.X : Polynomial ℝ) ^ (n + 1)) = Polynomial.X * Polynomial.X ^ n := by
      ring
    rw [hstep, heatOpTo_X_mul hdeg, ih, heatShiftPoly_succ]

/-- **The heat operator in the Hermite basis.** -/
theorem heatOpTo_eq_sum {t : ℝ} {m : ℕ} {R : Polynomial ℝ} (hR : R.natDegree ≤ m) :
    heatOpTo t m R
      = ∑ n ∈ Finset.range (R.natDegree + 1),
          Polynomial.C (R.coeff n) * heatShiftPoly t n := by
  conv_lhs => rw [R.as_sum_range_C_mul_X_pow]
  rw [heatOpTo_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [heatOpTo_C_mul, heatOpTo_X_pow t n (by omega)]

/-- The heat operator `e^{-(4t)^{-1}∂_u²}` applied to a polynomial. -/
noncomputable def heatOp (t : ℝ) (R : Polynomial ℝ) : Polynomial ℝ := heatOpTo t R.natDegree R

theorem heatOp_eq_sum (t : ℝ) (R : Polynomial ℝ) :
    heatOp t R
      = ∑ n ∈ Finset.range (R.natDegree + 1),
          Polynomial.C (R.coeff n) * heatShiftPoly t n :=
  heatOpTo_eq_sum (le_refl _)

/-! ## The Gaussian heat factorization -/

/-- **(24.189) The exact Gaussian heat factorization.**  For a real polynomial `R` and `t > 0`,

`∫ R(ix) e^{-tx²} e^{-iξx} dx = √(π/t) e^{-ξ²/(4t)} · [e^{-(4t)^{-1}∂_u²}R](ξ/(2t))`.

Applied to `R(u) = Q(-u²)²`, whose value at `u = ix` is `Q(x²)²`, this is the transform of
`Q(x²)²e^{-tx²}`. -/
theorem gaussHeatFourier {t : ℝ} (ht : 0 < t) (R : Polynomial ℝ) (ξ : ℝ) :
    (∫ x : ℝ, (Polynomial.aeval (Complex.I * (x : ℂ)) R) * gaussPhase t ξ x)
      = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
        * (((heatOp t R).eval (ξ / (2 * t)) : ℝ) : ℂ) := by
  have hone : ∀ n : ℕ, Complex.I ^ n * ((-1 : ℂ) ^ n * Complex.I ^ n) = 1 := by
    intro n
    have h2 : Complex.I ^ n * Complex.I ^ n = (-1 : ℂ) ^ n := by
      rw [← pow_add, ← two_mul, pow_mul, Complex.I_sq]
    calc Complex.I ^ n * ((-1 : ℂ) ^ n * Complex.I ^ n)
        = Complex.I ^ n * Complex.I ^ n * (-1 : ℂ) ^ n := by ring
      _ = (-1 : ℂ) ^ n * (-1 : ℂ) ^ n := by rw [h2]
      _ = ((-1 : ℂ) * (-1 : ℂ)) ^ n := by rw [mul_pow]
      _ = 1 := by norm_num
  have hsplit : ∀ x : ℝ, (Polynomial.aeval (Complex.I * (x : ℂ)) R) * gaussPhase t ξ x
      = ∑ n ∈ Finset.range (R.natDegree + 1),
          (((R.coeff n : ℝ) : ℂ) * Complex.I ^ n) * ((x : ℂ) ^ n * gaussPhase t ξ x) := by
    intro x
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.real_smul, mul_pow]
    ring
  have hEval : ((heatOp t R).eval (ξ / (2 * t)) : ℝ)
      = ∑ n ∈ Finset.range (R.natDegree + 1),
          R.coeff n * (heatShiftPoly t n).eval (ξ / (2 * t)) := by
    rw [heatOp_eq_sum, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun n _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]
  calc (∫ x : ℝ, (Polynomial.aeval (Complex.I * (x : ℂ)) R) * gaussPhase t ξ x)
      = ∫ x : ℝ, ∑ n ∈ Finset.range (R.natDegree + 1),
          (((R.coeff n : ℝ) : ℂ) * Complex.I ^ n) * ((x : ℂ) ^ n * gaussPhase t ξ x) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = ∑ n ∈ Finset.range (R.natDegree + 1),
          ∫ x : ℝ, (((R.coeff n : ℝ) : ℂ) * Complex.I ^ n) * ((x : ℂ) ^ n * gaussPhase t ξ x) :=
        MeasureTheory.integral_finsetSum _
          (fun n _ => (integrable_gaussMomentIntegrand ht n ξ).const_mul _)
    _ = ∑ n ∈ Finset.range (R.natDegree + 1),
          (((R.coeff n : ℝ) : ℂ) * Complex.I ^ n) * gaussMoment t n ξ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [gaussMoment, MeasureTheory.integral_const_mul]
    _ = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
          * (((heatOp t R).eval (ξ / (2 * t)) : ℝ) : ℂ) := by
        rw [hEval]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [gaussMoment_eq ht n ξ, gaussJetPoly_eval_eq]
        push_cast
        linear_combination (((R.coeff n : ℝ) : ℂ) * (Real.sqrt (Real.pi / t) : ℂ)
          * (((heatShiftPoly t n).eval (ξ / (2 * t)) : ℝ) : ℂ)
          * ((gaussKernel t ξ : ℝ) : ℂ)) * hone n

/-- The polynomial `R(u) = Q(-u²)²` takes the value `Q(x²)²` at `u = ix`. -/
theorem aeval_I_mul_sqComp (Q : Polynomial ℝ) (x : ℝ) :
    Polynomial.aeval (Complex.I * (x : ℂ)) ((Q.comp (-Polynomial.X ^ (2 : ℕ))) ^ (2 : ℕ))
      = (((Q.eval (x ^ (2 : ℕ))) ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hz : Polynomial.aeval (Complex.I * (x : ℂ)) (-Polynomial.X ^ (2 : ℕ) : Polynomial ℝ)
      = ((x ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [map_neg, map_pow, Polynomial.aeval_X]
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have hQ : Polynomial.aeval (((x ^ (2 : ℕ) : ℝ) : ℂ)) Q = ((Q.eval (x ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [show (((x ^ (2 : ℕ) : ℝ)) : ℂ) = algebraMap ℝ ℂ (x ^ (2 : ℕ)) from rfl,
      Polynomial.aeval_algebraMap_apply]
    simp
  rw [map_pow, Polynomial.aeval_comp, hz, hQ]
  push_cast
  ring

/-- **(24.189) in the form used for the shell filter.**  The transform of `Q(x²)²e^{-tx²}` is the
Gaussian times the heat operator applied to `R(u) = Q(-u²)²` at `u = ξ/(2t)`. -/
theorem gaussHeatFourier_sq {t : ℝ} (ht : 0 < t) (Q : Polynomial ℝ) (ξ : ℝ) :
    (∫ x : ℝ, (((Q.eval (x ^ (2 : ℕ))) ^ (2 : ℕ) : ℝ) : ℂ) * gaussPhase t ξ x)
      = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
        * (((heatOp t ((Q.comp (-Polynomial.X ^ (2 : ℕ))) ^ (2 : ℕ))).eval (ξ / (2 * t)) : ℝ) : ℂ) := by
  rw [← gaussHeatFourier ht ((Q.comp (-Polynomial.X ^ (2 : ℕ))) ^ (2 : ℕ)) ξ]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [aeval_I_mul_sqComp]

end

end RHTower
