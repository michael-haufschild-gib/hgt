import GaloisForLFunctions.HTGeometry.PolynomialGrowthLiouville

/-!
# Formal antiderivatives of polynomials

Over a field of characteristic zero every polynomial has a formal antiderivative.  mathlib does not
record the surjectivity of `Polynomial.derivative`, so the primitive is built here by dividing each
coefficient by its shifted exponent.

This is what turns "all derivatives above `d` vanish" into "is a polynomial": the derivative is a
polynomial by induction, its primitive is a polynomial, and the difference has zero derivative.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The formal antiderivative of a polynomial, with zero constant term. -/
noncomputable def polyAntideriv (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1)

/-- **The antiderivative differentiates back.** -/
theorem derivative_polyAntideriv (p : Polynomial ℂ) :
    Polynomial.derivative (polyAntideriv p) = p := by
  classical
  rw [polyAntideriv, map_sum]
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      Polynomial.derivative
          (Polynomial.C (p.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1))
        = Polynomial.monomial k (p.coeff k) := by
    intro k _
    have hk : ((k : ℂ) + 1) ≠ 0 := by
      have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast Nat.succ_ne_zero k
    have hcoef : p.coeff k / ((k : ℂ) + 1) * ((k + 1 : ℕ) : ℂ) = p.coeff k := by
      push_cast
      field_simp
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
      ← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, ← Polynomial.C_mul, hcoef,
      show k + 1 - 1 = k from by omega]
  rw [Finset.sum_congr rfl hterm]
  exact (Polynomial.as_sum_range' p (p.natDegree + 1) (by omega)).symm

/-- **The antiderivative as a function.** -/
theorem deriv_polyAntideriv_eval (p : Polynomial ℂ) (z : ℂ) :
    deriv (fun w => (polyAntideriv p).eval w) z = p.eval z := by
  have hd : HasDerivAt (fun w => (polyAntideriv p).eval w)
      ((Polynomial.derivative (polyAntideriv p)).eval z) z :=
    (polyAntideriv p).hasDerivAt z
  rw [hd.deriv, derivative_polyAntideriv]

/-! ## Vanishing high derivatives means polynomial -/

/-- **An entire function whose derivatives above `d` vanish is a polynomial.** -/
theorem exists_polynomial_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {d : ℕ} (h : ∀ z : ℂ, iteratedDeriv (d + 1) f z = 0) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  induction d generalizing f with
  | zero =>
      have hderiv : ∀ z : ℂ, deriv f z = 0 := by
        intro z
        have := h z
        rwa [iteratedDeriv_one] at this
      refine ⟨Polynomial.C (f 0), ?_⟩
      intro z
      rw [Polynomial.eval_C]
      exact is_const_of_deriv_eq_zero hf hderiv z 0
  | succ d ih =>
      have hana : AnalyticOnNhd ℂ f Set.univ :=
        DifferentiableOn.analyticOnNhd (fun z _ => (hf z).differentiableWithinAt) isOpen_univ
      have hdf : Differentiable ℂ (deriv f) := fun z =>
        ((hana.deriv) z (Set.mem_univ z)).differentiableAt
      have hstep : ∀ z : ℂ, iteratedDeriv (d + 1) (deriv f) z = 0 := by
        intro z
        have := h z
        rwa [iteratedDeriv_succ'] at this
      obtain ⟨q, hq⟩ := ih hdf hstep
      -- the difference with the primitive is constant
      have hdiff : Differentiable ℂ (fun w => f w - (polyAntideriv q).eval w) :=
        hf.sub (Polynomial.differentiable _)
      have hzero : ∀ z : ℂ, deriv (fun w => f w - (polyAntideriv q).eval w) z = 0 := by
        intro z
        have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
        have h2 : HasDerivAt (fun w => (polyAntideriv q).eval w)
            ((Polynomial.derivative (polyAntideriv q)).eval z) z :=
          (polyAntideriv q).hasDerivAt z
        have h3 : HasDerivAt (fun w => f w - (polyAntideriv q).eval w)
            (deriv f z - (Polynomial.derivative (polyAntideriv q)).eval z) z := h1.sub h2
        rw [h3.deriv, derivative_polyAntideriv, ← hq z]
        ring
      refine ⟨polyAntideriv q + Polynomial.C (f 0 - (polyAntideriv q).eval 0), ?_⟩
      intro z
      have hconst := is_const_of_deriv_eq_zero hdiff hzero z 0
      simp only [Polynomial.eval_add, Polynomial.eval_C]
      linear_combination hconst

/-! ## Liouville's theorem at polynomial growth, in final form -/

/-- **An entire function of polynomial growth is a polynomial.** -/
theorem exists_polynomial_of_polynomial_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} {d : ℕ} (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ M * (1 + ‖z‖) ^ d) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z :=
  exists_polynomial_of_iteratedDeriv_eq_zero hf
    (fun z => iteratedDeriv_eq_zero_of_polynomial_growth hf hgrowth (Nat.lt_succ_self d) z)

/-- **A transcendental entire function exceeds every polynomial bound.**  The contrapositive form,
which is how transcendence is used against a growth estimate. -/
theorem exists_norm_gt_of_not_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) (M : ℝ) (d : ℕ) :
    ∃ z : ℂ, M * (1 + ‖z‖) ^ d < ‖f z‖ := by
  by_contra hcon
  have hall : ∀ z : ℂ, ‖f z‖ ≤ M * (1 + ‖z‖) ^ d := by
    intro z
    by_contra hz
    exact hcon ⟨z, not_le.mp hz⟩
  exact hnp (exists_polynomial_of_polynomial_growth hf hall)

end GaloisForLFunctions.HTGeometry
