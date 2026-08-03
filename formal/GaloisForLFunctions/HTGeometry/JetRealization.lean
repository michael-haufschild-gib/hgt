import GaloisForLFunctions.HTGeometry.FamilyInversionJets

/-!
# Every finite jet vector is realized by a polynomial

A finite list of prescribed derivatives at a point is attained by the corresponding Taylor
polynomial.  This is the analytic replacement for a combinatorial solve: instead of inverting a
triangular jet substitution by hand, one realizes an arbitrary jet vector by an actual function and
lets the substitution be computed by the identities already proved for functions.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The Taylor polynomial with prescribed derivatives at the origin. -/
def jetPolynomial (n : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k / (k.factorial : ℂ)) * Polynomial.X ^ k

theorem coeff_jetPolynomial {n : ℕ} (c : ℕ → ℂ) {k : ℕ} (hk : k ≤ n) :
    (jetPolynomial n c).coeff k = c k / (k.factorial : ℂ) := by
  rw [jetPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hmem

/-- The `k`-th derivative of a polynomial at the origin reads off its `k`-th coefficient. -/
theorem eval_iterate_derivative_zero (p : Polynomial ℂ) (k : ℕ) :
    (Polynomial.derivative^[k] p).eval 0 = (k.factorial : ℂ) * p.coeff k := by
  have hfun : (Polynomial.derivative^[k]) p = (k.factorial • Polynomial.hasseDeriv k) p := by
    rw [Polynomial.factorial_smul_hasseDeriv]
  rw [hfun]
  have hsmul : (k.factorial • Polynomial.hasseDeriv k) p
      = (k.factorial : ℕ) • (Polynomial.hasseDeriv k p) := rfl
  rw [hsmul, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_smul,
    Polynomial.hasseDeriv_coeff]
  simp [nsmul_eq_mul]

/-- **Jet realization.**  Every finite prescription of derivatives at the origin is attained by a
polynomial. -/
theorem exists_polynomial_eval_iterate_derivative_eq (n : ℕ) (c : ℕ → ℂ) :
    ∃ p : Polynomial ℂ, ∀ k ≤ n, (Polynomial.derivative^[k] p).eval 0 = c k := by
  refine ⟨jetPolynomial n c, fun k hk => ?_⟩
  rw [eval_iterate_derivative_zero, coeff_jetPolynomial c hk]
  have hfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- **Jet realization for functions.**  Every finite prescription of derivatives at the origin is
attained by an entire function, smooth everywhere. -/
theorem exists_smooth_iteratedDeriv_zero_eq (n : ℕ) (c : ℕ → ℂ) :
    ∃ f : ℂ → ℂ, (∀ w : ℂ, ContDiffAt ℂ (⊤ : ℕ∞) f w) ∧
      ∀ k ≤ n, iteratedDeriv k f 0 = c k := by
  obtain ⟨p, hp⟩ := exists_polynomial_eval_iterate_derivative_eq n c
  refine ⟨fun w => Polynomial.eval w p, fun w => ?_, fun k hk => ?_⟩
  · have hcd : ContDiff ℂ (⊤ : ℕ∞) fun w : ℂ => Polynomial.eval w p := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (Polynomial.contDiff_aeval (𝕜 := ℂ) p ((⊤ : ℕ∞) : WithTop ℕ∞))
    exact hcd.contDiffAt
  · rw [iteratedDeriv_polynomial_eval, hp k hk]

end

end GaloisForLFunctions.HTGeometry
