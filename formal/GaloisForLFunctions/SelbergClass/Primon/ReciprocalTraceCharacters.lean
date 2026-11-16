import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra

/-!
# Reciprocal-root traces under prime spectral laws

The polynomials `Pₙ(x) = 2 Tₙ(x/2)` in the character formula of
Zehavi, Theorem 4.7, arXiv:2611.18218, are differences of second-kind
characters. Under each prime Kesten law their odd means vanish, while
their positive even means are strictly negative geometric differences.
The polynomial definition also covers the interval where the two roots
of `z² - xz + 1` are nonreal.
-/

noncomputable section

open MeasureTheory Polynomial

namespace GaloisForLFunctions.SelbergClass.Primon

/-- The power-sum polynomial of a reciprocal pair, in the spectral coordinate. -/
def reciprocalTraceCharacter (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => 2 * (Chebyshev.T ℝ (n : ℤ)).eval (x / 2), by fun_prop⟩

@[simp] theorem reciprocalTraceCharacter_zero (x : ℝ) :
    reciprocalTraceCharacter 0 x = 2 := by
  simp [reciprocalTraceCharacter]

@[simp] theorem reciprocalTraceCharacter_one (x : ℝ) :
    reciprocalTraceCharacter 1 x = x := by
  simp [reciprocalTraceCharacter]
  ring

/-- Reciprocal traces obey the same quadratic recurrence as the two reciprocal roots. -/
theorem reciprocalTraceCharacter_add_two (n : ℕ) (x : ℝ) :
    reciprocalTraceCharacter (n + 2) x =
      x * reciprocalTraceCharacter (n + 1) x - reciprocalTraceCharacter n x := by
  have h := congrArg (Polynomial.eval (x / 2)) (Chebyshev.T_add_two ℝ (n : ℤ))
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at h
  simp only [reciprocalTraceCharacter, ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_ofNat]
  rw [h]
  ring

/-- The reciprocal-root trace is the difference of two adjacent same-parity characters. -/
theorem reciprocalTraceCharacter_eq_sub (n : ℕ) (x : ℝ) :
    reciprocalTraceCharacter (n + 2) x =
      spectralCharacter (n + 2) x - spectralCharacter n x := by
  have h := congrArg (Polynomial.eval (x / 2)) (Chebyshev.two_mul_T_eq_U_sub_U ℝ (n : ℤ))
  simpa only [eval_mul, eval_ofNat, eval_sub, reciprocalTraceCharacter,
    spectralCharacter, ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_ofNat] using h

/-- On the compact spectral interval the trace is a single cosine mode. -/
theorem reciprocalTraceCharacter_cos (n : ℕ) (t : ℝ) :
    reciprocalTraceCharacter n (2 * Real.cos t) = 2 * Real.cos ((n : ℝ) * t) := by
  simp only [reciprocalTraceCharacter, ContinuousMap.coe_mk,
    show 2 * Real.cos t / 2 = Real.cos t by ring, Chebyshev.T_real_cos, Int.cast_natCast]

/-- Exact geometric cancellation of every positive even trace under the prime law. -/
theorem integral_kesten_reciprocalTrace_even (p : Nat.Primes) (n : ℕ) :
    (∫ x, reciprocalTraceCharacter (2 * n + 2) x ∂(kestenSpectralLaw p : Measure ℝ)) =
      (p : ℝ)⁻¹ ^ (n + 1) - (p : ℝ)⁻¹ ^ n := by
  simp_rw [reciprocalTraceCharacter_eq_sub]
  rw [integral_sub (integrable_kestenSpectralLaw_continuous p _)
    (integrable_kestenSpectralLaw_continuous p _)]
  rw [show 2 * n + 2 = 2 * (n + 1) by omega,
    integral_kesten_spectralCharacter_even, integral_kesten_spectralCharacter_even]

/-- All odd reciprocal traces cancel under each prime law. -/
theorem integral_kesten_reciprocalTrace_odd (p : Nat.Primes) (n : ℕ) :
    (∫ x, reciprocalTraceCharacter (2 * n + 1) x ∂(kestenSpectralLaw p : Measure ℝ)) = 0 := by
  cases n with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, reciprocalTraceCharacter_one,
      spectralCharacter_one] using integral_kesten_spectralCharacter_odd p 0
  | succ n =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    simp_rw [reciprocalTraceCharacter_eq_sub]
    rw [integral_sub (integrable_kestenSpectralLaw_continuous p _)
      (integrable_kestenSpectralLaw_continuous p _)]
    rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega,
      integral_kesten_spectralCharacter_odd, integral_kesten_spectralCharacter_odd, sub_self]

/-- A positive prime spectral measure can have strictly negative reciprocal trace means. -/
theorem integral_kesten_reciprocalTrace_even_neg (p : Nat.Primes) (n : ℕ) :
    (∫ x, reciprocalTraceCharacter (2 * n + 2) x ∂(kestenSpectralLaw p : Measure ℝ)) < 0 := by
  rw [integral_kesten_reciprocalTrace_even, pow_succ, sub_lt_zero]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hp)).mpr hp
  exact mul_lt_of_lt_one_right (pow_pos (inv_pos.mpr (lt_trans zero_lt_one hp)) n) hi

/-- The prime Favard polynomial separates into a reciprocal trace and a positive correction. -/
theorem kestenPolynomial_eq_reciprocalTrace (p : Nat.Primes) (n : ℕ) (x : ℝ) :
    (kestenPolynomial p (n + 2)).eval x =
      reciprocalTraceCharacter (n + 2) x + (1 - (p : ℝ)⁻¹) * spectralCharacter n x := by
  rw [kestenPolynomial_eval_spectral, reciprocalTraceCharacter_eq_sub]
  ring

/-- Same-parity reciprocal traces have the discrete-Laplacian Gram matrix. -/
theorem integral_semicircle_reciprocalTrace_mul (n m : ℕ) :
    (∫ x, reciprocalTraceCharacter (n + 2) x * reciprocalTraceCharacter (m + 2) x
      ∂(semicircleSpectralLaw : Measure ℝ)) =
      (if n = m then 2 else 0) - (if n + 2 = m then 1 else 0) -
        (if n = m + 2 then 1 else 0) := by
  have hi (a b : ℕ) : Integrable (fun x => spectralCharacter a x * spectralCharacter b x)
      (semicircleSpectralLaw : Measure ℝ) :=
    integrable_semicircleSpectralLaw_continuous (spectralCharacter a * spectralCharacter b)
  simp_rw [reciprocalTraceCharacter_eq_sub, sub_mul, mul_sub]
  have hsplit := integral_sub ((hi (n + 2) (m + 2)).sub (hi (n + 2) m))
    ((hi n (m + 2)).sub (hi n m))
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,
    integral_sub (hi (n + 2) (m + 2)) (hi (n + 2) m),
    integral_sub (hi n (m + 2)) (hi n m)]
  rw [integral_spectralCharacter_mul, integral_spectralCharacter_mul,
    integral_spectralCharacter_mul, integral_spectralCharacter_mul]
  simp only [Nat.add_right_cancel_iff]
  split_ifs <;> ring

/-- The derivative used in the Casimir calculation is a second-kind character,
including the spectral endpoints where a square-root formula is singular. -/
theorem hasDerivAt_reciprocalTraceCharacter (n : ℕ) (x : ℝ) :
    HasDerivAt (reciprocalTraceCharacter (n + 1))
      (((n : ℝ) + 1) * spectralCharacter n x) x := by
  have h := (((Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).hasDerivAt (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).const_mul 2
  have hd : 2 * ((Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).derivative.eval (x / 2) * (1 / 2)) =
      ((n : ℝ) + 1) * spectralCharacter n x := by
    simp [Chebyshev.T_derivative_eq_U, spectralCharacter] <;> ring
  rw [hd] at h
  exact h

theorem deriv_reciprocalTraceCharacter (n : ℕ) (x : ℝ) :
    deriv (reciprocalTraceCharacter (n + 1)) x =
      ((n : ℝ) + 1) * spectralCharacter n x :=
  (hasDerivAt_reciprocalTraceCharacter n x).deriv

/-- At the repeated-root endpoint the derivative is the square of the degree. -/
theorem deriv_reciprocalTraceCharacter_two (n : ℕ) :
    deriv (reciprocalTraceCharacter (n + 1)) 2 = ((n : ℝ) + 1) ^ 2 := by
  rw [deriv_reciprocalTraceCharacter]
  simp only [spectralCharacter, ContinuousMap.coe_mk, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Chebyshev.U_eval_one, Int.cast_natCast]
  ring

/-- Differentiation turns reciprocal traces into an orthogonal family under the semicircle law. -/
theorem integral_semicircle_reciprocalTrace_deriv_mul (n m : ℕ) :
    (∫ x, deriv (reciprocalTraceCharacter (n + 1)) x *
      deriv (reciprocalTraceCharacter (m + 1)) x
      ∂(semicircleSpectralLaw : Measure ℝ)) =
      if n = m then ((n : ℝ) + 1) ^ 2 else 0 := by
  simp_rw [deriv_reciprocalTraceCharacter]
  have he (x : ℝ) :
      (((n : ℝ) + 1) * spectralCharacter n x) *
        (((m : ℝ) + 1) * spectralCharacter m x) =
      (((n : ℝ) + 1) * ((m : ℝ) + 1)) *
        (spectralCharacter n x * spectralCharacter m x) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_spectralCharacter_mul]
  split_ifs with h
  · subst m
    ring
  · exact mul_zero _

/-- Odd-degree trace derivatives have positive geometric prime means. -/
theorem integral_kesten_reciprocalTrace_deriv_odd (p : Nat.Primes) (n : ℕ) :
    (∫ x, deriv (reciprocalTraceCharacter (2 * n + 1)) x
      ∂(kestenSpectralLaw p : Measure ℝ)) =
      (2 * (n : ℝ) + 1) * (p : ℝ)⁻¹ ^ n := by
  simp_rw [deriv_reciprocalTraceCharacter]
  rw [integral_const_mul, integral_kesten_spectralCharacter_even]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- Even-degree trace derivatives have zero prime mean. -/
theorem integral_kesten_reciprocalTrace_deriv_even (p : Nat.Primes) (n : ℕ) :
    (∫ x, deriv (reciprocalTraceCharacter (2 * n + 2)) x
      ∂(kestenSpectralLaw p : Measure ℝ)) = 0 := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp_rw [deriv_reciprocalTraceCharacter]
  rw [integral_const_mul, integral_kesten_spectralCharacter_odd, mul_zero]

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.reciprocalTraceCharacter_eq_sub
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kesten_reciprocalTrace_even
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kesten_reciprocalTrace_odd
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kesten_reciprocalTrace_even_neg
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenPolynomial_eq_reciprocalTrace
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_semicircle_reciprocalTrace_mul
#print axioms GaloisForLFunctions.SelbergClass.Primon.deriv_reciprocalTraceCharacter_two
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_semicircle_reciprocalTrace_deriv_mul
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kesten_reciprocalTrace_deriv_odd
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kesten_reciprocalTrace_deriv_even
