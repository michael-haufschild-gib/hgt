import GaloisForLFunctions.SelbergClass.Primon.KestenMcKay

/-!
# Kesten–McKay moments of symmetric-power characters

The cosine moments in Hartnoll–Yang, arXiv:2502.02661v2, (111), determine the
averages of the second-kind Chebyshev characters. Odd characters vanish and
the character of degree `2m` has mean `p⁻ᵐ`. This is the exact finite-prime
correction to the vanishing nonconstant Sato–Tate character moments.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Symmetric-power character evaluated at phase `πt`. -/
def phaseCharacter (n : ℕ) (t : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (Real.pi * t))

@[simp] theorem phaseCharacter_zero (t : ℝ) : phaseCharacter 0 t = 1 := by
  simp [phaseCharacter]

@[simp] theorem phaseCharacter_one (t : ℝ) :
    phaseCharacter 1 t = 2 * Real.cos (Real.pi * t) := by
  simp [phaseCharacter]

theorem continuous_phaseCharacter (n : ℕ) : Continuous (phaseCharacter n) := by
  unfold phaseCharacter
  fun_prop

/-- Adding two to the character degree introduces exactly one cosine mode. -/
theorem phaseCharacter_add_two (n : ℕ) (t : ℝ) :
    phaseCharacter (n + 2) t =
      2 * Real.cos (((n : ℝ) + 2) * (Real.pi * t)) + phaseCharacter n t := by
  simp only [phaseCharacter, Nat.cast_add, Nat.cast_ofNat,
    Polynomial.Chebyshev.U_eq_two_mul_T_add_U, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.Chebyshev.T_real_cos,
    Int.cast_add, Int.cast_natCast, Int.cast_ofNat]

/-- Mean of the symmetric-power character under the explicit prime phase density. -/
def phaseCharacterAverage (p : Nat.Primes) (n : ℕ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseCharacter n t

private theorem average_add_two (p : Nat.Primes) (n : ℕ) :
    phaseCharacterAverage p (n + 2) =
      2 * (∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * Real.cos (((n : ℝ) + 2) * (Real.pi * t))) +
      phaseCharacterAverage p n := by
  have hi : IntegrableOn (fun t : ℝ => 2 *
      (kestenMcKayDensity p t * Real.cos (((n : ℝ) + 2) * (Real.pi * t)))) (Ioo 0 1) :=
    (continuous_const.mul ((continuous_kestenMcKayDensity p).mul
      (by fun_prop))).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hj : IntegrableOn (fun t => kestenMcKayDensity p t * phaseCharacter n t) (Ioo 0 1) :=
    ((continuous_kestenMcKayDensity p).mul (continuous_phaseCharacter n)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have he : (fun t => kestenMcKayDensity p t * phaseCharacter (n + 2) t) =
      fun t => 2 * (kestenMcKayDensity p t * Real.cos (((n : ℝ) + 2) * (Real.pi * t))) +
        kestenMcKayDensity p t * phaseCharacter n t := by
    funext t
    rw [phaseCharacter_add_two]
    ring
  unfold phaseCharacterAverage
  rw [he, integral_add hi hj, integral_const_mul]

/-- Every even symmetric-power character has the nonzero prime correction `p⁻ᵐ`. -/
theorem phaseCharacterAverage_even (p : Nat.Primes) (m : ℕ) :
    phaseCharacterAverage p (2 * m) = ((p : ℝ)⁻¹) ^ m := by
  induction m with
  | zero => simp [phaseCharacterAverage, integral_kestenMcKayDensity]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, average_add_two, ih]
    have ha : ∀ t : ℝ,
        Real.cos ((((2 * m : ℕ) : ℝ) + 2) * (Real.pi * t)) =
          Real.cos (2 * Real.pi * ((m : ℝ) + 1) * t) := by
      intro t
      congr 1
      push_cast
      ring
    simp_rw [ha]
    rw [integral_kestenMcKayDensity_cos_succ]
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    simp only [pow_succ, inv_pow]
    field_simp [hp]
    ring

/-- Every odd symmetric-power character has zero prime phase average. -/
theorem phaseCharacterAverage_odd (p : Nat.Primes) (m : ℕ) :
    phaseCharacterAverage p (2 * m + 1) = 0 := by
  induction m with
  | zero =>
    have hc : (∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * Real.cos (Real.pi * t)) = 0 := by
      simpa using integral_kestenMcKayDensity_cos_odd p 0
    have he : (fun t => kestenMcKayDensity p t * phaseCharacter 1 t) =
        fun t => 2 * (kestenMcKayDensity p t * Real.cos (Real.pi * t)) := by
      funext t
      rw [phaseCharacter_one]
      ring
    change (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseCharacter 1 t) = 0
    rw [he, integral_const_mul, hc, mul_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, average_add_two, ih]
    have ha : ∀ t : ℝ,
        Real.cos ((((2 * m + 1 : ℕ) : ℝ) + 2) * (Real.pi * t)) =
          Real.cos (Real.pi * (2 * ((m + 1 : ℕ) : ℝ) + 1) * t) := by
      intro t
      congr 1
      push_cast
      ring
    simp_rw [ha]
    rw [integral_kestenMcKayDensity_cos_odd]
    ring

end
end GaloisForLFunctions.SelbergClass.Primon
