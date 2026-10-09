import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers
import GaloisForLFunctions.HTGeometry.RationalPhaseCharacterRankAperture

/-!
# Termination and resonance for the native diagonal torus derivation

The source divisibility rigidity excludes every nonzero polynomial
rescaling of a nonzero diagonal flow. The positive survivor is exact:
the terminating polynomials are precisely the resonant invariants.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {r : ℕ}

/-- The native torus frequency of a monomial exponent. -/
def paperRationalDiagonalWeight (omega : Fin r → ℝ) (s : Fin r →₀ ℕ) : ℂ :=
  ∑ i, (s i : ℂ) * (Complex.I * (omega i : ℂ))

/-- Each coefficient is multiplied by its own monomial frequency. -/
theorem paperRationalDiagonal_coeff (omega : Fin r → ℝ)
    (p : MvPolynomial (Fin r) ℂ) (s : Fin r →₀ ℕ) :
    MvPolynomial.coeff s (rationalDiagonalPolynomialDerivation omega p) =
      paperRationalDiagonalWeight omega s * MvPolynomial.coeff s p := by
  rw [rationalDiagonalPolynomialDerivation_eq_diagonalPolynomialDerivation,
    diagonalPolynomialDerivation, MvPolynomial.coeff_sum, paperRationalDiagonalWeight,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, MvPolynomial.coeff_C_mul, GaloisForLFunctions.coeff_X_mul_pderiv]
  ring

/-- Every jet has the corresponding power of the same frequency on each coefficient. -/
theorem paperRationalDiagonal_iterate_coeff (omega : Fin r → ℝ)
    (p : MvPolynomial (Fin r) ℂ) (s : Fin r →₀ ℕ) (m : ℕ) :
    MvPolynomial.coeff s ((rationalDiagonalPolynomialDerivation omega :
      MvPolynomial (Fin r) ℂ → MvPolynomial (Fin r) ℂ)^[m] p) =
      paperRationalDiagonalWeight omega s ^ m * MvPolynomial.coeff s p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', paperRationalDiagonal_coeff, ih, pow_succ]
    ring

/-- The full invariant ring consists exactly of polynomials supported on resonant monomials. -/
theorem paperRationalDiagonal_kernel_iff (omega : Fin r → ℝ)
    (p : MvPolynomial (Fin r) ℂ) :
    rationalDiagonalPolynomialDerivation omega p = 0 ↔
      ∀ s, MvPolynomial.coeff s p ≠ 0 → paperRationalDiagonalWeight omega s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (MvPolynomial.coeff s) h
    rw [paperRationalDiagonal_coeff, MvPolynomial.coeff_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hs
  · intro h
    ext s
    rw [paperRationalDiagonal_coeff, MvPolynomial.coeff_zero]
    by_cases hs : MvPolynomial.coeff s p = 0
    · rw [hs, mul_zero]
    · rw [h s hs, zero_mul]

/-- No nontrivial nilpotent jet chain exists: eventual annihilation already means invariance. -/
theorem paperRationalDiagonal_terminates_iff (omega : Fin r → ℝ)
    (p : MvPolynomial (Fin r) ℂ) :
    (∃ m, (rationalDiagonalPolynomialDerivation omega :
      MvPolynomial (Fin r) ℂ → MvPolynomial (Fin r) ℂ)^[m] p = 0) ↔
      rationalDiagonalPolynomialDerivation omega p = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    apply (paperRationalDiagonal_kernel_iff omega p).mpr
    intro s hs
    have he := congrArg (MvPolynomial.coeff s) hm
    rw [paperRationalDiagonal_iterate_coeff, MvPolynomial.coeff_zero] at he
    by_contra hw
    exact (mul_ne_zero (pow_ne_zero m hw) hs) he
  · intro h
    exact ⟨1, h⟩

/-- Source semi-invariant rigidity gives the complete polynomial-speed classification. -/
theorem paperRationalDiagonal_multiplier_iff (omega : Fin r → ℝ)
    (q : MvPolynomial (Fin r) ℂ) :
    IsLocallyNilpotent (q • rationalDiagonalPolynomialDerivation omega) ↔
      q = 0 ∨ ∀ i, omega i = 0 := by
  constructor
  · intro h
    by_cases hq : q = 0
    · exact Or.inl hq
    right
    intro i
    have hx := paperLND_fixed_of_dvd_apply
      (q • rationalDiagonalPolynomialDerivation omega) h (MvPolynomial.X i)
      ⟨q * MvPolynomial.C (Complex.I * (omega i : ℂ)), by
        simp only [Derivation.smul_apply, rationalDiagonalPolynomialDerivation_X, smul_eq_mul]
        ring⟩
    change q * rationalDiagonalPolynomialDerivation omega (MvPolynomial.X i) = 0 at hx
    rw [rationalDiagonalPolynomialDerivation_X] at hx
    have hw := (mul_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hq)).resolve_right
      (MvPolynomial.X_ne_zero i)
    have hw' : Complex.I * (omega i : ℂ) = 0 :=
      MvPolynomial.C_injective (Fin r) ℂ (hw.trans (map_zero MvPolynomial.C).symm)
    exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hw').resolve_left Complex.I_ne_zero)
  · rintro (rfl | h)
    · intro p
      exact ⟨1, by simp⟩
    · have hD : rationalDiagonalPolynomialDerivation omega = 0 := by
        apply MvPolynomial.derivation_ext
        intro i
        simp [h i]
      rw [hD, smul_zero]
      intro p
      exact ⟨1, rfl⟩

end

end GaloisForLFunctions.HTGeometry
