import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorArc

/-!
# Actual finite Fock automorphisms beyond the Taylor gauge

At every jet dimension at least three, the clock symmetry 1+D² is invertible but
is not a Taylor translation. It fixes the constant jet and has unit augmentation,
so neither of those two extra requirements reduces the full automorphism group
to the existing one-parameter gauge representation.

This is a finite concrete instance of the symmetry-versus-supplied-structure
comparison discussed in arXiv:2607.24901; no categorical reconstruction claim is
assumed.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The higher-order clock shear is a literal polynomial in the existing derivative. -/
def gomesFiniteFockQuadraticShear (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  gomesFiniteFockPolynomialHom N (1 + X ^ 2)

/-- The quadratic shear is precisely one plus the square of the actual clock. -/
theorem gomesFiniteFockQuadraticShear_eq (N : ℕ) :
    gomesFiniteFockQuadraticShear N = 1 + fockShiftMatrix N ^ 2 := by
  rw [gomesFiniteFockQuadraticShear, map_add, map_one, map_pow, gomesFiniteFockPolynomialHom_X]

/-- The higher-order shear commutes with the actual clock at every dimension. -/
theorem gomesFiniteFockQuadraticShear_commutes (N : ℕ) :
    Commute (gomesFiniteFockQuadraticShear N) (fockShiftMatrix N) :=
  (gomesFiniteFockCommutant_mem_iff _ _).mp (gomesFiniteFockPolynomialHom_mem N _)

/-- Every positive-dimensional quadratic clock shear is an automorphism. -/
theorem gomesFiniteFockQuadraticShear_isUnit (n : ℕ) :
    IsUnit (gomesFiniteFockQuadraticShear (n + 1)) := by
  apply (gomesFiniteFockPolynomialHom_isUnit_iff n _).mpr
  simp

/-- Every scalar jet is fixed by the quadratic shear. -/
theorem gomesFiniteFockQuadraticShear_constant (n : ℕ) (a : ℂ) :
    gomesFiniteFockQuadraticShear (n + 1) *ᵥ (a • coordVec 0) = a • coordVec 0 := by
  rw [gomesFiniteFockQuadraticShear_eq, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_smul, pow_two, ← Matrix.mulVec_mulVec,
    fockShiftMatrix_mulVec_constant, Matrix.mulVec_zero, smul_zero, add_zero]

/-- From the third jet onward, this explicit automorphism lies outside the entire Taylor family. -/
theorem gomesFiniteFockQuadraticShear_ne_taylor (n : ℕ) (z : ℂ) :
    gomesFiniteFockQuadraticShear (n + 3) ≠ fockTaylorMatrix (n + 3) z := by
  intro h
  rw [gomesFiniteFockQuadraticShear, ← gomesFiniteFockTaylorSymbol_matrix] at h
  have hc := (gomesFiniteFockPolynomialHom_eq_iff (n + 3) _ _).mp h
  let j1 : Fin (n + 3) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ (n + 1))⟩
  let j2 : Fin (n + 3) := ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ n))⟩
  have h1 := hc j1
  have h2 := hc j2
  rw [gomesFiniteFockTaylorSymbol, gomesFiniteFockCoefficientPolynomial_coeff] at h1 h2
  have hz : z = 0 := by
    simpa [j1, Polynomial.coeff_one] using h1.symm
  simp [j2, hz, Polynomial.coeff_one] at h2

/-- An actual invertible clock symmetry fixes constants yet escapes every existing Taylor gauge value. -/
theorem gomesFiniteFock_missing_taylor_automorphism (n : ℕ) :
    ∃ U : (Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)ˣ,
      Commute U.val (fockShiftMatrix (n + 3)) ∧
      (∀ a : ℂ, U.val *ᵥ (a • coordVec 0) = a • coordVec 0) ∧
      ∀ z : ℂ, U.val ≠ fockTaylorMatrix (n + 3) z := by
  obtain ⟨U, hU⟩ := gomesFiniteFockQuadraticShear_isUnit (n + 2)
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hU]
    exact gomesFiniteFockQuadraticShear_commutes _
  · intro a
    rw [hU]
    exact gomesFiniteFockQuadraticShear_constant (n + 2) a
  · intro z
    rw [hU]
    exact gomesFiniteFockQuadraticShear_ne_taylor n z

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
