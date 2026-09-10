import GaloisForLFunctions.HTGeometry.GomesFiniteFockCyclicClock
import GaloisForLFunctions.HTGeometry.TruncatedToeplitz

/-!
# Polynomial symbols for actual finite Fock matrices

The existing lower Toeplitz jet construction, transposed, is an algebra map whose
variable is exactly the actual Fock derivative. Its top column observes the
polynomial coefficients in reverse order.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The existing Toeplitz jet, transposed to act on derivative coordinates. -/
def gomesFiniteFockPolynomialHom (N : ℕ) : ℂ[X] →ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := (toeplitz N p).transpose
  map_zero' := by
    apply Matrix.ext
    intro i j
    simp [Matrix.transpose_apply, toeplitz_apply]
  map_one' := by rw [toeplitz_one, Matrix.transpose_one]
  map_add' p q := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, toeplitz_apply, Polynomial.coeff_add, Matrix.add_apply]
    split_ifs <;> simp
  map_mul' p q := by
    rw [mul_comm p q, ← toeplitz_mul, Matrix.transpose_mul]
  commutes' a := by
    apply Matrix.ext
    intro i j
    change (if i.val ≤ j.val then (C a).coeff (j.val - i.val) else 0) = _
    rw [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hle : i.val ≤ j.val
      · have hne : j.val - i.val ≠ 0 := by
          intro h
          apply hij
          exact Fin.ext (Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp h))
        simp [hle, Polynomial.coeff_C, hne, hij]
      · simp [hle, hij]

/-- Exact upper Toeplitz coefficients of every polynomial symbol. -/
theorem gomesFiniteFockPolynomialHom_apply (N : ℕ) (p : ℂ[X]) (i j : Fin N) :
    gomesFiniteFockPolynomialHom N p i j =
      if i.val ≤ j.val then p.coeff (j.val - i.val) else 0 := rfl

/-- The symbol variable is the existing finite derivative clock. -/
theorem gomesFiniteFockPolynomialHom_X (N : ℕ) :
    gomesFiniteFockPolynomialHom N X = fockShiftMatrix N := by
  apply Matrix.ext
  intro i j
  rw [gomesFiniteFockPolynomialHom_apply, fockShiftMatrix_apply]
  by_cases hle : i.val ≤ j.val
  · rw [if_pos hle, Polynomial.coeff_X]
    have he : j.val - i.val = 1 ↔ i.val + 1 = j.val := by
      constructor
      · intro h
        simpa [h] using Nat.add_sub_of_le hle
      · intro h
        rw [← h, Nat.add_sub_cancel_left]
    have he' : 1 = j.val - i.val ↔ i.val + 1 = j.val := eq_comm.trans he
    simp only [he']
  · have hne : i.val + 1 ≠ j.val := by
      intro h
      apply hle
      rw [← h]
      exact Nat.le_succ _
    rw [if_neg hle, if_neg hne]

/-- All symbol matrices commute with the actual derivative clock. -/
theorem gomesFiniteFockPolynomialHom_mem (N : ℕ) (p : ℂ[X]) :
    gomesFiniteFockPolynomialHom N p ∈ gomesFiniteFockCommutant N := by
  apply (gomesFiniteFockCommutant_mem_iff _ _).mpr
  rw [← gomesFiniteFockPolynomialHom_X]
  exact (Commute.all p X).map (gomesFiniteFockPolynomialHom N)

/-- The top column reads all coefficients below the finite horizon. -/
theorem gomesFiniteFockPolynomialHom_top (n : ℕ) (p : ℂ[X]) (i : Fin (n + 1)) :
    (gomesFiniteFockPolynomialHom (n + 1) p *ᵥ coordVec n) i = p.coeff i.rev.val := by
  change (gomesFiniteFockPolynomialHom (n + 1) p *ᵥ coordVec (Fin.last n).val) i = _
  rw [fockMatrix_mulVec_coord, gomesFiniteFockPolynomialHom_apply,
    Fin.val_last, if_pos i.is_le, Fin.val_rev, Nat.succ_sub_succ_eq_sub]

/-- The actual polynomial functional calculus is exactly the existing transposed Toeplitz map. -/
theorem gomesFiniteFockPolynomialHom_eq_aeval (N : ℕ) :
    gomesFiniteFockPolynomialHom N = Polynomial.aeval (fockShiftMatrix N) := by
  apply Polynomial.algHom_ext
  rw [gomesFiniteFockPolynomialHom_X, Polynomial.aeval_X]

/-- Polynomial symbols as elements of the full actual symmetry algebra. -/
def gomesFiniteFockSymbolHom (N : ℕ) : ℂ[X] →ₐ[ℂ] gomesFiniteFockCommutant N :=
  (gomesFiniteFockPolynomialHom N).codRestrict _ (gomesFiniteFockPolynomialHom_mem N)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
