import GaloisForLFunctions.RHTower.DeningerRationalWittHazewinkelHankel

/-!
# Higher-rank Hankel secant parameterization

This module constructs the actual `r`-atom moment parameterization
`X_n ↦ ∑_j U_j T_j^n`. Every `(r+1)`-minor of the generic Hankel matrix maps to zero over
an arbitrary commutative ring, including rings with nilpotents. The proof factors each evaluated
minor through an `(r+1) × r` and an `r × (r+1)` matrix and invokes the division-free rectangular
determinant theorem.
-/

namespace RHTower

noncomputable section
open scoped BigOperators
open MvPolynomial

/-- Target coordinates for `r` moment atoms: channel `0` is amplitude `U`, channel `1` is node
`T`. -/
abbrev DeningerHankelSecantIndex (r : ℕ) := Fin r × Fin 2

/-- `n`th moment of the universal ordered `r`-atom measure. -/
def deningerHankelSecantMoment
    (R : Type*) [CommRing R] (r n : ℕ) :
    MvPolynomial (DeningerHankelSecantIndex r) R :=
  ∑ j : Fin r,
    X (j, (0 : Fin 2)) * X (j, (1 : Fin 2)) ^ n

/-- Universal `r`-atom moment parameterization. -/
def deningerHankelSecantParameterization
    (R : Type*) [CommRing R] (r : ℕ) :
    MvPolynomial ℕ R →+* MvPolynomial (DeningerHankelSecantIndex r) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (deningerHankelSecantMoment R r)

@[simp] theorem deningerHankelSecantParameterization_X
    (R : Type*) [CommRing R] (r n : ℕ) :
    deningerHankelSecantParameterization R r (X n) =
      deningerHankelSecantMoment R r n := by
  simp [deningerHankelSecantParameterization]

/-- Generic unnormalized moment Hankel matrix. -/
def deningerGenericMomentHankel
    (R : Type*) [CommRing R] : Matrix ℕ ℕ (MvPolynomial ℕ R) :=
  fun i j => X (i + j)

/-- Generic ideal of all `(r+1)`-minors of the unnormalized moment Hankel matrix. -/
def deningerGenericHankelIdeal
    (R : Type*) [CommRing R] (r : ℕ) : Ideal (MvPolynomial ℕ R) :=
  deningerMatrixMinorIdeal (r + 1) (deningerGenericMomentHankel R)

/-- Evaluation of a generic Hankel entry is the corresponding universal atomic moment. -/
@[simp] theorem deningerHankelSecantParameterization_generic_entry
    (R : Type*) [CommRing R] (r i j : ℕ) :
    deningerHankelSecantParameterization R r
        (deningerGenericMomentHankel R i j) =
      deningerHankelSecantMoment R r (i + j) := by
  simp [deningerGenericMomentHankel]

/-- Left Vandermonde factor of an evaluated atomic Hankel block. -/
def deningerHankelSecantLeftFactor
    (R : Type*) [CommRing R] (r : ℕ) (rows : Fin (r + 1) → ℕ) :
    Matrix (Fin (r + 1)) (Fin r)
      (MvPolynomial (DeningerHankelSecantIndex r) R) :=
  fun i t => X (t, (1 : Fin 2)) ^ rows i

/-- Right weighted Vandermonde factor of an evaluated atomic Hankel block. -/
def deningerHankelSecantRightFactor
    (R : Type*) [CommRing R] (r : ℕ) (cols : Fin (r + 1) → ℕ) :
    Matrix (Fin r) (Fin (r + 1))
      (MvPolynomial (DeningerHankelSecantIndex r) R) :=
  fun t j => X (t, (0 : Fin 2)) * X (t, (1 : Fin 2)) ^ cols j

/-- Every evaluated `(r+1)` Hankel minor has an explicit rectangular atomic factorization. -/
theorem deningerHankelSecant_submatrix_factor
    (R : Type*) [CommRing R] (r : ℕ)
    (rows cols : Fin (r + 1) → ℕ) :
    (deningerHankelSecantParameterization R r).mapMatrix
        ((deningerGenericMomentHankel R).submatrix rows cols) =
      deningerHankelSecantLeftFactor R r rows *
        deningerHankelSecantRightFactor R r cols := by
  apply Matrix.ext
  intro i j
  change deningerHankelSecantParameterization R r
      (deningerGenericMomentHankel R (rows i) (cols j)) =
    ∑ t : Fin r,
      deningerHankelSecantLeftFactor R r rows i t *
        deningerHankelSecantRightFactor R r cols t j
  rw [deningerHankelSecantParameterization_generic_entry]
  simp only [deningerHankelSecantMoment]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [deningerHankelSecantLeftFactor,
    deningerHankelSecantRightFactor, pow_add]
  ring

/-- **Division-free secant vanishing.** Every `(r+1)` generic Hankel minor vanishes under the
`r`-atom parameterization over every commutative ring. -/
theorem deningerHankelSecantParameterization_minor_zero
    (R : Type*) [CommRing R] (r : ℕ)
    (rows cols : Fin (r + 1) → ℕ) :
    deningerHankelSecantParameterization R r
        (((deningerGenericMomentHankel R).submatrix rows cols).det) = 0 := by
  rw [(deningerHankelSecantParameterization R r).map_det,
    deningerHankelSecant_submatrix_factor]
  exact det_rectangular_factor_succ_eq_zero r _ _

/-- Generic `(r+1)` Hankel determinantal ideal is contained in the actual atomic secant kernel,
over arbitrary coefficient rings including nonreduced rings. -/
theorem deningerGenericHankelIdeal_le_secantParameterization_ker
    (R : Type*) [CommRing R] (r : ℕ) :
    deningerGenericHankelIdeal R r ≤
      RingHom.ker (deningerHankelSecantParameterization R r) := by
  rw [deningerGenericHankelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
  rintro p ⟨rows, cols, rfl⟩
  exact RingHom.mem_ker.mpr
    (deningerHankelSecantParameterization_minor_zero R r rows cols)

/-- The actual atomic secant kernel is prime whenever coefficients form a domain. -/
theorem deningerHankelSecantParameterization_ker_isPrime
    (R : Type*) [CommRing R] [IsDomain R] (r : ℕ) :
    (RingHom.ker (deningerHankelSecantParameterization R r)).IsPrime :=
  RingHom.ker_isPrime (deningerHankelSecantParameterization R r)

/-- Closed integral capstone: the universal ordered-atom secant kernel over `ℤ` is prime. -/
theorem deningerHankelSecantParameterization_int_ker_isPrime (r : ℕ) :
    (RingHom.ker (deningerHankelSecantParameterization ℤ r)).IsPrime :=
  deningerHankelSecantParameterization_ker_isPrime ℤ r

end
end RHTower
