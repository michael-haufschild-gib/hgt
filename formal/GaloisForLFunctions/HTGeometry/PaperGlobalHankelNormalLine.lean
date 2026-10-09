import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalLine
import GaloisForLFunctions.HTGeometry.PaperHankelIdealOrders
import GaloisForLFunctions.RHTower.DeningerHankelGlobalSecantPrime

/-!
# Polynomial normal lines for the countable Deninger Hankel ideal

Apply the source Rees coefficient kernel and nonnegative weights to the
native ideal of all `(r+1)`-minors in the countable moment polynomial ring.
Every algebraic obligation is discharged by native determinant theorems.
The result is an actual polynomial ring embedding into the associated
graded ring, without a finite-window, characteristic or rank restriction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

noncomputable section

variable (K : Type*) [Field K]

/-- The principal Hankel determinant in the countable moment coordinate ring. -/
def paperGlobalHankelPrincipalMinor (r : ℕ) : MvPolynomial ℕ K :=
  MvPolynomial.rename (Fin.val : Fin (2 * r + 1) → ℕ) (paperHankelPrincipalMinor K r)

/-- The selected polynomial is literally a native generic Hankel minor. -/
theorem paperGlobalHankelPrincipalMinor_eq_det (r : ℕ) :
    paperGlobalHankelPrincipalMinor K r =
      ((deningerGenericMomentHankel K).submatrix
        (Fin.val : Fin (r + 1) → ℕ) Fin.val).det :=
  rename_finiteHankelMaximalMinorOver K _ _

/-- It belongs to the full countable determinantal ideal. -/
theorem paperGlobalHankelPrincipalMinor_mem (r : ℕ) :
    paperGlobalHankelPrincipalMinor K r ∈ deningerGenericHankelIdeal K r := by
  rw [paperGlobalHankelPrincipalMinor_eq_det]
  exact deningerMatrixMinorDet_mem _ _ _ _

/-- The finite diagonally monic determinant remains nonzero under variable inclusion. -/
theorem paperGlobalHankelPrincipalMinor_ne_zero (r : ℕ) :
    paperGlobalHankelPrincipalMinor K r ≠ 0 := by
  intro h
  apply paperHankelPrincipalMinor_ne_zero K r 0
  apply MvPolynomial.rename_injective (Fin.val : Fin (2 * r + 1) → ℕ) Fin.val_injective
  simpa only [paperGlobalHankelPrincipalMinor, map_zero] using h

/-- Every generator of the countable ideal has total degree `r+1`. -/
theorem paperGlobalHankelIdeal_weightOrder (r : ℕ) :
    deningerGenericHankelIdeal K r ≤
      paperWeightOrderIdeal (fun _ : ℕ => (1 : ℤ)) (by intro _; exact zero_le_one) (r + 1 : ℕ) := by
  rw [deningerGenericHankelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
  rintro p ⟨rows, cols, rfl⟩
  exact paperWeightOrderIdeal_mem_of_homogeneous _ _
    (paperIsWeightedHomogeneous_int (deningerGenericHankelMinor_isHomogeneous K r rows cols))

/-- Actual native data for the source normal-line bridge, with every condition proved. -/
def paperGlobalHankelNormalData (r : ℕ) :
    PaperHomogeneousNormalData K ℕ (deningerGenericHankelIdeal K r) where
  generator := paperGlobalHankelPrincipalMinor K r
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := paperGlobalHankelPrincipalMinor_mem K r
  generator_ne_zero := paperGlobalHankelPrincipalMinor_ne_zero K r
  homogeneous := by
    rw [paperGlobalHankelPrincipalMinor_eq_det]
    exact paperIsWeightedHomogeneous_int (deningerGenericHankelMinor_isHomogeneous K r _ _)
  order_bound := paperGlobalHankelIdeal_weightOrder K r

/-- Every determinant power has exact order in the full countable Hankel ideal. -/
theorem paperGlobalHankelPrincipalMinor_pow_exact (r n : ℕ) :
    paperGlobalHankelPrincipalMinor K r ^ n ∈ deningerGenericHankelIdeal K r ^ n ∧
    paperGlobalHankelPrincipalMinor K r ^ n ∉ deningerGenericHankelIdeal K r ^ (n + 1) :=
  ⟨(paperGlobalHankelNormalData K r).pow_mem n, (paperGlobalHankelNormalData K r).pow_not_mem_succ n⟩

/-- The principal determinant's normal direction in the full associated graded ring. -/
def paperGlobalHankelNormalDirection (r : ℕ) :
    PaperIdealAssociatedGraded (deningerGenericHankelIdeal K r) :=
  (paperGlobalHankelNormalData K r).direction

/-- This global normal direction is nonnilpotent at every rank over every field. -/
theorem paperGlobalHankelNormalDirection_not_isNilpotent (r : ℕ) :
    ¬ IsNilpotent (paperGlobalHankelNormalDirection K r) :=
  (paperGlobalHankelNormalData K r).direction_not_isNilpotent

/-- Polynomial substitution into the global native associated graded ring. -/
def paperGlobalHankelNormalPolynomialMap (r : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (deningerGenericHankelIdeal K r) :=
  (paperGlobalHankelNormalData K r).polynomialMap

/-- No polynomial relation survives in the global Hankel normal direction. -/
theorem paperGlobalHankelNormalPolynomialMap_eq_zero_iff (r : ℕ) (p : Polynomial K) :
    paperGlobalHankelNormalPolynomialMap K r p = 0 ↔ p = 0 :=
  (paperGlobalHankelNormalData K r).polynomialMap_eq_zero_iff p

/-- An actual polynomial ring embeds into Deninger's countable Hankel associated graded ring. -/
theorem paperGlobalHankelNormalPolynomialMap_injective (r : ℕ) :
    Function.Injective (paperGlobalHankelNormalPolynomialMap K r) :=
  (paperGlobalHankelNormalData K r).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
