import GaloisForLFunctions.RHTower.SoninSeamDefect

/-!
# Pinned affine weld defects have zero Fitting boundary

The filtered weld forces every genuine primitive to carry a positive-order derivation symbol.  At a
pinned torsion presentation, the natural local realization of that action is a commutator with the
presentation.  Its order-zero source and target basis corrections factor through the presentation,
possibly modulo the local divisor equation.

Both pieces are already known separately to be Fitting-boundary zero.  This file combines them at
the actual affine-defect level: a commutator plus arbitrary right-factor and left-factor corrections
modulo `X^m` always has zero boundary class.  Conversely, every live boundary class is excluded from
the entire pinned affine family.

Thus the positive-order symbol isolated by `WeldOrderFiltration` cannot be realized locally by the
obvious derivative/prime commutator any more than its scalar correction can.  The result does not
construct a carrier or cutoff escape; it proves that any surviving completed obstruction must be
genuinely nonlocal and cannot be a pinned affine presentation defect.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The most general pinned affine defect built from a presentation commutator together with target
and source factor corrections modulo the local divisor equation. -/
def pinnedAffineWeldDefect (m : ℕ) (A σ Hright Kright Hleft Kleft :
    Matrix n n (Polynomial R)) : Matrix n n (Polynomial R) :=
  commutatorDefect A σ +
    (A * Hright + (X : Polynomial R) ^ m • Kright) +
    (Hleft * A + (X : Polynomial R) ^ m • Kleft)

/-- **Pinned affine vanishing.**  Every commutator-plus-factor realization has zero Fitting boundary
class.  No hypothesis on the action or correction matrices is needed. -/
theorem fittingBoundaryClass_pinnedAffineWeldDefect_eq_zero (m : ℕ)
    (A σ Hright Kright Hleft Kleft : Matrix n n (Polynomial R))
    (hdet : A.det = (X : Polynomial R) ^ m) :
    fittingBoundaryClass m A
      (pinnedAffineWeldDefect m A σ Hright Kright Hleft Kleft) = 0 := by
  rw [pinnedAffineWeldDefect,
    fittingBoundaryClass_add_left_factor_mod_X_pow m hdet,
    fittingBoundaryClass_add_right_factor_mod_X_pow m hdet,
    fittingBoundaryClass_commutatorDefect]

/-- **Live classes have no pinned affine realization.**  A nonzero Fitting boundary cannot be a
commutator corrected by arbitrary source/target presentation factors modulo `X^m`. -/
theorem nonzero_fittingBoundaryClass_not_pinnedAffineWeldDefect (m : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (X : Polynomial R) ^ m)
    (hclass : fittingBoundaryClass m A Delta ≠ 0) :
    ¬ ∃ σ Hright Kright Hleft Kleft : Matrix n n (Polynomial R),
      Delta = pinnedAffineWeldDefect m A σ Hright Kright Hleft Kleft := by
  rintro ⟨σ, Hright, Kright, Hleft, Kleft, rfl⟩
  exact hclass
    (fittingBoundaryClass_pinnedAffineWeldDefect_eq_zero
      m A σ Hright Kright Hleft Kleft hdet)

end RHTower

