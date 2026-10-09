import GaloisForLFunctions.HTGeometry.PaperWeightOrderIdeals
import GaloisForLFunctions.RHTower.DeningerDeterminantalLaplace
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.SuccPred

/-!
# Source weight bounds for native generic determinantal ideals

The paper's nonnegative weights apply to arbitrary rectangular matrices of
independent variables. All size-`q` minors have degree `q`, so the native
determinantal ideal has that lower weight bound. Injective row and column
selections give nonzero minors by renaming the universal determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

noncomputable section

variable (K : Type*) [CommRing K] {ι κ : Type*}

/-- Every selected generic minor is homogeneous in its matrix size. -/
theorem paperVariableMinor_homogeneous (q : ℕ) (rows : Fin q → ι) (cols : Fin q → κ) :
    (((Matrix.mvPolynomialX ι κ K).submatrix rows cols).det).IsHomogeneous q := by
  classical
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_
  have hprod : (∏ i : Fin q,
      (MvPolynomial.X (rows (s i), cols i) : MvPolynomial (ι × κ) K)).IsHomogeneous
        (∑ _i : Fin q, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => MvPolynomial.isHomogeneous_X K _
  have hq : (∑ _i : Fin q, 1) = q := by simp
  rw [hq] at hprod
  have hCast : ((Equiv.Perm.sign s : ℤ) : MvPolynomial (ι × κ) K) =
      MvPolynomial.C ((Equiv.Perm.sign s : ℤ) : K) :=
    (map_intCast (MvPolynomial.C : K →+* MvPolynomial (ι × κ) K) _).symm
  rw [hCast]
  simpa using (MvPolynomial.isHomogeneous_C (ι × κ) (((Equiv.Perm.sign s : ℤ) : K))).mul hprod

/-- All elements of the native generic minor ideal have the prescribed lower total degree. -/
theorem paperVariableMinorIdeal_weightOrder (ι κ : Type*) (q : ℕ) :
    deningerMatrixMinorIdeal q (Matrix.mvPolynomialX ι κ K) ≤
      paperWeightOrderIdeal (fun _ : ι × κ => (1 : ℤ)) (by intro _; exact zero_le_one) (q : ℤ) := by
  rw [deningerMatrixMinorIdeal, Ideal.span_le]
  rintro p ⟨rows, cols, rfl⟩
  exact paperWeightOrderIdeal_mem_of_homogeneous _ _
    (paperIsWeightedHomogeneous_int (paperVariableMinor_homogeneous K q rows cols))

/-- A selected minor is the variable-renaming image of the universal square determinant. -/
theorem paperVariableMinor_eq_rename (q : ℕ) (rows : Fin q → ι) (cols : Fin q → κ) :
    ((Matrix.mvPolynomialX ι κ K).submatrix rows cols).det =
      MvPolynomial.rename (fun p : Fin q × Fin q => (rows p.1, cols p.2))
        (Matrix.mvPolynomialX (Fin q) (Fin q) K).det := by
  rw [(MvPolynomial.rename (fun p : Fin q × Fin q => (rows p.1, cols p.2))).map_det]
  congr 1
  funext i j
  change (MvPolynomial.X (rows i, cols j) : MvPolynomial (ι × κ) K) =
    MvPolynomial.rename (fun p : Fin q × Fin q => (rows p.1, cols p.2)) (MvPolynomial.X (i, j))
  rw [MvPolynomial.rename_X]

/-- Independent row and column selections preserve the nonzero generic determinant. -/
theorem paperVariableMinor_ne_zero [Nontrivial K] (q : ℕ)
    (rows : Fin q → ι) (cols : Fin q → κ)
    (hr : Function.Injective rows) (hc : Function.Injective cols) :
    ((Matrix.mvPolynomialX ι κ K).submatrix rows cols).det ≠ 0 := by
  rw [paperVariableMinor_eq_rename]
  intro h
  apply Matrix.det_mvPolynomialX_ne_zero (Fin q) K
  apply MvPolynomial.rename_injective (fun p : Fin q × Fin q => (rows p.1, cols p.2))
    (by
      rintro ⟨i, j⟩ ⟨i', j'⟩ he
      exact Prod.ext (hr (congrArg Prod.fst he)) (hc (congrArg Prod.snd he)))
  simpa only [map_zero] using h

end

end GaloisForLFunctions.HTGeometry
