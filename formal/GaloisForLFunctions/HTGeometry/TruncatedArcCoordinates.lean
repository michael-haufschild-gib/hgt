import GaloisForLFunctions.HTGeometry.AlgebraicGroupJet
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.AdjoinRoot

/-!
# Linear coordinates on a truncated disc

This file gives the truncated arc algebra `R[t]/(t^(n+1))` its exact coefficient
coordinates.  The augmentation is the zeroth coordinate, and its kernel is linearly
equivalent to the `n` positive coefficients.  This is the coefficient-space input used
by smooth étale jet charts; it makes no global choice of coordinates on a smooth scheme.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable (R : Type u) [CommRing R] [Nontrivial R]

/-- Power basis of the truncated arc algebra. -/
noncomputable def truncatedArcBasisRaw (n : ℕ) :
    Module.Basis (Fin (X ^ (n + 1) : R[X]).natDegree) R (TruncatedArcAlgebra R n) :=
  AdjoinRoot.powerBasisAux' (monic_X.pow (n + 1))

/-- Coefficients of a truncated arc, initially indexed by the degree of its defining
monic polynomial. -/
noncomputable def truncatedArcLinearEquivRaw (n : ℕ) :
    TruncatedArcAlgebra R n ≃ₗ[R] (Fin (X ^ (n + 1) : R[X]).natDegree → R) :=
  (truncatedArcBasisRaw R n).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite R R _

/-- Index of the constant coefficient in the raw power basis. -/
def truncatedArcRawZeroIndex (n : ℕ) : Fin (X ^ (n + 1) : R[X]).natDegree :=
  ⟨0, by rw [natDegree_X_pow]; omega⟩

/-- The zeroth raw power-basis coordinate is evaluation at `t = 0`. -/
theorem truncatedArcLinearEquivRaw_apply_zero (n : ℕ) (z : TruncatedArcAlgebra R n) :
    truncatedArcLinearEquivRaw R n z (truncatedArcRawZeroIndex R n) =
      truncatedArcAugmentation R n z := by
  change (AdjoinRoot.powerBasisAux' (monic_X.pow (n + 1))).repr z
      (truncatedArcRawZeroIndex R n) = _
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [truncatedArcAugmentation_mk]
  change (p %ₘ (X ^ (n + 1))).coeff 0 = p.eval 0
  have h := congrArg (Polynomial.eval 0) (modByMonic_add_div p (X ^ (n + 1)))
  rw [coeff_zero_eq_eval_zero]
  simpa using h

/-- The power-basis index is exactly `Fin (n + 1)`. -/
noncomputable def truncatedArcIndexEquiv (n : ℕ) :
    Fin (X ^ (n + 1) : R[X]).natDegree ≃ Fin (n + 1) :=
  { toFun := fun i => ⟨i, by simpa using i.isLt⟩
    invFun := fun i => ⟨i, by simpa using i.isLt⟩
    left_inv := fun i => Fin.ext rfl
    right_inv := fun i => Fin.ext rfl }

/-- Reindex raw coefficient functions by `Fin (n + 1)`. -/
noncomputable def truncatedArcReindexEquiv (n : ℕ) :
    (Fin (X ^ (n + 1) : R[X]).natDegree → R) ≃ₗ[R] (Fin (n + 1) → R) where
  toFun f i := f ((truncatedArcIndexEquiv R n).symm i)
  invFun f i := f (truncatedArcIndexEquiv R n i)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact coefficient coordinates on `R[t]/(t^(n+1))`. -/
noncomputable def truncatedArcLinearEquiv (n : ℕ) :
    TruncatedArcAlgebra R n ≃ₗ[R] (Fin (n + 1) → R) :=
  truncatedArcLinearEquivRaw R n ≪≫ₗ truncatedArcReindexEquiv R n

/-- In normalized coordinates, the zeroth coefficient is the augmentation. -/
theorem truncatedArcLinearEquiv_apply_zero (n : ℕ) (z : TruncatedArcAlgebra R n) :
    truncatedArcLinearEquiv R n z 0 = truncatedArcAugmentation R n z := by
  change truncatedArcLinearEquivRaw R n z ((truncatedArcIndexEquiv R n).symm 0) = _
  rw [show (truncatedArcIndexEquiv R n).symm 0 = truncatedArcRawZeroIndex R n by
    apply Fin.ext
    rfl]
  exact truncatedArcLinearEquivRaw_apply_zero R n z

/-- The augmentation ideal of the order-`n` truncated disc consists exactly of its
positive-degree coefficients. -/
noncomputable def basedTruncatedArcLinearEquiv (n : ℕ) :
    LinearMap.ker (truncatedArcAugmentation R n).toLinearMap ≃ₗ[R] (Fin n → R) where
  toFun z i := truncatedArcLinearEquiv R n z.1 i.succ
  invFun f := ⟨(truncatedArcLinearEquiv R n).symm (Fin.cons 0 f), by
    change truncatedArcAugmentation R n
      ((truncatedArcLinearEquiv R n).symm (Fin.cons 0 f)) = 0
    rw [← truncatedArcLinearEquiv_apply_zero R n]
    simp⟩
  left_inv z := by
    apply Subtype.ext
    apply (truncatedArcLinearEquiv R n).injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 = truncatedArcLinearEquiv R n z.1 0
      rw [truncatedArcLinearEquiv_apply_zero R n]
      exact z.2.symm
    · simp
  right_inv f := by
    ext i
    simp
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

end

end GaloisForLFunctions.HTGeometry
