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

/-- Coefficient coordinates of a polynomial class are its coefficients below the truncation
order. -/
theorem truncatedArcLinearEquiv_mk_apply (n : ℕ) (p : R[X]) (j : Fin (n + 1)) :
    truncatedArcLinearEquiv R n (Ideal.Quotient.mk (truncatedArcIdeal R n) p) j =
      p.coeff j := by
  change (AdjoinRoot.powerBasisAux' (monic_X.pow (n + 1))).repr
      (Ideal.Quotient.mk (truncatedArcIdeal R n) p)
      ((truncatedArcIndexEquiv R n).symm j) = p.coeff j
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  change (p %ₘ (X ^ (n + 1))).coeff ((truncatedArcIndexEquiv R n).symm j) = p.coeff j
  have hj : (((truncatedArcIndexEquiv R n).symm j : Fin _) : ℕ) = j := rfl
  rw [hj]
  have hdvd : X ^ (n + 1) ∣ p %ₘ (X ^ (n + 1)) - p :=
    dvd_modByMonic_sub p (X ^ (n + 1))
  have hc := (X_pow_dvd_iff.mp hdvd) j j.isLt
  simpa [coeff_sub, sub_eq_zero] using hc

variable {K S : Type u} [CommRing K] [CommRing S]
variable [Nontrivial S] [Algebra K R] [Algebra K S]

/-- Truncated-disc coefficient coordinates commute with extension of coefficient algebras. -/
theorem truncatedArcLinearEquiv_map (n : ℕ) (f : R →ₐ[K] S)
    (z : TruncatedArcAlgebra R n) (j : Fin (n + 1)) :
    truncatedArcLinearEquiv S n (mapTruncatedArcAlgHom n f z) j =
      f (truncatedArcLinearEquiv R n z j) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [mapTruncatedArcAlgHom_mk, truncatedArcLinearEquiv_mk_apply,
    truncatedArcLinearEquiv_mk_apply, coeff_map]
  rfl

/-- Coefficient coordinates valid uniformly for all commutative rings, including the zero ring. -/
noncomputable def truncatedArcCoordinateEquiv (R : Type u) [CommRing R] (n : ℕ) :
    TruncatedArcAlgebra R n ≃ₗ[R] (Fin (n + 1) → R) := by
  by_cases h : Nontrivial R
  · letI : Nontrivial R := h
    exact truncatedArcLinearEquiv R n
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact
      { toFun := fun _ _ => 0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        map_smul' := fun _ _ => Subsingleton.elim _ _ }

/-- Uniform coefficient coordinates commute with every coefficient-algebra morphism. -/
theorem truncatedArcCoordinateEquiv_map
    {R S K : Type u} [CommRing R] [CommRing S] [CommRing K]
    [Algebra K R] [Algebra K S]
    (n : ℕ) (f : R →ₐ[K] S) (z : TruncatedArcAlgebra R n) (j : Fin (n + 1)) :
    truncatedArcCoordinateEquiv S n (mapTruncatedArcAlgHom n f z) j =
      f (truncatedArcCoordinateEquiv R n z j) := by
  by_cases hS : Nontrivial S
  · letI : Nontrivial S := hS
    letI : Nontrivial R := f.toRingHom.domain_nontrivial
    simp only [truncatedArcCoordinateEquiv, dif_pos]
    exact truncatedArcLinearEquiv_map R n f z j
  · letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    exact Subsingleton.elim _ _

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
