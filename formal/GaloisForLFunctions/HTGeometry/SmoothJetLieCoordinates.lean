import GaloisForLFunctions.HTGeometry.TruncatedArcCoordinates
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Smooth local Lie coordinates for finite jets

The local model of a smooth relative scheme is affine space.  This file proves the
coordinate statement for that model without a dimension count or cardinality shortcut:
an order-`n` arc based at `x` is exactly an ordered family of `n` tangent vectors.

For a smooth group scheme, an étale chart at the identity transports this equivalence by
the formally étale jet-pullback theorem.  That transport is kept separate in
`FormalEtaleJetCompatibility` so the coordinate calculation and étale descent remain
independently reusable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (ι : Type v)

/-- Arcs on affine `ι`-space based at the point `x`. -/
abbrev AffineSpaceBasedArc (n : ℕ) (x : ι → R) :=
  { φ : MvPolynomial ι R →ₐ[R] TruncatedArcAlgebra R n //
    (truncatedArcAugmentation R n).comp φ = MvPolynomial.aeval x }

/-- A based affine-space arc is exactly one augmentation-ideal element per variable. -/
noncomputable def affineSpaceBasedArcKernelEquiv (n : ℕ) (x : ι → R) :
    AffineSpaceBasedArc R ι n x ≃
      (ι → LinearMap.ker (truncatedArcAugmentation R n).toLinearMap) where
  toFun φ i := ⟨φ.1 (MvPolynomial.X i) -
      algebraMap R (TruncatedArcAlgebra R n) (x i), by
    change truncatedArcAugmentation R n
      (φ.1 (MvPolynomial.X i) - algebraMap R (TruncatedArcAlgebra R n) (x i)) = 0
    have h := DFunLike.congr_fun φ.2 (MvPolynomial.X i)
    simpa using sub_eq_zero.mpr h⟩
  invFun v := ⟨MvPolynomial.aeval (fun i =>
      algebraMap R (TruncatedArcAlgebra R n) (x i) + (v i).1), by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    have hv : truncatedArcAugmentation R n (v i).1 = 0 := (v i).2
    rw [map_add, truncatedArcAugmentation_algebraMap, hv, add_zero]⟩
  left_inv φ := by
    apply Subtype.ext
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv v := by
    funext i
    apply Subtype.ext
    simp

/-- Coefficient coordinates on based arcs of affine space. -/
noncomputable def affineSpaceBasedArcCoefficientEquiv (n : ℕ) (x : ι → R) :
    AffineSpaceBasedArc R ι n x ≃ (ι → Fin n → R) where
  toFun φ i := basedTruncatedArcLinearEquiv R n
    (affineSpaceBasedArcKernelEquiv R ι n x φ i)
  invFun c := (affineSpaceBasedArcKernelEquiv R ι n x).symm
    (fun i => (basedTruncatedArcLinearEquiv R n).symm (c i))
  left_inv φ := by
    apply (affineSpaceBasedArcKernelEquiv R ι n x).injective
    funext i
    simp
  right_inv c := by
    funext i j
    simp

/-- **Smooth Lie-coordinate identification for the affine local model.** A based order-`n`
arc is one tangent vector `ι → R` for each positive jet order. -/
noncomputable def affineSpaceBasedArcLieEquiv (n : ℕ) (x : ι → R) :
    AffineSpaceBasedArc R ι n x ≃ (Fin n → ι → R) where
  toFun φ j i := affineSpaceBasedArcCoefficientEquiv R ι n x φ i j
  invFun c := (affineSpaceBasedArcCoefficientEquiv R ι n x).symm (fun i j => c j i)
  left_inv φ := by
    apply (affineSpaceBasedArcCoefficientEquiv R ι n x).injective
    rw [Equiv.apply_symm_apply]
  right_inv c := by
    ext j i
    simp

end

end GaloisForLFunctions.HTGeometry
