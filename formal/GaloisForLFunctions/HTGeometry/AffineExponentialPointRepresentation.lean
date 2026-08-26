import GaloisForLFunctions.HTGeometry.AffineExponentialPointEvaluation

/-!
# Algebra maps are points of the additive-exponential group

Every algebra homomorphism from the coordinate algebra of `Gₐⁿ × Gₘⁿ` to a field is evaluation
at a concrete point.  The additive coordinates are recovered on the standard basis.  The torus
coordinates are recovered from the units obtained by mapping the free character-lattice basis.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialPointRepresentation

noncomputable section

open AffineExponentialGroup AffineExponentialPointEvaluation

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- Restriction of a mixed point to the torus coordinate factor. -/
def torusRestriction {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) :
    TorusCoordinateAlgebra k n →ₐ[k] L :=
  χ.comp Algebra.TensorProduct.includeLeft

/-- Restriction of a mixed point to the additive coordinate factor. -/
def additiveRestriction {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) :
    AdditiveCoordinateAlgebra k n →ₐ[k] L :=
  χ.comp Algebra.TensorProduct.includeRight

/-- Unit-valued character of the free torus lattice induced by an algebra map. -/
def torusUnitCharacter {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) :
    Multiplicative (Fin n →₀ ℤ) →* Lˣ :=
  (((torusRestriction χ).toMonoidHom.comp
    (AddMonoidAlgebra.of k (Fin n →₀ ℤ))).toHomUnits)

/-- Concrete additive-exponential point represented by an algebra map. -/
def pointOfAlgHom {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) : Point L n :=
  ofCoordinates
    (fun i => additiveRestriction χ
      (SymmetricAlgebra.ι k (Fin n → k) (additiveBasisVector k i)))
    (fun i => torusUnitCharacter χ
      (Multiplicative.ofAdd (Finsupp.single i 1)))

/-- The reconstructed torus coordinates recover the entire free-lattice character. -/
theorem character_pointOfAlgHom {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L)
    (m : Fin n →₀ ℤ) :
    AlgebraicTorusCharacter.character (torusPart (pointOfAlgHom χ)) m =
      torusUnitCharacter χ (Multiplicative.ofAdd m) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp [pointOfAlgHom]
  | single_add i z m hi hz ih =>
      rw [AlgebraicTorusCharacter.character_add, ih]
      rw [show Multiplicative.ofAdd (Finsupp.single i z + m) =
        Multiplicative.ofAdd (Finsupp.single i z) * Multiplicative.ofAdd m from rfl,
        map_mul]
      congr 1
      rw [AlgebraicTorusCharacter.character_single]
      change (torusUnitCharacter χ (Multiplicative.ofAdd (Finsupp.single i 1))) ^ z = _
      have hpow : Multiplicative.ofAdd (Finsupp.single i z) =
          (Multiplicative.ofAdd (Finsupp.single i 1)) ^ z := by
        apply Multiplicative.toAdd.injective
        ext j
        simp
      rw [hpow, map_zpow]

/-- Torus evaluation at the represented point is the original torus restriction. -/
theorem torusEval_pointOfAlgHom {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) :
    AlgebraicTorusCharacter.eval (k := k) (torusPart (pointOfAlgHom χ)) =
      torusRestriction χ := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp [AlgebraicTorusCharacter.eval_single, character_pointOfAlgHom,
      torusUnitCharacter, torusRestriction]
  · ext

/-- Additive evaluation at the represented point is the original additive restriction. -/
theorem additiveEval_pointOfAlgHom {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L) :
    additiveEval (k := k) (additivePart (pointOfAlgHom χ)) = additiveRestriction χ := by
  classical
  apply SymmetricAlgebra.algHom_ext
  let F : (Fin n → k) →ₗ[k] L :=
    (additiveRestriction χ).toLinearMap.comp (SymmetricAlgebra.ι k (Fin n → k))
  have hlin : additiveLinearEval (k := k) (additivePart (pointOfAlgHom χ)) = F := by
    apply (Pi.basisFun k (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply]
    change additiveLinearEval (k := k) (additivePart (pointOfAlgHom χ))
      (additiveBasisVector k i) = _
    rw [additiveLinearEval_additiveBasisVector]
    rfl
  apply LinearMap.ext
  intro v
  change additiveEval (k := k) (additivePart (pointOfAlgHom χ))
    (SymmetricAlgebra.ι k (Fin n → k) v) =
      additiveRestriction χ (SymmetricAlgebra.ι k (Fin n → k) v)
  rw [additiveEval_ι]
  exact DFunLike.congr_fun hlin v

/-- Every mixed-coordinate algebra map is evaluation at its represented point. -/
theorem eval_pointOfAlgHom {n : ℕ} (χ : CoordinateAlgebra k n →ₐ[k] L)
    (w : CoordinateAlgebra k n) :
    eval (k := k) (pointOfAlgHom χ) w = χ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a b =>
      rw [eval_tmul]
      rw [DFunLike.congr_fun (torusEval_pointOfAlgHom χ) a]
      rw [DFunLike.congr_fun (additiveEval_pointOfAlgHom χ) b]
      change χ (a ⊗ₜ[k] 1) * χ (1 ⊗ₜ[k] b) = χ (a ⊗ₜ[k] b)
      rw [← map_mul]
      simp

end
end AffineExponentialPointRepresentation
end GaloisForLFunctions.HTGeometry
