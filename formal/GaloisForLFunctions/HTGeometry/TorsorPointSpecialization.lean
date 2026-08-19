import GaloisForLFunctions.HTGeometry.TorsorDecomposition

/-!
# Specialising the torsor decomposition at a point

Given the decomposition `A ≅ R ⊗_C E` and a `C`-point of `E`, base change along the point produces
a specialisation `A → R` which is the identity on `R` and evaluates the constants at the point.

For a Picard--Vessiot ring and its tensor square this is exactly the passage from a point of the
difference Galois group to an element of it: the specialisation restricts to the identity on the
left copy, so `DifferenceSpecialization.rightComponent` turns it into a difference automorphism of
`R`.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C R A : Type*} [Field C] [CommRing R] [CommRing A]
  [Algebra C R] [Algebra C A] [Algebra R A] [IsScalarTower C R A]

/-- Base change of a `C`-point of `E` to a map on the decomposed tensor product. -/
def pointBaseChange (E : Subalgebra C A) (χ : E →ₐ[C] C) : (R ⊗[C] E) →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) ((Algebra.ofId C R).comp χ)
    (fun _ _ => Commute.all _ _)

omit [Algebra R A] [IsScalarTower C R A] in
@[simp] theorem pointBaseChange_tmul (E : Subalgebra C A) (χ : E →ₐ[C] C) (r : R) (e : E) :
    pointBaseChange (R := R) E χ (r ⊗ₜ[C] e) = r * algebraMap C R (χ e) :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **The specialisation attached to a point.** -/
def specializationOfPoint (E : Subalgebra C A) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (χ : E →ₐ[C] C) : A →ₐ[R] R :=
  (pointBaseChange (R := R) E χ).comp
    (tensorDecompositionEquiv (R := R) E b hgen hindep).symm.toAlgHom

/-- The specialisation is the identity on the base. -/
@[simp] theorem specializationOfPoint_algebraMap (E : Subalgebra C A) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (χ : E →ₐ[C] C) (r : R) :
    specializationOfPoint (R := R) E b hgen hindep χ (algebraMap R A r) = r := by
  have h := (specializationOfPoint (R := R) E b hgen hindep χ).commutes r
  rw [h]
  simp

/-- The specialisation evaluates the constants at the point. -/
theorem specializationOfPoint_coe (E : Subalgebra C A) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (χ : E →ₐ[C] C) (e : E) :
    specializationOfPoint (R := R) E b hgen hindep χ (e : A) = algebraMap C R (χ e) := by
  have hsymm : (tensorDecompositionEquiv (R := R) E b hgen hindep).symm (e : A)
      = (1 : R) ⊗ₜ[C] e := by
    apply (tensorDecompositionEquiv (R := R) E b hgen hindep).injective
    rw [AlgEquiv.apply_symm_apply]
    show (e : A) = tensorDecompositionHom (R := R) E ((1 : R) ⊗ₜ[C] e)
    rw [tensorDecompositionHom_tmul]
    simp
  show pointBaseChange (R := R) E χ
    ((tensorDecompositionEquiv (R := R) E b hgen hindep).symm (e : A)) = _
  rw [hsymm, pointBaseChange_tmul, one_mul]

end

end GaloisForLFunctions.HTGeometry
