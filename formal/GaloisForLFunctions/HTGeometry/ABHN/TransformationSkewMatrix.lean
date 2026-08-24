import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite transformation crossed products are matrix algebras

For a finite group `G`, let `G` act on `K^G` by right translation.  This file proves

`(K^G) ⋊ G ≃ₐ[K] End_K(K^G)`.

The proof exhibits every standard matrix unit as a translated point mass.  This split crossed
product is the centralizer factor in the cyclic-algebra tensor-product formula.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Functions carrying the right-translation action. -/
@[reducible] def TransformationFunctions (K G : Type*) := G → K

@[ext]
theorem TransformationFunctions.ext {K G : Type*}
    {f h : TransformationFunctions K G} (eq : ∀ g, f g = h g) : f = h :=
  funext eq

instance {K G : Type*} [Semiring K] : Semiring (TransformationFunctions K G) :=
  inferInstanceAs (Semiring (G → K))

instance {K G : Type*} [CommSemiring K] : CommSemiring (TransformationFunctions K G) :=
  inferInstanceAs (CommSemiring (G → K))

instance {K G : Type*} [CommSemiring K] : Algebra K (TransformationFunctions K G) :=
  inferInstanceAs (Algebra K (G → K))

instance {K G : Type*} [Group G] : SMul G (TransformationFunctions K G) where
  smul g f := fun τ => f (τ * g)

instance {K G : Type*} [Semiring K] [Group G] :
    MulSemiringAction G (TransformationFunctions K G) where
  smul_zero g := rfl
  smul_add g f h := rfl
  smul_one g := rfl
  smul_mul g f h := rfl
  one_smul f := by
    funext τ
    change f (τ * 1) = f τ
    rw [mul_one]
  mul_smul g h f := by
    funext τ
    change f (τ * (g * h)) = f ((τ * g) * h)
    rw [mul_assoc]

instance {K G : Type*} [CommSemiring K] [Group G] :
    SMulCommClass G K (TransformationFunctions K G) where
  smul_comm _ _ _ := rfl

variable (K G : Type*) [Field K] [Group G] [Fintype G] [DecidableEq G]

/-- Pointwise multiplication representation of the coefficient algebra. -/
noncomputable def transformationCoefficientAction :
    TransformationFunctions K G →ₐ[K] Module.End K (TransformationFunctions K G) where
  toFun f :=
    { toFun := fun v τ => f τ * v τ
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }
  map_one' := by ext v τ; simp
  map_mul' := by intros; ext v τ; simp [Module.End.mul_apply, mul_assoc]
  map_zero' := by ext v τ; simp
  map_add' := by intros; ext v τ; simp [add_mul]
  commutes' := by intros; ext v τ; simp

/-- Right-translation representation of the acting group. -/
noncomputable def transformationTranslationAction :
    G →* Module.End K (TransformationFunctions K G) where
  toFun g :=
    { toFun := fun f => g • f
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f τ; simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    apply TransformationFunctions.ext
    intro τ
    change v (τ * (g * h)) = v ((τ * g) * h)
    rw [mul_assoc]

/-- Translation and pointwise multiplication obey the skew covariance relation. -/
theorem transformation_covariant (f : TransformationFunctions K G) (g : G) :
    transformationCoefficientAction K G (g • f) * transformationTranslationAction K G g =
      transformationTranslationAction K G g * transformationCoefficientAction K G f := by
  apply LinearMap.ext
  intro v
  apply TransformationFunctions.ext
  intro τ
  change f (τ * g) * v (τ * g) = f (τ * g) * v (τ * g)
  rfl

/-- Regular representation of the finite transformation crossed product. -/
noncomputable def transformationSkewRepresentation :
    SkewMonoidAlgebra (TransformationFunctions K G) G →ₐ[K]
      Module.End K (TransformationFunctions K G) :=
  SkewMonoidAlgebra.liftNCAlgHom (transformationCoefficientAction K G)
    (transformationTranslationAction K G)
    (fun {f} g => transformation_covariant K G f g)

@[simp]
theorem transformationSkewRepresentation_single
    (g : G) (f : TransformationFunctions K G) :
    transformationSkewRepresentation K G (SkewMonoidAlgebra.single g f) =
      transformationCoefficientAction K G f * transformationTranslationAction K G g := by
  exact SkewMonoidAlgebra.liftNC_single _ _ _ _

@[simp]
theorem transformationSkewRepresentation_single_apply
    (g : G) (f v : TransformationFunctions K G) (τ : G) :
    transformationSkewRepresentation K G (SkewMonoidAlgebra.single g f) v τ =
      f τ * v (τ * g) := by
  rw [transformationSkewRepresentation_single]
  rfl

/-- Every standard endomorphism matrix unit occurs in the regular representation. -/
theorem transformation_endBasis_mem_range (i j : G) :
    (Pi.basisFun K G).end (i, j) ∈
      LinearMap.range (transformationSkewRepresentation K G).toLinearMap := by
  classical
  refine ⟨SkewMonoidAlgebra.single (i⁻¹ * j) (Pi.basisFun K G i), ?_⟩
  apply (Pi.basisFun K G).ext
  intro k
  apply TransformationFunctions.ext
  intro τ
  change transformationSkewRepresentation K G
      (SkewMonoidAlgebra.single (i⁻¹ * j) (Pi.basisFun K G i))
        (Pi.basisFun K G k) τ =
    (Pi.basisFun K G).end (i, j) (Pi.basisFun K G k) τ
  rw [transformationSkewRepresentation_single_apply,
    Module.Basis.end_apply_apply]
  by_cases hiτ : i = τ
  · subst τ
    by_cases hjk : j = k
    · subst k
      simp [Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, hjk]
  · by_cases hjk : j = k
    · simp [Pi.basisFun_apply, hjk, hiτ]
    · simp [Pi.basisFun_apply, hjk, hiτ]

/-- The regular representation contains every endomorphism. -/
theorem transformationSkewRepresentation_surjective :
    Function.Surjective (transformationSkewRepresentation K G) := by
  change Function.Surjective (transformationSkewRepresentation K G).toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun K G).end.span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact transformation_endBasis_mem_range K G i j

/-- Coordinate formula for the regular crossed-product representation. -/
theorem transformationSkewRepresentation_apply
    (F : SkewMonoidAlgebra (TransformationFunctions K G) G)
    (v : TransformationFunctions K G) (τ : G) :
    transformationSkewRepresentation K G F v τ =
      ∑ g : G, F.coeff g τ * v (τ * g) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F H hF hH =>
      rw [map_add]
      simp only [SkewMonoidAlgebra.coeff_add]
      change transformationSkewRepresentation K G F v τ +
          transformationSkewRepresentation K G H v τ =
        ∑ x : G, (F.coeff x τ + H.coeff x τ) * v (τ * x)
      rw [hF, hH, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      change F.coeff x τ * v (τ * x) + H.coeff x τ * v (τ * x) =
        (F.coeff x τ + H.coeff x τ) * v (τ * x)
      rw [add_mul]
  | single g f =>
      rw [transformationSkewRepresentation_single_apply]
      rw [Finset.sum_eq_single g]
      · simp [SkewMonoidAlgebra.coeff_single]
      · intro h _ hh
        simp [SkewMonoidAlgebra.coeff_single, hh]
      · simp

/-- The regular representation is faithful. -/
theorem transformationSkewRepresentation_injective :
    Function.Injective (transformationSkewRepresentation K G) := by
  intro F H hFH
  apply SkewMonoidAlgebra.coeff_injective
  ext g τ
  have hcoordinate := congrArg
    (fun T : Module.End K (TransformationFunctions K G) =>
      T (Pi.basisFun K G (τ * g)) τ) hFH
  rw [transformationSkewRepresentation_apply,
    transformationSkewRepresentation_apply] at hcoordinate
  have hsumF :
      (∑ x : G, F.coeff x τ * (Pi.basisFun K G (τ * g)) (τ * x)) =
        F.coeff g τ := by
    rw [Finset.sum_eq_single g]
    · simp [Pi.basisFun_apply]
    · intro x _ hxg
      have hne : τ * g ≠ τ * x := fun h => hxg (mul_left_cancel h).symm
      simp [Pi.basisFun_apply, hne]
    · simp
  have hsumH :
      (∑ x : G, H.coeff x τ * (Pi.basisFun K G (τ * g)) (τ * x)) =
        H.coeff g τ := by
    rw [Finset.sum_eq_single g]
    · simp [Pi.basisFun_apply]
    · intro x _ hxg
      have hne : τ * g ≠ τ * x := fun h => hxg (mul_left_cancel h).symm
      simp [Pi.basisFun_apply, hne]
    · simp
  rw [hsumF, hsumH] at hcoordinate
  exact hcoordinate

/-- **Finite transformation algebra theorem.** The right-translation crossed product of `K^G`
by `G` is the full endomorphism algebra of `K^G`. -/
noncomputable def transformationSkewAlgEquiv :
    SkewMonoidAlgebra (TransformationFunctions K G) G ≃ₐ[K]
      Module.End K (TransformationFunctions K G) :=
  AlgEquiv.ofBijective (transformationSkewRepresentation K G)
    ⟨transformationSkewRepresentation_injective K G,
      transformationSkewRepresentation_surjective K G⟩

/-- A finite transformation crossed product is a simple split algebra. -/
theorem isSimpleRing_transformationSkew :
    IsSimpleRing (SkewMonoidAlgebra (TransformationFunctions K G) G) := by
  letI : Nonempty G := ⟨1⟩
  have hend : IsSimpleRing (Module.End K (TransformationFunctions K G)) := by
    exact IsSimpleRing.of_ringEquiv
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun K G)).symm.toRingEquiv
      (inferInstance : IsSimpleRing (Matrix G G K))
  exact IsSimpleRing.of_ringEquiv (transformationSkewAlgEquiv K G).symm.toRingEquiv hend

end

end GaloisForLFunctions.HTGeometry.ABHN
