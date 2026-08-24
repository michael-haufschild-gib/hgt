import GaloisForLFunctions.HTGeometry.StokesProjectivePresheafTensorFlat
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Exact total tensor by componentwise-projective complexes

For nonnegative chain complexes of module presheaves, every total degree is a finite coproduct over
an antidiagonal. Consequently, total left tensor preserves finite colimits. If the fixed complex is
componentwise projective, each antidiagonal summand preserves monomorphisms, so total left tensor is
an exact functor between abelian categories of chain complexes.

This categorical exactness is not K-flatness: no claim that total tensor maps quasi-isomorphisms is
made here.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace GaloisForLFunctions.IrregularStokes.ProjectiveComplexTensorExact

open ProjectivePresheafTensorFlat

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Module presheaves over the underlying ring presheaf of `A`. -/
abbrev ModulePresheaf := PresheafComplexTensor.ModulePresheaf A

/-- Nonnegative chain complexes of module presheaves. -/
abbrev ModulePresheafChainComplex := ChainComplex (ModulePresheaf A) ℕ

/-- Total left tensor by a componentwise-projective complex preserves monomorphisms. In each
degree, the map is a finite coproduct of monomorphisms indexed by the antidiagonal. -/
theorem totalTensorLeftPreservesMonomorphisms
    (P : ModulePresheafChainComplex A) [∀ n, Projective (P.X n)] :
    (@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P).PreservesMonomorphisms := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    PresheafComplexTensor.chainComplexMonoidalCategory A
  constructor
  intro X Y f _
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let B := (MonoidalCategory.curriedTensor (ModulePresheaf A)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  let Φ : ((B.obj P).obj X) ⟶ ((B.obj P).obj Y) :=
    (B.map (𝟙 P)).app X ≫ (B.obj P).map f
  change Mono ((HomologicalComplex₂.total.map Φ (ComplexShape.down ℕ)).f n)
  change Mono (GradedObject.mapMap (HomologicalComplex₂.toGradedObjectMap Φ)
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)
  change Mono (Limits.Sigma.map (fun x :
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} => HomologicalComplex₂.toGradedObjectMap Φ x))
  letI : Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) := by
    change Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n})
    infer_instance
  letI : HasBiproduct (fun x : (ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)) ⁻¹' {n} =>
      ((B.obj P).obj X).toGradedObject x) :=
    HasBiproduct.of_hasCoproduct _
  letI : HasBiproduct (fun x : (ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)) ⁻¹' {n} =>
      ((B.obj P).obj Y).toGradedObject x) :=
    HasBiproduct.of_hasCoproduct _
  letI (x : (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) :
      Mono (HomologicalComplex₂.toGradedObjectMap Φ x) := by
    rcases x with ⟨⟨i, j⟩, h⟩
    dsimp [Φ, B, HomologicalComplex₂.toGradedObjectMap]
    change Mono (((MonoidalCategory.curriedTensor (ModulePresheaf A)).map
        (𝟙 (P.X i))).app (X.X j) ≫
      ((MonoidalCategory.curriedTensor (ModulePresheaf A)).obj (P.X i)).map (f.f j))
    letI : IsIso ((MonoidalCategory.curriedTensor (ModulePresheaf A)).map
        (𝟙 (P.X i))) := by
      infer_instance
    letI : IsIso (((MonoidalCategory.curriedTensor (ModulePresheaf A)).map
        (𝟙 (P.X i))).app (X.X j)) := by
      infer_instance
    infer_instance
  apply Limits.Sigma.map_mono

/-- Total left tensor preserves zero morphisms. -/
noncomputable instance totalTensorLeftPreservesZeroMorphisms
    (P : ModulePresheafChainComplex A) :
    (@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P).PreservesZeroMorphisms := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    PresheafComplexTensor.chainComplexMonoidalCategory A
  constructor
  intro X Y
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change HomologicalComplex.ιMapBifunctor P X
      (MonoidalCategory.curriedTensor (ModulePresheaf A)) (ComplexShape.down ℕ) i j n h ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 P) (0 : X ⟶ Y)
        (MonoidalCategory.curriedTensor (ModulePresheaf A)) (ComplexShape.down ℕ)).f n = 0
  letI := PresheafDerivedTensor.tensorLeftAdditive A (P.X i)
  rw [HomologicalComplex.ι_mapBifunctorMap]
  have hz : (MonoidalCategory.tensorLeft (P.X i)).map
      (0 : X.X j ⟶ Y.X j) = 0 :=
    (MonoidalCategory.tensorLeft (P.X i)).map_zero (X.X j) (Y.X j)
  rw [show (0 : X ⟶ Y).f j = 0 by rfl, hz, zero_comp, comp_zero]

/-- Finite antidiagonal indexing total degree `n`. -/
abbrev Antidiagonal (n : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {n}

/-- Diagram of tensor summands indexed by the degree-`n` antidiagonal. -/
noncomputable def antidiagonalTensorDiagram
    (P : ModulePresheafChainComplex A) (n : ℕ) :
    ModulePresheafChainComplex A ⥤ Discrete (Antidiagonal n) ⥤ ModulePresheaf A where
  obj X := Discrete.functor (fun x =>
    P.X x.val.1 ⊗ X.X x.val.2)
  map {X Y} f := Discrete.natTrans (fun x =>
    (MonoidalCategory.tensorLeft (P.X x.as.val.1)).map (f.f x.as.val.2))
  map_id X := by
    apply NatTrans.ext
    funext x
    change (MonoidalCategory.tensorLeft (P.X x.as.val.1)).map
      (𝟙 (X.X x.as.val.2)) = 𝟙 _
    exact (MonoidalCategory.tensorLeft (P.X x.as.val.1)).map_id (X.X x.as.val.2)
  map_comp f g := by
    apply NatTrans.ext
    funext x
    change (MonoidalCategory.tensorLeft (P.X x.as.val.1)).map
      (f.f x.as.val.2 ≫ g.f x.as.val.2) = _
    exact (MonoidalCategory.tensorLeft (P.X x.as.val.1)).map_comp
      (f.f x.as.val.2) (g.f x.as.val.2)

/-- Evaluating the antidiagonal diagram at `(i,j)` is degree-`j` evaluation followed by tensor
with `P_i`. -/
noncomputable def antidiagonalTensorEvaluationIso
    (P : ModulePresheafChainComplex A) (n : ℕ)
    (x : Discrete (Antidiagonal n)) :
    antidiagonalTensorDiagram A P n ⋙
        (evaluation (Discrete (Antidiagonal n)) (ModulePresheaf A)).obj x ≅
      HomologicalComplex.eval (ModulePresheaf A) (ComplexShape.down ℕ) x.as.val.2 ⋙
        MonoidalCategory.tensorLeft (P.X x.as.val.1) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The antidiagonal tensor diagram functor preserves finite colimits pointwise. -/
theorem antidiagonalTensorDiagramPreservesFiniteColimits
    (P : ModulePresheafChainComplex A) (n : ℕ) :
    PreservesFiniteColimits (antidiagonalTensorDiagram A P n) := by
  apply preservesFiniteColimits_of_evaluation (antidiagonalTensorDiagram A P n)
  intro x
  exact preservesFiniteColimits_of_natIso
    (antidiagonalTensorEvaluationIso A P n x).symm

/-- Finite coproduct of all tensor summands in total degree `n`. -/
noncomputable def degreeAntidiagonalTensorFunctor
    (P : ModulePresheafChainComplex A) (n : ℕ) :
    ModulePresheafChainComplex A ⥤ ModulePresheaf A :=
  antidiagonalTensorDiagram A P n ⋙ colim

/-- The finite coproduct of antidiagonal tensor summands preserves finite colimits. -/
theorem degreeAntidiagonalTensorFunctorPreservesFiniteColimits
    (P : ModulePresheafChainComplex A) (n : ℕ) :
    PreservesFiniteColimits (degreeAntidiagonalTensorFunctor A P n) := by
  letI : PreservesFiniteColimits (antidiagonalTensorDiagram A P n) :=
    antidiagonalTensorDiagramPreservesFiniteColimits A P n
  dsimp [degreeAntidiagonalTensorFunctor]
  infer_instance

/-- Total left tensor followed by degree-`n` evaluation is the finite antidiagonal tensor
coproduct. -/
noncomputable def tensorLeftEvalIsoDegreeAntidiagonal
    (P : ModulePresheafChainComplex A) (n : ℕ) :
    @MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
          (PresheafComplexTensor.chainComplexMonoidalCategory A) P ⋙
        HomologicalComplex.eval (ModulePresheaf A) (ComplexShape.down ℕ) n ≅
      degreeAntidiagonalTensorFunctor A P n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change ((@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P).map f).f n =
        (degreeAntidiagonalTensorFunctor A P n).map f
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    change HomologicalComplex.ιMapBifunctor P X
        (MonoidalCategory.curriedTensor (ModulePresheaf A)) (ComplexShape.down ℕ) i j n h ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 P) f
            (MonoidalCategory.curriedTensor (ModulePresheaf A)) (ComplexShape.down ℕ)).f n =
      HomologicalComplex.ιMapBifunctor P X
        (MonoidalCategory.curriedTensor (ModulePresheaf A)) (ComplexShape.down ℕ) i j n h ≫
          (degreeAntidiagonalTensorFunctor A P n).map f
    rw [HomologicalComplex.ι_mapBifunctorMap]
    have hid : ((MonoidalCategory.curriedTensor (ModulePresheaf A)).map
        (𝟙 (P.X i))).app (X.X j) = 𝟙 _ :=
      congrArg (fun α => α.app (X.X j))
        ((MonoidalCategory.curriedTensor (ModulePresheaf A)).map_id (P.X i))
    have hidP : HomologicalComplex.Hom.f (𝟙 P) i = 𝟙 (P.X i) := rfl
    rw [hidP, hid, Category.id_comp]
    exact (colimit.ι_map ((antidiagonalTensorDiagram A P n).map f)
      (Discrete.mk ⟨(i, j), h⟩)).symm)

/-- Total left tensor by any nonnegative complex preserves finite colimits. -/
noncomputable instance totalTensorLeftPreservesFiniteColimits
    (P : ModulePresheafChainComplex A) :
    PreservesFiniteColimits (@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P) where
  preservesFiniteColimits J _ _ := by
    letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
      PresheafComplexTensor.chainComplexMonoidalCategory A
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    letI : PreservesFiniteColimits (degreeAntidiagonalTensorFunctor A P n) :=
      degreeAntidiagonalTensorFunctorPreservesFiniteColimits A P n
    exact preservesColimitsOfShape_of_natIso
      (tensorLeftEvalIsoDegreeAntidiagonal A P n).symm

/-- Total left tensor by a componentwise-projective complex preserves categorical homology in the
abelian category of nonnegative chain complexes. This is abelian exactness, not K-flatness. -/
theorem componentwiseProjectiveTotalTensorLeftPreservesHomology
    (P : ModulePresheafChainComplex A) [∀ n, Projective (P.X n)] :
    (@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P).PreservesHomology := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    PresheafComplexTensor.chainComplexMonoidalCategory A
  letI : (MonoidalCategory.tensorLeft P).PreservesMonomorphisms :=
    totalTensorLeftPreservesMonomorphisms A P
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels
    (MonoidalCategory.tensorLeft P)

/-- Total left tensor by a componentwise-projective complex maps exact short complexes of chain
complexes to exact short complexes. -/
theorem componentwiseProjectiveTotalTensorLeft_map_exact
    (P : ModulePresheafChainComplex A) [∀ n, Projective (P.X n)]
    (S : ShortComplex (ModulePresheafChainComplex A)) (hS : S.Exact) :
    (S.map (@MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P)).Exact := by
  let F := @MonoidalCategory.tensorLeft (ModulePresheafChainComplex A) _
    (PresheafComplexTensor.chainComplexMonoidalCategory A) P
  letI : F.PreservesZeroMorphisms := totalTensorLeftPreservesZeroMorphisms A P
  letI : PreservesFiniteColimits F := totalTensorLeftPreservesFiniteColimits A P
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hF : F.PreservesHomology := by
    dsimp [F]
    exact componentwiseProjectiveTotalTensorLeftPreservesHomology A P
  exact (((Functor.exact_tfae F).out 2 1 rfl rfl).mp hF) S hS

end GaloisForLFunctions.IrregularStokes.ProjectiveComplexTensorExact
