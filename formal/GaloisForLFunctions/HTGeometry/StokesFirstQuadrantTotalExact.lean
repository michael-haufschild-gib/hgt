import GaloisForLFunctions.HTGeometry.StokesProjectiveComplexTensorExact

/-!
# Exactness of first-quadrant totalization

For bicomplexes of module presheaves indexed by two copies of `ℕ`, every total degree is a finite
antidiagonal. Consequently, the total-complex functor preserves finite colimits and monomorphisms,
hence homology and exact short complexes.

This is exactness of totalization as a functor on bicomplexes. It is one input to the separate
finite-filtration proof of K-flatness; it does not itself imply that total tensor preserves
quasi-isomorphisms.
-/

open CategoryTheory Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.FirstQuadrantTotalExact

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Module presheaves over the underlying ring presheaf of `A`. -/
abbrev ModulePresheaf := PresheafComplexTensor.ModulePresheaf A

/-- First-quadrant bicomplexes of module presheaves. -/
abbrev ModulePresheafBicomplex :=
  HomologicalComplex₂ (ModulePresheaf A) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- Finite antidiagonal indexing total degree `n`. -/
abbrev Antidiagonal (n : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {n}

/-- Degree-`n` antidiagonal diagram of a bicomplex. -/
noncomputable def antidiagonalDiagram (n : ℕ) :
    ModulePresheafBicomplex A ⥤ Discrete (Antidiagonal n) ⥤ ModulePresheaf A where
  obj K := Discrete.functor (fun x => (K.X x.val.1).X x.val.2)
  map {K L} φ := Discrete.natTrans (fun x => (φ.f x.as.val.1).f x.as.val.2)
  map_id K := by
    apply NatTrans.ext
    funext x
    rfl
  map_comp φ ψ := by
    apply NatTrans.ext
    funext x
    rfl

/-- Evaluating the antidiagonal diagram at `(i,j)` is double complex evaluation. -/
noncomputable def antidiagonalEvaluationIso (n : ℕ) (x : Discrete (Antidiagonal n)) :
    antidiagonalDiagram A n ⋙
        (evaluation (Discrete (Antidiagonal n)) (ModulePresheaf A)).obj x ≅
      HomologicalComplex.eval
          (HomologicalComplex (ModulePresheaf A) (ComplexShape.down ℕ))
          (ComplexShape.down ℕ) x.as.val.1 ⋙
        HomologicalComplex.eval (ModulePresheaf A) (ComplexShape.down ℕ) x.as.val.2 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Antidiagonal diagrams preserve finite colimits pointwise. -/
theorem antidiagonalDiagramPreservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (antidiagonalDiagram A n) := by
  apply preservesFiniteColimits_of_evaluation (antidiagonalDiagram A n)
  intro x
  exact preservesFiniteColimits_of_natIso
    (antidiagonalEvaluationIso A n x).symm

/-- Finite coproduct of all bicomplex entries in total degree `n`. -/
noncomputable def degreeAntidiagonalFunctor (n : ℕ) :
    ModulePresheafBicomplex A ⥤ ModulePresheaf A :=
  antidiagonalDiagram A n ⋙ colim

/-- Degree-`n` antidiagonal coproduct preserves finite colimits. -/
theorem degreeAntidiagonalFunctorPreservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (degreeAntidiagonalFunctor A n) := by
  letI : PreservesFiniteColimits (antidiagonalDiagram A n) :=
    antidiagonalDiagramPreservesFiniteColimits A n
  dsimp [degreeAntidiagonalFunctor]
  infer_instance

/-- Totalization followed by degree-`n` evaluation is the antidiagonal coproduct. -/
noncomputable def totalEvalIsoDegreeAntidiagonal (n : ℕ) :
    HomologicalComplex₂.totalFunctor (ModulePresheaf A)
          (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
        HomologicalComplex.eval (ModulePresheaf A) (ComplexShape.down ℕ) n ≅
      degreeAntidiagonalFunctor A n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- First-quadrant totalization preserves finite colimits. -/
noncomputable instance totalFunctorPreservesFiniteColimits :
    PreservesFiniteColimits
      (HomologicalComplex₂.totalFunctor (ModulePresheaf A)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    letI : PreservesFiniteColimits (degreeAntidiagonalFunctor A n) :=
      degreeAntidiagonalFunctorPreservesFiniteColimits A n
    exact preservesColimitsOfShape_of_natIso
      (totalEvalIsoDegreeAntidiagonal A n).symm

/-- First-quadrant totalization preserves monomorphisms because each total degree is a finite
coproduct of componentwise monomorphisms. -/
theorem totalFunctorPreservesMonomorphisms :
    (HomologicalComplex₂.totalFunctor (ModulePresheaf A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)).PreservesMonomorphisms := by
  constructor
  intro K L φ _
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (GradedObject.mapMap (HomologicalComplex₂.toGradedObjectMap φ)
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) n)
  change Mono (Limits.Sigma.map (fun x : Antidiagonal n =>
    HomologicalComplex₂.toGradedObjectMap φ x))
  letI : Finite (Antidiagonal n) := by
    change Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n})
    infer_instance
  letI : HasBiproduct (fun x : Antidiagonal n => K.toGradedObject x) :=
    HasBiproduct.of_hasCoproduct _
  letI : HasBiproduct (fun x : Antidiagonal n => L.toGradedObject x) :=
    HasBiproduct.of_hasCoproduct _
  letI (x : Antidiagonal n) :
      Mono (HomologicalComplex₂.toGradedObjectMap φ x) := by
    rcases x with ⟨⟨i, j⟩, h⟩
    dsimp [HomologicalComplex₂.toGradedObjectMap]
    letI : Mono (φ.f i) := by
      change Mono ((HomologicalComplex.eval _ _ i).map φ)
      infer_instance
    change Mono ((HomologicalComplex.eval _ _ j).map (φ.f i))
    infer_instance
  apply Limits.Sigma.map_mono

/-- First-quadrant totalization preserves categorical homology. -/
theorem totalFunctorPreservesHomology :
    (HomologicalComplex₂.totalFunctor (ModulePresheaf A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)).PreservesHomology := by
  let F := HomologicalComplex₂.totalFunctor (ModulePresheaf A)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  letI : F.PreservesMonomorphisms := totalFunctorPreservesMonomorphisms A
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels F

/-- First-quadrant totalization maps exact short complexes of bicomplexes to exact short
complexes. -/
theorem totalFunctor_map_exact
    (S : ShortComplex (ModulePresheafBicomplex A)) (hS : S.Exact) :
    (S.map (HomologicalComplex₂.totalFunctor (ModulePresheaf A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))).Exact := by
  let F := HomologicalComplex₂.totalFunctor (ModulePresheaf A)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  letI : HasBinaryBiproducts (ModulePresheafBicomplex A) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hF : F.PreservesHomology := by
    dsimp [F]
    exact totalFunctorPreservesHomology A
  exact (((Functor.exact_tfae F).out 2 1 rfl rfl).mp hF) S hS

/-- First-quadrant totalization maps short exact sequences of bicomplexes to short exact
sequences of total complexes. -/
theorem totalFunctor_map_shortExact
    (S : ShortComplex (ModulePresheafBicomplex A)) (hS : S.ShortExact) :
    (S.map (HomologicalComplex₂.totalFunctor (ModulePresheaf A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))).ShortExact := by
  let F := HomologicalComplex₂.totalFunctor (ModulePresheaf A)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  letI : HasBinaryBiproducts (ModulePresheafBicomplex A) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hF : F.PreservesHomology := by
    dsimp [F]
    exact totalFunctorPreservesHomology A
  exact (((Functor.exact_tfae F).out 2 0 rfl rfl).mp hF) S hS

end GaloisForLFunctions.IrregularStokes.FirstQuadrantTotalExact
