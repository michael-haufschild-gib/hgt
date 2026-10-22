import GaloisForLFunctions.RHTower.Deninger.DeningerCellFiltration
import GaloisForLFunctions.HTGeometry.DirectLimitExact

/-!
# Pro-Ind global sections of a system of character stages

The pro-Ind global sections of a cofiltered system of stages are the filtered colimit of the global
sections of the finite stages, and its higher cohomology is the colimit of the higher cohomologies.
Vanishing at every stage therefore gives vanishing in the colimit, and a stagewise short exact
sequence of sections stays short exact after the colimit, because a filtered colimit of modules
preserves injectivity, exactness and surjectivity.

Together with the acyclicity of free analytic sheaves of finite rank and the induction over a finite
cell filtration, this is the statement that pro-Ind derived global sections commute with a relative
cell attachment.

* `RHTower.deningerStageSections`, `RHTower.deningerProIndSections` : the sections of a stage and
  their colimit.
* `RHTower.deningerProIndCohomology` : the pro-Ind higher cohomology.
* `RHTower.deningerProInd_acyclic` : stagewise vanishing gives pro-Ind vanishing.
* `RHTower.deningerProInd_sections_shortExact` : a stagewise short exact sequence of sections stays
  short exact in the pro-Ind colimit.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
  GaloisForLFunctions.HTGeometry

universe w

section Stages

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {X : ι → TopCat.{0}}

/-- The global sections of a sheaf at a finite stage. -/
abbrev deningerStageSections (F : ∀ i, TopCat.Sheaf AddCommGrpCat.{0} (X i)) (i : ι) : Type :=
  ToType ((F i).1.obj (op (⊤ : Opens (X i))))

/-- **The pro-Ind global sections of a system of stages**: the filtered colimit of the global
sections of the finite stages along the given transitions. -/
abbrev deningerProIndSections (F : ∀ i, TopCat.Sheaf AddCommGrpCat.{0} (X i))
    (τ : ∀ i j, i ≤ j → deningerStageSections F i →ₗ[ℤ] deningerStageSections F j) : Type :=
  Module.DirectLimit (deningerStageSections F) τ

/-- **The pro-Ind cohomology of a system of stages** in a given degree: the filtered colimit of the
cohomologies of the finite stages along the given transitions. -/
abbrev deningerProIndCohomology
    [∀ i, CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} (X i))]
    (F : ∀ i, TopCat.Sheaf AddCommGrpCat.{0} (X i)) (n : ℕ)
    (τ : ∀ i j, i ≤ j → deningerSheafCohomology.{w} (⊤ : Opens (X i)) (F i) n →ₗ[ℤ]
      deningerSheafCohomology.{w} (⊤ : Opens (X j)) (F j) n) : Type w :=
  Module.DirectLimit (fun i => deningerSheafCohomology.{w} (⊤ : Opens (X i)) (F i) n) τ

/-- **Stagewise vanishing gives vanishing in the colimit.**  A class of the colimit comes from a
stage, where it is zero. -/
theorem deningerProInd_acyclic {H : ι → Type*} [∀ i, AddCommGroup (H i)]
    (τ : ∀ i j, i ≤ j → H i →ₗ[ℤ] H j) (hzero : ∀ i (x : H i), x = 0)
    (ξ : Module.DirectLimit H τ) : ξ = 0 := by
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
  rw [hzero i x, map_zero]

/-- **The pro-Ind higher cohomology of a system of acyclic stages vanishes.**  This is the pro-Ind
acyclicity that Cartan's theorem B gives on each finite character stage. -/
theorem deningerProInd_cohomology_eq_zero
    [∀ i, CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} (X i))]
    (F : ∀ i, TopCat.Sheaf AddCommGrpCat.{0} (X i)) (n : ℕ)
    (τ : ∀ i j, i ≤ j → deningerSheafCohomology.{w} (⊤ : Opens (X i)) (F i) (n + 1) →ₗ[ℤ]
      deningerSheafCohomology.{w} (⊤ : Opens (X j)) (F j) (n + 1))
    (hacy : ∀ i, DeningerAcyclicOn.{w} (F i) ⊤)
    (ξ : deningerProIndCohomology.{w} F (n + 1) τ) : ξ = 0 :=
  deningerProInd_acyclic τ (fun i x => hacy i n x) ξ

end Stages

section ProIndCell

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {A B C : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, AddCommGroup (C i)]
  {τA : ∀ i j, i ≤ j → A i →ₗ[ℤ] A j} {τB : ∀ i j, i ≤ j → B i →ₗ[ℤ] B j}
  {τC : ∀ i j, i ≤ j → C i →ₗ[ℤ] C j}

/-- **A stagewise short exact sequence of sections stays short exact in the pro-Ind colimit.**  This
is the passage from a finite character stage to the pro-Ind model: injectivity, exactness and
surjectivity each survive a filtered colimit of modules. -/
theorem deningerProInd_sections_shortExact [DirectedSystem A fun i j h => τA i j h]
    [DirectedSystem B fun i j h => τB i j h] [DirectedSystem C fun i j h => τC i j h]
    (g : ∀ i, A i →ₗ[ℤ] B i) (hg : ∀ i j h, g j ∘ₗ τA i j h = τB i j h ∘ₗ g i)
    (g' : ∀ i, B i →ₗ[ℤ] C i) (hg' : ∀ i j h, g' j ∘ₗ τB i j h = τC i j h ∘ₗ g' i)
    (hinj : ∀ i, Function.Injective (g i)) (hexact : ∀ i, Function.Exact (g i) (g' i))
    (hsurj : ∀ i, Function.Surjective (g' i)) :
    Function.Injective (Module.DirectLimit.map (f := τA) (f' := τB) g hg) ∧
      Function.Exact (Module.DirectLimit.map (f := τA) (f' := τB) g hg)
        (Module.DirectLimit.map (f := τB) (f' := τC) g' hg') ∧
      Function.Surjective (Module.DirectLimit.map (f := τB) (f' := τC) g' hg') :=
  ⟨directLimit_map_injective g hg hinj,
    directLimit_map_exact g hg g' hg' hexact,
    directLimit_map_surjective g' hg' hsurj⟩

end ProIndCell

section ProIndCellStages

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {X : ι → TopCat.{0}} [∀ i, CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} (X i))]

/-- The map induced on global sections by a morphism of sheaves, as a `ℤ`-linear map. -/
noncomputable def deningerSectionsMap {Y : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} Y}
    (φ : F ⟶ G) :
    ToType (F.1.obj (op (⊤ : Opens Y))) →ₗ[ℤ] ToType (G.1.obj (op (⊤ : Opens Y))) :=
  AddMonoidHom.toIntLinearMap (ConcreteCategory.hom (φ.1.app (op ⊤)))

variable {P Q G : ∀ i, TopCat.Sheaf AddCommGrpCat.{0} (X i)}

omit [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  [∀ i, CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} (X i))] in
/-- The sections of a cell attachment are exact at the middle stage: the composite is zero because
the attachment is, and a section killed by the attachment comes from the previous stage. -/
theorem deningerSectionsMap_exact {i : ι} {a : P i ⟶ Q i} {b : Q i ⟶ G i}
    (hz : a ≫ b = 0) (hSE : (ShortComplex.mk a b hz).ShortExact) :
    Function.Exact (deningerSectionsMap a) (deningerSectionsMap b) := by
  refine fun y => ⟨fun hy => ?_, ?_⟩
  · have hy' : ConcreteCategory.hom
        ((ShortComplex.mk a b hz).g.1.app (op (⊤ : Opens (X i)))) y = 0 := hy
    exact deningerSections_exact hSE ⊤ y hy'
  rintro ⟨x, rfl⟩
  have hcomp : ConcreteCategory.hom ((a ≫ b).1.app (op (⊤ : Opens (X i)))) x
      = ConcreteCategory.hom (b.1.app (op (⊤ : Opens (X i))))
        (ConcreteCategory.hom (a.1.app (op (⊤ : Opens (X i)))) x) := by
    rfl
  show ConcreteCategory.hom (b.1.app (op (⊤ : Opens (X i))))
    (ConcreteCategory.hom (a.1.app (op (⊤ : Opens (X i)))) x) = 0
  rw [← hcomp, hz]
  rfl

/-- **`(7)`: pro-Ind derived global sections commute with a relative cell attachment.**  At every
finite stage the sections of the attachment are short exact — injective because the attachment is a
monomorphism, exact in the middle because sections are left exact, and surjective because the
previous stage is acyclic — and each of the three properties survives the filtered colimit that
defines the pro-Ind sections. -/
theorem deningerProInd_cellAttachment_shortExact
    (a : ∀ i, P i ⟶ Q i) (b : ∀ i, Q i ⟶ G i) (hz : ∀ i, a i ≫ b i = 0)
    (hSE : ∀ i, (ShortComplex.mk (a i) (b i) (hz i)).ShortExact)
    (hacy : ∀ i, DeningerAcyclicOn.{w} (P i) ⊤)
    {τP : ∀ i j, i ≤ j → deningerStageSections P i →ₗ[ℤ] deningerStageSections P j}
    {τQ : ∀ i j, i ≤ j → deningerStageSections Q i →ₗ[ℤ] deningerStageSections Q j}
    {τG : ∀ i j, i ≤ j → deningerStageSections G i →ₗ[ℤ] deningerStageSections G j}
    [DirectedSystem (deningerStageSections P) fun i j h => τP i j h]
    [DirectedSystem (deningerStageSections Q) fun i j h => τQ i j h]
    [DirectedSystem (deningerStageSections G) fun i j h => τG i j h]
    (hτa : ∀ i j h, deningerSectionsMap (a j) ∘ₗ τP i j h
      = τQ i j h ∘ₗ deningerSectionsMap (a i))
    (hτb : ∀ i j h, deningerSectionsMap (b j) ∘ₗ τQ i j h
      = τG i j h ∘ₗ deningerSectionsMap (b i)) :
    Function.Injective (Module.DirectLimit.map (f := τP) (f' := τQ)
        (fun i => deningerSectionsMap (a i)) hτa) ∧
      Function.Exact (Module.DirectLimit.map (f := τP) (f' := τQ)
          (fun i => deningerSectionsMap (a i)) hτa)
        (Module.DirectLimit.map (f := τQ) (f' := τG)
          (fun i => deningerSectionsMap (b i)) hτb) ∧
      Function.Surjective (Module.DirectLimit.map (f := τQ) (f' := τG)
        (fun i => deningerSectionsMap (b i)) hτb) :=
  deningerProInd_sections_shortExact _ hτa _ hτb
    (fun i => by
      haveI := (hSE i).mono_f
      exact deningerSections_injective_of_mono (a i) ⊤)
    (fun i => deningerSectionsMap_exact (hz i) (hSE i))
    (fun i => deningerSections_surjective_of_acyclic.{w, 0} (hSE i) ⊤ (hacy i))

end ProIndCellStages

end RHTower
