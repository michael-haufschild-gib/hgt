import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineSectionPushout
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Finite étale traces of functions and forms on affine opens. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

private abbrev fibreAlgebra (U : X.Opens) :
    Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) :=
  (f.app U).hom.toAlgebra

omit [Etale f] in
private theorem fibreFinite {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
    Module.Finite (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) :=
  f.finite_app U hU

private theorem fibreEtale {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
    Algebra.Etale (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := by
  have h := f.etale_appLE hU (hU.preimage f) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

omit [IsFinite f] [Etale f] in
private theorem fibreScalarTower (hf : f ≫ s = t) (U : X.Opens) :
    letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
    IsScalarTower k (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := by
  letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
  exact IsScalarTower.of_algebraMap_eq fun r => ((sectionPullback hf U).commutes r).symm

variable (s t) in
/-- Trace of functions along a finite étale morphism over an affine open. -/
def affineSectionTrace {U : X.Opens} (hU : IsAffineOpen U) :
    SectionRing t (f ⁻¹ᵁ U) →+ SectionRing s U :=
  letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
  letI := fibreFinite (s := s) (t := t) (f := f) hU
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  (finiteEtaleAlgebraTrace (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U))).toAddMonoidHom

/-- Trace of functions commutes with restriction between affine opens. -/
theorem affineSectionTrace_res {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : V ⟶ U) (b : SectionRing t (f ⁻¹ᵁ U)) :
    sectionRes s i (affineSectionTrace (f := f) s t hU b) =
      affineSectionTrace (f := f) s t hV (sectionRes t ((Opens.map f.base).map i) b) := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  let C := SectionRing s V
  let D := SectionRing t (f ⁻¹ᵁ V)
  let r := sectionRes s i
  let r' := sectionRes t ((Opens.map f.base).map i)
  letI : Algebra A B := fibreAlgebra U
  letI : Algebra C D := fibreAlgebra V
  letI : Algebra A C := r.toRingHom.toAlgebra
  letI : Algebra B D := r'.toRingHom.toAlgebra
  letI : Algebra A D := ((f.app V).hom.comp r.toRingHom).toAlgebra
  letI : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a =>
    ConcreteCategory.congr_hom (f.naturality i.op) a
  letI : Algebra.IsPushout A C B D :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_affineSections f hU hV i).flip
  letI := fibreFinite (s := s) (t := t) (f := f) hU
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  letI := fibreFinite (s := s) (t := t) (f := f) hV
  letI := fibreEtale (s := s) (t := t) (f := f) hV
  exact (finiteEtaleAlgebraTrace_baseChange (S := C) (C := D) A B b).symm

/-- Trace of forms along a finite étale morphism over an affine open. -/
def affineFormTrace (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    FormsOn t (f ⁻¹ᵁ U) n →+ FormsOn s U n :=
  letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := fibreAlgebra U
  letI := fibreScalarTower hf U
  letI := fibreFinite (s := s) (t := t) (f := f) hU
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  (finiteEtaleFormTrace k (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) n).toAddMonoidHom

theorem affineFormTrace_smul (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ)
    (a : SectionRing s U) (ω : FormsOn t (f ⁻¹ᵁ U) n) :
    affineFormTrace hf hU n (sectionPullback hf U a • ω) = a • affineFormTrace hf hU n ω := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  letI : Algebra A B := fibreAlgebra U
  letI := fibreScalarTower hf U
  letI := fibreFinite (s := s) (t := t) (f := f) hU
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  exact (finiteEtaleFormTrace k A B n).map_smul a ω

theorem affineFormTrace_smul_pullback (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U)
    (n : ℕ) (b : SectionRing t (f ⁻¹ᵁ U)) (ω : FormsOn s U n) :
    affineFormTrace hf hU n (b • ExteriorDifferentials.map (sectionPullback hf U) n ω) =
      affineSectionTrace (f := f) s t hU b • ω := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  letI : Algebra A B := fibreAlgebra U
  letI := fibreScalarTower hf U
  letI := fibreFinite (s := s) (t := t) (f := f) hU
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  rw [← algebraFormPullback_eq_map k A B (sectionPullback hf U) rfl]
  exact finiteEtaleFormTrace_smul_pullback k A B n b ω

private theorem affineForms_induction (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U)
    (n : ℕ) {P : FormsOn t (f ⁻¹ᵁ U) n → Prop}
    (h0 : P 0) (ha : ∀ y z, P y → P z → P (y + z))
    (hb : ∀ (b : SectionRing t (f ⁻¹ᵁ U)) (ω : FormsOn s U n),
      P (b • ExteriorDifferentials.map (sectionPullback hf U) n ω))
    (y : FormsOn t (f ⁻¹ᵁ U) n) : P y := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  letI : Algebra A B := fibreAlgebra U
  letI := fibreScalarTower hf U
  letI := fibreEtale (s := s) (t := t) (f := f) hU
  let h := algebraFormPullback_isBaseChange k A B n
  obtain ⟨z, rfl⟩ := h.equiv.surjective y
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact h0
  | add a b ha' hb' => rw [map_add]; exact ha _ _ ha' hb'
  | tmul b ω =>
    rw [h.equiv_tmul, algebraFormPullback_eq_map k A B (sectionPullback hf U) rfl]
    exact hb b ω

/-- Trace of forms commutes with restriction between affine opens. -/
theorem affineFormTrace_res (hf : f ≫ s = t) {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (i : V ⟶ U) (n : ℕ) (y : FormsOn t (f ⁻¹ᵁ U) n) :
    ExteriorDifferentials.map (sectionRes s i) n (affineFormTrace hf hU n y) =
      affineFormTrace hf hV n
        (ExteriorDifferentials.map (sectionRes t ((Opens.map f.base).map i)) n y) := by
  refine affineForms_induction hf hU n (P := fun ω =>
    ExteriorDifferentials.map (sectionRes s i) n (affineFormTrace hf hU n ω) =
      affineFormTrace hf hV n (ExteriorDifferentials.map
        (sectionRes t ((Opens.map f.base).map i)) n ω)) (by simp only [map_zero]) ?_ ?_ y
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro b ω
    rw [affineFormTrace_smul_pullback, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      formsOn_pullback_natural, affineFormTrace_smul_pullback]
    exact congrArg (fun a : SectionRing s V => a • ExteriorDifferentials.map (sectionRes s i) n ω)
      (affineSectionTrace_res (f := f) hU hV i b)

end GlobalTheory.SchemeCohomology
