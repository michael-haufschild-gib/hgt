import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.SchemeTangentCriteria
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! The group law on dual-number tangent vectors is addition in the
square-zero coordinate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpTangent

open TangentCrit

universe u

abbrev Sp (R : Type) [CommRing R] := Spec (CommRingCat.of R)

private abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    Sp R' ⟶ Sp R := Spec.map (CommRingCat.ofHom f)

abbrev epsR (R : Type) [CommRing R] : Over (Sp R) := Over.mk (dualBase R)

variable {R : Type} [CommRing R] in
private def epsScaleR (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

/-- The zero section of the dual-number scheme maps to the group unit. -/
def IsTangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (w : epsR R ⟶ G) : Prop :=
  dualPt R ≫ w.left = η[G].left

/-- Two ring maps with jointly zero kernel detect maps from their common
spectrum when the first spectrum map is surjective. -/
private theorem hom_ext_of_ker_inf {D E₁ E₂ : CommRingCat.{u}} (p₁ : D ⟶ E₁) (p₂ : D ⟶ E₂)
    (hs : Function.Surjective (Spec.map p₁)) (h : ∀ d, p₁ d = 0 → p₂ d = 0 → d = 0)
    {X : Scheme.{u}} {g g' : Spec D ⟶ X} (h₁ : Spec.map p₁ ≫ g = Spec.map p₁ ≫ g')
    (h₂ : Spec.map p₂ ≫ g = Spec.map p₂ ≫ g') : g = g' := by
  have hsurj : Function.Surjective (equalizer.ι g g') := by
    intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨equalizer.lift _ h₁ z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have : IsClosedImmersion (equalizer.ι g g') :=
    .of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have key : ∀ {E : CommRingCat.{u}} (p : D ⟶ E) (_ : Spec.map p ≫ g = Spec.map p ≫ g')
      (d : Γ(Spec D, ⊤)), (equalizer.ι g g').appTop d = 0 → p ((Scheme.ΓSpecIso D).hom d) = 0 := by
    intro E p hp d hd
    have e : (Spec.map p).appTop d = 0 := by
      rw [← equalizer.lift_ι _ hp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hd, map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, e, map_zero]
  have : IsIso (equalizer.ι g g') := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).mpr ?_)
    intro d hd
    apply (Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h _ (key p₁ h₁ d hd) (key p₂ h₂ d hd)
  rw [← cancel_epi (equalizer.ι g g'), equalizer.condition]

section Ring

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]

def epsZero (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (dualPt R) (dualPt_dualBase R)

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

@[simp] lemma epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := rfl

lemma isTangent_iff (w : epsR R ⟶ G) : IsTangent w ↔ epsZero R ≫ w = 1 := by
  rw [← one_eq_one]
  exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩

lemma isTangent_comp {w : epsR R ⟶ G} (hw : IsTangent w) (f : G ⟶ H) [IsMonHom f] :
    IsTangent (w ≫ f) := by
  rw [isTangent_iff] at hw ⊢
  rw [← Category.assoc, hw, one_comp]

def tangentMap (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    {w : epsR R ⟶ H // IsTangent w} := ⟨w.1 ≫ f, isTangent_comp w.2 f⟩

@[simp] lemma tangentMap_coe (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    (tangentMap f w).1 = w.1 ≫ f := rfl

@[reassoc]
lemma epsZero_epsScale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp [epsScaleR]

@[reassoc]
lemma epsScale_mul (a b : R) : epsScale a ≫ epsScale b = epsScale (a * b) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, _root_.mul_assoc]

lemma epsScale_one : epsScale (1 : R) = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR]

lemma epsScale_zero : epsScale (0 : R) = toUnit _ ≫ epsZero R := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

lemma isTangent_epsScale (c : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    IsTangent (epsScale c ≫ w) := by
  rw [isTangent_iff] at hw ⊢
  rw [epsZero_epsScale_assoc, hw]

lemma epsScale_zero_comp {w : epsR R ⟶ G} (hw : IsTangent w) : epsScale 0 ≫ w = 1 := by
  rw [epsScale_zero, Category.assoc, (isTangent_iff w).mp hw, comp_one]

def sqZeroMap {M N : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (l : M →ₗ[R] N) :
    Over.mk (spMap (algebraMap R (TrivSqZeroExt R N))) ⟶
      Over.mk (spMap (algebraMap R (TrivSqZeroExt R M))) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMap_comp_eq {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] (l : R →ₗ[R] M) (l' : M →ₗ[R] R) :
    sqZeroMap l' ≫ sqZeroMap l = epsScale (l' (l 1)) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [epsScaleR, this]

/-- A tangent vector applied to a sum of square-zero parameters is the
product of the two tangent-group points. -/
theorem epsScale_add_comp (a b : R) {w : epsR R ⟶ G} (hw : IsTangent w) :
    epsScale (a + b) ≫ w = (epsScale a ≫ w) * (epsScale b ≫ w) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : sqZeroMap (i₁ + i₂) ≫ w = (sqZeroMap i₁ ≫ w) * (sqZeroMap i₂ ≫ w) := by
    ext1
    refine hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.fst R R R) ≫ _ = sqZeroMap (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMap (LinearMap.snd R R R) ≫ _ = sqZeroMap (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMap_comp_eq]
      simp [i₁, i₂, epsScale_zero_comp hw]
  have := congrArg (sqZeroMap (a • LinearMap.fst R R R + b • LinearMap.snd R R R) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMap_comp_eq] at this
  simpa [i₁, i₂] using this

/-- The differential of multiplication by `n` at the identity is
scalar multiplication by `n`. -/
theorem pow_eq_epsScale_comp {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    w ^ n = epsScale (n : R) ≫ w := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, epsScale_zero_comp hw]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, epsScale_add_comp _ _ hw, ih, epsScale_one, Category.id_comp]

end Ring

end GlobalTheory.GrpTangent
