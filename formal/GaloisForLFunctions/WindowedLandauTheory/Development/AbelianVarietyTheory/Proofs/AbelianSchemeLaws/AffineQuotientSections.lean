import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineBaseChangeSectionRings
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Tactic.LinearCombination

/-! On affine opens, pullback to a quotient of the base reduces functions modulo the
extended ideal. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.AbLaw.SmallExtension

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}

section Quotient

variable {I : Ideal R} {π : Y ⟶ X} {f : Y ⟶ Spec (CommRingCat.of (R ⧸ I))}
  (H : IsPullback π f p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  {W : X.Opens} (hW : IsAffineOpen W)

include H hW in
theorem app_surjective_of_quotient : Function.Surjective (π.app W) := by
  have hq := IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  haveI : IsClosedImmersion π := MorphismProperty.of_isPullback H.flip hq
  exact π.app_surjective W hW

/-- The kernel on affine sections is the extension of the base ideal. -/
theorem ker_app_of_quotient :
    letI := sectionAlgebra p W
    RingHom.ker (π.app W).hom = I.map (algebraMap R Γ(X, W)) := by
  let A := Γ(X, W)
  letI := sectionAlgebra p W
  letI := sectionAlgebra f (π ⁻¹ᵁ W)
  let J := I.map (algebraMap R A)
  have hp := isPushout_sectionAlgebra H hW rfl
  let l : R ⧸ I →+* A ⧸ J := Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp (algebraMap R A)) fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)
  have hl : CommRingCat.ofHom (algebraMap R (R ⧸ I)) ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    ext r
    rfl
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have e := ConcreteCategory.congr_hom (hp.inr_desc _ _ hl) x
    change (hp.desc _ _ hl) (π.appLE W (π ⁻¹ᵁ W) le_rfl x) = Ideal.Quotient.mk J x at e
    rw [Scheme.Hom.appLE_eq_app, show π.app W x = 0 from hx, map_zero] at e
    exact e.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change π.app W (algebraMap R A r) = 0
    rw [Scheme.Hom.app_eq_appLE, appLE_base_algebraMap H.w le_rfl,
      show algebraMap R (R ⧸ I) r = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

end Quotient

section Principal

variable {ε : R} {π : Y ⟶ X} {f : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
  (H : IsPullback π f p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
  {W : X.Opens} (hW : IsAffineOpen W)

theorem exists_eq_mul_of_app_eq_zero {x : Γ(X, W)} (hx : π.app W x = 0) :
    letI := sectionAlgebra p W
    ∃ y, x = algebraMap R Γ(X, W) ε * y := by
  letI := sectionAlgebra p W
  have hm : x ∈ RingHom.ker (π.app W).hom := hx
  rw [ker_app_of_quotient H hW, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hm
  exact hm

theorem isUnit_of_app_of_square_zero (hε : ε * ε = 0) {x : Γ(X, W)}
    (hx : IsUnit (π.app W x)) : IsUnit x := by
  letI := sectionAlgebra p W
  obtain ⟨b, hb⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := app_surjective_of_quotient H hW b
  obtain ⟨c, hc⟩ := exists_eq_mul_of_app_eq_zero H hW
    (x := x * y - 1) (by rw [map_sub, map_mul, hb, map_one, sub_self])
  let e := algebraMap R Γ(X, W) ε
  have he : e * e = 0 := by rw [← map_mul, hε, map_zero]
  have hunit : IsUnit (1 + e * c) :=
    IsUnit.of_mul_eq_one (1 - e * c) (by linear_combination -(c * c) * he)
  change x * y - 1 = e * c at hc
  rw [← hc, add_sub_cancel] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end Principal

section Flat

variable [IsLocalRing R] {ε : R}

private theorem mem_map_maximalIdeal_of_mul_eq_zero {A : Type} [CommRing A] [Algebra R A]
    [Module.Flat R A] (hne : ε ≠ 0) {a : A} (ha : algebraMap R A ε * a = 0) :
    a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
  obtain ⟨n, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := R) (M := A) (f := fun _ : Unit => ε) (x := fun _ => a)
    (by rwa [Fintype.sum_unique, Algebra.smul_def])
  rw [show a = ∑ j, c () j • y j from hy ()]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  have he := hc j
  rw [Fintype.sum_unique] at he
  exact fun hu => hne (hu.mul_left_eq_zero.1 he)

private theorem mul_eq_zero_of_mem_map {A : Type} [CommRing A] [Algebra R A]
    (hε : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) {x : A}
    (hx : x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    algebraMap R A ε * x = 0 := by
  have h : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤
      LinearMap.ker (LinearMap.mulLeft A (algebraMap R A ε)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap R A ε * algebraMap R A a = 0
    rw [mul_comm, ← map_mul, hε a ha, map_zero]
  exact h hx

variable {π : Y ⟶ X} {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
  (H : IsPullback π f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  {W : X.Opens} (hW : IsAffineOpen W)

/-- Multiplication by a nonzero small-extension parameter on a flat affine chart has kernel
equal to reduction to the closed fibre. -/
theorem mul_scalar_eq_zero_iff [Flat p] (hne : ε ≠ 0)
    (hε : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) (x : Γ(X, W)) :
    letI := sectionAlgebra p W
    algebraMap R Γ(X, W) ε * x = 0 ↔ π.app W x = 0 := by
  letI := sectionAlgebra p W
  haveI : Module.Flat R Γ(X, W) := show (algebraMap R Γ(X, W)).Flat from
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (p.flat_appLE (isAffineOpen_top _) hW le_top)
  change _ ↔ x ∈ RingHom.ker (π.app W).hom
  rw [ker_app_of_quotient H hW]
  exact ⟨fun hx => mem_map_maximalIdeal_of_mul_eq_zero hne hx, mul_eq_zero_of_mem_map hε⟩

end Flat

end GlobalTheory.AbLaw.SmallExtension
