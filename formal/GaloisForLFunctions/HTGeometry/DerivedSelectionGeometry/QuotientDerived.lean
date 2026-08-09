import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.DerivedFibre

/-!
# Derived functors of a quotient by a regular scalar

Let `N` be a projective `R`-module and `t ∈ R` a scalar acting regularly on `N`.  The quotient
`N ⧸ tN` has the length-one free resolution `N --t--> N`, so its derived functors are the cokernel
and kernel of multiplication by `t`:

* `extOneSmulIso` — `Ext¹(N ⧸ tN, Y) ≅ Hom(N,Y) ⧸ t·Hom(N,Y)`;
* `torOneSmulIso` — `Tor₁(N ⧸ tN, Y) ≅ {z ∈ N ⊗ Y : t z = 0}`;
* `isZero_extSmul_add_two`, `isZero_torSmul_add_two` — everything above degree one vanishes;
* `torOneSmulIsoTensor` — when `t` annihilates `Y`, `Tor₁(N ⧸ tN, Y) ≅ N ⊗ Y`.

The transport lemmas `extCongrLeft` and `torCongrLeft` move these statements along an isomorphism
of the first variable.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits Opposite TensorProduct

universe u

section Transport

variable {R : Type u} [CommRing R]

/-- `Ext` transported along an isomorphism of the first variable. -/
noncomputable def extCongrLeft {X X' : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ)
    (Y : ModuleCat.{u} R) :
    ((Ext R (ModuleCat.{u} R) n).obj (op X)).obj Y ≅
      ((Ext R (ModuleCat.{u} R) n).obj (op X')).obj Y :=
  ((Ext R (ModuleCat.{u} R) n).mapIso e.symm.op).app Y

/-- `Tor` transported along an isomorphism of the first variable. -/
noncomputable def torCongrLeft {X X' : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ)
    (Y : ModuleCat.{u} R) :
    (((Tor' (ModuleCat.{u} R) n).obj X).obj Y) ≅ (((Tor' (ModuleCat.{u} R) n).obj X').obj Y) :=
  ((Tor' (ModuleCat.{u} R) n).mapIso e).app Y

end Transport

section QuotSmul

variable {R : Type u} [CommRing R] {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] (t : R)

/-- Multiplication by `t` commutes with any isomorphism, so it induces one on the quotients. -/
noncomputable def quotSmulRangeEquiv (e : M ≃ₗ[R] M') :
    (M ⧸ LinearMap.range (t • LinearMap.id : M →ₗ[R] M)) ≃ₗ[R]
      (M' ⧸ LinearMap.range (t • LinearMap.id : M' →ₗ[R] M')) :=
  Submodule.Quotient.equiv _ _ e (by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq]
    constructor
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨t • e.symm x, ⟨e.symm x, rfl⟩, by simp⟩)

theorem range_smul_id_eq_span (t : R) :
    LinearMap.range (t • LinearMap.id : R →ₗ[R] R) = (Ideal.span {t} : Ideal R) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul,
    Ideal.mem_span_singleton, dvd_def]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

end QuotSmul

section Setup

variable {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]
  {t : R} {p : Submodule R N}
  (hp : LinearMap.range (t • LinearMap.id : N →ₗ[R] N) = p) (ht : IsSMulRegular N t)

include ht in
theorem injective_smul_id : Function.Injective (t • LinearMap.id : N →ₗ[R] N) := ht

include hp ht in
theorem smulShortExact :
    (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).ShortExact :=
  presShortComplex_shortExact hp (injective_smul_id ht)

theorem presShortComplex_f_eq :
    (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).f = t • 𝟙 (ModuleCat.of R N) := rfl

variable (Y : ModuleCat.{u} R)

theorem leftComp_smul_id :
    Linear.leftComp R Y (t • 𝟙 (ModuleCat.of R N))
      = (t • LinearMap.id : (ModuleCat.of R N ⟶ Y) →ₗ[R] (ModuleCat.of R N ⟶ Y)) := by
  refine LinearMap.ext fun φ => ?_
  simp [Linear.leftComp]

theorem map_smul_id :
    (tensorRightFunctor Y).map (t • 𝟙 (ModuleCat.of R N))
      = t • 𝟙 ((tensorRightFunctor Y).obj (ModuleCat.of R N)) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

theorem leftComp_presShortComplex_f :
    Linear.leftComp R Y (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).f
      = (t • LinearMap.id : (ModuleCat.of R N ⟶ Y) →ₗ[R] (ModuleCat.of R N ⟶ Y)) :=
  leftComp_smul_id Y

theorem map_presShortComplex_f :
    (tensorRightFunctor Y).map (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).f
      = t • 𝟙 ((tensorRightFunctor Y).obj (ModuleCat.of R N)) :=
  map_smul_id Y

variable [Module.Projective R N]

include hp ht

/-- **`Ext¹` of a quotient by a regular scalar.** -/
noncomputable def extOneSmulIso :
    ((Ext R (ModuleCat.{u} R) 1).obj (op (ModuleCat.of R (N ⧸ p)))).obj Y ≅
      ModuleCat.of R ((ModuleCat.of R N ⟶ Y) ⧸
        LinearMap.range (t • LinearMap.id : (ModuleCat.of R N ⟶ Y) →ₗ[R] _)) :=
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₁ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  extOneIso Y (smulShortExact hp ht) ≪≫
    (Submodule.quotEquivOfEq _ _ (by rw [leftComp_presShortComplex_f]; rfl)).toModuleIso

/-- **Higher `Ext` of a quotient by a regular scalar vanishes.** -/
theorem isZero_extSmul_add_two (n : ℕ) :
    IsZero (((Ext R (ModuleCat.{u} R) (n + 2)).obj (op (ModuleCat.of R (N ⧸ p)))).obj Y) :=
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₁ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  isZero_ext_add_two Y (smulShortExact hp ht) n

/-- **`Tor₁` of a quotient by a regular scalar.** -/
noncomputable def torOneSmulIso :
    (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (N ⧸ p))).obj Y) ≅
      ModuleCat.of R (LinearMap.ker
        (t • LinearMap.id : ((tensorRightFunctor Y).obj (ModuleCat.of R N)) →ₗ[R] _)) :=
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₁ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  torOneIso Y (smulShortExact hp ht) ≪≫
    (LinearEquiv.ofEq _ _ (by rw [map_presShortComplex_f]; rfl)).toModuleIso

/-- **Higher `Tor` of a quotient by a regular scalar vanishes.** -/
theorem isZero_torSmul_add_two (n : ℕ) :
    IsZero ((((Tor' (ModuleCat.{u} R) (n + 2)).obj (ModuleCat.of R (N ⧸ p))).obj Y)) :=
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₁ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  haveI : Projective (presShortComplex (t • LinearMap.id : N →ₗ[R] N) p hp).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  isZero_tor_add_two Y (smulShortExact hp ht) n

end Setup

section Annihilated

variable {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]
  {t : R} {Y : Type u} [AddCommGroup Y] [Module R Y]

/-- A scalar annihilating one factor annihilates the tensor product. -/
theorem smul_tensor_eq_zero (hY : ∀ y : Y, t • y = 0) (z : N ⊗[R] Y) : t • z = 0 := by
  induction z with
  | zero => simp
  | tmul n y =>
      have h : t • (n ⊗ₜ[R] y) = n ⊗ₜ[R] (t • y) := by rw [tmul_smul]
      rw [h, hY y, tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

theorem ker_smul_id_eq_top (hY : ∀ y : Y, t • y = 0) :
    LinearMap.ker (t • LinearMap.id : (N ⊗[R] Y) →ₗ[R] (N ⊗[R] Y)) = ⊤ :=
  eq_top_iff.2 fun z _ => smul_tensor_eq_zero hY z

end Annihilated

end GaloisForLFunctions.HTGeometry.DerivedSelection
