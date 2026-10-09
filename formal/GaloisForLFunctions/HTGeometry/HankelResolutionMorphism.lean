import GaloisForLFunctions.HTGeometry.HankelResolutionGlobalSections
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The resolution morphism of the Hankel secant variety

The identification `A ≅ Γ(Y, 𝒪_Y)` of the secant ring with the global sections of the incidence
variety gives, through `Y → Spec Γ(Y, 𝒪_Y)`, a morphism `π : Y → Spec A`.

* `π^# : A → Γ(Y, 𝒪_Y)` is an isomorphism (`hankelResolution_appTop_isIso`).
* `π` is proper: composed with the closed immersion `Spec A → 𝔸^N` it is the structure map
  `Proj B → Spec B_0` (proper, `B` being of finite type over `B_0`) followed by the closed immersion
  `Spec B_0 → 𝔸^N` of the moments (`hankelResolution_isProper`).
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory

universe u

variable {K : Type u} [Field K] {r N : ℕ}

variable (K r N) in
/-- The secant ring `K[x_0, …, x_{N-1}] / secantIdealUpTo` of the first `j + r` moments (for
`j = N - r` the Hankel secant ring `K[x] / I_r`). -/
abbrev SecantRing (j : ℕ) := MvPolynomial (Fin N) K ⧸ secantIdealUpTo K N r j

variable {j : ℕ}

variable (K r N) in
/-- `A ≅ Γ(Y, 𝒪_Y)` in `CommRingCat`. -/
noncomputable def secantGlobalIso [CharZero K] (hj : j + r ≤ N) :
    CommRingCat.of (SecantRing K r N j) ≅ Γ(HankelY K r N j, ⊤) where
  hom := CommRingCat.ofHom (secantGlobalEquiv hj).toRingHom
  inv := CommRingCat.ofHom (secantGlobalEquiv hj).symm.toRingHom
  hom_inv_id := CommRingCat.hom_ext (RingHom.ext (secantGlobalEquiv hj).symm_apply_apply)
  inv_hom_id := CommRingCat.hom_ext (RingHom.ext (secantGlobalEquiv hj).apply_symm_apply)

variable (K r N) in
/-- **The resolution morphism** `Y → Spec A`. -/
noncomputable def hankelResolution [CharZero K] (hj : j + r ≤ N) :
    HankelY K r N j ⟶ Spec (CommRingCat.of (SecantRing K r N j)) :=
  (HankelY K r N j).toSpecΓ ≫ Spec.map (secantGlobalIso K r N hj).hom

/-- **`π^#` is an isomorphism on global sections.** -/
theorem hankelResolution_appTop_isIso [CharZero K] (hj : j + r ≤ N) :
    IsIso (hankelResolution K r N hj).appTop := by
  set e := secantGlobalIso K r N hj
  have h : (Spec.map e.hom).appTop = (Scheme.ΓSpecIso _).hom ≫ e.hom ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hankelResolution, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, h]
  infer_instance

instance finiteType_quotGrading (j : ℕ) :
    Algebra.FiniteType (quotGrading K r N j 0) (HankelQuot K r N j) := by
  haveI : IsScalarTower K (quotGrading K r N j 0) (HankelQuot K r N j) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := quotGrading K r N j 0)
      (A := HankelQuot K r N j) fun _ => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType K _ _

/-- `π` followed by `Spec A → 𝔸^N` is `Proj B → Spec B_0 → 𝔸^N`. -/
theorem hankelResolution_comp_quotient [CharZero K] (hj : j + r ≤ N) :
    hankelResolution K r N hj ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
      = Proj.toSpecZero (quotGrading K r N j) ≫
          Spec.map (CommRingCat.ofHom (momentToZero K r N j)) := by
  rw [toSpecZero_eq, hankelResolution, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rfl

/-- **`π` is proper.** -/
theorem hankelResolution_isProper [CharZero K] (hj : j + r ≤ N) :
    IsProper (hankelResolution K r N hj) := by
  set g : Spec (CommRingCat.of (SecantRing K r N j)) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) K)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
  have hcomp := hankelResolution_comp_quotient (K := K) hj
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (momentToZero K r N j))) :=
    IsClosedImmersion.spec_of_surjective _ (momentToZero_surjective j)
  haveI : IsProper (hankelResolution K r N hj ≫ g) := by
    rw [hcomp]
    infer_instance
  exact IsProper.of_comp _ g

end HTGeometry
