import GaloisForLFunctions.RHTower.Deninger.DeningerThreeTermOperations
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The totalization of the three-term arithmetic complex

The three-term arithmetic complex is the cochain complex with the generic source in degrees zero
and one and the finite-plus-real boundary object in degree two, and nothing else.  Its terms vanish
in every degree above two, hence so does its homology: this is the vanishing of arithmetic
cohomology outside degrees `0, 1, 2`.  In the three surviving degrees the homology of the
totalization is the kernel of the generic differential, the residue kernel modulo generic
boundaries, and the boundary object modulo the residue image.

* `deningerThreeTermCochain` : the totalization.
* `deningerThreeTermCochain_isZero_homology` : vanishing outside degrees `0, 1, 2`.
* `deningerThreeTermCochain_homologyIso0/1/2` : the three surviving groups.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

section Totalization

universe u v

variable {R : Type u} [CommRing R] {A0 A1 A2 : Type v}
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)

/-- **The totalization of the three-term arithmetic complex**: the cochain complex with the generic
source in degrees zero and one, the boundary object in degree two, and zero in every other
degree. -/
noncomputable def deningerThreeTermCochain : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.mk (ModuleCat.of R A0) (ModuleCat.of R A1) (ModuleCat.of R A2)
    (ModuleCat.ofHom C.d0) (ModuleCat.ofHom C.d1)
    (by
      ext x
      exact LinearMap.congr_fun C.d1_comp_d0 x)
    (fun _ => ⟨ModuleCat.of R PUnit.{v + 1}, 0, by simp⟩)

theorem deningerThreeTermCochain_X_zero :
    (deningerThreeTermCochain C).X 0 = ModuleCat.of R A0 := rfl

theorem deningerThreeTermCochain_X_one :
    (deningerThreeTermCochain C).X 1 = ModuleCat.of R A1 := rfl

theorem deningerThreeTermCochain_X_two :
    (deningerThreeTermCochain C).X 2 = ModuleCat.of R A2 := rfl

/-- **The totalization has no terms above degree two.** -/
theorem deningerThreeTermCochain_X_add_three (k : ℕ) :
    (deningerThreeTermCochain C).X (k + 3) = ModuleCat.of R PUnit.{v + 1} := rfl

theorem deningerThreeTermCochain_isZero_X {n : ℕ} (hn : 3 ≤ n) :
    IsZero ((deningerThreeTermCochain C).X n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [deningerThreeTermCochain_X_add_three]
  exact ModuleCat.isZero_of_subsingleton _

/-- **Arithmetic cohomology vanishes outside degrees `0, 1, 2`.** -/
theorem deningerThreeTermCochain_isZero_homology {n : ℕ} (hn : 3 ≤ n) :
    IsZero ((deningerThreeTermCochain C).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ ((deningerThreeTermCochain C).sc n)
    (deningerThreeTermCochain_isZero_X C hn)

theorem deningerThreeTermCochain_d_zero_one :
    (deningerThreeTermCochain C).d 0 1 = ModuleCat.ofHom C.d0 :=
  CochainComplex.mk_d_1_0 _ _ _ _ _ _ _

theorem deningerThreeTermCochain_d_one_two :
    (deningerThreeTermCochain C).d 1 2 = ModuleCat.ofHom C.d1 :=
  CochainComplex.mk_d_2_0 _ _ _ _ _ _ _

end Totalization

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits

section TotalizationHomology

universe u v

variable {R : Type u} [CommRing R] {A0 A1 A2 : Type v}
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)

/-- The degree-one short complex of the totalization, with its differentials named. -/
noncomputable def deningerThreeTermSC1 : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom C.d0) (ModuleCat.ofHom C.d1)
    (by
      ext x
      exact LinearMap.congr_fun C.d1_comp_d0 x)

/-- The degree-zero short complex of the totalization. -/
noncomputable def deningerThreeTermSC0 : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (0 : ModuleCat.of R A0 ⟶ ModuleCat.of R A0) (ModuleCat.ofHom C.d0) (by simp)

/-- The degree-two short complex of the totalization. -/
noncomputable def deningerThreeTermSC2 : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom C.d1)
    (0 : ModuleCat.of R A2 ⟶ ModuleCat.of R PUnit.{v + 1}) (by simp)

theorem deningerThreeTermCochain_d_two_three :
    (deningerThreeTermCochain C).d 2 3 = 0 := by
  have h : (deningerThreeTermCochain C).d 2 3 =
      (0 : ModuleCat.of R A2 ⟶ ModuleCat.of R PUnit.{v + 1}) ≫
        eqToHom (by rfl : (deningerThreeTermCochain C).X 3 = (deningerThreeTermCochain C).X 3) := by
    rfl
  rw [h, zero_comp]
  rfl

theorem deningerThreeTermCochain_d_zero_zero :
    (deningerThreeTermCochain C).d 0 0 = 0 :=
  (deningerThreeTermCochain C).shape 0 0 (by simp)

set_option backward.isDefEq.respectTransparency false in
noncomputable def deningerThreeTermCochain_scIso1 :
    (deningerThreeTermCochain C).sc' 0 1 2 ≅ deningerThreeTermSC1 C :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_zero_one C).symm)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_one_two C).symm)

set_option backward.isDefEq.respectTransparency false in
noncomputable def deningerThreeTermCochain_scIso0 :
    (deningerThreeTermCochain C).sc' 0 0 1 ≅ deningerThreeTermSC0 C :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_zero_zero C).symm)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_zero_one C).symm)

set_option backward.isDefEq.respectTransparency false in
noncomputable def deningerThreeTermCochain_scIso2 :
    (deningerThreeTermCochain C).sc' 1 2 3 ≅ deningerThreeTermSC2 C :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_one_two C).symm)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (deningerThreeTermCochain_d_two_three C).symm)

/-- The image of the generic differential inside the residue cocycles, in the two descriptions. -/
theorem deningerThreeTermRange_eq :
    LinearMap.range (C.d0.codRestrict (LinearMap.ker C.d1)
        (fun a => LinearMap.congr_fun C.d1_comp_d0 a))
      = C.boundaries1.comap C.cycles1.subtype := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- **Degree one of the totalization is the arithmetic `H¹`.** -/
noncomputable def deningerThreeTermCochain_homologyIso1 :
    (deningerThreeTermCochain C).homology 1 ≅ ModuleCat.of R C.H1 :=
  (deningerThreeTermCochain C).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (deningerThreeTermCochain_scIso1 C) ≪≫
    (deningerThreeTermSC1 C).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (deningerThreeTermRange_eq C)).toModuleIso

/-- **Degree zero of the totalization is the arithmetic `H⁰`.** -/
noncomputable def deningerThreeTermCochain_homologyIso0 :
    (deningerThreeTermCochain C).homology 0 ≅ ModuleCat.of R C.H0 :=
  (deningerThreeTermCochain C).homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (deningerThreeTermCochain_scIso0 C) ≪≫
    (deningerThreeTermSC0 C).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEqBot _ (by
      refine le_antisymm ?_ bot_le
      rintro _ ⟨a, rfl⟩
      exact Subtype.ext rfl)).toModuleIso

theorem deningerThreeTermSC2_ker :
    LinearMap.ker (deningerThreeTermSC2 C).g.hom = ⊤ := by
  show LinearMap.ker (0 : A2 →ₗ[R] PUnit.{v + 1}) = ⊤
  exact LinearMap.ker_zero

/-- **Degree two of the totalization is the arithmetic `H²`.** -/
noncomputable def deningerThreeTermCochain_homologyIso2 :
    (deningerThreeTermCochain C).homology 2 ≅ ModuleCat.of R C.H2 :=
  (deningerThreeTermCochain C).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (deningerThreeTermCochain_scIso2 C) ≪≫
    (deningerThreeTermSC2 C).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ C.boundaries2
      ((LinearEquiv.ofEq _ ⊤ (deningerThreeTermSC2_ker C)).trans Submodule.topEquiv)
      (by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨w, ⟨a, rfl⟩, rfl⟩
          exact ⟨a, rfl⟩
        · rintro _ ⟨a, rfl⟩
          exact ⟨(deningerThreeTermSC2 C).moduleCatToCycles a, ⟨a, rfl⟩, rfl⟩)).toModuleIso

end TotalizationHomology

end RHTower
