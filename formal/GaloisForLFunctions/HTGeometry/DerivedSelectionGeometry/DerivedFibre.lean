import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.TwoTermResolution

/-!
# `Ext` and `Tor` of a module with a two-term projective resolution

For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of modules with `S.X₁` and `S.X₂`
projective, the derived functors of `S.X₃` are computed by the length-one resolution
`S.X₁ ⟶ S.X₂`:

* `extOneIso` — `Ext¹(S.X₃, Y) ≅ (S.X₁ ⟶ Y) ⧸ range (S.f ≫ ·)`;
* `isZero_ext_add_two` — `Extⁿ⁺²(S.X₃, Y) = 0`;
* `torOneIso` — `Tor₁(S.X₃, Y) ≅ ker (S.f ⊗ Y)`;
* `isZero_tor_add_two` — `Torₙ₊₂(S.X₃, Y) = 0`.

The two module-theoretic homology lemmas used throughout are

* `homologyIsoQuotRange` — a short complex of modules whose third term is trivial has homology the
  cokernel of its first map;
* `homologyIsoKer` — a short complex of modules whose first term is trivial has homology the kernel
  of its second map.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits Opposite

universe u

section HomologyOfModules

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))

theorem ker_g_eq_top_of_subsingleton (h3 : Subsingleton S.X₃) :
    LinearMap.ker S.g.hom = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  simpa using h3.elim (S.g x) 0

/-- When the third term is trivial, the cycles of a short complex of modules are everything. -/
noncomputable def kerTopEquiv (h3 : Subsingleton S.X₃) :
    ↥(LinearMap.ker S.g.hom) ≃ₗ[R] S.X₂ :=
  (LinearEquiv.ofEq _ _ (ker_g_eq_top_of_subsingleton S h3)).trans Submodule.topEquiv

@[simp] theorem kerTopEquiv_apply (h3 : Subsingleton S.X₃) (v : LinearMap.ker S.g.hom) :
    kerTopEquiv S h3 v = (v : S.X₂) := rfl

theorem map_range_moduleCatToCycles (h3 : Subsingleton S.X₃) :
    Submodule.map (kerTopEquiv S h3 : ↥(LinearMap.ker S.g.hom) →ₗ[R] S.X₂)
        (LinearMap.range S.moduleCatToCycles) = LinearMap.range S.f.hom := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨S.moduleCatToCycles x, ⟨x, rfl⟩, rfl⟩

/-- **Homology of a short complex of modules with trivial third term** is the cokernel of the
first map. -/
noncomputable def homologyIsoQuotRange (h3 : Subsingleton S.X₃) :
    S.homology ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (kerTopEquiv S h3)
      (map_range_moduleCatToCycles S h3)).toModuleIso

theorem range_moduleCatToCycles_eq_bot_of_subsingleton (h1 : Subsingleton S.X₁) :
    LinearMap.range S.moduleCatToCycles = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro v ⟨x, rfl⟩
  rw [Submodule.mem_bot, h1.elim x 0, map_zero]

/-- **Homology of a short complex of modules with trivial first term** is the kernel of the second
map. -/
noncomputable def homologyIsoKer (h1 : Subsingleton S.X₁) :
    S.homology ≅ ModuleCat.of R (LinearMap.ker S.g.hom) :=
  S.moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEqBot _ (range_moduleCatToCycles_eq_bot_of_subsingleton S h1)).toModuleIso

end HomologyOfModules

section KerTransport

variable {R : Type u} [CommRing R] {A B C D : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- **Kernels along an isomorphic factorisation.**  If `a = c ∘ b ∘ e` with `e` and `c`
isomorphisms, then `e` restricts to an isomorphism `ker a ≃ ker b`. -/
noncomputable def kerEquivOfComp (a : A →ₗ[R] D) (b : B →ₗ[R] C) (e : A ≃ₗ[R] B) (c : C ≃ₗ[R] D)
    (h : ∀ x, a x = c (b (e x))) :
    ↥(LinearMap.ker a) ≃ₗ[R] ↥(LinearMap.ker b) := by
  refine LinearEquiv.ofBijective
    ((e : A →ₗ[R] B).restrict (p := LinearMap.ker a) (q := LinearMap.ker b) fun x hx => ?_)
    ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    have h0 : c (b (e x)) = 0 := by rw [← h x, hx]
    have h1 : b (e x) = 0 := by
      have := congrArg c.symm h0
      simpa using this
    simpa using h1
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  · rintro ⟨w, hw⟩
    refine ⟨⟨e.symm w, ?_⟩, Subtype.ext (by simp)⟩
    rw [LinearMap.mem_ker, h, e.apply_symm_apply, LinearMap.mem_ker.1 hw, map_zero]

end KerTransport

section Ext

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)} (Y : ModuleCat.{u} R)

/-- The cochain complex of a two-term resolution against a fixed target. -/
noncomputable abbrev twoTermYoneda : CochainComplex (ModuleCat.{u} R) ℕ :=
  (twoTermCplx S).linearYonedaObj R Y

theorem subsingleton_twoTermYoneda_X (n : ℕ) (h : 2 ≤ n) :
    Subsingleton ((twoTermYoneda (S := S) Y).X n) :=
  ⟨fun f g => (isZero_twoTermCplx_X S n h).eq_of_src f g⟩

theorem range_twoTermYoneda_d :
    LinearMap.range ((twoTermYoneda (S := S) Y).d 0 1).hom
      = LinearMap.range (Linear.leftComp R Y ((twoTermCplx S).d 1 0)) := rfl

/-- Precomposition with the degree-one identification of the two-term complex. -/
noncomputable def yonedaShift₁ :
    ((twoTermCplx S).X 1 ⟶ Y) ≃ₗ[R] (S.X₁ ⟶ Y) where
  toFun φ := (twoTermXIso₁ S).inv ≫ φ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  invFun ψ := (twoTermXIso₁ S).hom ≫ ψ
  left_inv φ := by simp
  right_inv ψ := by simp

theorem map_range_yonedaShift₁ :
    Submodule.map (yonedaShift₁ (S := S) Y : ((twoTermCplx S).X 1 ⟶ Y) →ₗ[R] (S.X₁ ⟶ Y))
        (LinearMap.range (Linear.leftComp R Y ((twoTermCplx S).d 1 0)))
      = LinearMap.range (Linear.leftComp R Y S.f) := by
  ext ψ
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨w, ⟨φ, rfl⟩, rfl⟩
    refine ⟨(twoTermXIso₀ S).inv ≫ φ, ?_⟩
    show S.f ≫ (twoTermXIso₀ S).inv ≫ φ
        = (twoTermXIso₁ S).inv ≫ (twoTermCplx S).d 1 0 ≫ φ
    rw [twoTermCplx_d]
    simp
  · rintro ⟨φ, rfl⟩
    refine ⟨(twoTermCplx S).d 1 0 ≫ (twoTermXIso₀ S).hom ≫ φ, ⟨(twoTermXIso₀ S).hom ≫ φ, rfl⟩, ?_⟩
    show (twoTermXIso₁ S).inv ≫ (twoTermCplx S).d 1 0 ≫ (twoTermXIso₀ S).hom ≫ φ = S.f ≫ φ
    rw [twoTermCplx_d]
    simp

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
include hS

/-- **`Ext¹` from a two-term projective resolution.**  `Ext¹(S.X₃, Y)` is the cokernel of
precomposition with `S.f` on `Hom(S.X₂, Y) → Hom(S.X₁, Y)`. -/
noncomputable def extOneIso :
    ((Ext R (ModuleCat.{u} R) 1).obj (op S.X₃)).obj Y ≅
      ModuleCat.of R ((S.X₁ ⟶ Y) ⧸ LinearMap.range (Linear.leftComp R Y S.f)) :=
  (twoTermResolution hS).isoExt 1 Y ≪≫
    (twoTermYoneda (S := S) Y).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    homologyIsoQuotRange _ (subsingleton_twoTermYoneda_X Y 2 (by omega)) ≪≫
    (Submodule.Quotient.equiv _ _ (yonedaShift₁ (S := S) Y)
      (by
        rw [show LinearMap.range
              ((HomologicalComplex.sc' (twoTermYoneda (S := S) Y) 0 1 2).f).hom
            = LinearMap.range (Linear.leftComp R Y ((twoTermCplx S).d 1 0)) from
              range_twoTermYoneda_d Y]
        exact map_range_yonedaShift₁ Y)).toModuleIso

/-- **Higher `Ext` vanishing.**  A module with a length-one projective resolution has no `Ext`
beyond degree one. -/
theorem isZero_ext_add_two (n : ℕ) :
    IsZero (((Ext R (ModuleCat.{u} R) (n + 2)).obj (op S.X₃)).obj Y) := by
  refine IsZero.of_iso ?_ ((twoTermResolution hS).isoExt (n + 2) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  haveI := subsingleton_twoTermYoneda_X (S := S) Y (n + 2) (by omega)
  exact HomologicalComplex.ExactAt.of_isZero
    (ModuleCat.isZero_of_subsingleton (M := (twoTermYoneda (S := S) Y).X (n + 2)))

end Ext

section Tor

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)} (Y : ModuleCat.{u} R)

/-- Tensoring on the right by a fixed module. -/
noncomputable abbrev tensorRightFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj Y

/-- The tensored two-term complex. -/
noncomputable abbrev twoTermTensor : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((tensorRightFunctor Y).mapHomologicalComplex _).obj (twoTermCplx S)

theorem subsingleton_twoTermTensor_X (n : ℕ) (h : 2 ≤ n) :
    Subsingleton ((twoTermTensor (S := S) Y).X n) :=
  ModuleCat.isZero_iff_subsingleton.1
    (Functor.map_isZero (tensorRightFunctor Y) (isZero_twoTermCplx_X S n h))

/-- Degree-one identification of the tensored two-term complex. -/
noncomputable def tensorIso₁ :
    (twoTermTensor (S := S) Y).X 1 ≅ (tensorRightFunctor Y).obj S.X₁ :=
  (tensorRightFunctor Y).mapIso (twoTermXIso₁ S)

/-- Degree-zero identification of the tensored two-term complex. -/
noncomputable def tensorIso₀ :
    (twoTermTensor (S := S) Y).X 0 ≅ (tensorRightFunctor Y).obj S.X₂ :=
  (tensorRightFunctor Y).mapIso (twoTermXIso₀ S)

theorem twoTermTensor_d_eq :
    (twoTermTensor (S := S) Y).d 1 0
      = (tensorIso₁ (S := S) Y).hom ≫
        (tensorRightFunctor Y).map S.f ≫ (tensorIso₀ (S := S) Y).inv := by
  show (tensorRightFunctor Y).map ((twoTermCplx S).d 1 0) = _
  rw [twoTermCplx_d, Functor.map_comp, Functor.map_comp]
  rfl

/-- Transport along the degree-one identification of the tensored complex. -/
noncomputable def tensorShift₁ :
    ↥(LinearMap.ker ((twoTermTensor (S := S) Y).d 1 0).hom) ≃ₗ[R]
      ↥(LinearMap.ker ((tensorRightFunctor Y).map S.f).hom) :=
  kerEquivOfComp _ _ (tensorIso₁ (S := S) Y).toLinearEquiv
    (tensorIso₀ (S := S) Y).symm.toLinearEquiv
    (fun x => by
      have h := congrArg (fun (m : ModuleCat.Hom _ _) => m.hom x) (twoTermTensor_d_eq (S := S) Y)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      simp only [Iso.toLinearEquiv_apply, Iso.symm_hom]
      exact h)

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
include hS

/-- **`Tor₁` from a two-term projective resolution.**  `Tor₁(S.X₃, Y)` is the kernel of
`S.f ⊗ Y`. -/
noncomputable def torOneIso :
    (((Tor' (ModuleCat.{u} R) 1).obj S.X₃).obj Y) ≅
      ModuleCat.of R (LinearMap.ker ((tensorRightFunctor Y).map S.f).hom) :=
  (twoTermResolution hS).isoLeftDerivedObj (tensorRightFunctor Y) 1 ≪≫
    (twoTermTensor (S := S) Y).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    homologyIsoKer _ (subsingleton_twoTermTensor_X Y 2 (by omega)) ≪≫
    (tensorShift₁ (S := S) Y).toModuleIso

/-- **Higher `Tor` vanishing.** -/
theorem isZero_tor_add_two (n : ℕ) :
    IsZero ((((Tor' (ModuleCat.{u} R) (n + 2)).obj S.X₃).obj Y)) := by
  refine IsZero.of_iso ?_
    ((twoTermResolution hS).isoLeftDerivedObj (tensorRightFunctor Y) (n + 2))
  show IsZero ((twoTermTensor (S := S) Y).homology (n + 2))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  haveI := subsingleton_twoTermTensor_X (S := S) Y (n + 2) (by omega)
  exact HomologicalComplex.ExactAt.of_isZero
    (ModuleCat.isZero_of_subsingleton (M := (twoTermTensor (S := S) Y).X (n + 2)))

end Tor

end GaloisForLFunctions.HTGeometry.DerivedSelection
