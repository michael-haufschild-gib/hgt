import Mathlib

/-!
# Two-term projective resolutions

A short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` in an abelian category whose two left terms
are projective is a projective resolution of `S.X₃` of length one.  This file packages that
statement as a `CategoryTheory.ProjectiveResolution`, which is what computes the derived functors
of `S.X₃`.

* `twoTermCplx` — the two-term chain complex `S.X₁ ⟶ S.X₂` in degrees `1, 0`;
* `twoTermPi` — the augmentation to `S.X₃` in degree `0`;
* `twoTermResolution` — the projective resolution.

The second half specialises this to modules: for an injective map `f : M →ₗ[R] N` of projective
modules and a submodule `p = range f`, the presentation `M --f--> N ↠ N ⧸ p` is a projective
resolution of `N ⧸ p`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits

universe v u

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)

theorem rel10 : (ComplexShape.down ℕ).Rel 1 0 := by simp

/-- The two-term complex `S.X₁ ⟶ S.X₂` in degrees `1` and `0`. -/
noncomputable def twoTermCplx : ChainComplex C ℕ :=
  HomologicalComplex.double S.f rel10

/-- Degree-one identification. -/
noncomputable def twoTermXIso₁ : (twoTermCplx S).X 1 ≅ S.X₁ :=
  HomologicalComplex.doubleXIso₀ S.f rel10

/-- Degree-zero identification. -/
noncomputable def twoTermXIso₀ : (twoTermCplx S).X 0 ≅ S.X₂ :=
  HomologicalComplex.doubleXIso₁ S.f rel10 (by decide)

theorem twoTermCplx_d :
    (twoTermCplx S).d 1 0 = (twoTermXIso₁ S).hom ≫ S.f ≫ (twoTermXIso₀ S).inv :=
  HomologicalComplex.double_d S.f rel10 (by decide)

theorem isZero_twoTermCplx_X (n : ℕ) (h : 2 ≤ n) : IsZero ((twoTermCplx S).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ (by omega) (by omega)

instance projective_twoTermCplx_X [Projective S.X₁] [Projective S.X₂] (n : ℕ) :
    Projective ((twoTermCplx S).X n) := by
  match n with
  | 0 => exact Projective.of_iso (twoTermXIso₀ S).symm inferInstance
  | 1 => exact Projective.of_iso (twoTermXIso₁ S).symm inferInstance
  | (n + 2) => exact (isZero_twoTermCplx_X S (n + 2) (by omega)).projective

theorem twoTerm_d_comp_g : (twoTermXIso₀ S).hom ≫ S.g = (twoTermXIso₀ S).hom ≫ S.g := rfl

theorem twoTermCplx_d_comp_g : (twoTermCplx S).d 1 0 ≫ (twoTermXIso₀ S).hom ≫ S.g = 0 := by
  rw [twoTermCplx_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, S.zero, comp_zero]

/-- The augmentation of the two-term complex onto `S.X₃`. -/
noncomputable def twoTermPi :
    twoTermCplx S ⟶ (ChainComplex.single₀ C).obj S.X₃ :=
  ((twoTermCplx S).toSingle₀Equiv _).symm
    ⟨(twoTermXIso₀ S).hom ≫ S.g, by rw [twoTermCplx_d_comp_g]⟩

theorem twoTermPi_f0 : (twoTermPi S).f 0 = (twoTermXIso₀ S).hom ≫ S.g := by
  simp [twoTermPi]

theorem d10_comp_pi0 : (twoTermCplx S).d 1 0 ≫ (twoTermPi S).f 0 = 0 := by
  rw [← (twoTermPi S).comm 1 0, HomologicalComplex.single_obj_d, comp_zero]

theorem comm12 : (twoTermXIso₁ S).hom ≫ S.f = (twoTermCplx S).d 1 0 ≫ (twoTermXIso₀ S).hom := by
  rw [twoTermCplx_d]
  simp

theorem comm23 : (twoTermXIso₀ S).hom ≫ S.g = (twoTermPi S).f 0 ≫ (Iso.refl S.X₃).hom := by
  rw [twoTermPi_f0]
  simp

/-- The degree-zero comparison short complex is isomorphic to `S` itself. -/
noncomputable def scIso0 :
    ShortComplex.mk ((twoTermCplx S).d 1 0) ((twoTermPi S).f 0) (d10_comp_pi0 S) ≅ S :=
  ShortComplex.isoMk (twoTermXIso₁ S) (twoTermXIso₀ S) (Iso.refl _) (comm12 S) (comm23 S)

variable {S} (hS : S.ShortExact)
include hS

theorem exact_sc0 :
    (ShortComplex.mk ((twoTermCplx S).d 1 0) ((twoTermPi S).f 0) (d10_comp_pi0 S)).Exact :=
  ShortComplex.exact_of_iso (scIso0 S).symm hS.exact

theorem epi_pi0 : Epi ((twoTermPi S).f 0) := by
  have : Epi S.g := hS.epi_g
  rw [twoTermPi_f0]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ this

theorem quasiIsoAt_zero : QuasiIsoAt (twoTermPi S) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  exact ⟨exact_sc0 hS, epi_pi0 hS⟩

theorem mono_d10 : Mono ((twoTermCplx S).d 1 0) := by
  have : Mono S.f := hS.mono_f
  rw [twoTermCplx_d]
  infer_instance

theorem exactAt_one : (twoTermCplx S).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  have hz : (twoTermCplx S).d 2 1 = 0 :=
    (isZero_twoTermCplx_X S 2 (by omega)).eq_of_src _ _
  have hmono : Mono ((twoTermCplx S).d 1 0) := mono_d10 hS
  exact (ShortComplex.exact_iff_mono _ hz).2 hmono

theorem exactAt_succ (m : ℕ) : (twoTermCplx S).ExactAt (m + 1) := by
  match m with
  | 0 => exact exactAt_one hS
  | (m + 1) =>
      exact HomologicalComplex.ExactAt.of_isZero (isZero_twoTermCplx_X S (m + 2) (by omega))

theorem quasiIso_twoTermPi : QuasiIso (twoTermPi S) where
  quasiIsoAt m := by
    match m with
    | 0 => exact quasiIsoAt_zero hS
    | (m + 1) =>
        rw [quasiIsoAt_iff_exactAt' (twoTermPi S) (m + 1)
          (ChainComplex.exactAt_succ_single_obj _ _)]
        exact exactAt_succ hS m

/-- **A short exact sequence with projective left terms is a projective resolution of its
cokernel.** -/
noncomputable def twoTermResolution [Projective S.X₁] [Projective S.X₂] :
    ProjectiveResolution S.X₃ where
  complex := twoTermCplx S
  π := twoTermPi S
  projective := projective_twoTermCplx_X S
  quasiIso := quasiIso_twoTermPi hS

end Abelian

section Modules

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The presentation short complex `M --f--> N ↠ N ⧸ p` attached to a linear map `f` whose range
is the submodule `p`. -/
noncomputable def presShortComplex (f : M →ₗ[R] N) (p : Submodule R N)
    (hp : LinearMap.range f = p) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom p.mkQ) (by
    ext x
    simpa using (Submodule.Quotient.mk_eq_zero p).2 (hp ▸ LinearMap.mem_range_self f x))

@[simp] theorem presShortComplex_X₁ (f : M →ₗ[R] N) (p : Submodule R N)
    (hp : LinearMap.range f = p) : (presShortComplex f p hp).X₁ = ModuleCat.of R M := rfl

@[simp] theorem presShortComplex_X₂ (f : M →ₗ[R] N) (p : Submodule R N)
    (hp : LinearMap.range f = p) : (presShortComplex f p hp).X₂ = ModuleCat.of R N := rfl

@[simp] theorem presShortComplex_X₃ (f : M →ₗ[R] N) (p : Submodule R N)
    (hp : LinearMap.range f = p) : (presShortComplex f p hp).X₃ = ModuleCat.of R (N ⧸ p) := rfl

theorem presShortComplex_shortExact {f : M →ₗ[R] N} {p : Submodule R N}
    (hp : LinearMap.range f = p) (hf : Function.Injective f) :
    (presShortComplex f p hp).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).2 hf
  epi_g := (ModuleCat.epi_iff_surjective _).2 p.mkQ_surjective
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range f = LinearMap.ker p.mkQ
    rw [Submodule.ker_mkQ, hp]

/-- **The presentation resolution.**  For an injective map `f : M →ₗ[R] N` between projective
modules, `M --f--> N` resolves `N ⧸ range f`. -/
noncomputable def presResolution {f : M →ₗ[R] N} {p : Submodule R N}
    (hp : LinearMap.range f = p) (hf : Function.Injective f)
    [Module.Projective R M] [Module.Projective R N] :
    ProjectiveResolution (ModuleCat.of R (N ⧸ p)) :=
  haveI : Projective (presShortComplex f p hp).X₁ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R M)
  haveI : Projective (presShortComplex f p hp).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (P := ModuleCat.of R N)
  twoTermResolution (S := presShortComplex f p hp) (presShortComplex_shortExact hp hf)

end Modules

end GaloisForLFunctions.HTGeometry.DerivedSelection
