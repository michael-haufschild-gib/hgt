import Mathlib

/-!
# The free resolution of a cyclic module by a regular element

For a commutative ring `R` and a non-zerodivisor `t`, the two-term complex

`0 → R --t--> R → R/(t) → 0`

is a free resolution of the cyclic module `R/(t)`.  This file packages it as a
`CategoryTheory.ProjectiveResolution` in `ModuleCat R`, which is what computes the derived functors
`Ext` and `Tor` of `R/(t)`.

* `cyclicCplx` — the two-term chain complex `R --t--> R` in degrees `1, 0`;
* `cyclicPi` — the augmentation to `R/(t)` in degree `0`;
* `cyclicResolution` — the projective resolution.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits

universe u

variable {R : Type u} [CommRing R] (t : R)

/-- Multiplication by `t` as a map of `R`-modules. -/
noncomputable def mulT : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.lsmul R R t)

@[simp] theorem mulT_apply (r : R) : mulT t (show (ModuleCat.of R R) from r) = t * r := rfl

theorem rel10 : (ComplexShape.down ℕ).Rel 1 0 := by simp

/-- The two-term complex `R --t--> R` in degrees `1` and `0`. -/
noncomputable def cyclicCplx : ChainComplex (ModuleCat.{u} R) ℕ :=
  HomologicalComplex.double (mulT t) rel10

/-- Degree-one identification. -/
noncomputable def isoX1 : (cyclicCplx t).X 1 ≅ ModuleCat.of R R :=
  HomologicalComplex.doubleXIso₀ (mulT t) rel10

/-- Degree-zero identification. -/
noncomputable def isoX0 : (cyclicCplx t).X 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.doubleXIso₁ (mulT t) rel10 (by decide)

theorem cyclicCplx_d : (cyclicCplx t).d 1 0 = (isoX1 t).hom ≫ mulT t ≫ (isoX0 t).inv :=
  HomologicalComplex.double_d (mulT t) rel10 (by decide)

theorem isZero_cyclicCplx_X (n : ℕ) (h : 2 ≤ n) : IsZero ((cyclicCplx t).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ (by omega) (by omega)

instance projective_cyclicCplx_X (n : ℕ) : Projective ((cyclicCplx t).X n) := by
  match n with
  | 0 => exact Projective.of_iso (isoX0 t).symm inferInstance
  | 1 => exact Projective.of_iso (isoX1 t).symm inferInstance
  | (n + 2) => exact (isZero_cyclicCplx_X t (n + 2) (by omega)).projective

/-- The quotient map `R → R/(t)`. -/
noncomputable def cyclicQuot : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span {t}) :=
  ModuleCat.ofHom (Ideal.span {t}).mkQ

theorem mulT_comp_quot : mulT t ≫ cyclicQuot t = 0 := by
  ext
  simp [mulT, cyclicQuot]

/-- The augmentation of the two-term complex onto `R/(t)`. -/
noncomputable def cyclicPi :
    cyclicCplx t ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R (R ⧸ Ideal.span {t})) :=
  ((cyclicCplx t).toSingle₀Equiv _).symm
    ⟨(isoX0 t).hom ≫ cyclicQuot t, by
      rw [cyclicCplx_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, mulT_comp_quot]
      simp⟩

theorem cyclicPi_f0 : (cyclicPi t).f 0 = (isoX0 t).hom ≫ cyclicQuot t := by
  simp [cyclicPi]

theorem d10_comp_pi0 : (cyclicCplx t).d 1 0 ≫ (cyclicPi t).f 0 = 0 := by
  rw [← (cyclicPi t).comm 1 0, HomologicalComplex.single_obj_d, comp_zero]

/-- The short complex `R --t--> R --> R/(t)` is exact. -/
theorem exact_mulT_quot : (ShortComplex.mk (mulT t) (cyclicQuot t) (mulT_comp_quot t)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext r
  simp [mulT, cyclicQuot, Ideal.mem_span_singleton, LinearMap.mem_range, eq_comm, dvd_def]

theorem comm12 : (isoX1 t).hom ≫ mulT t = (cyclicCplx t).d 1 0 ≫ (isoX0 t).hom := by
  rw [cyclicCplx_d]
  simp

theorem comm23 : (isoX0 t).hom ≫ cyclicQuot t
    = (cyclicPi t).f 0 ≫ (Iso.refl (ModuleCat.of R (R ⧸ Ideal.span {t}))).hom := by
  rw [cyclicPi_f0]
  simp

/-- The degree-zero comparison short complex is isomorphic to `R --t--> R --> R/(t)`. -/
noncomputable def scIso0 :
    ShortComplex.mk ((cyclicCplx t).d 1 0) ((cyclicPi t).f 0) (d10_comp_pi0 t) ≅
      ShortComplex.mk (mulT t) (cyclicQuot t) (mulT_comp_quot t) :=
  ShortComplex.isoMk (isoX1 t) (isoX0 t) (Iso.refl _) (comm12 t) (comm23 t)

theorem exact_sc0 :
    (ShortComplex.mk ((cyclicCplx t).d 1 0) ((cyclicPi t).f 0) (d10_comp_pi0 t)).Exact :=
  ShortComplex.exact_of_iso (scIso0 t).symm (exact_mulT_quot t)

theorem epi_pi0 : Epi ((cyclicPi t).f 0) := by
  have hquot : Epi (cyclicQuot t) := by
    rw [cyclicQuot, ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, rfl⟩
  rw [cyclicPi_f0]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ hquot

theorem quasiIsoAt_zero : QuasiIsoAt (cyclicPi t) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  exact ⟨exact_sc0 t, epi_pi0 t⟩

variable (ht : IsSMulRegular R t)
include ht

theorem mono_d10 : Mono ((cyclicCplx t).d 1 0) := by
  rw [cyclicCplx_d]
  have : Mono (mulT t) := by
    rw [ModuleCat.mono_iff_injective]
    exact ht
  infer_instance

theorem exactAt_one : (cyclicCplx t).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  have hz : (cyclicCplx t).d 2 1 = 0 :=
    (isZero_cyclicCplx_X t 2 (by omega)).eq_of_src _ _
  have hmono : Mono ((cyclicCplx t).d 1 0) := mono_d10 t ht
  exact (ShortComplex.exact_iff_mono _ hz).2 hmono

theorem exactAt_succ (m : ℕ) : (cyclicCplx t).ExactAt (m + 1) := by
  match m with
  | 0 => exact exactAt_one t ht
  | (m + 1) =>
      exact HomologicalComplex.ExactAt.of_isZero (isZero_cyclicCplx_X t (m + 2) (by omega))

theorem quasiIso_cyclicPi : QuasiIso (cyclicPi t) where
  quasiIsoAt m := by
    match m with
    | 0 => exact quasiIsoAt_zero t
    | (m + 1) =>
        rw [quasiIsoAt_iff_exactAt' (cyclicPi t) (m + 1)
          (ChainComplex.exactAt_succ_single_obj _ _)]
        exact exactAt_succ t ht m

/-- **The free resolution of the cyclic module `R/(t)` by a regular element `t`.** -/
noncomputable def cyclicResolution :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span {t})) where
  complex := cyclicCplx t
  π := cyclicPi t
  projective := projective_cyclicCplx_X t
  quasiIso := quasiIso_cyclicPi t ht

end GaloisForLFunctions.HTGeometry.DerivedSelection
