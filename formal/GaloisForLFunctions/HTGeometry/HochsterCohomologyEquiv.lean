import GaloisForLFunctions.HTGeometry.HochsterCodimFaces

/-!
# Hochster's formula as a module isomorphism

The strand correspondence identifies, pointwise, the multidegree-`σ` Koszul cycles with the reduced
simplicial cocycles of the induced subcomplex `Δ_σ` and the multidegree-`σ` Koszul boundaries with its
coboundaries.  This file turns that correspondence into an isomorphism of `F`-modules between the two
subquotients: the multidegree-`σ` Koszul homology of the Stanley–Reisner ring in degree `p+1` and the
reduced simplicial cohomology of `Δ_σ` in codimension `p+1`.

The strand map is injective on the cochains supported on the codimension-`(p+1)` faces and its image
is exactly the multidegree-`σ` strand module, so it is an isomorphism of cochain groups; it carries
cocycles onto cycles and coboundaries onto boundaries, so it descends to the subquotients.

This is Hochster's formula for an arbitrary finite complex, in every degree, over an arbitrary
commutative ring: no shellability, no Cohen–Macaulayness, no characteristic assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### The reduced cochain complex of the induced subcomplex -/

/-- Reduced simplicial cocycles of `Δ_σ` in codimension `p+1`: cochains supported on the
codimension-`(p+1)` faces whose coboundary vanishes on every codimension-`p` face. -/
def inducedCocycles (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule F (Finset α → F) :=
  inducedCochains F facets σ (p + 1) ⊓
    LinearMap.ker ((codimRestrictₗ F facets σ p).comp (simplicialCoboundaryₗ F))

/-- Reduced simplicial coboundaries of `Δ_σ` in codimension `p+1`. -/
def inducedCoboundaries (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) : Submodule F (Finset α → F) :=
  LinearMap.range ((codimRestrictₗ F facets σ (p + 1)).comp (simplicialCoboundaryₗ F))

omit [Fintype α] in
theorem mem_inducedCocycles {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    {g : Finset α → F} :
    g ∈ inducedCocycles F facets σ p ↔ g ∈ inducedCochains F facets σ (p + 1) ∧
      ∀ J : Finset α, IsCodimFace facets σ p J → simplicialCoboundary F g J = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun J hJ => ?_⟩
    have h3 : codimRestrictₗ F facets σ p (simplicialCoboundary F g) = 0 := h2
    have h4 := congrFun h3 J
    rwa [codimRestrictₗ_apply_of_isCodimFace _ hJ] at h4
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    show codimRestrictₗ F facets σ p (simplicialCoboundary F g) = 0
    funext J
    by_cases hJ : IsCodimFace facets σ p J
    · rw [codimRestrictₗ_apply_of_isCodimFace _ hJ, h2 J hJ]
      rfl
    · rw [codimRestrictₗ_apply_of_not _ hJ]
      rfl

omit [Fintype α] in
theorem mem_inducedCoboundaries {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    {g : Finset α → F} :
    g ∈ inducedCoboundaries F facets σ p ↔
      ∃ h : Finset α → F, codimRestrictₗ F facets σ (p + 1) (simplicialCoboundary F h) = g :=
  Iff.rfl

omit [Fintype α] in
/-- A coboundary is determined on the codimension-`(p+1)` faces, so for a cochain supported there the
abstract condition is the pointwise one. -/
theorem mem_inducedCoboundaries_iff {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    {g : Finset α → F} (hg : g ∈ inducedCochains F facets σ (p + 1)) :
    g ∈ inducedCoboundaries F facets σ p ↔
      ∃ h : Finset α → F, ∀ J : Finset α, IsCodimFace facets σ (p + 1) J →
        simplicialCoboundary F h J = g J := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h, fun J hJ => ?_⟩
    simp only [LinearMap.comp_apply, simplicialCoboundaryₗ_apply]
    exact (codimRestrictₗ_apply_of_isCodimFace _ hJ).symm
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    funext J
    simp only [LinearMap.comp_apply, simplicialCoboundaryₗ_apply]
    by_cases hJ : IsCodimFace facets σ (p + 1) J
    · rw [codimRestrictₗ_apply_of_isCodimFace _ hJ, hh J hJ]
    · rw [codimRestrictₗ_apply_of_not _ hJ, hg J hJ]

omit [Fintype α] in
/-- **Coboundaries are cocycles.**  `δ² = 0` survives the restriction, because the coboundary at a
codimension-`p` face reads only codimension-`(p+1)` faces. -/
theorem inducedCoboundaries_le_inducedCocycles (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) :
    inducedCoboundaries F facets σ p ≤ inducedCocycles F facets σ p := by
  rintro _ ⟨h, rfl⟩
  simp only [LinearMap.comp_apply, simplicialCoboundaryₗ_apply]
  refine mem_inducedCocycles.mpr ⟨codimRestrictₗ_mem_inducedCochains facets σ (p + 1) _,
    fun J hJ => ?_⟩
  rw [simplicialCoboundary_codimRestrictₗ _ hJ]
  exact congrFun (simplicialCoboundary_simplicialCoboundary (F := F) h) J

/-! ### The multidegree-`σ` strand module -/

/-- The multidegree-`σ` part of the alternating Koszul complex in degree `p`: the image of the
cochains of `Δ_σ` in codimension `p` under the strand map. -/
def srStrandModule (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule F ((Fin p → α) → stanleyReisnerRing F facets) :=
  Submodule.map (strandTensorₗ F facets σ p) (inducedCochains F facets σ p)

/-- The multidegree-`σ` Koszul cycles in degree `p+1`. -/
def srStrandCycles (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule F ((Fin (p + 1) → α) → stanleyReisnerRing F facets) :=
  srStrandModule F facets σ (p + 1) ⊓
    Submodule.restrictScalars F (koszulCycles (p := p) (srVertexX F facets))

/-- The multidegree-`σ` Koszul boundaries in degree `p+1`. -/
def srStrandBoundaries (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) : Submodule F ((Fin (p + 1) → α) → stanleyReisnerRing F facets) :=
  srStrandModule F facets σ (p + 1) ⊓
    Submodule.restrictScalars F (koszulBoundaries (p := p) (srVertexX F facets))

theorem srStrandBoundaries_le_srStrandCycles (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) :
    srStrandBoundaries F facets σ p ≤ srStrandCycles F facets σ p :=
  inf_le_inf_left _ (Submodule.restrictScalars_mono F
    (koszulBoundaries_le_koszulCycles (p := p) (srVertexX F facets)))

/-! ### The strand map transports the two filtrations -/

/-- **Cocycles go to cycles and back.** -/
theorem map_inducedCocycles (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule.map (strandTensorₗ F facets σ (p + 1)) (inducedCocycles F facets σ p)
      = srStrandCycles F facets σ p := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hg1, hg2⟩ := mem_inducedCocycles.mp hg
    refine ⟨⟨g, hg1, rfl⟩, ?_, strandTensor_isAltTensor facets σ g⟩
    show koszulD (srVertexX F facets) (strandTensor F facets σ (p := p + 1) g) = 0
    rw [koszulD_strandTensor_eq_zero_iff facets σ g,
      forall_tuple_iff_forall_isCodimFace facets σ
        (fun J => simplicialCoboundary F g J = 0)]
    exact hg2
  · rintro b ⟨⟨g, hg, rfl⟩, hcyc⟩
    refine ⟨g, mem_inducedCocycles.mpr ⟨hg, ?_⟩, rfl⟩
    rw [← forall_tuple_iff_forall_isCodimFace facets σ
      (fun J => simplicialCoboundary F g J = 0),
      ← koszulD_strandTensor_eq_zero_iff facets σ g]
    exact hcyc.1

/-- **Coboundaries go to boundaries and back.** -/
theorem map_inducedCoboundaries (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule.map (strandTensorₗ F facets σ (p + 1)) (inducedCoboundaries F facets σ p)
      = srStrandBoundaries F facets σ p := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    have hg1 : g ∈ inducedCochains F facets σ (p + 1) :=
      inducedCoboundaries_le_inducedCocycles facets σ p hg |>.1
    obtain ⟨h, hh⟩ := (mem_inducedCoboundaries_iff hg1).mp hg
    refine ⟨⟨g, hg1, rfl⟩, ?_⟩
    show strandTensor F facets σ (p := p + 1) g ∈ koszulBoundaries (p := p) (srVertexX F facets)
    rw [hochster_strand_boundary_iff facets σ g]
    exact ⟨h, (forall_tuple_iff_forall_isCodimFace facets σ
      (fun J => simplicialCoboundary F h J = g J)).mpr hh⟩
  · rintro b ⟨⟨g, hg, rfl⟩, hbd⟩
    have hbd' : strandTensor F facets σ (p := p + 1) g
        ∈ koszulBoundaries (p := p) (srVertexX F facets) := hbd
    rw [hochster_strand_boundary_iff facets σ g] at hbd'
    obtain ⟨h, hh⟩ := hbd'
    refine ⟨g, (mem_inducedCoboundaries_iff hg).mpr ⟨h, ?_⟩, rfl⟩
    exact (forall_tuple_iff_forall_isCodimFace facets σ
      (fun J => simplicialCoboundary F h J = g J)).mp hh

/-! ### The isomorphism -/

theorem strandTensorₗ_mem_srStrandCycles (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ)
    {g : Finset α → F} (hg : g ∈ inducedCocycles F facets σ p) :
    strandTensorₗ F facets σ (p + 1) g ∈ srStrandCycles F facets σ p := by
  rw [← map_inducedCocycles facets σ p]
  exact ⟨g, hg, rfl⟩

/-- **The strand map is an isomorphism of cocycle modules.** -/
def hochsterCocycleEquiv (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    ↥(inducedCocycles F facets σ p) ≃ₗ[F] ↥(srStrandCycles F facets σ p) :=
  LinearEquiv.ofBijective
    ((strandTensorₗ F facets σ (p + 1)).restrict
      (fun _ hg => strandTensorₗ_mem_srStrandCycles facets σ p hg))
    ⟨by
      intro x y hxy
      have hsub : (x : Finset α → F) - (y : Finset α → F) ∈ inducedCochains F facets σ (p + 1) :=
        Submodule.sub_mem _ (mem_inducedCocycles.mp x.2).1 (mem_inducedCocycles.mp y.2).1
      have hz : strandTensorₗ F facets σ (p + 1) ((x : Finset α → F) - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val hxy
      have := strandTensorₗ_injective_on facets σ (p + 1) hsub hz
      exact Subtype.ext (sub_eq_zero.mp this),
     by
      rintro ⟨b, hb⟩
      rw [← map_inducedCocycles facets σ p] at hb
      obtain ⟨g, hg, hgb⟩ := hb
      exact ⟨⟨g, hg⟩, Subtype.ext hgb⟩⟩

@[simp]
theorem hochsterCocycleEquiv_coe (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ)
    (x : ↥(inducedCocycles F facets σ p)) :
    ((hochsterCocycleEquiv facets σ p x : ↥(srStrandCycles F facets σ p)) :
        (Fin (p + 1) → α) → stanleyReisnerRing F facets)
      = strandTensor F facets σ (p := p + 1) (x : Finset α → F) := rfl

/-- The reduced simplicial cohomology of the induced subcomplex `Δ_σ` in codimension `p+1`. -/
abbrev inducedReducedCohomology (F : Type*) [CommRing F] (facets : Finset (Finset α))
    (σ : Finset α) (p : ℕ) : Type _ :=
  ↥(inducedCocycles F facets σ p) ⧸
    (inducedCoboundaries F facets σ p).comap (inducedCocycles F facets σ p).subtype

/-- The multidegree-`σ` Koszul homology of the Stanley–Reisner ring in degree `p+1`. -/
abbrev srStrandTor (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Type _ :=
  ↥(srStrandCycles F facets σ p) ⧸
    (srStrandBoundaries F facets σ p).comap (srStrandCycles F facets σ p).subtype

theorem map_comap_inducedCoboundaries (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule.map (hochsterCocycleEquiv (F := F) facets σ p).toLinearMap
      ((inducedCoboundaries F facets σ p).comap (inducedCocycles F facets σ p).subtype)
      = (srStrandBoundaries F facets σ p).comap (srStrandCycles F facets σ p).subtype := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    show (strandTensor F facets σ (p := p + 1) (x : Finset α → F)) ∈ srStrandBoundaries F facets σ p
    rw [← map_inducedCoboundaries facets σ p]
    exact ⟨(x : Finset α → F), hx, rfl⟩
  · intro y hy
    have hy' : (y : (Fin (p + 1) → α) → stanleyReisnerRing F facets)
        ∈ srStrandBoundaries F facets σ p := hy
    rw [← map_inducedCoboundaries facets σ p] at hy'
    obtain ⟨g, hg, hgy⟩ := hy'
    have hgc : g ∈ inducedCocycles F facets σ p :=
      inducedCoboundaries_le_inducedCocycles facets σ p hg
    exact ⟨⟨g, hgc⟩, hg, Subtype.ext hgy⟩

/-- **Hochster's formula, as an isomorphism of modules.**  For every finite complex, every
multidegree `σ` and every degree, the multidegree-`σ` Koszul homology of the Stanley–Reisner ring is
isomorphic to the reduced simplicial cohomology of the induced subcomplex `Δ_σ` in the complementary
codimension -- over an arbitrary commutative ring, with no shellability, Cohen–Macaulay or
characteristic hypothesis. -/
def hochsterCohomologyEquiv (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    inducedReducedCohomology F facets σ p ≃ₗ[F] srStrandTor F facets σ p :=
  Submodule.Quotient.equiv _ _ (hochsterCocycleEquiv facets σ p)
    (map_comap_inducedCoboundaries facets σ p)

/-- **The ranks match.**  Hochster's formula in numerical form: the multidegree-`σ` Koszul homology
and the reduced cohomology of the induced subcomplex have the same rank. -/
theorem finrank_srStrandTor (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Module.finrank F (srStrandTor F facets σ p)
      = Module.finrank F (inducedReducedCohomology F facets σ p) :=
  ((hochsterCohomologyEquiv facets σ p).finrank_eq).symm

/-! ### Transfer of nonvanishing -/

/-- **A multidegree-`σ` cycle bounds in the whole Koszul complex only if it bounds inside its own
multidegree.**  So the multidegree-`σ` homology injects into the full Koszul homology and no class is
lost. -/
theorem mem_koszulBoundaries_iff_mem_srStrandBoundaries (facets : Finset (Finset α))
    (σ : Finset α) (p : ℕ) {b : (Fin (p + 1) → α) → stanleyReisnerRing F facets}
    (hb : b ∈ srStrandCycles F facets σ p) :
    b ∈ koszulBoundaries (p := p) (srVertexX F facets)
      ↔ b ∈ srStrandBoundaries F facets σ p :=
  ⟨fun h => ⟨hb.1, h⟩, fun h => h.2⟩

/-- **A cochain of `Δ_σ` bounds exactly when its strand element bounds.** -/
theorem strandTensor_mem_koszulBoundaries_iff (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) {g : Finset α → F} (hg : g ∈ inducedCochains F facets σ (p + 1)) :
    strandTensor F facets σ (p := p + 1) g ∈ koszulBoundaries (p := p) (srVertexX F facets)
      ↔ g ∈ inducedCoboundaries F facets σ p := by
  constructor
  · intro hbd
    have hmem : strandTensor F facets σ (p := p + 1) g ∈ srStrandBoundaries F facets σ p :=
      ⟨⟨g, hg, rfl⟩, hbd⟩
    rw [← map_inducedCoboundaries facets σ p] at hmem
    obtain ⟨g', hg', hgg⟩ := hmem
    have hg'1 : g' ∈ inducedCochains F facets σ (p + 1) :=
      (inducedCoboundaries_le_inducedCocycles facets σ p hg').1
    have hsub : g' - g ∈ inducedCochains F facets σ (p + 1) := Submodule.sub_mem _ hg'1 hg
    have hz : strandTensorₗ F facets σ (p + 1) (g' - g) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hgg
    have := strandTensorₗ_injective_on facets σ (p + 1) hsub hz
    rwa [sub_eq_zero.mp this] at hg'
  · intro hbd
    have : strandTensor F facets σ (p := p + 1) g ∈ srStrandBoundaries F facets σ p := by
      rw [← map_inducedCoboundaries facets σ p]
      exact ⟨g, hbd, rfl⟩
    exact this.2

/-- **Nonvanishing transfer.**  A reduced cohomology class of the induced subcomplex `Δ_σ` that is
not a coboundary produces a Koszul class that is not a boundary. -/
theorem strandTensor_not_mem_koszulBoundaries (facets : Finset (Finset α)) (σ : Finset α)
    (p : ℕ) {g : Finset α → F} (hg : g ∈ inducedCocycles F facets σ p)
    (hng : g ∉ inducedCoboundaries F facets σ p) :
    strandTensor F facets σ (p := p + 1) g ∉ koszulBoundaries (p := p) (srVertexX F facets) :=
  fun hbd => hng ((strandTensor_mem_koszulBoundaries_iff facets σ p
    (mem_inducedCocycles.mp hg).1).mp hbd)

end

end GaloisForLFunctions.HTGeometry
