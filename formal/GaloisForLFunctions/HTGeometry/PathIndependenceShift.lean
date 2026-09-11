import GaloisForLFunctions.HTGeometry.PathIndependenceCochain

/-!
# Relabeling the tail of a path independence complex

The tail complex of the path on `{0, …, n+2}` lives on `{3, …, n+2}`; relabeling by `v ↦ v+3`
identifies it with the path complex on `{0, …, n-1}`. The relabeling is an order-preserving
bijection, so the incidence signs transport unchanged and the transport of cochains is a genuine
chain map, with no sign.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Finset

variable {F : Type*} [CommRing F]

/-! ### The relabeling of vertex sets -/

theorem add_three_injective : Function.Injective (fun v : ℕ => v + 3) := by
  intro a b h
  simpa using h

theorem shiftSet_card (σ : Finset ℕ) : (σ.image (fun v => v + 3)).card = σ.card :=
  Finset.card_image_of_injective σ add_three_injective

theorem mem_shiftSet {σ : Finset ℕ} {u : ℕ} :
    u ∈ σ.image (fun v => v + 3) ↔ ∃ v ∈ σ, v + 3 = u := by
  simp [Finset.mem_image]

theorem shiftSet_isTailSet (σ : Finset ℕ) : IsTailSet (σ.image (fun v => v + 3)) := by
  intro u hu
  obtain ⟨v, _, rfl⟩ := mem_shiftSet.mp hu
  omega

theorem shiftSet_erase (σ : Finset ℕ) (v : ℕ) :
    (σ.image (fun u => u + 3)).erase (v + 3) = (σ.erase v).image (fun u => u + 3) := by
  ext u
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, w, hw, rfl⟩
    exact ⟨w, ⟨by omega, hw⟩, rfl⟩
  · rintro ⟨w, ⟨hwv, hw⟩, rfl⟩
    exact ⟨by omega, w, hw, rfl⟩

theorem unshiftSet_shiftSet (σ : Finset ℕ) :
    (σ.image (fun v => v + 3)).image (fun v => v - 3) = σ := by
  rw [Finset.image_image]
  have h : (fun v : ℕ => v - 3) ∘ (fun v : ℕ => v + 3) = id := by
    funext v
    simp
  rw [h, Finset.image_id]

theorem shiftSet_unshiftSet {τ : Finset ℕ} (hτ : IsTailSet τ) :
    (τ.image (fun v => v - 3)).image (fun v => v + 3) = τ := by
  rw [Finset.image_image]
  have h : Set.EqOn ((fun v : ℕ => v + 3) ∘ (fun v : ℕ => v - 3)) id (τ : Set ℕ) := by
    intro v hv
    have h3 := hτ v (by simpa using hv)
    simp only [Function.comp_apply, id_eq]
    omega
  rw [Finset.image_congr h, Finset.image_id]

theorem isPathFace_iff_isTailFace {n : ℕ} {σ : Finset ℕ} :
    IsPathFace n σ ↔ IsTailFace (n + 3) (σ.image (fun v => v + 3)) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, shiftSet_isTailSet σ⟩
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := mem_shiftSet.mp hu
      have := h.1 v hv
      omega
    · intro u hu hu1
      obtain ⟨v, hv, rfl⟩ := mem_shiftSet.mp hu
      obtain ⟨w, hw, hwe⟩ := mem_shiftSet.mp hu1
      refine h.2 v hv ?_
      have hwv : w = v + 1 := by omega
      rwa [hwv] at hw
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      have := h.1.1 (v + 3) (Finset.mem_image_of_mem _ hv)
      omega
    · intro v hv hv1
      refine h.1.2 (v + 3) (Finset.mem_image_of_mem _ hv) ?_
      have hmem := Finset.mem_image_of_mem (fun u : ℕ => u + 3) hv1
      have hrw : v + 1 + 3 = v + 3 + 1 := by omega
      rwa [hrw] at hmem

/-! ### The transport of cochains -/

instance instDecidableIsTailSet (τ : Finset ℕ) : Decidable (IsTailSet τ) :=
  decidable_of_iff (∀ v ∈ τ, 3 ≤ v) Iff.rfl

/-- Transport of a tail cochain to the relabeled path complex. -/
def shiftCochain (F : Type*) [CommRing F] (f : Finset ℕ → F) (σ : Finset ℕ) : F :=
  f (σ.image (fun v => v + 3))

/-- The inverse transport, guarded on tail sets. -/
def unshiftCochain (F : Type*) [CommRing F] (g : Finset ℕ → F) (τ : Finset ℕ) : F :=
  if IsTailSet τ then g (τ.image (fun v => v - 3)) else 0

/-- The incidence signs transport unchanged: `v ↦ v+3` is order preserving. -/
theorem faceSign_shiftSet (σ : Finset ℕ) (v : ℕ) :
    faceSign F (σ.image (fun u => u + 3)) (v + 3) = faceSign F σ v := by
  have hfilter : (σ.image (fun u => u + 3)).filter (· < v + 3)
      = (σ.filter (· < v)).image (fun u => u + 3) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hlt⟩
      exact ⟨w, ⟨hw, by omega⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hlt⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, by omega⟩
  rw [faceSign, faceSign, hfilter, Finset.card_image_of_injective _ add_three_injective]

theorem shiftCochain_simplicialCoboundary (f : Finset ℕ → F) (σ : Finset ℕ) :
    simplicialCoboundary F (shiftCochain F f) σ
      = shiftCochain F (simplicialCoboundary F f) σ := by
  have hreindex : ∑ u ∈ σ.image (fun v => v + 3),
        faceSign F (σ.image (fun w => w + 3)) u * f ((σ.image (fun w => w + 3)).erase u)
      = ∑ v ∈ σ, faceSign F (σ.image (fun w => w + 3)) (v + 3) *
        f ((σ.image (fun w => w + 3)).erase (v + 3)) :=
    Finset.sum_image (fun a _ b _ h => add_three_injective h)
  rw [shiftCochain, simplicialCoboundary_apply, simplicialCoboundary_apply, hreindex]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [faceSign_shiftSet, shiftSet_erase]
  rfl

/-! ### The transport is a chain map between the two complexes -/

theorem unshiftSet_card {τ : Finset ℕ} (hτ : IsTailSet τ) :
    (τ.image (fun v => v - 3)).card = τ.card := by
  have h := shiftSet_card (τ.image (fun v => v - 3))
  rw [shiftSet_unshiftSet hτ] at h
  exact h.symm

theorem shiftCochain_unshiftCochain (g : Finset ℕ → F) :
    shiftCochain F (unshiftCochain F g) = g := by
  funext ρ
  rw [shiftCochain, unshiftCochain, if_pos (shiftSet_isTailSet ρ), unshiftSet_shiftSet ρ]

theorem unshiftCochain_shiftCochain {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ tailSupported F (n + 3) j) : unshiftCochain F (shiftCochain F f) = f := by
  funext τ
  rw [unshiftCochain]
  by_cases hts : IsTailSet τ
  · rw [if_pos hts, shiftCochain, shiftSet_unshiftSet hts]
  · rw [if_neg hts]
    exact (hf τ (Or.inr (fun h => hts h.2))).symm

theorem shiftCochain_pathCoboundary (f : Finset ℕ → F) (n : ℕ) (σ : Finset ℕ) :
    pathCoboundary F n (shiftCochain F f) σ
      = shiftCochain F (tailCoboundary F (n + 3) f) σ := by
  by_cases hσ : IsPathFace n σ
  · rw [pathCoboundary_of_face hσ, shiftCochain_simplicialCoboundary, shiftCochain,
      shiftCochain, tailCoboundary_of_face (isPathFace_iff_isTailFace.mp hσ)]
  · rw [pathCoboundary_of_not_face hσ, shiftCochain,
      tailCoboundary_of_not_face (fun h => hσ (isPathFace_iff_isTailFace.mpr h))]

theorem unshiftCochain_tailCoboundary (g : Finset ℕ → F) (n : ℕ) (τ : Finset ℕ) :
    tailCoboundary F (n + 3) (unshiftCochain F g) τ
      = unshiftCochain F (pathCoboundary F n g) τ := by
  by_cases hτ : IsTailFace (n + 3) τ
  · have hts : IsTailSet τ := hτ.2
    have hface : IsPathFace n (τ.image (fun v => v - 3)) := by
      rw [isPathFace_iff_isTailFace, shiftSet_unshiftSet hts]
      exact hτ
    have hsum : simplicialCoboundary F (unshiftCochain F g) τ
        = simplicialCoboundary F g (τ.image (fun v => v - 3)) := by
      have hshift := shiftCochain_simplicialCoboundary (F := F) (unshiftCochain F g)
        (τ.image (fun v => v - 3))
      rw [shiftCochain_unshiftCochain] at hshift
      simp only [shiftCochain] at hshift
      rw [shiftSet_unshiftSet hts] at hshift
      exact hshift.symm
    rw [tailCoboundary_of_face hτ, unshiftCochain, if_pos hts, pathCoboundary_of_face hface,
      hsum]
  · rw [tailCoboundary_of_not_face hτ, unshiftCochain]
    by_cases hts : IsTailSet τ
    · rw [if_pos hts, pathCoboundary_of_not_face (fun h => hτ (by
        rw [isPathFace_iff_isTailFace, shiftSet_unshiftSet hts] at h
        exact h))]
    · rw [if_neg hts]

/-! ### The transport on the graded pieces -/

theorem shiftCochain_mem_pathSupported {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ tailSupported F (n + 3) j) : shiftCochain F f ∈ pathSupported F n j := by
  intro σ hσ
  rw [shiftCochain]
  refine hf _ ?_
  rcases hσ with hc | hface
  · left
    rw [shiftSet_card]
    exact hc
  · right
    exact fun h => hface (isPathFace_iff_isTailFace.mpr h)

theorem unshiftCochain_mem_tailSupported {n j : ℕ} {g : Finset ℕ → F}
    (hg : g ∈ pathSupported F n j) : unshiftCochain F g ∈ tailSupported F (n + 3) j := by
  intro τ hτ
  rw [unshiftCochain]
  by_cases hts : IsTailSet τ
  · rw [if_pos hts]
    refine hg _ ?_
    rcases hτ with hc | hface
    · left
      rw [unshiftSet_card hts]
      exact hc
    · right
      intro h
      refine hface ?_
      rw [isPathFace_iff_isTailFace, shiftSet_unshiftSet hts] at h
      exact h
  · rw [if_neg hts]

/-! ### The transport as linear maps -/

theorem unshiftCochain_apply_of_tail {τ : Finset ℕ} (hτ : IsTailSet τ) (g : Finset ℕ → F) :
    unshiftCochain F g τ = g (τ.image (fun v => v - 3)) := by
  rw [unshiftCochain, if_pos hτ]

theorem unshiftCochain_apply_of_not_tail {τ : Finset ℕ} (hτ : ¬ IsTailSet τ)
    (g : Finset ℕ → F) : unshiftCochain F g τ = 0 := by
  rw [unshiftCochain, if_neg hτ]

/-- The relabeling transport as an `F`-linear map. -/
def shiftCochainₗ (F : Type*) [CommRing F] : (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := shiftCochain F
  map_add' f g := by funext σ; rfl
  map_smul' r f := by funext σ; rfl

/-- The inverse relabeling transport as an `F`-linear map. -/
def unshiftCochainₗ (F : Type*) [CommRing F] : (Finset ℕ → F) →ₗ[F] (Finset ℕ → F) where
  toFun := unshiftCochain F
  map_add' g h := by
    funext τ
    by_cases hts : IsTailSet τ
    · simp only [Pi.add_apply, unshiftCochain_apply_of_tail hts]
    · simp only [Pi.add_apply, unshiftCochain_apply_of_not_tail hts, add_zero]
  map_smul' r g := by
    funext τ
    by_cases hts : IsTailSet τ
    · simp only [RingHom.id_apply, Pi.smul_apply, unshiftCochain_apply_of_tail hts]
    · simp only [RingHom.id_apply, Pi.smul_apply, unshiftCochain_apply_of_not_tail hts,
        smul_zero]

theorem shiftCochain_zero : shiftCochain F (0 : Finset ℕ → F) = 0 :=
  (shiftCochainₗ F).map_zero

theorem unshiftCochain_zero : unshiftCochain F (0 : Finset ℕ → F) = 0 :=
  (unshiftCochainₗ F).map_zero

/-! ### The transport of cocycles and coboundaries -/

theorem shiftCochain_mem_pathCocycles {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ tailCocycles F (n + 3) j) : shiftCochain F f ∈ pathCocycles F n j := by
  refine ⟨shiftCochain_mem_pathSupported hf.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show pathCoboundary F n (shiftCochain F f) = 0
  funext σ
  rw [shiftCochain_pathCoboundary, tailCoboundary_eq_zero_of_mem_tailCocycles hf,
    shiftCochain_zero]

theorem unshiftCochain_mem_tailCocycles {n j : ℕ} {g : Finset ℕ → F}
    (hg : g ∈ pathCocycles F n j) : unshiftCochain F g ∈ tailCocycles F (n + 3) j := by
  refine ⟨unshiftCochain_mem_tailSupported hg.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  show tailCoboundary F (n + 3) (unshiftCochain F g) = 0
  funext τ
  rw [unshiftCochain_tailCoboundary, pathCoboundary_eq_zero_of_mem_pathCocycles hg,
    unshiftCochain_zero]

theorem shiftCochain_mem_pathCoboundaries {n j : ℕ} {f : Finset ℕ → F}
    (hf : f ∈ tailCoboundaries F (n + 3) j) : shiftCochain F f ∈ pathCoboundaries F n j := by
  match j with
  | 0 =>
    have hfb : f ∈ (⊥ : Submodule F (Finset ℕ → F)) := hf
    rw [(Submodule.mem_bot F).mp hfb, shiftCochain_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    obtain ⟨h, hh, rfl⟩ := hf
    refine ⟨shiftCochain F h, shiftCochain_mem_pathSupported hh, ?_⟩
    show pathCoboundary F n (shiftCochain F h) = shiftCochain F (tailCoboundary F (n + 3) h)
    funext σ
    exact shiftCochain_pathCoboundary h n σ

theorem unshiftCochain_mem_tailCoboundaries {n j : ℕ} {g : Finset ℕ → F}
    (hg : g ∈ pathCoboundaries F n j) :
    unshiftCochain F g ∈ tailCoboundaries F (n + 3) j := by
  match j with
  | 0 =>
    have hgb : g ∈ (⊥ : Submodule F (Finset ℕ → F)) := hg
    rw [(Submodule.mem_bot F).mp hgb, unshiftCochain_zero]
    exact Submodule.zero_mem _
  | (i + 1) =>
    obtain ⟨h, hh, rfl⟩ := hg
    refine ⟨unshiftCochain F h, unshiftCochain_mem_tailSupported hh, ?_⟩
    show tailCoboundary F (n + 3) (unshiftCochain F h)
      = unshiftCochain F (pathCoboundary F n h)
    funext τ
    exact unshiftCochain_tailCoboundary h n τ

/-! ### The relabeling isomorphism of reduced cohomology -/

/-- The relabeling transport on cocycles. -/
def shiftCocycles (F : Type*) [CommRing F] (n j : ℕ) :
    tailCocycles F (n + 3) j →ₗ[F] pathCocycles F n j :=
  LinearMap.restrict (shiftCochainₗ F) (fun _ hx => shiftCochain_mem_pathCocycles hx)

/-- The inverse relabeling transport on cocycles. -/
def unshiftCocycles (F : Type*) [CommRing F] (n j : ℕ) :
    pathCocycles F n j →ₗ[F] tailCocycles F (n + 3) j :=
  LinearMap.restrict (unshiftCochainₗ F) (fun _ hx => unshiftCochain_mem_tailCocycles hx)

/-- The relabeling on reduced cohomology. -/
def shiftCohomology (F : Type*) [CommRing F] (n j : ℕ) :
    tailCohomology F (n + 3) j →ₗ[F] pathCohomology F n j :=
  Submodule.mapQ _ _ (shiftCocycles F n j) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ tailCoboundaries F (n + 3) j := hx
    show shiftCochain F (x : Finset ℕ → F) ∈ pathCoboundaries F n j
    exact shiftCochain_mem_pathCoboundaries hxv)

/-- The inverse relabeling on reduced cohomology. -/
def unshiftCohomology (F : Type*) [CommRing F] (n j : ℕ) :
    pathCohomology F n j →ₗ[F] tailCohomology F (n + 3) j :=
  Submodule.mapQ _ _ (unshiftCocycles F n j) (by
    intro x hx
    have hxv : (x : Finset ℕ → F) ∈ pathCoboundaries F n j := hx
    show unshiftCochain F (x : Finset ℕ → F) ∈ tailCoboundaries F (n + 3) j
    exact unshiftCochain_mem_tailCoboundaries hxv)

theorem shiftCohomology_unshiftCohomology (n j : ℕ) (x : pathCohomology F n j) :
    shiftCohomology F n j (unshiftCohomology F n j x) = x := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [unshiftCohomology, Submodule.mapQ_apply, shiftCohomology, Submodule.mapQ_apply]
  refine congrArg _ (Subtype.ext ?_)
  show shiftCochain F (unshiftCochain F (g : Finset ℕ → F)) = (g : Finset ℕ → F)
  exact shiftCochain_unshiftCochain _

theorem unshiftCohomology_shiftCohomology (n j : ℕ) (y : tailCohomology F (n + 3) j) :
    unshiftCohomology F n j (shiftCohomology F n j y) = y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [shiftCohomology, Submodule.mapQ_apply, unshiftCohomology, Submodule.mapQ_apply]
  refine congrArg _ (Subtype.ext ?_)
  show unshiftCochain F (shiftCochain F (f : Finset ℕ → F)) = (f : Finset ℕ → F)
  exact unshiftCochain_shiftCochain f.property.1

/-- **The relabeling isomorphism.** The tail complex of the path on `{0,…,n+2}` has the same
reduced cohomology, in every occupation degree, as the path complex on `{0,…,n-1}`. -/
def tailCohomologyEquiv (F : Type*) [CommRing F] (n j : ℕ) :
    tailCohomology F (n + 3) j ≃ₗ[F] pathCohomology F n j :=
  LinearEquiv.ofLinear (shiftCohomology F n j) (unshiftCohomology F n j)
    (LinearMap.ext fun x => shiftCohomology_unshiftCohomology n j x)
    (LinearMap.ext fun y => unshiftCohomology_shiftCohomology n j y)

/-- **The card's displayed shift.** `H̃^(j+1)(Ind P_(n+3)) ≅ H̃^j(Ind P_n)`. -/
def pathCohomologyShiftEquiv (F : Type*) [CommRing F] (n j : ℕ) :
    pathCohomology F (n + 3) (j + 1) ≃ₗ[F] pathCohomology F n j :=
  (pathCohomologyEquiv F (n + 3) j (by omega)).trans (tailCohomologyEquiv F n j)

end
end GaloisForLFunctions.HTGeometry
