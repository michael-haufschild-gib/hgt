import GaloisForLFunctions.HTGeometry.HochsterMultidegreeExhaustion

/-!
# Cochains of an induced subcomplex, indexed by codimension

Hochster's correspondence is stated on tuples: a condition is imposed at every injective `p`-tuple of
vertices of `σ` whose complement in `σ` is a face.  The complements of those tuples are exactly the
faces of the induced subcomplex `Δ_σ` of codimension `p` in `σ`, and every such face arises from a
tuple -- its own increasing enumeration.

This file makes that dictionary explicit and uses it to build the reduced cochain module of `Δ_σ` in
each codimension, the restriction projection onto it, and the strand map as an `F`-linear map.  The
projection is invisible to the coboundary at a codimension-`p` face, because every vertex deletion of
such a face is again a face, of codimension `p+1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### Codimension-`p` faces of the induced subcomplex -/

/-- A codimension-`p` face of the induced subcomplex `Δ_σ`: a face of `Δ` contained in `σ` with `p`
vertices of `σ` missing. -/
def IsCodimFace (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) (J : Finset α) : Prop :=
  J ⊆ σ ∧ J.card + p = σ.card ∧ IsFaceOf (↑facets : Set (Finset α)) J

omit [LinearOrder α] [Fintype α] in
/-- Deleting a vertex from a codimension-`p` face gives a codimension-`(p+1)` face. -/
theorem isCodimFace_erase {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ} {J : Finset α}
    (hJ : IsCodimFace facets σ p J) {v : α} (hv : v ∈ J) :
    IsCodimFace facets σ (p + 1) (J.erase v) := by
  refine ⟨(Finset.erase_subset v J).trans hJ.1, ?_,
    isFaceOf_mono (Finset.erase_subset v J) hJ.2.2⟩
  have hcard : (J.erase v).card = J.card - 1 := Finset.card_erase_of_mem hv
  have hpos : 1 ≤ J.card := Finset.card_pos.mpr ⟨v, hv⟩
  have := hJ.2.1
  omega

omit [LinearOrder α] [Fintype α] in
/-- The complement of an injective tuple with entries in `σ` is a codimension-`p` face when it is a
face at all. -/
theorem isCodimFace_sdiff_image (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {v : Fin p → α} (h1 : ∀ t, v t ∈ σ) (h2 : Function.Injective v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ)) :
    IsCodimFace facets σ p (σ \ Finset.image v Finset.univ) := by
  have hsub : Finset.image v Finset.univ ⊆ σ := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact h1 t
  have hcard : (Finset.image v Finset.univ).card = p := by
    rw [Finset.card_image_of_injective _ h2, Finset.card_univ, Fintype.card_fin]
  have hle : p ≤ σ.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  refine ⟨Finset.sdiff_subset, ?_, hf⟩
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  omega

omit [Fintype α] in
/-- Every codimension-`p` face is the complement of an injective tuple: its own increasing
enumeration. -/
theorem exists_tuple_of_isCodimFace (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {J : Finset α} (hJ : IsCodimFace facets σ p J) :
    ∃ v : Fin p → α, (∀ t, v t ∈ σ) ∧ Function.Injective v ∧
      σ \ Finset.image v Finset.univ = J := by
  obtain ⟨hsub, hcard, _⟩ := hJ
  have hle : J.card ≤ σ.card := Finset.card_le_card hsub
  have hc : (σ \ J).card = p := by
    have hadd := Finset.card_sdiff_add_card_eq_card hsub
    omega
  refine ⟨⇑((σ \ J).orderEmbOfFin hc), fun t => ?_, RelEmbedding.injective _, ?_⟩
  · exact (Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem _ hc t)).1
  · have himg : Finset.image (⇑((σ \ J).orderEmbOfFin hc)) Finset.univ = σ \ J := by
      apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
    rw [himg, Finset.sdiff_sdiff_eq_self hsub]

omit [Fintype α] in
/-- **The tuple guard is the codimension-face guard.**  A property holds at the complement of every
injective tuple with entries in `σ` whose complement is a face exactly when it holds at every
codimension-`p` face of `Δ_σ`. -/
theorem forall_tuple_iff_forall_isCodimFace (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (P : Finset α → Prop) :
    (∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
        IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
        P (σ \ Finset.image v Finset.univ))
      ↔ ∀ J : Finset α, IsCodimFace facets σ p J → P J := by
  constructor
  · intro h J hJ
    obtain ⟨v, h1, h2, rfl⟩ := exists_tuple_of_isCodimFace facets σ hJ
    exact h v h1 h2 hJ.2.2
  · intro h v h1 h2 hf
    exact h _ (isCodimFace_sdiff_image facets σ h1 h2 hf)

/-! ### The reduced cochain module of the induced subcomplex -/

/-- The reduced simplicial cochains of `Δ_σ` in codimension `p`: functions supported on the
codimension-`p` faces.  Codimension `p = σ.card` is the augmentation slot, so the complex is the
reduced one. -/
def inducedCochains (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    Submodule F (Finset α → F) where
  carrier := {g | ∀ J : Finset α, ¬ IsCodimFace facets σ p J → g J = 0}
  add_mem' hf hg := fun J hJ => by simp only [Pi.add_apply, hf J hJ, hg J hJ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun J hJ => by
    show r * _ = 0
    rw [hf J hJ, mul_zero]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
theorem mem_inducedCochains {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    {g : Finset α → F} :
    g ∈ inducedCochains F facets σ p ↔ ∀ J : Finset α, ¬ IsCodimFace facets σ p J → g J = 0 :=
  Iff.rfl

open Classical in
/-- Restriction of a cochain to the codimension-`p` faces of `Δ_σ`. -/
def codimRestrictₗ (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    (Finset α → F) →ₗ[F] (Finset α → F) where
  toFun g := fun J => if IsCodimFace facets σ p J then g J else 0
  map_add' g h := by
    funext J
    by_cases hJ : IsCodimFace facets σ p J
    · simp only [Pi.add_apply, if_pos hJ]
    · simp only [Pi.add_apply, if_neg hJ, add_zero]
  map_smul' r g := by
    funext J
    by_cases hJ : IsCodimFace facets σ p J
    · simp only [Pi.smul_apply, if_pos hJ, RingHom.id_apply]
    · simp only [Pi.smul_apply, if_neg hJ, RingHom.id_apply, smul_eq_mul, mul_zero]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
theorem codimRestrictₗ_apply_of_isCodimFace {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    (g : Finset α → F) {J : Finset α} (hJ : IsCodimFace facets σ p J) :
    codimRestrictₗ F facets σ p g J = g J := by
  classical
  show (if IsCodimFace facets σ p J then g J else 0) = g J
  rw [if_pos hJ]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
theorem codimRestrictₗ_apply_of_not {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    (g : Finset α → F) {J : Finset α} (hJ : ¬ IsCodimFace facets σ p J) :
    codimRestrictₗ F facets σ p g J = 0 := by
  classical
  show (if IsCodimFace facets σ p J then g J else 0) = 0
  rw [if_neg hJ]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
theorem codimRestrictₗ_mem_inducedCochains (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ)
    (g : Finset α → F) : codimRestrictₗ F facets σ p g ∈ inducedCochains F facets σ p :=
  fun _ hJ => codimRestrictₗ_apply_of_not g hJ

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
theorem codimRestrictₗ_eq_self {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    {g : Finset α → F} (hg : g ∈ inducedCochains F facets σ p) :
    codimRestrictₗ F facets σ p g = g := by
  funext J
  by_cases hJ : IsCodimFace facets σ p J
  · exact codimRestrictₗ_apply_of_isCodimFace g hJ
  · rw [codimRestrictₗ_apply_of_not g hJ, hg J hJ]

omit [Fintype α] in
/-- **The projection is invisible to the coboundary.**  At a codimension-`p` face the coboundary only
reads codimension-`(p+1)` faces, where the projection changes nothing. -/
theorem simplicialCoboundary_codimRestrictₗ {facets : Finset (Finset α)} {σ : Finset α} {p : ℕ}
    (f : Finset α → F) {J : Finset α} (hJ : IsCodimFace facets σ p J) :
    simplicialCoboundary F (codimRestrictₗ F facets σ (p + 1) f) J
      = simplicialCoboundary F f J := by
  simp only [simplicialCoboundary]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [codimRestrictₗ_apply_of_isCodimFace f (isCodimFace_erase hJ hv)]

/-! ### The strand map as a linear map -/

omit [Fintype α] in
/-- The strand map is `F`-linear in the cochain. -/
theorem strandTensor_add (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g h : Finset α → F) :
    strandTensor F facets σ (p := p) (g + h)
      = strandTensor F facets σ (p := p) g + strandTensor F facets σ (p := p) h := by
  funext v
  simp only [strandTensor, Pi.add_apply]
  by_cases hv : (∀ t, v t ∈ σ) ∧ Function.Injective v
  · rw [if_pos hv, if_pos hv, if_pos hv, mul_add, add_smul]
  · rw [if_neg hv, if_neg hv, if_neg hv, add_zero]

omit [Fintype α] in
theorem strandTensor_smul (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (r : F) (g : Finset α → F) :
    strandTensor F facets σ (p := p) (r • g) = r • strandTensor F facets σ (p := p) g := by
  funext v
  simp only [strandTensor, Pi.smul_apply, smul_eq_mul]
  by_cases hv : (∀ t, v t ∈ σ) ∧ Function.Injective v
  · rw [if_pos hv, if_pos hv, smul_smul]
    congr 1
    ring
  · rw [if_neg hv, if_neg hv, smul_zero]

/-- The strand map as an `F`-linear map from cochains to alternating Koszul tensors. -/
def strandTensorₗ (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ) :
    (Finset α → F) →ₗ[F] ((Fin p → α) → stanleyReisnerRing F facets) where
  toFun := strandTensor F facets σ
  map_add' := strandTensor_add facets σ
  map_smul' r g := strandTensor_smul facets σ r g

omit [Fintype α] in
@[simp]
theorem strandTensorₗ_apply (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ)
    (g : Finset α → F) :
    strandTensorₗ F facets σ p g = strandTensor F facets σ (p := p) g := rfl

omit [Fintype α] in
/-- **The strand map is injective on the cochains of the induced subcomplex.**  It sees exactly the
values at the codimension-`p` faces, and those determine a cochain supported there. -/
theorem strandTensorₗ_injective_on (facets : Finset (Finset α)) (σ : Finset α) (p : ℕ)
    {g : Finset α → F} (hg : g ∈ inducedCochains F facets σ p)
    (hz : strandTensorₗ F facets σ p g = 0) : g = 0 := by
  funext J
  by_cases hJ : IsCodimFace facets σ p J
  · have h := (strandTensor_eq_zero_iff facets σ (p := p) g).mp hz
    rw [forall_tuple_iff_forall_isCodimFace facets σ (fun J => g J = 0)] at h
    exact h J hJ
  · exact hg J hJ

end

end GaloisForLFunctions.HTGeometry
