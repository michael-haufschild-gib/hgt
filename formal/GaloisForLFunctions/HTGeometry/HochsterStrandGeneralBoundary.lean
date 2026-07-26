import GaloisForLFunctions.HTGeometry.HochsterStrandGeneralDegree

/-!
# Hochster's correspondence in every Koszul degree: strand boundaries are exactly coboundaries

The strand chain map `strandTensor` intertwines the reduced simplicial coboundary of an induced
subcomplex `Δ_σ` with the Koszul differential in every degree (`koszulD_strandTensor`), so every
reduced coboundary becomes a Koszul boundary (`strandTensor_coboundary_mem_koszulBoundaries`).  This
file proves the converse in every degree, completing the strand equivalence:

`strandTensor (p+1) g ∈ koszulBoundaries ↔ ∃ h, δh = g on the codimension-`(p+1)` faces of σ`.

The primitive is reconstructed from the face detectors of the alternating `(p+2)`-tensor, exactly as
at degrees one and two, but now uniformly:

* `srFaceDetector_koszulD` — the face detector of a general Koszul differential is the sum, over the
  vertices of the face, of the deleted-vertex detectors of the prepended tensor;
* `tupleCochain` — the degree-uniform replacement for `pairCochain` and `tripleCochain`: a cochain is
  built from a *permutation-invariant* weight on tuples by evaluating it at the **canonical increasing
  enumeration** `Finset.orderEmbOfFin` of the complement.  This replaces the ad-hoc `p < q < r` guards
  and the hand-made sorting arguments; `exists_perm_comp_of_image_eq` supplies the permutation
  relating an arbitrary injective tuple to the canonical one, and the weight is invariant under it.

The weight used is `(-1)^(p+1) · tupleSign σ u · (detector of b at u)`, a product of two families that
each transform by the sign of the permutation, hence invariant; the leading `(-1)^(p+1)` cancels the
rotation sign of the chain map, and `tupleSign_mul_self` closes the computation.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-! ### Two uniform ingredients -/

/-- The iterated incidence sign is a sign: it squares to `1`. -/
theorem tupleSign_mul_self : ∀ {p : ℕ} (σ : Finset α) (v : Fin p → α),
    tupleSign F σ v * tupleSign F σ v = 1 := by
  intro p
  induction p with
  | zero => intro σ v; rw [tupleSign_zero]; ring
  | succ q ih =>
    intro σ v
    rw [tupleSign_succ]
    have h1 := faceSign_mul_self (F := F) σ (v 0)
    have h2 := ih (σ.erase (v 0)) (Fin.tail v)
    linear_combination
      (tupleSign F (σ.erase (v 0)) (Fin.tail v) * tupleSign F (σ.erase (v 0)) (Fin.tail v)) * h1 + h2

omit [DecidableEq α] [LinearOrder α] in
/-- Two injective tuples that hit the same values differ by a permutation of the index set. -/
theorem exists_perm_comp_of_mem {m : ℕ} {u e : Fin m → α}
    (he : Function.Injective e) (hmem : ∀ t, ∃ s, u s = e t) :
    ∃ π : Equiv.Perm (Fin m), u ∘ ⇑π = e := by
  classical
  choose f hf using hmem
  have hfinj : Function.Injective f := by
    intro a c hac
    exact he (by rw [← hf a, ← hf c, hac])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), funext fun t => hf t⟩

/-! ### The face detector of a general Koszul differential -/

variable [Fintype α]

omit [LinearOrder α] in
/-- The `J`-face detector of a Koszul differential is the sum over `k ∈ J` of the deleted-vertex
detectors of the tensor with `k` prepended. -/
theorem srFaceDetector_koszulD {p : ℕ} (facets : Finset (Finset α)) {J : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J)
    (b : (Fin (p + 1) → α) → stanleyReisnerRing F facets) (w : Fin p → α) :
    srFaceDetector F facets J hJ (koszulD (srVertexX F facets) b w)
      = ∑ k ∈ J, srFaceDetector F facets (J.erase k)
          (isFaceOf_mono (Finset.erase_subset k J) hJ) (b (Fin.cons k w)) := by
  rw [koszulD, map_sum,
    Finset.sum_congr rfl (fun k _ => srFaceDetector_mul_srVertexX facets hJ (b (Fin.cons k w))),
    Finset.sum_ite_mem, Finset.univ_inter]

/-! ### The degree-uniform cochain attached to a permutation-invariant weight -/

/-- The cochain attached to a weight on tuples: evaluate the weight at the canonical increasing
enumeration of the complement.  For a permutation-invariant weight this is the degree-uniform
replacement for `pairCochain` and `tripleCochain`. -/
def tupleCochain (F : Type*) [CommRing F] (σ : Finset α) {m : ℕ} (W : (Fin m → α) → F) :
    Finset α → F :=
  fun ρ => if h : (σ \ ρ).card = m then W ((σ \ ρ).orderEmbOfFin h) else 0

omit [Fintype α] in
/-- **Evaluation of the uniform cochain.**  At the complement of an injective tuple with entries in
`σ`, the cochain is the weight of that tuple. -/
theorem tupleCochain_sdiff {σ : Finset α} {m : ℕ} {W : (Fin m → α) → F}
    (hW : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)), W (x ∘ ⇑π) = W x)
    (u : Fin m → α) (hu : Function.Injective u) (humem : ∀ t, u t ∈ σ) :
    tupleCochain F σ W (σ \ Finset.image u Finset.univ) = W u := by
  have hsub : Finset.image u Finset.univ ⊆ σ := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact humem t
  have hss : σ \ (σ \ Finset.image u Finset.univ) = Finset.image u Finset.univ :=
    Finset.sdiff_sdiff_eq_self hsub
  have hcard : (σ \ (σ \ Finset.image u Finset.univ)).card = m := by
    rw [hss, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  show (if h : (σ \ (σ \ Finset.image u Finset.univ)).card = m then
      W ((σ \ (σ \ Finset.image u Finset.univ)).orderEmbOfFin h) else 0) = W u
  rw [dif_pos hcard]
  obtain ⟨π, hπ⟩ := exists_perm_comp_of_mem
    (u := u) (e := ⇑((σ \ (σ \ Finset.image u Finset.univ)).orderEmbOfFin hcard))
    (RelEmbedding.injective _)
    (fun t => by
      have hx := Finset.orderEmbOfFin_mem (σ \ (σ \ Finset.image u Finset.univ)) hcard t
      obtain ⟨sIdx, _, hs⟩ := Finset.mem_image.mp (Finset.mem_of_subset (le_of_eq hss) hx)
      exact ⟨sIdx, hs⟩)
  rw [← hπ, hW u π]

/-! ### Strand elements agreeing on the faces -/

omit [LinearOrder α] [Fintype α] in
/-- The face detector does not depend on the presentation of the face. -/
theorem srFaceDetector_congr (facets : Finset (Finset α)) {J K : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) (hK : IsFaceOf (↑facets : Set (Finset α)) K)
    (hJK : J = K) (r : stanleyReisnerRing F facets) :
    srFaceDetector F facets J hJ r = srFaceDetector F facets K hK r := by
  subst hJK; rfl

omit [Fintype α] in
/-- Strand elements built from cochains agreeing on the codimension-`p` **faces** of `σ` coincide. -/
theorem strandTensor_congr (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {g g' : Finset α → F}
    (hgg : ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
      IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
      g (σ \ Finset.image v Finset.univ) = g' (σ \ Finset.image v Finset.univ)) :
    strandTensor F facets σ (p := p) g = strandTensor F facets σ (p := p) g' := by
  funext v
  simp only [strandTensor]
  by_cases hv : (∀ t, v t ∈ σ) ∧ Function.Injective v
  · rw [if_pos hv, if_pos hv]
    by_cases hface : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ)
    · rw [hgg v hv.1 hv.2 hface]
    · rw [srProd_eq_zero_of_not_isFace facets hface, smul_zero, smul_zero]
  · rw [if_neg hv, if_neg hv]

/-! ### Hochster's correspondence in every degree -/

/-- **Hochster's correspondence in every Koszul degree.**  A multidegree-`σ` strand element at Koszul
degree `p+1` is a Koszul boundary **iff** its cochain agrees, on the codimension-`(p+1)` faces of `σ`,
with a reduced simplicial coboundary of the induced subcomplex `Δ_σ`.  Unconditional, for every finite
complex, every multidegree and every degree. -/
theorem hochster_strand_boundary_iff (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    strandTensor F facets σ (p := p + 1) g ∈ koszulBoundaries (p := p) (srVertexX F facets)
      ↔ ∃ h : Finset α → F, ∀ v : Fin (p + 1) → α, (∀ t, v t ∈ σ) → Function.Injective v →
          IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
          simplicialCoboundary F h (σ \ Finset.image v Finset.univ)
            = g (σ \ Finset.image v Finset.univ) := by
  classical
  constructor
  · rintro ⟨b, hb, hbg⟩
    have hbalt : IsAltTensor b := hb
    set n : (Fin (p + 2) → α) → F := fun u =>
      if hf : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image u Finset.univ) then
        srFaceDetector F facets (σ \ Finset.image u Finset.univ) hf (b u) else 0 with hndef
    have hn : ∀ (u : Fin (p + 2) → α) (π : Equiv.Perm (Fin (p + 2))),
        n (u ∘ ⇑π) = (Equiv.Perm.sign π : ℤ) • n u := by
      intro u π
      have himg : Finset.image (u ∘ ⇑π) Finset.univ = Finset.image u Finset.univ :=
        image_comp_perm u π
      simp only [hndef, himg]
      by_cases hf : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image u Finset.univ)
      · rw [dif_pos hf, dif_pos hf, hbalt.comp_perm π u, map_zsmul]
      · rw [dif_neg hf, dif_neg hf, smul_zero]
    set W : (Fin (p + 2) → α) → F := fun u =>
      if (∀ t, u t ∈ σ) ∧ Function.Injective u then
        (-1 : F) ^ (p + 1) * tupleSign F σ u * n u else 0 with hWdef
    have hWinv : ∀ (x : Fin (p + 2) → α) (π : Equiv.Perm (Fin (p + 2))), W (x ∘ ⇑π) = W x := by
      intro x π
      by_cases hg : (∀ t, x t ∈ σ) ∧ Function.Injective x
      · have hg' : (∀ t, (x ∘ ⇑π) t ∈ σ) ∧ Function.Injective (x ∘ ⇑π) :=
          ⟨fun t => hg.1 _, hg.2.comp π.injective⟩
        simp only [hWdef]
        rw [if_pos hg', if_pos hg, tupleSign_comp_perm σ x hg.1 hg.2 π, hn x π]
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> rw [hs]
        · simp
        · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
          ring
      · have hg' : ¬ ((∀ t, (x ∘ ⇑π) t ∈ σ) ∧ Function.Injective (x ∘ ⇑π)) := by
          intro hc
          refine hg ⟨fun t => ?_, ?_⟩
          · have := hc.1 (π.symm t)
            simpa using this
          · intro a c hac
            have hh : (x ∘ ⇑π) (π.symm a) = (x ∘ ⇑π) (π.symm c) := by simpa using hac
            simpa using hc.2 hh
        simp only [hWdef]
        rw [if_neg hg', if_neg hg]
    refine ⟨tupleCochain F σ W, fun v hvmem hvinj hface => ?_⟩
    set τ := σ \ Finset.image v Finset.univ with hτ
    have hins : ∀ k : α, σ \ Finset.image (Fin.cons k v : Fin (p + 2) → α) Finset.univ
        = τ.erase k := by
      intro k
      rw [image_cons, Finset.sdiff_insert, ← hτ]
    have hrow : ∑ k ∈ τ, n (Fin.cons k v) = tupleSign F σ v * g τ := by
      have hdet := srFaceDetector_koszulD facets hface b v
      have hleft : srFaceDetector F facets τ hface (koszulD (srVertexX F facets) b v)
          = srFaceDetector F facets τ hface (strandTensor F facets σ (p := p + 1) g v) := by
        rw [show koszulD (srVertexX F facets) b = strandTensor F facets σ (p := p + 1) g from hbg]
      have hright : srFaceDetector F facets τ hface (strandTensor F facets σ (p := p + 1) g v)
          = tupleSign F σ v * g τ := by
        show srFaceDetector F facets τ hface
            (if (∀ t, v t ∈ σ) ∧ Function.Injective v then _ else 0) = _
        rw [if_pos ⟨hvmem, hvinj⟩, ← hτ, map_smul, srFaceDetector_prod, smul_eq_mul, mul_one]
      rw [← hright, ← hleft, hdet]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [hndef]
      rw [dif_pos (show IsFaceOf (↑facets : Set (Finset α))
          (σ \ Finset.image (Fin.cons k v : Fin (p + 2) → α) Finset.univ) from by
        rw [hins k]; exact isFaceOf_mono (Finset.erase_subset k τ) hface)]
      exact srFaceDetector_congr (F := F) facets _ _ (hins k) _
    show ∑ k ∈ τ, faceSign F τ k * tupleCochain F σ W (τ.erase k) = g τ
    have hval : ∀ k ∈ τ, faceSign F τ k * tupleCochain F σ W (τ.erase k)
        = tupleSign F σ v * n (Fin.cons k v) := by
      intro k hk
      have hkσ : k ∈ σ := (Finset.mem_sdiff.mp hk).1
      have hkimg : k ∉ Finset.image v Finset.univ := (Finset.mem_sdiff.mp hk).2
      have hguard := cons_guard ⟨hvmem, hvinj⟩ hkσ hkimg
      rw [← hins k, tupleCochain_sdiff hWinv (Fin.cons k v) hguard.2 hguard.1]
      simp only [hWdef]
      rw [if_pos hguard]
      have hsnoc := tupleSign_snoc_eq_cons (F := F) σ v k hguard.1 hguard.2
      rw [tupleSign_snoc σ v k, ← hτ] at hsnoc
      have hfsq := faceSign_mul_self (F := F) τ k
      linear_combination (-(faceSign F τ k * n (Fin.cons k v))) * hsnoc
        + (tupleSign F σ v * n (Fin.cons k v)) * hfsq
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, hrow, ← mul_assoc,
      tupleSign_mul_self σ v, one_mul]
  · rintro ⟨h, hh⟩
    have hmem := strandTensor_coboundary_mem_koszulBoundaries facets σ (p := p) h
    rwa [strandTensor_congr facets σ (p := p + 1)
      (g := simplicialCoboundary F h) (g' := g) (fun v hv1 hv2 hface => hh v hv1 hv2 hface)] at hmem

/-! ### The cycle half in every degree -/

omit [Fintype α] in
/-- A strand element vanishes exactly when its cochain vanishes on the codimension-`p` faces of `σ`:
values at nonface complements are invisible. -/
theorem strandTensor_eq_zero_iff (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    strandTensor F facets σ (p := p) g = 0
      ↔ ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
          IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
          g (σ \ Finset.image v Finset.univ) = 0 := by
  constructor
  · intro hz v hv1 hv2 hface
    have hv := congrFun hz v
    rw [show strandTensor F facets σ (p := p) g v
        = (tupleSign F σ v * g (σ \ Finset.image v Finset.univ))
          • ∏ w ∈ σ \ Finset.image v Finset.univ, srVertexX F facets w from
      if_pos ⟨hv1, hv2⟩] at hv
    have hdet := congrArg (srFaceDetector F facets (σ \ Finset.image v Finset.univ) hface) hv
    rw [map_smul, srFaceDetector_prod, smul_eq_mul, mul_one, Pi.zero_apply, map_zero] at hdet
    have hsq := tupleSign_mul_self (F := F) σ v
    linear_combination (tupleSign F σ v) * hdet - (g (σ \ Finset.image v Finset.univ)) * hsq
  · intro hg
    have hzero : strandTensor F facets σ (p := p) g
        = strandTensor F facets σ (p := p) (fun _ => (0 : F)) :=
      strandTensor_congr facets σ (fun v h1 h2 hf => by rw [hg v h1 h2 hf])
    rw [hzero]
    funext v
    simp only [strandTensor, mul_zero, zero_smul, Pi.zero_apply, ite_self]

/-- **The cycle half in every degree.**  A strand element is a Koszul cycle exactly when its cochain
is a reduced simplicial cocycle on the codimension-`p` faces of `σ`. -/
theorem koszulD_strandTensor_eq_zero_iff (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    koszulD (srVertexX F facets) (strandTensor F facets σ (p := p + 1) g) = 0
      ↔ ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
          IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
          simplicialCoboundary F g (σ \ Finset.image v Finset.univ) = 0 := by
  have hsq : (-1 : F) ^ p * (-1 : F) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [koszulD_strandTensor facets σ g, ← strandTensor_eq_zero_iff facets σ]
  constructor
  · intro hz
    funext v
    have hv := congrFun hz v
    calc strandTensor F facets σ (p := p) (simplicialCoboundary F g) v
        = ((-1 : F) ^ p * (-1 : F) ^ p)
            • strandTensor F facets σ (p := p) (simplicialCoboundary F g) v := by
          rw [hsq, one_smul]
      _ = (-1 : F) ^ p • ((-1 : F) ^ p
            • strandTensor F facets σ (p := p) (simplicialCoboundary F g) v) := by
          rw [smul_smul]
      _ = (-1 : F) ^ p • (0 : stanleyReisnerRing F facets) := by rw [hv]; rfl
      _ = 0 := smul_zero _
  · intro hz
    funext v
    show (-1 : F) ^ p • strandTensor F facets σ (p := p) (simplicialCoboundary F g) v = 0
    rw [congrFun hz v]
    exact smul_zero _

/-- **Hochster's correspondence in every Koszul degree, packaged.**  For a multidegree-`σ` strand
element, being a Koszul cycle is being a reduced simplicial cocycle of the induced subcomplex `Δ_σ`,
and being a Koszul boundary is being a reduced simplicial coboundary — for every finite complex, every
multidegree and every degree, unconditionally and characteristic-freely. -/
theorem hochster_strand_correspondence (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    (koszulD (srVertexX F facets) (strandTensor F facets σ (p := p + 1) g) = 0
        ↔ ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
            IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
            simplicialCoboundary F g (σ \ Finset.image v Finset.univ) = 0)
      ∧ (strandTensor F facets σ (p := p + 1) g ∈ koszulBoundaries (p := p) (srVertexX F facets)
        ↔ ∃ h : Finset α → F, ∀ v : Fin (p + 1) → α, (∀ t, v t ∈ σ) → Function.Injective v →
            IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
            simplicialCoboundary F h (σ \ Finset.image v Finset.univ)
              = g (σ \ Finset.image v Finset.univ)) :=
  ⟨koszulD_strandTensor_eq_zero_iff facets σ g, hochster_strand_boundary_iff facets σ g⟩

end

end GaloisForLFunctions.HTGeometry
