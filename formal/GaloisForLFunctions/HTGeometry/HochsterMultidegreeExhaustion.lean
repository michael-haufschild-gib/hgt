import GaloisForLFunctions.HTGeometry.HochsterStrandGeneralBoundary
import GaloisForLFunctions.HTGeometry.StanleyReisnerMultigrading

/-!
# The strand map exhausts the multidegree-`σ` part of the alternating Koszul complex

The strand map `strandTensor` is a chain map in every Koszul degree and reflects cycles and boundaries
exactly (`hochster_strand_correspondence`).  What remained for a genuine identification of the
multidegree-`σ` Koszul homology with the reduced cohomology of the induced subcomplex `Δ_σ` was
**surjectivity**: that every multidegree-`σ` tensor of the alternating Koszul complex is `strandTensor g`
for some cochain `g`.  This file proves it.

`IsMultidegreeStrand` is the (definitional) multidegree condition: the tensor vanishes off injective
tuples with entries in `σ`, and on those it is a scalar multiple of the complementary squarefree
monomial `∏_{σ ∖ v[Fin p]} x` — precisely the degree-`(σ ∖ v[Fin p])` graded piece of the
Stanley–Reisner ring, which is free of rank one on that monomial
(`StanleyReisnerMultigrading.srFaceDetector_smul_prod`).

* `strandTensor_isMultidegreeStrand` — the strand map lands there;
* `strandTensor_strandCochain` — and hits everything: for an alternating multidegree-`σ` tensor `b`,
  `strandTensor (strandCochain b) = b`, where `strandCochain b` is the `tupleCochain` of the weight
  `tupleSign σ u · (face detector of b at u)`.  The scalar is recovered by the face detector when the
  complement is a face, and is invisible when it is not, because then the monomial vanishes.
* `hochster_multidegree_strand_correspondence` — consequently the cycle/boundary correspondence holds
  for an **arbitrary** alternating multidegree-`σ` tensor, not only for those presented as strand
  images: multidegree-`σ` Koszul cycles are exactly the reduced simplicial cocycles of `Δ_σ` and
  multidegree-`σ` Koszul boundaries are exactly its coboundaries, in every degree, for every finite
  complex, unconditionally and characteristic-freely.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-- Being a face of a finite facet family is decidable: the defining existential ranges over the
facet `Finset`. -/
instance decidableIsFaceOfCoe (facets : Finset (Finset α)) (J : Finset α) :
    Decidable (IsFaceOf (↑facets : Set (Finset α)) J) :=
  decidable_of_iff (∃ G ∈ facets, J ⊆ G) (by simp [IsFaceOf])

/-! ### The multidegree condition -/

/-- A tensor is a **multidegree-`σ` strand element** when it vanishes off injective tuples with
entries in `σ` and, on those, is a scalar multiple of the complementary squarefree monomial. -/
def IsMultidegreeStrand (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α)
    {p : ℕ} (b : (Fin p → α) → stanleyReisnerRing F facets) : Prop :=
  (∀ v : Fin p → α, ¬ ((∀ t, v t ∈ σ) ∧ Function.Injective v) → b v = 0) ∧
    ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
      ∃ c : F, b v = c • ∏ w ∈ σ \ Finset.image v Finset.univ, srVertexX F facets w

omit [Fintype α] in
/-- The strand map lands in the multidegree-`σ` part. -/
theorem strandTensor_isMultidegreeStrand (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    IsMultidegreeStrand F facets σ (strandTensor F facets σ (p := p) g) :=
  ⟨fun _ hv => if_neg hv,
    fun v h1 h2 => ⟨tupleSign F σ v * g (σ \ Finset.image v Finset.univ), if_pos ⟨h1, h2⟩⟩⟩

/-! ### The cochain attached to a tensor -/

/-- The face detector of a tensor at the complement of a tuple. -/
def strandDetector (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (b : (Fin p → α) → stanleyReisnerRing F facets) : (Fin p → α) → F :=
  fun u => if hf : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image u Finset.univ) then
      srFaceDetector F facets (σ \ Finset.image u Finset.univ) hf (b u) else 0

omit [LinearOrder α] [Fintype α] in
/-- The face detector of an alternating tensor transforms by the sign of the permutation. -/
theorem strandDetector_comp_perm (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {b : (Fin p → α) → stanleyReisnerRing F facets} (hb : IsAltTensor b)
    (u : Fin p → α) (π : Equiv.Perm (Fin p)) :
    strandDetector F facets σ b (u ∘ ⇑π)
      = (Equiv.Perm.sign π : ℤ) • strandDetector F facets σ b u := by
  have himg := image_comp_perm u π
  simp only [strandDetector, himg]
  by_cases hf : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image u Finset.univ)
  · rw [dif_pos hf, dif_pos hf, hb.comp_perm π u, map_zsmul]
  · rw [dif_neg hf, dif_neg hf, smul_zero]

/-- The permutation-invariant weight attached to a tensor: the iterated incidence sign times the face
detector, a product of two families that each transform by the sign. -/
def strandWeight (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (b : (Fin p → α) → stanleyReisnerRing F facets) : (Fin p → α) → F :=
  fun u => if (∀ t, u t ∈ σ) ∧ Function.Injective u then
      tupleSign F σ u * strandDetector F facets σ b u else 0

omit [Fintype α] in
/-- The weight attached to an alternating tensor is invariant under permutations of the tuple: both
factors transform by the sign. -/
theorem strandWeight_comp_perm (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {b : (Fin p → α) → stanleyReisnerRing F facets} (hb : IsAltTensor b)
    (u : Fin p → α) (π : Equiv.Perm (Fin p)) :
    strandWeight F facets σ b (u ∘ ⇑π) = strandWeight F facets σ b u := by
  by_cases hg : (∀ t, u t ∈ σ) ∧ Function.Injective u
  · have hg' : (∀ t, (u ∘ ⇑π) t ∈ σ) ∧ Function.Injective (u ∘ ⇑π) :=
      ⟨fun t => hg.1 _, hg.2.comp π.injective⟩
    simp only [strandWeight]
    rw [if_pos hg', if_pos hg, tupleSign_comp_perm σ u hg.1 hg.2 π,
      strandDetector_comp_perm facets σ hb u π]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> rw [hs]
    · simp
    · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
      ring
  · have hg' : ¬ ((∀ t, (u ∘ ⇑π) t ∈ σ) ∧ Function.Injective (u ∘ ⇑π)) := by
      intro hc
      refine hg ⟨fun t => ?_, ?_⟩
      · have := hc.1 (π.symm t)
        simpa using this
      · intro a c hac
        have hh : (u ∘ ⇑π) (π.symm a) = (u ∘ ⇑π) (π.symm c) := by simpa using hac
        simpa using hc.2 hh
    simp only [strandWeight]
    rw [if_neg hg', if_neg hg]

/-- The reduced cochain of `Δ_σ` attached to a multidegree-`σ` tensor. -/
def strandCochain (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (b : (Fin p → α) → stanleyReisnerRing F facets) : Finset α → F :=
  tupleCochain F σ (strandWeight F facets σ b)

/-! ### Exhaustion -/

omit [Fintype α] in
/-- **The strand map exhausts the multidegree-`σ` part.**  Every alternating multidegree-`σ` tensor is
the strand image of its own cochain.  The scalar at a tuple is recovered by the face detector when the
complement is a face, and is invisible otherwise because the complementary monomial then vanishes. -/
theorem strandTensor_strandCochain (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    {b : (Fin p → α) → stanleyReisnerRing F facets} (hb : IsAltTensor b)
    (hstr : IsMultidegreeStrand F facets σ b) :
    strandTensor F facets σ (p := p) (strandCochain F facets σ b) = b := by
  funext v
  by_cases hv : (∀ t, v t ∈ σ) ∧ Function.Injective v
  · obtain ⟨c, hc⟩ := hstr.2 v hv.1 hv.2
    show (if (∀ t, v t ∈ σ) ∧ Function.Injective v then
        (tupleSign F σ v * strandCochain F facets σ b (σ \ Finset.image v Finset.univ))
          • ∏ w ∈ σ \ Finset.image v Finset.univ, srVertexX F facets w
      else 0) = b v
    rw [if_pos hv, strandCochain,
      tupleCochain_sdiff (strandWeight_comp_perm facets σ hb) v hv.2 hv.1]
    by_cases hface : IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ)
    · have hdet : strandDetector F facets σ b v = c := by
        simp only [strandDetector]
        rw [dif_pos hface, hc, srFaceDetector_smul_prod]
      simp only [strandWeight]
      rw [if_pos hv, hdet, ← mul_assoc, tupleSign_mul_self, one_mul, hc]
    · rw [srProd_eq_zero_of_not_isFace facets hface, smul_zero, hc,
        srProd_eq_zero_of_not_isFace facets hface, smul_zero]
  · show (if (∀ t, v t ∈ σ) ∧ Function.Injective v then _ else 0) = b v
    rw [if_neg hv]
    exact (hstr.1 v hv).symm

/-! ### Hochster's correspondence for arbitrary multidegree-`σ` tensors -/

/-- **Hochster's correspondence at every degree, for an arbitrary multidegree-`σ` tensor.**  A
multidegree-`σ` element of the alternating Koszul complex is a Koszul cycle exactly when its cochain
is a reduced simplicial cocycle of the induced subcomplex `Δ_σ`, and a Koszul boundary exactly when
its cochain is a reduced simplicial coboundary.  Together with `strandTensor_strandCochain` this
identifies the multidegree-`σ` Koszul homology with the reduced cohomology of `Δ_σ` in every degree,
for every finite complex, unconditionally. -/
theorem hochster_multidegree_strand_correspondence (facets : Finset (Finset α)) (σ : Finset α)
    {p : ℕ} {b : (Fin (p + 1) → α) → stanleyReisnerRing F facets} (hb : IsAltTensor b)
    (hstr : IsMultidegreeStrand F facets σ b) :
    (koszulD (srVertexX F facets) b = 0
        ↔ ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
            IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
            simplicialCoboundary F (strandCochain F facets σ b)
              (σ \ Finset.image v Finset.univ) = 0)
      ∧ (b ∈ koszulBoundaries (p := p) (srVertexX F facets)
        ↔ ∃ h : Finset α → F, ∀ v : Fin (p + 1) → α, (∀ t, v t ∈ σ) → Function.Injective v →
            IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
            simplicialCoboundary F h (σ \ Finset.image v Finset.univ)
              = strandCochain F facets σ b (σ \ Finset.image v Finset.univ)) := by
  have hbe : strandTensor F facets σ (p := p + 1) (strandCochain F facets σ b) = b :=
    strandTensor_strandCochain facets σ hb hstr
  set g := strandCochain F facets σ b with hgdef
  rw [← hbe]
  exact hochster_strand_correspondence facets σ g

end

end GaloisForLFunctions.HTGeometry
