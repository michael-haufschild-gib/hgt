import GaloisForLFunctions.HTGeometry.HochsterMultidegreeTorOne

/-!
# The Hochster strand chain map in degree three, and the characteristic-free `d₂ ∘ d₃ = 0`

The strand chain map from the reduced cochains of an induced subcomplex `Δ_σ` to the multidegree-`σ`
Koszul strand was built in degrees one and two (`strandOne`, `strandTwo`,
`srKoszulRelation_strandOne`, `srKoszulBoundary_strandTwo`).  This file extends it to degree three and
fixes the representation convention that the extension needs.

The corpus differential `srKoszulBoundary c i = ∑_j (c i j − c j i) x_j` is the standard alternating
`d₂` read on **strictly-upper-triangular representatives** of alternating `2`-tensors: on such a
representative it computes `∑_j a i j x_j`, whereas on the antisymmetric tensor itself it computes
`2 ∑_j a i j x_j`.  Since `srKoszulBoundary3` produces antisymmetric tensors, composing the two
directly carries a factor `2`, which is invisible in the corpus statement `d₂ ∘ d₃ = 0` but would
destroy a characteristic-free `Tor₂` correspondence.  Passing through `koszulUpperTri` removes it:

* `srKoszulBoundary_koszulUpperTri` — on an antisymmetric, zero-diagonal tensor the corpus
  differential of the upper-triangular representative is exactly `∑_j a i j x_j`;
* `srKoszulBoundary_koszulUpperTri_srKoszulBoundary3` — hence the **standard** `d₂ ∘ d₃ = 0`,
  unconditional and characteristic-free (the `(j,k)`-involution against the symmetric monomial
  product, with the diagonal killed by alternation).

The degree-three strand map `strandThree` sends a cochain on the codimension-three faces of `σ` to an
alternating `3`-tensor, using the iterated incidence sign
`faceSign σ i · faceSign (σ ∖ i) j · faceSign (σ ∖ {i,j}) k`, which is alternating because adjacent
transpositions are exactly the two instances of `faceSign_mul_faceSign_erase_antisymm`.  The chain-map
identity is

`koszulUpperTri (d₃ (strandThree h)) = strandTwo (δh)`,

so the strand maps intertwine the reduced simplicial coboundary with the Koszul differential one level
higher.  In particular every coboundary of a codimension-three cochain lands on a genuine Koszul
`3`-boundary, which is the backward half of Hochster's correspondence at `Tor₂`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### Upper-triangular representatives -/

/-- The strictly-upper-triangular representative of a `2`-tensor: the canonical representative of an
alternating tensor that the corpus differential `∑_j (c i j − c j i) x_j` reads without a factor `2`. -/
def koszulUpperTri {M : Type*} [Zero M] (a : α → α → M) : α → α → M :=
  fun i j => if i < j then a i j else 0

omit [DecidableEq α] in
/-- **The corpus differential on an upper-triangular representative is the standard one.**  For an
antisymmetric `2`-tensor with vanishing diagonal, `∑_j (uᵢⱼ − uⱼᵢ) x_j = ∑_j aᵢⱼ x_j`. -/
theorem srKoszulBoundary_koszulUpperTri (facets : Finset (Finset α))
    {a : α → α → stanleyReisnerRing F facets} (hanti : ∀ i j, a i j + a j i = 0)
    (hdiag : ∀ i, a i i = 0) (i : α) :
    srKoszulBoundary facets (koszulUpperTri a) i = ∑ j, a i j * srVertexX F facets j := by
  rw [srKoszulBoundary]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [koszulUpperTri]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, if_neg (asymm h), sub_zero]
  · subst h
    rw [if_neg (lt_irrefl i), sub_zero, hdiag i, zero_mul]
  · rw [if_neg (asymm h), if_pos h, zero_sub]
    linear_combination (-(srVertexX F facets j)) * hanti i j

omit [DecidableEq α] in
/-- **The standard `d₂ ∘ d₃ = 0`, characteristic-free.**  Reading the third Koszul differential of an
alternating `3`-tensor through its upper-triangular representative, the second differential
annihilates it — with no factor `2`, so the composite is a genuine complex in every characteristic. -/
theorem srKoszulBoundary_koszulUpperTri_srKoszulBoundary3 (facets : Finset (Finset α))
    {b : α → α → α → stanleyReisnerRing F facets} (hb : IsAlternating3 b) :
    srKoszulBoundary facets (koszulUpperTri (srKoszulBoundary3 facets b)) = 0 := by
  have hanti : ∀ i j, srKoszulBoundary3 facets b i j + srKoszulBoundary3 facets b j i = 0 := by
    intro i j
    rw [srKoszulBoundary3_antisymm facets hb i j]; ring
  have hdiag : ∀ i, srKoszulBoundary3 facets b i i = 0 := by
    intro i
    rw [srKoszulBoundary3]
    exact Finset.sum_eq_zero (fun k _ => by rw [hb.alt i i k (Or.inl rfl), zero_mul])
  funext i
  rw [srKoszulBoundary_koszulUpperTri facets hanti hdiag i]
  simp only [Pi.zero_apply, srKoszulBoundary3, Finset.sum_mul]
  rw [← Finset.sum_product']
  refine antisym_prod_sum_zero
    (fun j k => b i j k * srVertexX F facets k * srVertexX F facets j) ?_ ?_
  · intro j k
    show b i j k * srVertexX F facets k * srVertexX F facets j
      + b i k j * srVertexX F facets j * srVertexX F facets k = 0
    rw [hb.antisym23 i j k]; ring
  · intro j
    show b i j j * srVertexX F facets j * srVertexX F facets j = 0
    rw [hb.alt i j j (Or.inr (Or.inl rfl))]; ring

/-! ### The iterated incidence sign -/

omit [Fintype α] in
/-- The iterated incidence sign is antisymmetric in its first two vertices. -/
theorem faceSign3_antisym12 {σ : Finset α} {i j : α} (hi : i ∈ σ) (hj : j ∈ σ) (hij : i ≠ j)
    (k : α) :
    faceSign F σ j * faceSign F (σ.erase j) i * faceSign F ((σ.erase j).erase i) k
      = - (faceSign F σ i * faceSign F (σ.erase i) j * faceSign F ((σ.erase i).erase j) k) := by
  have hs := faceSign_mul_faceSign_erase_antisymm (F := F) hi hj hij
  rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]
  linear_combination (faceSign F ((σ.erase i).erase j) k) * hs

omit [Fintype α] in
/-- The iterated incidence sign is antisymmetric in its last two vertices. -/
theorem faceSign3_antisym23 {σ : Finset α} {i j k : α} (hj : j ∈ σ.erase i) (hk : k ∈ σ.erase i)
    (hjk : j ≠ k) :
    faceSign F σ i * faceSign F (σ.erase i) k * faceSign F ((σ.erase i).erase k) j
      = - (faceSign F σ i * faceSign F (σ.erase i) j * faceSign F ((σ.erase i).erase j) k) := by
  have hs := faceSign_mul_faceSign_erase_antisymm (F := F) hj hk hjk
  linear_combination (faceSign F σ i) * hs

/-! ### The degree-three strand map -/

/-- The degree-three strand map: a cochain on the codimension-three faces of `σ` becomes an
alternating multidegree-`σ` Koszul `3`-tensor, weighted by the iterated incidence sign. -/
def strandThree (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α)
    (h : Finset α → F) : α → α → α → stanleyReisnerRing F facets :=
  fun i j k => if i ∈ σ ∧ j ∈ σ ∧ k ∈ σ ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k then
      (faceSign F σ i * faceSign F (σ.erase i) j * faceSign F ((σ.erase i).erase j) k
          * h (((σ.erase i).erase j).erase k))
        • ∏ w ∈ ((σ.erase i).erase j).erase k, srVertexX F facets w
    else 0

omit [Fintype α] in
/-- The degree-three strand map lands in alternating tensors, so it feeds the third Koszul
differential. -/
theorem strandThree_isAlternating3 (facets : Finset (Finset α)) (σ : Finset α) (h : Finset α → F) :
    IsAlternating3 (strandThree F facets σ h) := by
  refine ⟨fun i j k => ?_, fun i j k => ?_, fun i j k hrep => ?_⟩
  · simp only [strandThree]
    by_cases hg : i ∈ σ ∧ j ∈ σ ∧ k ∈ σ ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k
    · obtain ⟨hi, hj, hk, hij, hjk, hik⟩ := hg
      rw [if_pos ⟨hi, hj, hk, hij, hjk, hik⟩,
        if_pos ⟨hj, hi, hk, Ne.symm hij, hik, hjk⟩,
        show ((σ.erase j).erase i).erase k = ((σ.erase i).erase j).erase k from by
          rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm],
        ← neg_smul, faceSign3_antisym12 hi hj hij k]
      congr 1
      ring
    · rw [if_neg hg, if_neg (fun hc => hg ⟨hc.2.1, hc.1, hc.2.2.1, Ne.symm hc.2.2.2.1,
        hc.2.2.2.2.2, hc.2.2.2.2.1⟩), neg_zero]
  · simp only [strandThree]
    by_cases hg : i ∈ σ ∧ j ∈ σ ∧ k ∈ σ ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k
    · obtain ⟨hi, hj, hk, hij, hjk, hik⟩ := hg
      rw [if_pos ⟨hi, hj, hk, hij, hjk, hik⟩,
        if_pos ⟨hi, hk, hj, hik, Ne.symm hjk, hij⟩,
        show ((σ.erase i).erase k).erase j = ((σ.erase i).erase j).erase k from
          Finset.erase_right_comm,
        ← neg_smul,
        faceSign3_antisym23 (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩)
          (Finset.mem_erase.mpr ⟨Ne.symm hik, hk⟩) hjk]
      congr 1
      ring
    · rw [if_neg hg, if_neg (fun hc => hg ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2.2.2,
        Ne.symm hc.2.2.2.2.1, hc.2.2.2.1⟩), neg_zero]
  · refine if_neg (fun hc => ?_)
    rcases hrep with hr | hr | hr
    · exact hc.2.2.2.1 hr
    · exact hc.2.2.2.2.1 hr
    · exact hc.2.2.2.2.2 hr

/-- **Chain map in degree three.**  The upper-triangular representative of the third Koszul
differential of the degree-three strand map is the degree-two strand map of the coboundary.  So the
strand maps intertwine the reduced simplicial coboundary of `Δ_σ` with the Koszul differential at the
next level, for every finite complex and every multidegree. -/
theorem koszulUpperTri_srKoszulBoundary3_strandThree (facets : Finset (Finset α)) (σ : Finset α)
    (h : Finset α → F) :
    koszulUpperTri (srKoszulBoundary3 facets (strandThree F facets σ h))
      = strandTwo F facets σ (simplicialCoboundary F h) := by
  funext i j
  simp only [koszulUpperTri, strandTwo]
  by_cases hij : i < j
  · rw [if_pos hij]
    by_cases hmem : i ∈ σ ∧ j ∈ σ
    · obtain ⟨hi, hj⟩ := hmem
      rw [if_pos ⟨hij, hi, hj⟩, srKoszulBoundary3]
      have hterm : ∀ k : α, strandThree F facets σ h i j k * srVertexX F facets k
          = if k ∈ (σ.erase i).erase j then
              (faceSign F σ i * faceSign F (σ.erase i) j
                  * (faceSign F ((σ.erase i).erase j) k * h (((σ.erase i).erase j).erase k)))
                • ∏ w ∈ (σ.erase i).erase j, srVertexX F facets w
            else 0 := by
        intro k
        simp only [strandThree]
        by_cases hk : k ∈ (σ.erase i).erase j
        · have h1 := Finset.mem_erase.mp hk
          have hkj : k ≠ j := h1.1
          have h2 := Finset.mem_erase.mp h1.2
          have hki : k ≠ i := h2.1
          have hkσ : k ∈ σ := h2.2
          rw [if_pos ⟨hi, hj, hkσ, hij.ne, Ne.symm hkj, Ne.symm hki⟩, if_pos hk,
            smul_mul_assoc,
            Finset.prod_erase_mul ((σ.erase i).erase j) (srVertexX F facets) hk]
          congr 1
          ring
        · rw [if_neg hk, if_neg (fun hc => hk (Finset.mem_erase.mpr ⟨Ne.symm hc.2.2.2.2.1,
            Finset.mem_erase.mpr ⟨Ne.symm hc.2.2.2.2.2, hc.2.2.1⟩⟩)), zero_mul]
      rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_mem, Finset.univ_inter,
        ← Finset.sum_smul]
      congr 1
      show _ = faceSign F σ i * faceSign F (σ.erase i) j
        * ∑ v ∈ (σ.erase i).erase j, faceSign F ((σ.erase i).erase j) v
            * h (((σ.erase i).erase j).erase v)
      rw [Finset.mul_sum]
    · rw [if_neg (fun hc => hmem ⟨hc.2.1, hc.2.2⟩), srKoszulBoundary3]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      simp only [strandThree]
      rw [if_neg (fun hc => hmem ⟨hc.1, hc.2.1⟩), zero_mul]
  · rw [if_neg hij, if_neg (fun hc => hij hc.1)]

omit [Fintype α] in
/-- Degree-two strand elements built from cochains agreeing on the codimension-two **faces** of `σ`
coincide: values at nonface slots are invisible because the monomial vanishes. -/
theorem strandTwo_congr (facets : Finset (Finset α)) (σ : Finset α) {g g' : Finset α → F}
    (hgg : ∀ i j, i ∈ σ → j ∈ σ → i ≠ j →
      IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) →
      g ((σ.erase i).erase j) = g' ((σ.erase i).erase j)) :
    strandTwo F facets σ g = strandTwo F facets σ g' := by
  funext i j
  simp only [strandTwo]
  by_cases hc : i < j ∧ i ∈ σ ∧ j ∈ σ
  · rw [if_pos hc, if_pos hc]
    by_cases hface : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j)
    · rw [hgg i j hc.2.1 hc.2.2 hc.1.ne hface]
    · rw [srProd_eq_zero_of_not_isFace facets hface, smul_zero, smul_zero]
  · rw [if_neg hc, if_neg hc]

/-- **Backward half of Hochster's correspondence at `Tor₂`.**  If a degree-two strand cochain agrees
on the codimension-two faces of `σ` with the coboundary of a codimension-three cochain, then the
corresponding multidegree-`σ` Koszul `2`-chain is the (upper-triangular) third Koszul boundary of an
alternating `3`-tensor.  So the strand chain map carries reduced coboundaries of `Δ_σ` into genuine
Koszul boundaries one level up, characteristic-freely. -/
theorem strandTwo_isKoszulBoundary3_of_coboundary (facets : Finset (Finset α)) (σ : Finset α)
    (g h : Finset α → F)
    (hgh : ∀ i j, i ∈ σ → j ∈ σ → i ≠ j →
      IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) →
      simplicialCoboundary F h ((σ.erase i).erase j) = g ((σ.erase i).erase j)) :
    ∃ b : α → α → α → stanleyReisnerRing F facets, IsAlternating3 b ∧
      koszulUpperTri (srKoszulBoundary3 facets b) = strandTwo F facets σ g :=
  ⟨strandThree F facets σ h, strandThree_isAlternating3 facets σ h, by
    rw [koszulUpperTri_srKoszulBoundary3_strandThree]
    exact strandTwo_congr facets σ hgh⟩

end

end GaloisForLFunctions.HTGeometry
