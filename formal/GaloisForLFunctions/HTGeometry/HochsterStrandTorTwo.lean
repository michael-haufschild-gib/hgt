import GaloisForLFunctions.HTGeometry.HochsterStrandDegreeThree

/-!
# Hochster's correspondence at `Tor₂`: strand boundaries are exactly coboundaries

The degree-three chain map `koszulUpperTri (d₃ (strandThree h)) = strandTwo (δh)` gives one half of
Hochster's correspondence at `Tor₂`: a coboundary of a codimension-three cochain becomes a genuine
Koszul `3`-boundary.  This file proves the converse, so that the multidegree-`σ` strand boundaries at
Koszul degree two are *exactly* the reduced simplicial coboundaries of the induced subcomplex `Δ_σ`,
for every finite complex and every multidegree, unconditionally.

The primitive is reconstructed from the face detectors of the alternating `3`-tensor.  The resulting
coefficient family `n i j k` is alternating, and the codimension-three cochain is

`tripleCochain σ n (τ) = ∑_{p<q<r ∈ σ, τ = σ ∖ {p,q,r}} faceSign₃ σ p q r · n p q r`,

the triple analogue of `pairCochain`.  Two ingredients make its evaluation work at an *arbitrary*
distinct triple, not only at a sorted one:

* `sdiff_inj_of_subset` and `sorted_triple_eq` — the complement `σ ∖ {i,j,k}` determines the triple as
  a set, and a set has exactly one increasing enumeration, so the guarded sum has a single surviving
  term;
* `tripleWeight_swap12`, `tripleWeight_swap23` — the weight `faceSign₃ σ i j k · n i j k` is a product
  of two alternating families, hence **symmetric**; so the surviving sorted term equals the weight at
  the original triple.

The `p < q < r` guard is what keeps everything characteristic-free: an unguarded symmetrization over
the six orderings would produce a factor `6`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### Complements of triples -/

omit [LinearOrder α] [Fintype α] in
/-- Deleting three vertices one at a time is deleting the triple. -/
theorem erase3_eq_sdiff (σ : Finset α) (i j k : α) :
    ((σ.erase i).erase j).erase k = σ \ {i, j, k} := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [LinearOrder α] [Fintype α] in
/-- Complements inside `σ` determine the subset. -/
theorem sdiff_inj_of_subset {σ J K : Finset α} (hJ : J ⊆ σ) (hK : K ⊆ σ) (h : σ \ J = σ \ K) :
    J = K := by
  rw [← Finset.sdiff_sdiff_eq_self hJ, ← Finset.sdiff_sdiff_eq_self hK, h]

omit [Fintype α] in
/-- A three-element set has exactly one increasing enumeration. -/
theorem sorted_triple_eq {p q r i j k : α} (hpq : p < q) (hqr : q < r) (hij : i < j) (hjk : j < k)
    (hset : ({p, q, r} : Finset α) = {i, j, k}) : p = i ∧ q = j ∧ r = k := by
  have hple : ∀ x ∈ ({p, q, r} : Finset α), p ≤ x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_refl _
    · exact hpq.le
    · exact (hpq.trans hqr).le
  have hile : ∀ x ∈ ({i, j, k} : Finset α), i ≤ x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_refl _
    · exact hij.le
    · exact (hij.trans hjk).le
  have hrge : ∀ x ∈ ({p, q, r} : Finset α), x ≤ r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hpq.trans hqr).le
    · exact hqr.le
    · exact le_refl _
  have hkge : ∀ x ∈ ({i, j, k} : Finset α), x ≤ k := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hij.trans hjk).le
    · exact hjk.le
    · exact le_refl _
  have hpi : p = i :=
    le_antisymm (hple i (by rw [hset]; simp)) (hile p (by rw [← hset]; simp))
  have hrk : r = k :=
    le_antisymm (hkge r (by rw [← hset]; simp)) (hrge k (by rw [hset]; simp))
  refine ⟨hpi, ?_, hrk⟩
  have hq' : q ∈ ({i, j, k} : Finset α) := by rw [← hset]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
  rcases hq' with h | h | h
  · exact absurd (h.trans hpi.symm) hpq.ne'
  · exact h
  · exact absurd (h.trans hrk.symm) hqr.ne

/-! ### The triple weight and its symmetry -/

omit [Fintype α] in
/-- The iterated incidence sign of a triple. -/
def faceSign3 (F : Type*) [CommRing F] (σ : Finset α) (i j k : α) : F :=
  faceSign F σ i * faceSign F (σ.erase i) j * faceSign F ((σ.erase i).erase j) k

/-- The weight attached to an ordered triple by an alternating coefficient family: a product of two
alternating families, hence symmetric under every permutation of the triple. -/
def tripleWeight (F : Type*) [CommRing F] (σ : Finset α) (n : α → α → α → F) (i j k : α) : F :=
  faceSign3 F σ i j k * n i j k

omit [Fintype α] in
/-- The triple weight is invariant under the first adjacent transposition. -/
theorem tripleWeight_swap12 {σ : Finset α} {n : α → α → α → F} (hn : IsAlternating3 n)
    {i j : α} (hi : i ∈ σ) (hj : j ∈ σ) (hij : i ≠ j) (k : α) :
    tripleWeight F σ n j i k = tripleWeight F σ n i j k := by
  simp only [tripleWeight, faceSign3]
  rw [faceSign3_antisym12 hi hj hij k, hn.antisym12 j i k]
  ring

omit [Fintype α] in
/-- The triple weight is invariant under the second adjacent transposition. -/
theorem tripleWeight_swap23 {σ : Finset α} {n : α → α → α → F} (hn : IsAlternating3 n)
    {i j k : α} (hj : j ∈ σ.erase i) (hk : k ∈ σ.erase i) (hjk : j ≠ k) :
    tripleWeight F σ n i k j = tripleWeight F σ n i j k := by
  simp only [tripleWeight, faceSign3]
  rw [faceSign3_antisym23 hj hk hjk, hn.antisym23 i k j]
  ring

/-! ### The codimension-three cochain -/

/-- The codimension-three cochain attached to an alternating coefficient family: the triple analogue
of `pairCochain`, with the increasing-triple guard that avoids the factor `6`. -/
def tripleCochain (F : Type*) [CommRing F] (σ : Finset α) (n : α → α → α → F) : Finset α → F :=
  fun τ => ∑ p ∈ σ, ∑ q ∈ σ, ∑ r ∈ σ,
    if p < q ∧ q < r ∧ τ = σ \ {p, q, r} then tripleWeight F σ n p q r else 0

omit [Fintype α] in
/-- Only the increasing enumeration of a triple survives the guard. -/
theorem triple_guard_eq {σ : Finset α} {i j k p q r : α}
    (hi : i ∈ σ) (hj : j ∈ σ) (hk : k ∈ σ) (hp : p ∈ σ) (hq : q ∈ σ) (hr : r ∈ σ)
    (hij : i < j) (hjk : j < k) (hpq : p < q) (hqr : q < r)
    (heq : σ \ ({i, j, k} : Finset α) = σ \ {p, q, r}) : p = i ∧ q = j ∧ r = k := by
  have hsub1 : ({i, j, k} : Finset α) ⊆ σ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hsub2 : ({p, q, r} : Finset α) ⊆ σ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  exact sorted_triple_eq hpq hqr hij hjk (sdiff_inj_of_subset hsub1 hsub2 heq).symm

omit [Fintype α] in
/-- Evaluation of the codimension-three cochain at an increasing triple. -/
theorem tripleCochain_sdiff_sorted {σ : Finset α} {n : α → α → α → F} {i j k : α}
    (hi : i ∈ σ) (hj : j ∈ σ) (hk : k ∈ σ) (hij : i < j) (hjk : j < k) :
    tripleCochain F σ n (σ \ {i, j, k}) = tripleWeight F σ n i j k := by
  show (∑ p ∈ σ, ∑ q ∈ σ, ∑ r ∈ σ,
      if p < q ∧ q < r ∧ σ \ ({i, j, k} : Finset α) = σ \ {p, q, r} then
        tripleWeight F σ n p q r else 0) = _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · exact if_pos ⟨hij, hjk, rfl⟩
      · intro r hr hrk
        refine if_neg (fun hc => hrk ?_)
        exact (triple_guard_eq hi hj hk hi hj hr hij hjk hc.1 hc.2.1 hc.2.2).2.2
      · intro hmem; exact absurd hk hmem
    · intro q hq hqj
      refine Finset.sum_eq_zero (fun r hr => if_neg (fun hc => hqj ?_))
      exact (triple_guard_eq hi hj hk hi hq hr hij hjk hc.1 hc.2.1 hc.2.2).2.1
    · intro hmem; exact absurd hj hmem
  · intro p hp hpi
    refine Finset.sum_eq_zero (fun q hq => Finset.sum_eq_zero (fun r hr => if_neg (fun hc => hpi ?_)))
    exact (triple_guard_eq hi hj hk hp hq hr hij hjk hc.1 hc.2.1 hc.2.2).1
  · intro hmem; exact absurd hi hmem

omit [Fintype α] in
/-- **Evaluation of the codimension-three cochain at an arbitrary distinct triple.**  The guard keeps
the increasing enumeration; the symmetry of the weight identifies it with the given ordering. -/
theorem tripleCochain_sdiff {σ : Finset α} {n : α → α → α → F} (hn : IsAlternating3 n) {i j k : α}
    (hi : i ∈ σ) (hj : j ∈ σ) (hk : k ∈ σ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    tripleCochain F σ n (σ \ {i, j, k}) = tripleWeight F σ n i j k := by
  have hje : j ∈ σ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hke : k ∈ σ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, hk⟩
  have hie : i ∈ σ.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  have hke' : k ∈ σ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjk, hk⟩
  have hie' : i ∈ σ.erase k := Finset.mem_erase.mpr ⟨hik, hi⟩
  have hje' : j ∈ σ.erase k := Finset.mem_erase.mpr ⟨hjk, hj⟩
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · rcases lt_or_gt_of_ne hjk with hjk' | hjk'
    · exact tripleCochain_sdiff_sorted hi hj hk hij' hjk'
    · rcases lt_or_gt_of_ne hik with hik' | hik'
      · rw [show ({i, j, k} : Finset α) = {i, k, j} from by ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
          tripleCochain_sdiff_sorted hi hk hj hik' hjk']
        exact tripleWeight_swap23 hn hje hke hjk
      · rw [show ({i, j, k} : Finset α) = {k, i, j} from by ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
          tripleCochain_sdiff_sorted hk hi hj hik' hij']
        rw [tripleWeight_swap12 hn hi hk hik j]
        exact tripleWeight_swap23 hn hje hke hjk
  · rcases lt_or_gt_of_ne hik with hik' | hik'
    · rw [show ({i, j, k} : Finset α) = {j, i, k} from by ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
        tripleCochain_sdiff_sorted hj hi hk hij' hik']
      exact tripleWeight_swap12 hn hi hj hij k
    · rcases lt_or_gt_of_ne hjk with hjk' | hjk'
      · rw [show ({i, j, k} : Finset α) = {j, k, i} from by ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
          tripleCochain_sdiff_sorted hj hk hi hjk' hik']
        rw [tripleWeight_swap23 hn hie hke' hik]
        exact tripleWeight_swap12 hn hi hj hij k
      · rw [show ({i, j, k} : Finset α) = {k, j, i} from by ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
          tripleCochain_sdiff_sorted hk hj hi hjk' hij']
        rw [tripleWeight_swap23 hn hie' hje' hij]
        rw [tripleWeight_swap12 hn hi hk hik j]
        exact tripleWeight_swap23 hn hje hke hjk

/-! ### The coboundary of the codimension-three cochain -/

omit [Fintype α] in
/-- **The coboundary of the reconstructed primitive.**  At a codimension-two set of `σ` the coboundary
of `tripleCochain σ n` is the incidence sign of the pair times the row sum of the coefficient
family. -/
theorem simplicialCoboundary_tripleCochain {σ : Finset α} {n : α → α → α → F}
    (hn : IsAlternating3 n) {i j : α} (hi : i ∈ σ) (hj : j ∈ σ) (hij : i ≠ j) :
    simplicialCoboundary F (tripleCochain F σ n) ((σ.erase i).erase j)
      = faceSign F σ i * faceSign F (σ.erase i) j
          * ∑ k ∈ (σ.erase i).erase j, n i j k := by
  show ∑ k ∈ (σ.erase i).erase j, faceSign F ((σ.erase i).erase j) k
      * tripleCochain F σ n (((σ.erase i).erase j).erase k) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkσ : k ∈ σ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
  rw [erase3_eq_sdiff, tripleCochain_sdiff hn hi hj hkσ hij (Ne.symm hkj) (Ne.symm hki)]
  simp only [tripleWeight, faceSign3]
  have hsq := faceSign_mul_self (F := F) ((σ.erase i).erase j) k
  linear_combination (faceSign F σ i * faceSign F (σ.erase i) j * n i j k) * hsq

/-! ### The face detector of a third Koszul boundary -/

omit [LinearOrder α] in
/-- The `J`-face detector of a third Koszul boundary at `(i,j)` is the sum over `k ∈ J` of the
deleted-vertex detectors of the coefficients. -/
theorem srFaceDetector_srKoszulBoundary3 (facets : Finset (Finset α)) {J : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J)
    (b : α → α → α → stanleyReisnerRing F facets) (i j : α) :
    srFaceDetector F facets J hJ (srKoszulBoundary3 facets b i j)
      = ∑ k ∈ J, srFaceDetector F facets (J.erase k)
          (isFaceOf_mono (Finset.erase_subset k J) hJ) (b i j k) := by
  rw [srKoszulBoundary3, map_sum,
    Finset.sum_congr rfl (fun k _ => srFaceDetector_mul_srVertexX facets hJ (b i j k)),
    Finset.sum_ite_mem, Finset.univ_inter]

/-! ### Hochster's correspondence at `Tor₂` -/

/-- **Forward half of Hochster's correspondence at `Tor₂`.**  If a degree-two strand element is the
(upper-triangular) third Koszul boundary of an alternating `3`-tensor, then its cochain agrees on the
codimension-two faces of `σ` with a genuine reduced simplicial coboundary of `Δ_σ`.

The primitive is the `tripleCochain` of the face detectors of the tensor; the detector identity turns
the boundary equation into the row sums, and the evaluation of `tripleCochain` at arbitrary distinct
triples converts those row sums into the coboundary. -/
theorem exists_coboundary_of_strandTwo_isKoszulBoundary3 (facets : Finset (Finset α))
    (σ : Finset α) (g : Finset α → F) {b : α → α → α → stanleyReisnerRing F facets}
    (hb : IsAlternating3 b)
    (hbg : koszulUpperTri (srKoszulBoundary3 facets b) = strandTwo F facets σ g) :
    ∃ h : Finset α → F, ∀ i j, i ∈ σ → j ∈ σ → i ≠ j →
      IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) →
      simplicialCoboundary F h ((σ.erase i).erase j) = g ((σ.erase i).erase j) := by
  classical
  set n : α → α → α → F := fun i j k =>
    if hf : IsFaceOf (↑facets : Set (Finset α)) (((σ.erase i).erase j).erase k) then
      srFaceDetector F facets (((σ.erase i).erase j).erase k) hf (b i j k) else 0 with hndef
  have hn : IsAlternating3 n := by
    refine ⟨fun i j k => ?_, fun i j k => ?_, fun i j k hrep => ?_⟩
    · simp only [hndef]
      rw [show ((σ.erase j).erase i).erase k = ((σ.erase i).erase j).erase k from by
        rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]]
      by_cases hf : IsFaceOf (↑facets : Set (Finset α)) (((σ.erase i).erase j).erase k)
      · rw [dif_pos hf, dif_pos hf, hb.antisym12 i j k, map_neg]
      · rw [dif_neg hf, dif_neg hf, neg_zero]
    · simp only [hndef]
      rw [show ((σ.erase i).erase k).erase j = ((σ.erase i).erase j).erase k from
        Finset.erase_right_comm]
      by_cases hf : IsFaceOf (↑facets : Set (Finset α)) (((σ.erase i).erase j).erase k)
      · rw [dif_pos hf, dif_pos hf, hb.antisym23 i j k, map_neg]
      · rw [dif_neg hf, dif_neg hf, neg_zero]
    · simp only [hndef]
      by_cases hf : IsFaceOf (↑facets : Set (Finset α)) (((σ.erase i).erase j).erase k)
      · rw [dif_pos hf, hb.alt i j k hrep, map_zero]
      · rw [dif_neg hf]
  have key : ∀ i j, i ∈ σ → j ∈ σ → i < j →
      IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) →
      simplicialCoboundary F (tripleCochain F σ n) ((σ.erase i).erase j)
        = g ((σ.erase i).erase j) := by
    intro i j hi hj hij hface
    have hrow : ∑ k ∈ (σ.erase i).erase j, n i j k
        = faceSign F σ i * faceSign F (σ.erase i) j * g ((σ.erase i).erase j) := by
      have hcong := congrFun (congrFun hbg i) j
      have hleft : srFaceDetector F facets ((σ.erase i).erase j) hface
          (koszulUpperTri (srKoszulBoundary3 facets b) i j)
          = ∑ k ∈ (σ.erase i).erase j, n i j k := by
        show srFaceDetector F facets ((σ.erase i).erase j) hface
            (if i < j then srKoszulBoundary3 facets b i j else 0) = _
        rw [if_pos hij, srFaceDetector_srKoszulBoundary3 facets hface b i j]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [hndef]
        rw [dif_pos (isFaceOf_mono (Finset.erase_subset k ((σ.erase i).erase j)) hface)]
      have hright : srFaceDetector F facets ((σ.erase i).erase j) hface
          (strandTwo F facets σ g i j)
          = faceSign F σ i * faceSign F (σ.erase i) j * g ((σ.erase i).erase j) := by
        show srFaceDetector F facets ((σ.erase i).erase j) hface
            (if i < j ∧ i ∈ σ ∧ j ∈ σ then _ else 0) = _
        rw [if_pos ⟨hij, hi, hj⟩, map_smul, srFaceDetector_prod, smul_eq_mul, mul_one]
      rw [← hleft, hcong, hright]
    rw [simplicialCoboundary_tripleCochain hn hi hj hij.ne, hrow]
    have hsq := faceSign_mul_self (F := F) σ i
    have hsq' := faceSign_mul_self (F := F) (σ.erase i) j
    linear_combination (faceSign F (σ.erase i) j * faceSign F (σ.erase i) j
        * g ((σ.erase i).erase j)) * hsq
      + (g ((σ.erase i).erase j)) * hsq'
  refine ⟨tripleCochain F σ n, fun i j hi hj hij hface => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hi hj h hface
  · have hswap : (σ.erase j).erase i = (σ.erase i).erase j := Finset.erase_right_comm
    have := key j i hj hi h (by rw [hswap]; exact hface)
    rwa [hswap] at this

/-- **Hochster's correspondence at `Tor₂`, for arbitrary complexes and multidegrees.**  A
multidegree-`σ` degree-two strand element is an (upper-triangular) third Koszul boundary **iff** its
cochain agrees on the codimension-two faces of `σ` with a reduced simplicial coboundary of the induced
subcomplex `Δ_σ`.  Unconditional, characteristic-free, for every finite complex. -/
theorem hochster_multidegree_torTwo_boundary_iff (facets : Finset (Finset α)) (σ : Finset α)
    (g : Finset α → F) :
    (∃ b : α → α → α → stanleyReisnerRing F facets, IsAlternating3 b ∧
        koszulUpperTri (srKoszulBoundary3 facets b) = strandTwo F facets σ g)
      ↔ (∃ h : Finset α → F, ∀ i j, i ∈ σ → j ∈ σ → i ≠ j →
          IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) →
          simplicialCoboundary F h ((σ.erase i).erase j) = g ((σ.erase i).erase j)) := by
  constructor
  · rintro ⟨b, hb, hbg⟩
    exact exists_coboundary_of_strandTwo_isKoszulBoundary3 facets σ g hb hbg
  · rintro ⟨h, hh⟩
    exact strandTwo_isKoszulBoundary3_of_coboundary facets σ g h hh

end

end GaloisForLFunctions.HTGeometry
