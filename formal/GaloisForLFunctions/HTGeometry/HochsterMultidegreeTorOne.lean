import GaloisForLFunctions.HTGeometry.HollowSimplexReducedCohomology

/-!
# Hochster's formula at `Tor₁` for an arbitrary finite complex and an arbitrary multidegree

For a finite complex `Δ` presented by its facet family and a vertex set `σ`, the multidegree-`σ`
strand of the first Koszul homology of the Stanley–Reisner ring is Hochster's `Tor_{1,σ}`, and his
formula identifies it with the reduced cohomology `H̃^{|σ|−2}(Δ_σ)` of the induced subcomplex.  The
corpus contained this only for hollow simplices (`srHollowSimplexSyzygyVec_boundary_iff`, where the
answer is one-dimensional) and, on the topological side, only in degree `1` through graph-specific
Betti formulas.  Using the general reduced simplicial cochain complex (`SimplicialCochainComplex`)
this file proves the correspondence for **every** finite complex and **every** multidegree.

The multidegree-`σ` strand of the Koszul `1`-chains is exactly the family
`srHollowSimplexSyzygyVec F facets σ l`, `l : α → F`; its `i`-th slot is automatically `0` when
`σ ∖ i` is a nonface, matching the fact that a cochain of `Δ_σ` only lives on faces.  The dictionary
is the incidence sign: `l i ↔ faceSign σ i · l i`.

* `srKoszulRelation_srHollowSimplexSyzygyVec` — the strand's Koszul differential is
  `(∑_{i∈σ} l i) · ∏_σ x`, so a strand element is a cycle exactly when `σ` is a nonface or
  `∑_{i∈σ} l i = 0` (`srHollowSimplexSyzygyVec_isCycle_iff`) — matching, on the topological side, the
  cocycle condition `(δa)(σ) = ∑_{i∈σ} faceSign σ i · a i = 0` in the slot that survives only when
  `σ ∈ Δ`.
* `hochster_multidegree_boundary_iff` — the boundary halves agree: a strand element is a first Koszul
  boundary **iff** the matching top cochain is a simplicial coboundary on the codimension-one faces of
  `σ`.  Both directions are explicit.  Forward: the face detectors of the antisymmetrized `2`-chain
  give an antisymmetric coefficient family whose `pairCochain` is the primitive.  Backward: the
  sign-corrected `pairCochain` of the given cochain, supported on the codimension-two faces of `σ`,
  is the `2`-chain.
* `hochster_multidegree_torOne_correspondence` — the two halves packaged: cycles match cocycles and
  boundaries match coboundaries under `l ↦ (i ↦ faceSign σ i · l i)`, i.e. Hochster's formula at
  `i = 1` for arbitrary complexes and arbitrary multidegrees.

The ordered-pair guard `p < q` in `pairCochain` is what keeps the construction characteristic-free: an
unguarded symmetrization would produce a factor `2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### Deleting two vertices -/

omit [LinearOrder α] [Fintype α] in
/-- Two double deletions from `σ` agree exactly when the deleted pairs agree. -/
theorem erase_erase_eq_erase_erase_iff {σ : Finset α} {i v p q : α}
    (hi : i ∈ σ) (hv : v ∈ σ) (hp : p ∈ σ) (hq : q ∈ σ) (hiv : i ≠ v) :
    (σ.erase i).erase v = (σ.erase p).erase q ↔ ((i = p ∧ v = q) ∨ (i = q ∧ v = p)) := by
  constructor
  · intro heq
    have hiB : i ∉ (σ.erase p).erase q := by
      rw [← heq]
      exact fun h => (Finset.notMem_erase i σ) (Finset.mem_of_mem_erase h)
    have hvB : v ∉ (σ.erase p).erase q := by
      rw [← heq]
      exact Finset.notMem_erase v _
    have hi' : i = q ∨ i = p := by
      by_cases h1 : i = q
      · exact Or.inl h1
      · by_cases h2 : i = p
        · exact Or.inr h2
        · exact absurd (Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h2, hi⟩⟩) hiB
    have hv' : v = q ∨ v = p := by
      by_cases h1 : v = q
      · exact Or.inl h1
      · by_cases h2 : v = p
        · exact Or.inr h2
        · exact absurd (Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h2, hv⟩⟩) hvB
    rcases hi' with hiq | hip
    · rcases hv' with hvq | hvp
      · exact absurd (hiq.trans hvq.symm) hiv
      · exact Or.inr ⟨hiq, hvp⟩
    · rcases hv' with hvq | hvp
      · exact Or.inl ⟨hip, hvq⟩
      · exact absurd (hip.trans hvp.symm) hiv
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.erase_right_comm

/-! ### The sign-corrected pair cochain -/

omit [Fintype α] in
/-- The sign-corrected pair weight is symmetric on an antisymmetric coefficient family: both the
incidence-sign product and the coefficient change sign under the swap. -/
theorem signedPair_symm {σ : Finset α} {b : α → α → F} (hb : ∀ i j, b i j + b j i = 0)
    {i v : α} (hi : i ∈ σ) (hv : v ∈ σ) (hiv : i ≠ v) :
    faceSign F σ v * faceSign F (σ.erase v) i * b v i
      = faceSign F σ i * faceSign F (σ.erase i) v * b i v := by
  have hs := faceSign_mul_faceSign_erase_antisymm (F := F) hi hv hiv
  linear_combination (-(b i v)) * hs
    + (faceSign F σ v * faceSign F (σ.erase v) i) * (hb i v)

omit [Fintype α] in
/-- The sign-corrected pair weight is symmetric on a symmetric coefficient family after the sign
flip: this is the shape used to build a Koszul `2`-chain from a cochain. -/
theorem signedPair_symm' {σ : Finset α} (g : Finset α → F) {i v : α}
    (hi : i ∈ σ) (hv : v ∈ σ) (hiv : i ≠ v) :
    -(faceSign F σ v * faceSign F (σ.erase v) i * g ((σ.erase v).erase i))
      = faceSign F σ i * faceSign F (σ.erase i) v * g ((σ.erase i).erase v) := by
  have hs := faceSign_mul_faceSign_erase_antisymm (F := F) hi hv hiv
  rw [show (σ.erase v).erase i = (σ.erase i).erase v from Finset.erase_right_comm]
  linear_combination (-(g ((σ.erase i).erase v))) * hs

/-- The cochain on codimension-two faces of `σ` attached to a coefficient family, with the incidence
sign correction and the ordered-pair guard that avoids double counting. -/
def pairCochain (F : Type*) [CommRing F] (σ : Finset α) (b : α → α → F) : Finset α → F :=
  fun τ => ∑ p ∈ σ, ∑ q ∈ σ,
    if p < q ∧ τ = (σ.erase p).erase q then
      faceSign F σ p * faceSign F (σ.erase p) q * b p q else 0

omit [Fintype α] in
/-- The pair cochain reads off the sign-corrected coefficient at every codimension-two face. -/
theorem pairCochain_erase_erase {σ : Finset α} {b : α → α → F} (hb : ∀ i j, b i j + b j i = 0)
    {i v : α} (hi : i ∈ σ) (hv : v ∈ σ) (hiv : i ≠ v) :
    pairCochain F σ b ((σ.erase i).erase v)
      = faceSign F σ i * faceSign F (σ.erase i) v * b i v := by
  show (∑ p ∈ σ, ∑ q ∈ σ,
      if p < q ∧ (σ.erase i).erase v = (σ.erase p).erase q then
        faceSign F σ p * faceSign F (σ.erase p) q * b p q else 0) = _
  rcases lt_or_gt_of_ne hiv with hlt | hlt
  · rw [Finset.sum_eq_single i, Finset.sum_eq_single v]
    · exact if_pos ⟨hlt, rfl⟩
    · intro q hq hqv
      refine if_neg (fun hcon => ?_)
      rcases (erase_erase_eq_erase_erase_iff hi hv hi hq hiv).mp hcon.2 with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact hqv h2.symm
      · exact hiv h2.symm
    · intro hmem; exact absurd hv hmem
    · intro p hp hpi
      refine Finset.sum_eq_zero (fun q hq => if_neg (fun hcon => ?_))
      rcases (erase_erase_eq_erase_erase_iff hi hv hp hq hiv).mp hcon.2 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hpi h1.symm
      · have hvi : v < i := by rw [h2, h1]; exact hcon.1
        exact absurd hlt (asymm hvi)
    · intro hmem; exact absurd hi hmem
  · rw [Finset.sum_eq_single v, Finset.sum_eq_single i]
    · rw [if_pos ⟨hlt, Finset.erase_right_comm⟩]
      exact signedPair_symm hb hi hv hiv
    · intro q hq hqi
      refine if_neg (fun hcon => ?_)
      rcases (erase_erase_eq_erase_erase_iff hi hv hv hq hiv).mp hcon.2 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hiv h1
      · exact hqi h1.symm
    · intro hmem; exact absurd hi hmem
    · intro p hp hpv
      refine Finset.sum_eq_zero (fun q hq => if_neg (fun hcon => ?_))
      rcases (erase_erase_eq_erase_erase_iff hi hv hp hq hiv).mp hcon.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : i < v := by rw [h1, h2]; exact hcon.1
        exact absurd hlt (asymm this)
      · exact hpv h2.symm
    · intro hmem; exact absurd hv hmem

/-! ### The cycle half of the strand -/

omit [LinearOrder α] in
/-- The Koszul differential of a multidegree-`σ` strand element is the coefficient sum times the full
`σ`-monomial. -/
theorem srKoszulRelation_srHollowSimplexSyzygyVec (facets : Finset (Finset α)) (σ : Finset α)
    (l : α → F) :
    srKoszulRelation facets (srHollowSimplexSyzygyVec F facets σ l)
      = (∑ i ∈ σ, l i) • ∏ w ∈ σ, srVertexX F facets w := by
  rw [srKoszulRelation, Finset.sum_congr rfl (fun v _ =>
    show srHollowSimplexSyzygyVec F facets σ l v * srVertexX F facets v
        = if v ∈ σ then l v • ∏ w ∈ σ, srVertexX F facets w else 0 from by
      simp only [srHollowSimplexSyzygyVec]
      by_cases hv : v ∈ σ
      · rw [if_pos hv, if_pos hv, smul_mul_assoc,
          Finset.prod_erase_mul σ (srVertexX F facets) hv]
      · rw [if_neg hv, if_neg hv, zero_mul]),
    Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_smul]

omit [LinearOrder α] in
/-- **The cycle criterion on a strand.**  When `σ` is a face, a multidegree-`σ` strand element is a
first Koszul cycle exactly when its coefficient sum vanishes — the algebraic mirror of the cocycle
condition `∑_{i∈σ} faceSign σ i · a i = 0` in the top slot of the cochain complex of `Δ_σ`. -/
theorem srHollowSimplexSyzygyVec_isCycle_iff (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : IsFaceOf (↑facets : Set (Finset α)) σ) (l : α → F) :
    srKoszulRelation facets (srHollowSimplexSyzygyVec F facets σ l) = 0 ↔ ∑ i ∈ σ, l i = 0 := by
  rw [srKoszulRelation_srHollowSimplexSyzygyVec]
  constructor
  · intro h
    have := congrArg (srFaceDetector F facets σ hσ) h
    rwa [map_smul, srFaceDetector_prod, smul_eq_mul, mul_one, map_zero] at this
  · intro h; rw [h, zero_smul]

/-! ### The boundary half: Hochster's formula at `Tor₁` -/

/-- **Hochster's formula at `Tor₁`, for every finite complex and every multidegree.**  A
multidegree-`σ` strand element `w(l)` of the Koszul `1`-chains is a first Koszul boundary **iff** the
matching top cochain `i ↦ faceSign σ i · l i` of the induced subcomplex `Δ_σ` is a simplicial
coboundary on the codimension-one faces of `σ`.

Both directions are explicit.  Forward: applying the face detector `srFaceDetector (σ ∖ i)` to the
boundary equation turns the antisymmetrized `2`-chain into an antisymmetric scalar family `b` with
`∑_{j∈σ∖i} b i j = l i`, and `pairCochain σ b` is the required primitive.  Backward: the
sign-corrected `pairCochain` of the given cochain, placed on the codimension-two monomials of `σ`, is
the required `2`-chain; slots where `σ ∖ i` is a nonface impose no condition because the corresponding
monomial vanishes. -/
theorem hochster_multidegree_boundary_iff (facets : Finset (Finset α)) (σ : Finset α) (l : α → F) :
    (∃ cc : α → α → stanleyReisnerRing F facets,
        srKoszulBoundary facets cc = srHollowSimplexSyzygyVec F facets σ l)
      ↔ (∃ h : Finset α → F, ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) →
          simplicialCoboundary F h (σ.erase i) = faceSign F σ i * l i) := by
  classical
  constructor
  · rintro ⟨cc, hcc⟩
    set b : α → α → F := fun i j =>
      if hf : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) then
        srFaceDetector F facets ((σ.erase i).erase j) hf (cc i j - cc j i) else 0 with hbdef
    have hb : ∀ i j, b i j + b j i = 0 := by
      intro i j
      simp only [hbdef]
      rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]
      by_cases hfc : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j)
      · rw [dif_pos hfc, dif_pos hfc, ← map_add,
          show (cc i j - cc j i) + (cc j i - cc i j) = 0 by abel, map_zero]
      · rw [dif_neg hfc, dif_neg hfc, add_zero]
    refine ⟨pairCochain F σ b, fun i hi hface => ?_⟩
    have hrow : ∑ j ∈ σ.erase i, b i j = l i := by
      have hdet := srFaceDetector_srKoszulBoundary facets hface cc i
      rw [hcc] at hdet
      have hleft : srFaceDetector F facets (σ.erase i) hface
          (srHollowSimplexSyzygyVec F facets σ l i) = l i := by
        rw [srHollowSimplexSyzygyVec, if_pos hi, map_smul, srFaceDetector_prod, smul_eq_mul, mul_one]
      rw [hleft] at hdet
      rw [hdet]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hbdef]
      rw [dif_pos (isFaceOf_mono (Finset.erase_subset j (σ.erase i)) hface)]
    show ∑ v ∈ σ.erase i, faceSign F (σ.erase i) v
        * pairCochain F σ b ((σ.erase i).erase v) = _
    rw [Finset.sum_congr rfl (fun v hv =>
      show faceSign F (σ.erase i) v * pairCochain F σ b ((σ.erase i).erase v)
          = faceSign F σ i * b i v from by
        rw [pairCochain_erase_erase hb hi (Finset.mem_of_mem_erase hv)
          (Ne.symm (Finset.ne_of_mem_erase hv))]
        have := faceSign_mul_self (F := F) (σ.erase i) v
        linear_combination (faceSign F σ i * b i v) * this), ← Finset.mul_sum, hrow]
  · rintro ⟨h, hh⟩
    refine ⟨fun i j => if i < j ∧ i ∈ σ ∧ j ∈ σ then
        (faceSign F σ i * faceSign F (σ.erase i) j * h ((σ.erase i).erase j))
          • ∏ w ∈ (σ.erase i).erase j, srVertexX F facets w
      else 0, ?_⟩
    funext m
    rw [srKoszulBoundary]
    by_cases hm : m ∈ σ
    · have hterm : ∀ j : α, (((if m < j ∧ m ∈ σ ∧ j ∈ σ then
            (faceSign F σ m * faceSign F (σ.erase m) j * h ((σ.erase m).erase j))
              • ∏ w ∈ (σ.erase m).erase j, srVertexX F facets w else 0)
          - (if j < m ∧ j ∈ σ ∧ m ∈ σ then
            (faceSign F σ j * faceSign F (σ.erase j) m * h ((σ.erase j).erase m))
              • ∏ w ∈ (σ.erase j).erase m, srVertexX F facets w else 0))
          * srVertexX F facets j)
          = if j ∈ σ.erase m then
              (faceSign F σ m * faceSign F (σ.erase m) j * h ((σ.erase m).erase j))
                • ∏ w ∈ σ.erase m, srVertexX F facets w
            else 0 := by
        intro j
        by_cases hj : j ∈ σ.erase m
        · have hjσ : j ∈ σ := Finset.mem_of_mem_erase hj
          have hjm : j ≠ m := Finset.ne_of_mem_erase hj
          rw [if_pos hj]
          rcases lt_or_gt_of_ne hjm with hlt | hlt
          · rw [if_neg (fun hc => absurd hc.1 (asymm hlt)), if_pos ⟨hlt, hjσ, hm⟩, zero_sub,
              ← neg_smul, signedPair_symm' h hm hjσ (Ne.symm hjm),
              show (σ.erase j).erase m = (σ.erase m).erase j from Finset.erase_right_comm,
              smul_mul_assoc, Finset.prod_erase_mul (σ.erase m) (srVertexX F facets) hj]
          · rw [if_pos ⟨hlt, hm, hjσ⟩, if_neg (fun hc => absurd hc.1 (asymm hlt)), sub_zero,
              smul_mul_assoc, Finset.prod_erase_mul (σ.erase m) (srVertexX F facets) hj]
        · rw [if_neg hj]
          by_cases hjσ : j ∈ σ
          · have hjm : j = m := by
              by_contra hc
              exact hj (Finset.mem_erase.mpr ⟨hc, hjσ⟩)
            subst hjm
            simp
          · rw [if_neg (fun hc => hjσ hc.2.2), if_neg (fun hc => hjσ hc.2.1), sub_zero, zero_mul]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem, Finset.univ_inter,
        ← Finset.sum_smul, srHollowSimplexSyzygyVec, if_pos hm]
      by_cases hface : IsFaceOf (↑facets : Set (Finset α)) (σ.erase m)
      · have hsum : ∑ j ∈ σ.erase m,
            faceSign F σ m * faceSign F (σ.erase m) j * h ((σ.erase m).erase j) = l m := by
          have hcob := hh m hm hface
          rw [show simplicialCoboundary F h (σ.erase m)
              = ∑ v ∈ σ.erase m, faceSign F (σ.erase m) v * h ((σ.erase m).erase v) from rfl]
            at hcob
          have hmul : ∑ j ∈ σ.erase m,
              faceSign F σ m * faceSign F (σ.erase m) j * h ((σ.erase m).erase j)
              = faceSign F σ m * ∑ j ∈ σ.erase m,
                faceSign F (σ.erase m) j * h ((σ.erase m).erase j) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by ring)
          rw [hmul, hcob]
          have := faceSign_mul_self (F := F) σ m
          linear_combination (l m) * this
        rw [hsum]
      · rw [srProd_eq_zero_of_not_isFace facets hface, smul_zero, smul_zero]
    · rw [srHollowSimplexSyzygyVec, if_neg hm]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg (fun hc => hm hc.2.1), if_neg (fun hc => hm hc.2.2), sub_zero, zero_mul]

/-- **Hochster's formula at `Tor₁` for arbitrary complexes and multidegrees, packaged.**  Under the
incidence-sign dictionary `l ↦ (i ↦ faceSign σ i · l i)`, the multidegree-`σ` strand of the first
Koszul homology of the Stanley–Reisner ring matches the top reduced cohomology of the induced
subcomplex `Δ_σ`: cycles correspond to cocycles and boundaries to coboundaries. -/
theorem hochster_multidegree_torOne_correspondence (facets : Finset (Finset α)) (σ : Finset α)
    (hσ : IsFaceOf (↑facets : Set (Finset α)) σ) (l : α → F) :
    (srKoszulRelation facets (srHollowSimplexSyzygyVec F facets σ l) = 0
        ↔ ∑ i ∈ σ, faceSign F σ i * (faceSign F σ i * l i) = 0)
      ∧ ((∃ cc : α → α → stanleyReisnerRing F facets,
            srKoszulBoundary facets cc = srHollowSimplexSyzygyVec F facets σ l)
          ↔ (∃ h : Finset α → F, ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) →
              simplicialCoboundary F h (σ.erase i) = faceSign F σ i * l i)) := by
  refine ⟨?_, hochster_multidegree_boundary_iff facets σ l⟩
  rw [srHollowSimplexSyzygyVec_isCycle_iff facets σ hσ l]
  constructor
  · intro hs
    rw [← hs]
    exact Finset.sum_congr rfl (fun i _ => by rw [← mul_assoc, faceSign_mul_self, one_mul])
  · intro hs
    rw [← hs]
    exact (Finset.sum_congr rfl (fun i _ => by rw [← mul_assoc, faceSign_mul_self, one_mul])).symm

end

end GaloisForLFunctions.HTGeometry
