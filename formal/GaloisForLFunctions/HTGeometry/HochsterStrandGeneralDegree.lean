import GaloisForLFunctions.HTGeometry.KoszulTupleSign
import GaloisForLFunctions.HTGeometry.HochsterMultidegreeTorOne

/-!
# The Hochster strand chain map in every Koszul degree

The strand maps from the reduced cochains of an induced subcomplex `Δ_σ` to the multidegree-`σ`
Koszul strand were built one degree at a time (`strandOne`, `strandTwo`, `strandThree`).  With the
degree-uniform iterated incidence sign `tupleSign` and its alternation (`KoszulTupleSign`) they become
a single map in every degree, into the alternating Koszul complex of `GeneralKoszulComplex`:

`strandTensor facets σ g v = tupleSign σ v · g (σ ∖ v[Fin p]) · ∏_{σ ∖ v[Fin p]} x`  on injective
tuples with entries in `σ`, and `0` elsewhere.

* `strandTensor_isAltTensor` — it lands in `koszulAltTensors`, because the guard and the complement
  `σ ∖ v[Fin p]` are permutation-invariant while `tupleSign` is alternating.
* `koszulD_strandTensor` — the **chain-map identity in every degree**:
  `koszulD x (strandTensor (p+1) g) = (-1)^p · strandTensor p (δg)`.
  The sign is intrinsic: the Koszul differential contracts the *first* slot, while the simplicial
  coboundary deletes a vertex from the *complement*, and moving the contracted vertex from the front
  of the tuple to the back costs the cyclic rotation `finRotate (p+1)`, whose sign is `(-1)^p`.

The two facts that carry the computation are `tupleSign_cons` (peeling the contracted vertex off the
front) and `tupleSign_snoc` (peeling it off the back, where it meets exactly the complement
`σ ∖ v[Fin p]` and so produces the simplicial incidence sign `faceSign (σ ∖ v[Fin p]) k`).

`strandTensor_one` identifies degree one with the previously built `strandOne`, so the degree-uniform
map extends the hand-built low-degree ones rather than replacing them.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-! ### Prepending a vertex to a tuple -/

omit [LinearOrder α] in
/-- The image of a tuple with a vertex prepended. -/
theorem image_cons {p : ℕ} (w : Fin p → α) (k : α) :
    Finset.image (Fin.cons k w : Fin (p + 1) → α) Finset.univ
      = insert k (Finset.image w Finset.univ) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨t, rfl⟩
    exact Fin.cases (Or.inl (by simp)) (fun i => Or.inr ⟨i, by simp⟩) t
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨i.succ, by simp⟩

omit [LinearOrder α] in
/-- The image of a tuple is the image of its head together with the image of its tail. -/
theorem image_eq_insert_image_tail {p : ℕ} (w : Fin (p + 1) → α) :
    Finset.image w Finset.univ = insert (w 0) (Finset.image (Fin.tail w) Finset.univ) := by
  conv_lhs => rw [← Fin.cons_self_tail w]
  rw [image_cons]

omit [LinearOrder α] in
/-- Prepending a vertex outside the image of an injective tuple keeps it injective. -/
theorem cons_injective {p : ℕ} {w : Fin p → α} {k : α} (hw : Function.Injective w)
    (hk : k ∉ Finset.image w Finset.univ) :
    Function.Injective (Fin.cons k w : Fin (p + 1) → α) := by
  intro a b hab
  revert hab
  refine Fin.cases ?_ (fun x => ?_) a <;> refine Fin.cases ?_ (fun y => ?_) b
  · intro _; rfl
  · intro hc
    exact absurd (Finset.mem_image.mpr ⟨y, Finset.mem_univ y, by simpa using hc.symm⟩) hk
  · intro hc
    exact absurd (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simpa using hc⟩) hk
  · intro hc
    simp only [Fin.cons_succ] at hc
    exact congrArg Fin.succ (hw hc)

omit [LinearOrder α] in
/-- The guard of the strand map is inherited by a tuple with a new vertex prepended. -/
theorem cons_guard {p : ℕ} {w : Fin p → α} {k : α} {σ : Finset α}
    (hw : (∀ t, w t ∈ σ) ∧ Function.Injective w) (hkσ : k ∈ σ)
    (hkimg : k ∉ Finset.image w Finset.univ) :
    (∀ t, (Fin.cons k w : Fin (p + 1) → α) t ∈ σ) ∧
      Function.Injective (Fin.cons k w : Fin (p + 1) → α) :=
  ⟨fun t => Fin.cases (by simpa using hkσ) (fun i => by simpa using hw.1 i) t,
    cons_injective hw.2 hkimg⟩

/-! ### Peeling the head and the tail of a tuple -/

/-- Peeling the contracted vertex off the **front** of a tuple. -/
theorem tupleSign_cons {p : ℕ} (σ : Finset α) (w : Fin p → α) (k : α) :
    tupleSign F σ (Fin.cons k w) = faceSign F σ k * tupleSign F (σ.erase k) w := by
  rw [tupleSign_succ, Fin.cons_zero, Fin.tail_cons]

/-- Peeling the contracted vertex off the **back** of a tuple: there it meets exactly the complement
of the tuple's image, producing the simplicial incidence sign of the complement. -/
theorem tupleSign_snoc : ∀ {p : ℕ} (σ : Finset α) (w : Fin p → α) (k : α),
    tupleSign F σ (Fin.snoc w k)
      = tupleSign F σ w * faceSign F (σ \ Finset.image w Finset.univ) k := by
  intro p
  induction p with
  | zero =>
    intro σ w k
    have h0 : (Fin.snoc w k : Fin 1 → α) 0 = k := by
      show (Fin.snoc w k : Fin 1 → α) (Fin.last 0) = k
      rw [Fin.snoc_last]
    rw [tupleSign_succ, h0, tupleSign_zero, tupleSign_zero, mul_one, one_mul,
      show Finset.image w (Finset.univ : Finset (Fin 0)) = ∅ from by simp,
      Finset.sdiff_empty]
  | succ q ih =>
    intro σ w k
    have h0 : (Fin.snoc w k : Fin (q + 2) → α) 0 = w 0 := by
      show (Fin.snoc w k : Fin (q + 2) → α) (Fin.castSucc 0) = w 0
      rw [Fin.snoc_castSucc]
    have htail : Fin.tail (Fin.snoc w k : Fin (q + 2) → α) = Fin.snoc (Fin.tail w) k := by
      funext t
      refine Fin.lastCases ?_ (fun i => ?_) t
      · show (Fin.snoc w k : Fin (q + 2) → α) (Fin.succ (Fin.last q))
            = (Fin.snoc (Fin.tail w) k : Fin (q + 1) → α) (Fin.last q)
        rw [show Fin.succ (Fin.last q) = Fin.last (q + 1) from rfl, Fin.snoc_last, Fin.snoc_last]
      · show (Fin.snoc w k : Fin (q + 2) → α) (Fin.succ i.castSucc)
            = (Fin.snoc (Fin.tail w) k : Fin (q + 1) → α) i.castSucc
        rw [Fin.snoc_castSucc,
          show Fin.succ i.castSucc = Fin.castSucc i.succ from Fin.succ_castSucc i,
          Fin.snoc_castSucc]
        rfl
    have hset : (σ.erase (w 0)) \ Finset.image (Fin.tail w) Finset.univ
        = σ \ Finset.image w Finset.univ := by
      rw [image_eq_insert_image_tail, Finset.sdiff_insert]
      ext x
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
      tauto
    rw [tupleSign_succ, h0, htail, ih (σ.erase (w 0)) (Fin.tail w) k, hset, tupleSign_succ σ w]
    ring

/-! ### Moving the contracted vertex from the front to the back -/

omit [DecidableEq α] [LinearOrder α] in
/-- Moving the first entry of a tuple to the last position is the cyclic rotation. -/
theorem snoc_eq_cons_comp_finRotate {p : ℕ} (w : Fin p → α) (k : α) :
    (Fin.snoc w k : Fin (p + 1) → α) = (Fin.cons k w : Fin (p + 1) → α) ∘ ⇑(finRotate (p + 1)) := by
  funext t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]

/-- **Moving the contracted vertex to the back costs `(-1)^p`.**  The cyclic rotation `finRotate (p+1)`
has sign `(-1)^p`, and `tupleSign` transforms by the sign. -/
theorem tupleSign_snoc_eq_cons {p : ℕ} (σ : Finset α) (w : Fin p → α) (k : α)
    (hmem : ∀ t, (Fin.cons k w : Fin (p + 1) → α) t ∈ σ)
    (hinj : Function.Injective (Fin.cons k w : Fin (p + 1) → α)) :
    tupleSign F σ (Fin.snoc w k) = (-1 : F) ^ p * tupleSign F σ (Fin.cons k w) := by
  rw [snoc_eq_cons_comp_finRotate,
    tupleSign_comp_perm σ (Fin.cons k w) hmem hinj (finRotate (p + 1)), sign_finRotate (p + 1)]
  simp [zsmul_eq_mul]

/-! ### The degree-uniform strand map -/

variable [Fintype α]

/-- The **degree-uniform strand map**: a cochain on the codimension-`p` faces of `σ` becomes the
multidegree-`σ` Koszul `p`-tensor weighted by the iterated incidence sign. -/
def strandTensor (F : Type*) [CommRing F] (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) : (Fin p → α) → stanleyReisnerRing F facets :=
  fun v => if (∀ t, v t ∈ σ) ∧ Function.Injective v then
      (tupleSign F σ v * g (σ \ Finset.image v Finset.univ))
        • ∏ w ∈ σ \ Finset.image v Finset.univ, srVertexX F facets w
    else 0

omit [LinearOrder α] [Fintype α] in
/-- The image of a tuple is unchanged by precomposition with a permutation. -/
theorem image_comp_perm {p : ℕ} (v : Fin p → α) (π : Equiv.Perm (Fin p)) :
    Finset.image (v ∘ ⇑π) Finset.univ = Finset.image v Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨t, ht⟩ => ⟨π t, ht⟩, fun ⟨u, hu⟩ => ⟨π.symm u, by rwa [Equiv.apply_symm_apply]⟩⟩

omit [Fintype α] in
/-- **The strand map lands in the alternating Koszul complex.**  The guard and the complement are
permutation-invariant, and the iterated incidence sign is alternating. -/
theorem strandTensor_isAltTensor (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) : IsAltTensor (strandTensor F facets σ (p := p) g) := by
  refine ⟨fun v i j hij => ?_, fun v hv => ?_⟩
  · simp only [strandTensor]
    have himg := image_comp_perm v (Equiv.swap i j)
    by_cases hg : (∀ t, v t ∈ σ) ∧ Function.Injective v
    · have hg' : (∀ t, (v ∘ ⇑(Equiv.swap i j)) t ∈ σ) ∧
          Function.Injective (v ∘ ⇑(Equiv.swap i j)) :=
        ⟨fun t => hg.1 _, hg.2.comp (Equiv.swap i j).injective⟩
      rw [if_pos hg', if_pos hg, himg, tupleSign_swap σ v hg.1 hg.2 i j hij, ← neg_smul]
      congr 1
      ring
    · have hg' : ¬ ((∀ t, (v ∘ ⇑(Equiv.swap i j)) t ∈ σ) ∧
          Function.Injective (v ∘ ⇑(Equiv.swap i j))) := by
        intro hc
        refine hg ⟨fun t => ?_, ?_⟩
        · have := hc.1 (Equiv.swap i j t)
          simpa [Equiv.swap_apply_self] using this
        · intro a b hab
          have hh : (v ∘ ⇑(Equiv.swap i j)) (Equiv.swap i j a)
              = (v ∘ ⇑(Equiv.swap i j)) (Equiv.swap i j b) := by
            simpa [Equiv.swap_apply_self] using hab
          simpa using hc.2 hh
      rw [if_neg hg', if_neg hg, neg_zero]
  · exact if_neg (fun hc => hv hc.2)

omit [Fintype α] in
/-- Degree one of the uniform strand map is the previously built `strandOne`. -/
theorem strandTensor_one (facets : Finset (Finset α)) (σ : Finset α) (g : Finset α → F) (i : α) :
    strandTensor F facets σ (p := 1) g (fun _ => i) = strandOne F facets σ g i := by
  have himg : Finset.image (fun _ : Fin 1 => i) Finset.univ = {i} := by
    ext x; simp [eq_comm]
  have hsign : tupleSign F σ (fun _ : Fin 1 => i) = faceSign F σ i := by
    rw [tupleSign_succ, tupleSign_zero, mul_one]
  simp only [strandTensor, strandOne, srHollowSimplexSyzygyVec, himg,
    show σ \ ({i} : Finset α) = σ.erase i from by rw [← Finset.erase_eq]]
  by_cases hi : i ∈ σ
  · rw [if_pos ⟨fun _ => hi, Function.injective_of_subsingleton _⟩, if_pos hi, hsign]
  · rw [if_neg (fun hc => hi (hc.1 0)), if_neg hi]

/-! ### The chain map in every degree -/

/-- **The strand chain map, in every Koszul degree.**  The Koszul differential of the degree-`(p+1)`
strand map is `(-1)^p` times the degree-`p` strand map of the reduced simplicial coboundary.  The sign
is the cost of moving the contracted vertex from the front of the tuple to the back, i.e. the sign of
the cyclic rotation.  Unconditional, for every finite complex, every multidegree and every degree. -/
theorem koszulD_strandTensor (facets : Finset (Finset α)) (σ : Finset α) {p : ℕ}
    (g : Finset α → F) :
    koszulD (srVertexX F facets) (strandTensor F facets σ (p := p + 1) g)
      = fun w => (-1 : F) ^ p • strandTensor F facets σ (p := p) (simplicialCoboundary F g) w := by
  funext w
  by_cases hw : (∀ t, w t ∈ σ) ∧ Function.Injective w
  · set τ := σ \ Finset.image w Finset.univ with hτ
    have hterm : ∀ k : α,
        strandTensor F facets σ (p := p + 1) g (Fin.cons k w) * srVertexX F facets k
          = if k ∈ τ then
              ((-1 : F) ^ p * (tupleSign F σ w * (faceSign F τ k * g (τ.erase k))))
                • ∏ u ∈ τ, srVertexX F facets u
            else 0 := by
      intro k
      by_cases hk : k ∈ τ
      · have hkσ : k ∈ σ := (Finset.mem_sdiff.mp hk).1
        have hkimg : k ∉ Finset.image w Finset.univ := (Finset.mem_sdiff.mp hk).2
        have hguard := cons_guard hw hkσ hkimg
        have hsnoc := tupleSign_snoc_eq_cons (F := F) σ w k hguard.1 hguard.2
        have hsq : (-1 : F) ^ p * (-1 : F) ^ p = 1 := by
          rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
        have hcons : tupleSign F σ (Fin.cons k w)
            = (-1 : F) ^ p * (tupleSign F σ w * faceSign F τ k) := by
          rw [tupleSign_snoc σ w k, ← hτ] at hsnoc
          linear_combination (-((-1 : F) ^ p)) * hsnoc
            - (tupleSign F σ (Fin.cons k w)) * hsq
        simp only [strandTensor]
        rw [if_pos hguard, if_pos hk, image_cons w k, Finset.sdiff_insert, ← hτ, smul_mul_assoc,
          Finset.prod_erase_mul τ (srVertexX F facets) hk, hcons]
        congr 1
        ring
      · have hguard : ¬ ((∀ t, (Fin.cons k w : Fin (p + 1) → α) t ∈ σ) ∧
            Function.Injective (Fin.cons k w : Fin (p + 1) → α)) := by
          intro hc
          refine hk (Finset.mem_sdiff.mpr ⟨by simpa using hc.1 0, ?_⟩)
          intro hmem
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
          have hcc : (Fin.cons k w : Fin (p + 1) → α) 0
              = (Fin.cons k w : Fin (p + 1) → α) i.succ := by simpa using hi.symm
          exact (Fin.succ_ne_zero i) (hc.2 hcc).symm
        simp only [strandTensor]
        rw [if_neg hguard, if_neg hk, zero_mul]
    show (∑ k, strandTensor F facets σ (p := p + 1) g (Fin.cons k w) * srVertexX F facets k) = _
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_mem, Finset.univ_inter,
      ← Finset.sum_smul]
    simp only [strandTensor, if_pos hw, ← hτ, smul_smul]
    congr 1
    rw [simplicialCoboundary_apply, Finset.mul_sum, Finset.mul_sum]
  · have hzero : ∀ k : α, strandTensor F facets σ (p := p + 1) g (Fin.cons k w) = 0 := by
      intro k
      refine if_neg (fun hc => hw ⟨fun t => by simpa using hc.1 t.succ, ?_⟩)
      intro a b hab
      have hcc : (Fin.cons k w : Fin (p + 1) → α) a.succ
          = (Fin.cons k w : Fin (p + 1) → α) b.succ := by simpa using hab
      exact Fin.succ_inj.mp (hc.2 hcc)
    show (∑ k, strandTensor F facets σ (p := p + 1) g (Fin.cons k w) * srVertexX F facets k) = _
    rw [Finset.sum_congr rfl (fun k _ => by rw [hzero k, zero_mul]), Finset.sum_const_zero]
    simp only [strandTensor, if_neg hw, smul_zero]

/-- **Every reduced coboundary of `Δ_σ` becomes a Koszul boundary, in every degree.**  The strand
chain map carries the reduced simplicial coboundary of the induced subcomplex into the boundaries of
the alternating Koszul complex, so it descends to a map from the reduced cohomology of `Δ_σ` to the
multidegree-`σ` Koszul homology at every degree. -/
theorem strandTensor_coboundary_mem_koszulBoundaries (facets : Finset (Finset α)) (σ : Finset α)
    {p : ℕ} (g : Finset α → F) :
    strandTensor F facets σ (p := p + 1) (simplicialCoboundary F g)
      ∈ koszulBoundaries (p := p) (srVertexX F facets) := by
  have halt : IsAltTensor (((-1 : F) ^ (p + 1)) • strandTensor F facets σ (p := p + 2) g) := by
    refine ⟨fun v i j hij => ?_, fun v hv => ?_⟩
    · show ((-1 : F) ^ (p + 1)) • strandTensor F facets σ (p := p + 2) g (v ∘ ⇑(Equiv.swap i j))
        = - (((-1 : F) ^ (p + 1)) • strandTensor F facets σ (p := p + 2) g v)
      rw [(strandTensor_isAltTensor facets σ g).swap_neg v i j hij, smul_neg]
    · show ((-1 : F) ^ (p + 1)) • strandTensor F facets σ (p := p + 2) g v = 0
      rw [(strandTensor_isAltTensor facets σ g).zero_of_not_injective v hv, smul_zero]
  refine ⟨((-1 : F) ^ (p + 1)) • strandTensor F facets σ (p := p + 2) g, ?_, ?_⟩
  · exact SetLike.mem_coe.mpr halt
  · have hsq : (-1 : F) ^ (p + 1) * (-1 : F) ^ (p + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    show koszulD (srVertexX F facets) (((-1 : F) ^ (p + 1)) •
        strandTensor F facets σ (p := p + 2) g) = _
    have hlin : koszulD (srVertexX F facets) (((-1 : F) ^ (p + 1)) •
        strandTensor F facets σ (p := p + 2) g)
        = ((-1 : F) ^ (p + 1)) • koszulD (srVertexX F facets)
            (strandTensor F facets σ (p := p + 2) g) := by
      funext u
      show (∑ k, ((-1 : F) ^ (p + 1) • strandTensor F facets σ (p := p + 2) g) (Fin.cons k u)
          * srVertexX F facets k)
          = (-1 : F) ^ (p + 1) • (∑ k, strandTensor F facets σ (p := p + 2) g (Fin.cons k u)
            * srVertexX F facets k)
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        simp only [Pi.smul_apply]
        rw [smul_mul_assoc])
    rw [hlin, koszulD_strandTensor facets σ g]
    funext u
    show (-1 : F) ^ (p + 1) • ((-1 : F) ^ (p + 1) •
      strandTensor F facets σ (p := p + 1) (simplicialCoboundary F g) u) = _
    rw [smul_smul, hsq, one_smul]

end

end GaloisForLFunctions.HTGeometry
