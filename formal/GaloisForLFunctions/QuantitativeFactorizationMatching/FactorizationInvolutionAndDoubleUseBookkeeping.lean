import GaloisForLFunctions.QuantitativeFactorizationMatching.GlobalDyadicGraphAndCofactorFibres

/-!
# Sign-Reversing Factorization Involutions, Double-Use Bookkeeping, and Alternating Resolution

Combinatorial calculus of explicit sign-reversing involutions on squarefree integer sets along
prescribed factorization relations `R`:

1. **`FactorizationInvolution R S` and exact matching equivalence**: An involution `τ : ℕ → ℕ`
   (`τ (τ n) = n`) fixing all integers outside `squarefreeOf S`, flipping Möbius sign `μ (τ n) = -μ n`
   on every moved integer `τ n ≠ n`, and satisfying `R n (τ n)` on moved positive-Möbius vertices.
   Restricting `τ` to `movedPos` establishes an exact equivalence with `OppositeParityMatching R S`
   preserving matched and unmatched sets.
2. **Disjoint support gluing (`glueDisjoint`)**: Pairwise-disjoint involutions across disjoint
   subsets `S_i ⊆ S` glue into a single collision-free `FactorizationInvolution R S` whose unmatched
   set on `⋃_i S_i` is the disjoint union of the component unmatched sets.
3. **Double-use endpoint bookkeeping (`sum_moebius_eq_jointUnmatched_sub_doubleUsed`)**: For any two
   involutions `τ₀, τ₁` on `S`, the Möbius sum over `S` equals the signed remainder on the jointly
   unmatched set minus the Möbius sum over `doubleUsedSet τ₀ τ₁ = τ₀.movedSet ∩ τ₁.movedSet`.
4. **Acyclic alternating-walk resolution (`resolveDoubleUse`)**: Resolving double-used endpoints
   along alternating `(τ₀, τ₁)`-walks yields a single involution `τ_*` retaining all `τ₀`-positive
   sources and all `τ₁`-negative targets. Between ordered-cofactor drops and `(1 → 2)` upward
   mergers, each walk step decreases `ω(n)` by `2`.
-/

open Finset
open scoped Classical BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Sign-reversing factorization involutions and matching equivalence -/

/-- An explicit sign-reversing involution on `ℕ` supported inside `squarefreeOf S` whose 2-cycles
pair positive-Möbius integers `a` with negative-Möbius integers `b` satisfying `R a b`. -/
structure FactorizationInvolution (R : ℕ → ℕ → Prop) (S : Finset ℕ) where
  toFun : ℕ → ℕ
  involutive : Function.Involutive toFun
  fixed_outside : ∀ n : ℕ, n ∉ squarefreeOf S → toFun n = n
  sign_flip : ∀ n : ℕ, toFun n ≠ n → μ (toFun n) = -μ n
  adj_pos : ∀ n : ℕ, toFun n ≠ n → μ n = 1 → R n (toFun n)

namespace FactorizationInvolution

instance {R : ℕ → ℕ → Prop} {S : Finset ℕ} :
    CoeFun (FactorizationInvolution R S) (fun _ => ℕ → ℕ) :=
  ⟨FactorizationInvolution.toFun⟩

variable {R : ℕ → ℕ → Prop} {S : Finset ℕ} (τ : FactorizationInvolution R S)

@[simp]
theorem apply_apply (n : ℕ) : τ (τ n) = n :=
  τ.involutive n

theorem injective : Function.Injective τ :=
  τ.involutive.injective

theorem moved_mem_squarefreeOf {n : ℕ} (h : τ n ≠ n) : n ∈ squarefreeOf S := by
  by_contra hnot
  exact h (τ.fixed_outside n hnot)

theorem apply_ne_self_iff {n : ℕ} : τ (τ n) ≠ τ n ↔ τ n ≠ n := by
  rw [τ.apply_apply, ne_comm]

theorem moved_apply {n : ℕ} (h : τ n ≠ n) : τ (τ n) ≠ τ n :=
  τ.apply_ne_self_iff.mpr h

/-- Monotonicity of allowed edge relations. -/
def mono {R' : ℕ → ℕ → Prop} (hR : ∀ {a b : ℕ}, R a b → R' a b) :
    FactorizationInvolution R' S where
  toFun := τ
  involutive := τ.involutive
  fixed_outside := τ.fixed_outside
  sign_flip := τ.sign_flip
  adj_pos := fun n hn hμ => hR (τ.adj_pos n hn hμ)

/-- Monotonicity of ambient finite sets. -/
def monoSubset {T : Finset ℕ} (hST : S ⊆ T) :
    FactorizationInvolution R T where
  toFun := τ
  involutive := τ.involutive
  fixed_outside := fun n hn =>
    τ.fixed_outside n fun hm =>
      hn (mem_filter.mpr ⟨hST (mem_filter.mp hm).1, (mem_filter.mp hm).2⟩)
  sign_flip := τ.sign_flip
  adj_pos := τ.adj_pos

/-- All squarefree elements of `S` moved by `τ`. -/
def movedSet : Finset ℕ :=
  (squarefreeOf S).filter fun n => τ n ≠ n

/-- Positive-Möbius (`μ = 1`) elements moved by `τ`. -/
def movedPos : Finset ℕ :=
  (posParity S).filter fun n => τ n ≠ n

/-- Negative-Möbius (`μ = -1`) elements moved by `τ`. -/
def movedNeg : Finset ℕ :=
  (negParity S).filter fun n => τ n ≠ n

/-- Squarefree elements of `S` fixed (left unmatched) by `τ`. -/
def unmatchedSet : Finset ℕ :=
  (squarefreeOf S).filter fun n => τ n = n

theorem mem_movedSet {n : ℕ} : n ∈ τ.movedSet ↔ τ n ≠ n :=
  ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨τ.moved_mem_squarefreeOf h, h⟩⟩

theorem movedPos_subset : τ.movedPos ⊆ posParity S :=
  filter_subset _ _

theorem movedNeg_subset : τ.movedNeg ⊆ negParity S :=
  filter_subset _ _

theorem disjoint_movedPos_movedNeg : Disjoint τ.movedPos τ.movedNeg :=
  Disjoint.mono τ.movedPos_subset τ.movedNeg_subset (disjoint_posParity_negParity S)

theorem movedSet_eq_union : τ.movedSet = τ.movedPos ∪ τ.movedNeg := by
  ext n
  simp only [movedSet, movedPos, movedNeg, squarefreeOf_eq_posParity_union_negParity,
    mem_filter, mem_union]
  tauto

theorem unmatchedSet_eq_sdiff : τ.unmatchedSet = squarefreeOf S \ τ.movedSet := by
  ext n
  simp only [unmatchedSet, movedSet, mem_filter, mem_sdiff]
  tauto

theorem disjoint_movedSet_unmatchedSet : Disjoint τ.movedSet τ.unmatchedSet := by
  rw [disjoint_left]
  intro n hm hu
  exact (mem_filter.mp hm).2 (mem_filter.mp hu).2

theorem movedSet_union_unmatchedSet : τ.movedSet ∪ τ.unmatchedSet = squarefreeOf S := by
  ext n
  simp only [movedSet, unmatchedSet, mem_union, mem_filter]
  exact ⟨fun h => h.elim And.left And.left,
    fun hn => if h : τ n = n then Or.inr ⟨hn, h⟩ else Or.inl ⟨hn, h⟩⟩

theorem apply_mem_movedNeg_of_mem_movedPos {n : ℕ} (hn : n ∈ τ.movedPos) :
    τ n ∈ τ.movedNeg := by
  obtain ⟨hnP, hne⟩ := mem_filter.mp hn
  have hμn : μ n = 1 := (mem_filter.mp hnP).2
  have hne' : τ (τ n) ≠ τ n := τ.moved_apply hne
  have hsq' : τ n ∈ squarefreeOf S := τ.moved_mem_squarefreeOf hne'
  have hμ' : μ (τ n) = -1 := by have := τ.sign_flip n hne; omega
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hsq').1, hμ'⟩, hne'⟩

theorem apply_mem_movedPos_of_mem_movedNeg {n : ℕ} (hn : n ∈ τ.movedNeg) :
    τ n ∈ τ.movedPos := by
  obtain ⟨hnN, hne⟩ := mem_filter.mp hn
  have hμn : μ n = -1 := (mem_filter.mp hnN).2
  have hne' : τ (τ n) ≠ τ n := τ.moved_apply hne
  have hsq' : τ n ∈ squarefreeOf S := τ.moved_mem_squarefreeOf hne'
  have hμ' : μ (τ n) = 1 := by have := τ.sign_flip n hne; omega
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hsq').1, hμ'⟩, hne'⟩

theorem image_movedPos : τ.movedPos.image τ = τ.movedNeg := by
  ext b
  simp only [mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact τ.apply_mem_movedNeg_of_mem_movedPos ha
  · intro hb
    exact ⟨τ b, τ.apply_mem_movedPos_of_mem_movedNeg hb, τ.apply_apply b⟩

theorem image_movedNeg : τ.movedNeg.image τ = τ.movedPos := by
  ext a
  simp only [mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact τ.apply_mem_movedPos_of_mem_movedNeg hb
  · intro ha
    exact ⟨τ a, τ.apply_mem_movedNeg_of_mem_movedPos ha, τ.apply_apply a⟩

theorem card_movedPos_eq_movedNeg : τ.movedPos.card = τ.movedNeg.card := by
  rw [← τ.image_movedPos, card_image_of_injective _ τ.injective]

theorem card_movedSet : τ.movedSet.card = 2 * τ.movedPos.card := by
  rw [τ.movedSet_eq_union, card_union_of_disjoint τ.disjoint_movedPos_movedNeg,
    ← τ.card_movedPos_eq_movedNeg, two_mul]

theorem card_unmatchedSet_add_movedSet :
    τ.unmatchedSet.card + τ.movedSet.card = (squarefreeOf S).card := by
  rw [add_comm, ← card_union_of_disjoint τ.disjoint_movedSet_unmatchedSet,
    τ.movedSet_union_unmatchedSet]

/-- Converting a `FactorizationInvolution` to its associated `OppositeParityMatching`. -/
def toMatching : OppositeParityMatching R S where
  sources := τ.movedPos
  partner := τ
  sources_subset := τ.movedPos_subset
  injOn := fun _ _ _ _ h => τ.injective h
  partner_mem := fun _ ha => τ.movedNeg_subset (τ.apply_mem_movedNeg_of_mem_movedPos ha)
  adj := fun a ha =>
    τ.adj_pos a (mem_filter.mp ha).2 (mem_filter.mp (τ.movedPos_subset ha)).2

@[simp]
theorem toMatching_sources : τ.toMatching.sources = τ.movedPos := rfl

@[simp]
theorem toMatching_targets : τ.toMatching.targets = τ.movedNeg :=
  τ.image_movedPos

@[simp]
theorem toMatching_matchedSet : τ.toMatching.matchedSet = τ.movedSet := by
  rw [OppositeParityMatching.matchedSet, τ.toMatching_sources, τ.toMatching_targets,
    τ.movedSet_eq_union]

@[simp]
theorem toMatching_unmatchedSet : τ.toMatching.unmatchedSet = τ.unmatchedSet := by
  rw [OppositeParityMatching.unmatchedSet, τ.toMatching_matchedSet, τ.unmatchedSet_eq_sdiff]

/-- Converting any `OppositeParityMatching` into an explicit `FactorizationInvolution`. -/
def ofMatching (M : OppositeParityMatching R S) : FactorizationInvolution R S := by
  let invPartner : ℕ → ℕ := fun n =>
    if hsrc : n ∈ M.sources then M.partner n
    else if htgt : ∃ a ∈ M.sources, M.partner a = n then htgt.choose
    else n
  have htgt_not_src : ∀ a ∈ M.sources, M.partner a ∉ M.sources := fun a ha hmem =>
    disjoint_left.mp M.disjoint_sources_targets hmem (mem_image_of_mem M.partner ha)
  have htgt_eval : ∀ a ∈ M.sources, invPartner (M.partner a) = a := by
    intro a ha
    have hex : ∃ x ∈ M.sources, M.partner x = M.partner a := ⟨a, ha, rfl⟩
    simp only [invPartner, dif_neg (htgt_not_src a ha), dif_pos hex]
    exact M.injOn hex.choose_spec.1 ha hex.choose_spec.2
  refine
    { toFun := invPartner
      involutive := fun n => ?_
      fixed_outside := fun n hn => ?_
      sign_flip := fun n hn => ?_
      adj_pos := fun n hn hμ => ?_ }
  · by_cases h1 : n ∈ M.sources
    · have hfn : invPartner n = M.partner n := dif_pos h1
      rw [hfn, htgt_eval n h1]
    · by_cases h2 : ∃ a ∈ M.sources, M.partner a = n
      · have hfn : invPartner n = h2.choose := by simp only [invPartner, dif_neg h1, dif_pos h2]
        rw [hfn]
        have ha : h2.choose ∈ M.sources := h2.choose_spec.1
        rw [show invPartner h2.choose = M.partner h2.choose from dif_pos ha]
        exact h2.choose_spec.2
      · have hfn : invPartner n = n := by simp only [invPartner, dif_neg h1, dif_neg h2]
        rw [hfn, hfn]
  · have hn_src : n ∉ M.sources := fun hs =>
      hn (M.matchedSet_subset (mem_union_left _ hs))
    have hn_tgt : ¬ ∃ a ∈ M.sources, M.partner a = n := by
      rintro ⟨a, ha, rfl⟩
      exact hn (M.matchedSet_subset (mem_union_right _ (mem_image_of_mem M.partner ha)))
    simp only [invPartner, dif_neg hn_src, dif_neg hn_tgt]
  · by_cases h1 : n ∈ M.sources
    · have hfn : invPartner n = M.partner n := dif_pos h1
      rw [hfn]
      have hμa : μ n = 1 := (mem_filter.mp (M.sources_subset h1)).2
      have hμb : μ (M.partner n) = -1 := (mem_filter.mp (M.partner_mem n h1)).2
      omega
    · by_cases h2 : ∃ a ∈ M.sources, M.partner a = n
      · have hfn : invPartner n = h2.choose := by simp only [invPartner, dif_neg h1, dif_pos h2]
        rw [hfn]
        have ha : h2.choose ∈ M.sources := h2.choose_spec.1
        have hμa : μ h2.choose = 1 := (mem_filter.mp (M.sources_subset ha)).2
        have hμn : μ n = -1 := h2.choose_spec.2 ▸ (mem_filter.mp (M.partner_mem _ ha)).2
        omega
      · simp only [invPartner, dif_neg h1, dif_neg h2] at hn
        exact False.elim (hn rfl)
  · by_cases h1 : n ∈ M.sources
    · rw [show invPartner n = M.partner n from dif_pos h1]
      exact M.adj n h1
    · by_cases h2 : ∃ a ∈ M.sources, M.partner a = n
      · have hμn : μ n = -1 :=
          h2.choose_spec.2 ▸ (mem_filter.mp (M.partner_mem _ h2.choose_spec.1)).2
        omega
      · simp only [invPartner, dif_neg h1, dif_neg h2] at hn
        exact False.elim (hn rfl)

theorem ofMatching_apply_source {M : OppositeParityMatching R S} {a : ℕ} (ha : a ∈ M.sources) :
    ofMatching M a = M.partner a := by
  change (if hsrc : a ∈ M.sources then M.partner a else _) = M.partner a
  exact dif_pos ha

@[simp]
theorem ofMatching_movedPos (M : OppositeParityMatching R S) :
    (ofMatching M).movedPos = M.sources := by
  ext a
  simp only [movedPos, mem_filter]
  constructor
  · rintro ⟨haP, hne⟩
    by_contra hnot
    have hμa : μ a = 1 := (mem_filter.mp haP).2
    have hnot_tgt : ¬ ∃ x ∈ M.sources, M.partner x = a := by
      rintro ⟨x, hx, rfl⟩
      have hμb : μ (M.partner x) = -1 := (mem_filter.mp (M.partner_mem x hx)).2
      omega
    change (if hsrc : a ∈ M.sources then M.partner a
      else if htgt : ∃ x ∈ M.sources, M.partner x = a then htgt.choose else a) ≠ a at hne
    simp only [dif_neg hnot, dif_neg hnot_tgt, ne_eq, not_true_eq_false] at hne
  · intro ha
    refine ⟨M.sources_subset ha, ?_⟩
    rw [ofMatching_apply_source ha]
    intro heq
    have h1 := (mem_filter.mp (M.sources_subset ha)).2
    have h2 := heq ▸ (mem_filter.mp (M.partner_mem a ha)).2
    omega

@[simp]
theorem ofMatching_movedNeg (M : OppositeParityMatching R S) :
    (ofMatching M).movedNeg = M.targets := by
  rw [← (ofMatching M).image_movedPos, ofMatching_movedPos, OppositeParityMatching.targets]
  refine image_congr fun a ha => ofMatching_apply_source ha

@[simp]
theorem ofMatching_movedSet (M : OppositeParityMatching R S) :
    (ofMatching M).movedSet = M.matchedSet := by
  rw [movedSet_eq_union, ofMatching_movedPos, ofMatching_movedNeg,
    OppositeParityMatching.matchedSet]

@[simp]
theorem ofMatching_unmatchedSet (M : OppositeParityMatching R S) :
    (ofMatching M).unmatchedSet = M.unmatchedSet := by
  rw [unmatchedSet_eq_sdiff, ofMatching_movedSet, OppositeParityMatching.unmatchedSet]

/-- Moved pairs cancel identically in the unweighted Möbius sum. -/
theorem sum_moebius_movedSet : ∑ n ∈ τ.movedSet, μ n = 0 := by
  rw [← τ.toMatching_matchedSet]
  exact τ.toMatching.sum_moebius_matchedSet

/-- The Möbius sum over `S` equals the Möbius sum over the fixed squarefree remainder. -/
theorem sum_moebius_eq_unmatched :
    ∑ n ∈ S, μ n = ∑ n ∈ τ.unmatchedSet, μ n := by
  have hsq : ∑ n ∈ S, μ n = ∑ n ∈ squarefreeOf S, μ n := by
    refine (sum_subset (filter_subset _ S) fun n _ hnot => ?_).symm
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h => hnot (mem_filter.mpr ⟨‹_›, h⟩)
  rw [hsq, ← τ.movedSet_union_unmatchedSet, sum_union τ.disjoint_movedSet_unmatchedSet,
    τ.sum_moebius_movedSet, zero_add]

theorem abs_sum_moebius_le_unmatched :
    |∑ n ∈ S, μ n| ≤ (τ.unmatchedSet.card : ℤ) := by
  rw [← τ.toMatching_unmatchedSet]
  exact τ.toMatching.abs_sum_moebius_le_unmatched

/-! ### 2. Gluing involutions across pairwise-disjoint subsets -/

/-- Gluing a family of `FactorizationInvolution`s supported on pairwise-disjoint subsets `B i ⊆ S`
into a single collision-free `FactorizationInvolution R S`. -/
def glueDisjoint {ι : Type*} (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hsub : ∀ i ∈ I, B i ⊆ S)
    (fam : ∀ i, FactorizationInvolution R (B i)) :
    FactorizationInvolution R S := by
  let g : ℕ → ℕ := fun n =>
    if hex : ∃ i ∈ I, n ∈ B i then fam hex.choose n else n
  have hmem_unique : ∀ {i j : ι} {n : ℕ}, i ∈ I → j ∈ I → n ∈ B i → n ∈ B j → i = j := by
    intro i j n hi hj hni hnj
    by_contra hne
    exact disjoint_left.mp (hdisj hi hj hne) hni hnj
  have hg_on : ∀ {i : ι} {n : ℕ}, i ∈ I → n ∈ B i → g n = fam i n := by
    intro i n hi hni
    have hex : ∃ j ∈ I, n ∈ B j := ⟨i, hi, hni⟩
    simp only [g, dif_pos hex]
    rw [hmem_unique hex.choose_spec.1 hi hex.choose_spec.2 hni]
  have hfam_stays : ∀ {i : ι} {n : ℕ}, n ∈ B i → fam i n ∈ B i := by
    intro i n hni
    by_cases hmv : fam i n = n
    · rwa [hmv]
    · exact (mem_filter.mp ((fam i).moved_mem_squarefreeOf
        ((fam i).moved_apply hmv))).1
  refine
    { toFun := g
      involutive := fun n => ?_
      fixed_outside := fun n hn => ?_
      sign_flip := fun n hn => ?_
      adj_pos := fun n hn hμ => ?_ }
  · by_cases hex : ∃ i ∈ I, n ∈ B i
    · obtain ⟨i, hi, hni⟩ := hex
      rw [hg_on hi hni, hg_on hi (hfam_stays hni), (fam i).apply_apply]
    · simp only [g, dif_neg hex]
  · by_cases hex : ∃ i ∈ I, n ∈ B i
    · obtain ⟨i, hi, hni⟩ := hex
      rw [hg_on hi hni]
      exact (fam i).fixed_outside n fun hsq =>
        hn (mem_filter.mpr ⟨hsub i hi hni, (mem_filter.mp hsq).2⟩)
    · simp only [g, dif_neg hex]
  · by_cases hex : ∃ i ∈ I, n ∈ B i
    · obtain ⟨i, hi, hni⟩ := hex
      rw [hg_on hi hni] at hn ⊢
      exact (fam i).sign_flip n hn
    · simp only [g, dif_neg hex] at hn
      exact False.elim (hn rfl)
  · by_cases hex : ∃ i ∈ I, n ∈ B i
    · obtain ⟨i, hi, hni⟩ := hex
      rw [hg_on hi hni] at hn ⊢
      exact (fam i).adj_pos n hn hμ
    · simp only [g, dif_neg hex] at hn
      exact False.elim (hn rfl)

theorem glueDisjoint_unmatchedSet_eq_biUnion {ι : Type*} (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = S)
    (fam : ∀ i, FactorizationInvolution R (B i)) :
    (glueDisjoint I B hdisj (fun _ hi => hcover ▸ subset_biUnion_of_mem B hi) fam).unmatchedSet =
      I.biUnion (fun i => (fam i).unmatchedSet) := by
  have hsub : ∀ i ∈ I, B i ⊆ S := fun _ hi => hcover ▸ subset_biUnion_of_mem B hi
  let G := glueDisjoint I B hdisj hsub fam
  have hmem_unique : ∀ {i j : ι} {n : ℕ}, i ∈ I → j ∈ I → n ∈ B i → n ∈ B j → i = j := by
    intro i j n hi hj hni hnj
    by_contra hne
    exact disjoint_left.mp (hdisj hi hj hne) hni hnj
  have hg_on : ∀ {i : ι} {n : ℕ}, i ∈ I → n ∈ B i → G n = fam i n := by
    intro i n hi hni
    have hex : ∃ j ∈ I, n ∈ B j := ⟨i, hi, hni⟩
    change (if hex : ∃ j ∈ I, n ∈ B j then fam hex.choose n else n) = fam i n
    rw [dif_pos hex, hmem_unique hex.choose_spec.1 hi hex.choose_spec.2 hni]
  ext n
  simp only [unmatchedSet, mem_filter, mem_biUnion, squarefreeOf]
  constructor
  · rintro ⟨⟨hnS, hsq⟩, hfix⟩
    rw [← hcover, mem_biUnion] at hnS
    obtain ⟨i, hi, hni⟩ := hnS
    exact ⟨i, hi, ⟨hni, hsq⟩, (hg_on hi hni).symm.trans hfix⟩
  · rintro ⟨i, hi, ⟨hni, hsq⟩, hfix⟩
    exact ⟨⟨hsub i hi hni, hsq⟩, (hg_on hi hni).trans hfix⟩

end FactorizationInvolution

/-! ### 3. Bookkeeping for endpoints used twice and the signed remainder -/

/-- Squarefree endpoints in `S` used by both `τ₀` and `τ₁`. -/
def doubleUsedSet {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) : Finset ℕ :=
  τ₀.movedSet ∩ τ₁.movedSet

/-- Positive-Möbius endpoints in `S` used by both `τ₀` and `τ₁`. -/
def doubleUsedPos {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) : Finset ℕ :=
  τ₀.movedPos ∩ τ₁.movedPos

/-- Negative-Möbius endpoints in `S` used by both `τ₀` and `τ₁`. -/
def doubleUsedNeg {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) : Finset ℕ :=
  τ₀.movedNeg ∩ τ₁.movedNeg

/-- Squarefree elements of `S` left fixed by both `τ₀` and `τ₁`. -/
def jointUnmatchedSet {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) : Finset ℕ :=
  squarefreeOf S \ (τ₀.movedSet ∪ τ₁.movedSet)

theorem doubleUsedSet_eq_union {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) :
    doubleUsedSet τ₀ τ₁ = doubleUsedPos τ₀ τ₁ ∪ doubleUsedNeg τ₀ τ₁ := by
  ext n
  simp only [doubleUsedSet, doubleUsedPos, doubleUsedNeg,
    FactorizationInvolution.movedSet_eq_union, mem_inter, mem_union]
  constructor
  · rintro ⟨h0p | h0n, h1p | h1n⟩
    · exact Or.inl ⟨h0p, h1p⟩
    · exact False.elim (disjoint_left.mp (disjoint_posParity_negParity S)
        (τ₀.movedPos_subset h0p) (τ₁.movedNeg_subset h1n))
    · exact False.elim (disjoint_right.mp (disjoint_posParity_negParity S)
        (τ₀.movedNeg_subset h0n) (τ₁.movedPos_subset h1p))
    · exact Or.inr ⟨h0n, h1n⟩
  · rintro (⟨h0p, h1p⟩ | ⟨h0n, h1n⟩)
    · exact ⟨Or.inl h0p, Or.inl h1p⟩
    · exact ⟨Or.inr h0n, Or.inr h1n⟩

/-- **Exact two-involution signed remainder identity with double-use bookkeeping**:
`∑_{n ∈ S} μ(n) = ∑_{n ∈ jointUnmatchedSet τ₀ τ₁} μ(n) - ∑_{n ∈ doubleUsedSet τ₀ τ₁} μ(n)`. -/
theorem sum_moebius_eq_jointUnmatched_sub_doubleUsed {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) :
    ∑ n ∈ S, μ n =
      (∑ n ∈ jointUnmatchedSet τ₀ τ₁, μ n) - (∑ n ∈ doubleUsedSet τ₀ τ₁, μ n) := by
  have hsq : ∑ n ∈ S, μ n = ∑ n ∈ squarefreeOf S, μ n := by
    refine (sum_subset (filter_subset _ S) fun n _ hnot => ?_).symm
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h =>
      hnot (mem_filter.mpr ⟨‹_›, h⟩)
  have hsub : τ₀.movedSet ∪ τ₁.movedSet ⊆ squarefreeOf S :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hsdiff := (sum_sdiff hsub (f := fun n => μ n)).symm
  have hunion := sum_union_inter (s₁ := τ₀.movedSet) (s₂ := τ₁.movedSet) (f := fun n => μ n)
  rw [τ₀.sum_moebius_movedSet, τ₁.sum_moebius_movedSet, add_zero] at hunion
  unfold jointUnmatchedSet doubleUsedSet
  rw [hsq, hsdiff]
  omega

/-- Exact inclusion–exclusion count of positive endpoints across two involutions. -/
theorem card_movedPos_union_add_doubleUsedPos {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S) :
    (τ₀.movedPos ∪ τ₁.movedPos).card + (doubleUsedPos τ₀ τ₁).card =
      τ₀.movedPos.card + τ₁.movedPos.card :=
  card_union_add_card_inter τ₀.movedPos τ₁.movedPos

/-- When `τ₁` only pairs negative vertices untouched by `τ₀`, every double-used endpoint has
positive Möbius sign (`μ = 1`), so the double-use signed charge equals `#(doubleUsedPos τ₀ τ₁)`. -/
theorem doubleUsedSet_eq_pos_of_disjoint_movedNeg {R₀ R₁ : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ : FactorizationInvolution R₀ S) (τ₁ : FactorizationInvolution R₁ S)
    (hdisj : Disjoint τ₀.movedNeg τ₁.movedNeg) :
    doubleUsedSet τ₀ τ₁ = doubleUsedPos τ₀ τ₁ ∧
      ∑ n ∈ doubleUsedSet τ₀ τ₁, μ n = ((doubleUsedPos τ₀ τ₁).card : ℤ) := by
  have hemp : doubleUsedNeg τ₀ τ₁ = ∅ := disjoint_iff_inter_eq_empty.mp hdisj
  have heq : doubleUsedSet τ₀ τ₁ = doubleUsedPos τ₀ τ₁ := by
    rw [doubleUsedSet_eq_union, hemp, union_empty]
  refine ⟨heq, ?_⟩
  rw [heq]
  calc ∑ n ∈ doubleUsedPos τ₀ τ₁, μ n
      = ∑ _n ∈ doubleUsedPos τ₀ τ₁, (1 : ℤ) :=
        sum_congr rfl fun n hn =>
          (mem_filter.mp (τ₀.movedPos_subset (mem_inter.mp hn).1)).2
    _ = ((doubleUsedPos τ₀ τ₁).card : ℤ) := by simp

/-! ### 4. Acyclic alternating-walk resolution of double-used endpoints -/

/-- A single two-edge alternating transition `x → τ₀ x = τ₁ y → y` between moved positive
endpoints of two involutions sharing a negative partner. -/
def InvolutionStep {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) (x y : ℕ) : Prop :=
  x ∈ τ₀.movedPos ∧ y ∈ τ₁.movedPos ∧ τ₀ x = τ₁ y

/-- Iterated alternating walks of `k` two-edge steps starting at `start`. -/
inductive InvolutionWalk {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) (start : ℕ) : ℕ → ℕ → Prop
  | nil : InvolutionWalk τ₀ τ₁ start 0 start
  | snoc {k x y : ℕ} :
      InvolutionWalk τ₀ τ₁ start k x → InvolutionStep τ₀ τ₁ x y →
        InvolutionWalk τ₀ τ₁ start (k + 1) y

theorem involutionStep_unique_right {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    {τ₀ τ₁ : FactorizationInvolution R S} {x y z : ℕ}
    (h₁ : InvolutionStep τ₀ τ₁ x y) (h₂ : InvolutionStep τ₀ τ₁ x z) : y = z :=
  τ₁.injective (h₁.2.2.symm.trans h₂.2.2)

/-- Alternating walks from `τ₀`-only positive starts never merge: the endpoint uniquely determines
both the starting vertex and the walk length. -/
theorem involutionWalk_unique_start_and_length {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    {τ₀ τ₁ : FactorizationInvolution R S} {a b k l x : ℕ}
    (ha : a ∉ τ₁.movedPos) (hb : b ∉ τ₁.movedPos)
    (hw₁ : InvolutionWalk τ₀ τ₁ a k x) (hw₂ : InvolutionWalk τ₀ τ₁ b l x) :
    a = b ∧ k = l := by
  induction hw₁ generalizing l with
  | nil =>
    cases hw₂ with
    | nil => exact ⟨rfl, rfl⟩
    | snoc _ hlast => exact False.elim (ha hlast.2.1)
  | snoc hw hstep ih =>
    cases hw₂ with
    | nil => exact False.elim (hb hstep.2.1)
    | snoc hw' hstep' =>
      have hprev : _ = _ := τ₀.injective (hstep.2.2.trans hstep'.2.2.symm)
      subst hprev
      obtain ⟨hab, hkl⟩ := ih hw'
      exact ⟨hab, congrArg Nat.succ hkl⟩

private def switchPos {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) (x : ℕ) : Prop :=
  ∃ a ∈ τ₀.movedPos, a ∉ τ₁.movedPos ∧ ∃ k : ℕ, InvolutionWalk τ₀ τ₁ a k x

private def resolveDoubleUseMatching {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) :
    OppositeParityMatching R S where
  sources := (τ₀.movedPos.filter (switchPos τ₀ τ₁)) ∪
    (τ₁.movedPos.filter fun x => ¬ switchPos τ₀ τ₁ x)
  partner x := if switchPos τ₀ τ₁ x then τ₀ x else τ₁ x
  sources_subset x hx := by
    simp only [mem_union, mem_filter] at hx
    exact hx.elim (fun h => τ₀.movedPos_subset h.1) (fun h => τ₁.movedPos_subset h.1)
  injOn x hx y hy heq := by
    simp only [mem_coe, mem_union, mem_filter] at hx hy
    have hstep_on : ∀ {u v : ℕ}, switchPos τ₀ τ₁ u → InvolutionStep τ₀ τ₁ u v →
        switchPos τ₀ τ₁ v := by
      rintro u v ⟨a, ha0, ha1, k, hw⟩ hst
      exact ⟨a, ha0, ha1, k + 1, hw.snoc hst⟩
    by_cases hx_on : switchPos τ₀ τ₁ x <;> by_cases hy_on : switchPos τ₀ τ₁ y <;>
      simp only [hx_on, hy_on, ↓reduceIte] at heq
    · exact τ₀.injective heq
    · have hold_x : x ∈ τ₀.movedPos := hx.elim And.left fun h => False.elim (h.2 hx_on)
      have hnew_y : y ∈ τ₁.movedPos := hy.elim (fun h => False.elim (hy_on h.2)) And.left
      exact False.elim (hy_on (hstep_on hx_on ⟨hold_x, hnew_y, heq⟩))
    · have hold_y : y ∈ τ₀.movedPos := hy.elim And.left fun h => False.elim (h.2 hy_on)
      have hnew_x : x ∈ τ₁.movedPos := hx.elim (fun h => False.elim (hx_on h.2)) And.left
      exact False.elim (hx_on (hstep_on hy_on ⟨hold_y, hnew_x, heq.symm⟩))
    · exact τ₁.injective heq
  partner_mem x hx := by
    simp only [mem_union, mem_filter] at hx
    by_cases hx_on : switchPos τ₀ τ₁ x
    · simp only [if_pos hx_on]
      have hm : x ∈ τ₀.movedPos := hx.elim And.left fun h => False.elim (h.2 hx_on)
      exact τ₀.movedNeg_subset (τ₀.apply_mem_movedNeg_of_mem_movedPos hm)
    · simp only [if_neg hx_on]
      have hm : x ∈ τ₁.movedPos := hx.elim (fun h => False.elim (hx_on h.2)) And.left
      exact τ₁.movedNeg_subset (τ₁.apply_mem_movedNeg_of_mem_movedPos hm)
  adj x hx := by
    simp only [mem_union, mem_filter] at hx
    by_cases hx_on : switchPos τ₀ τ₁ x
    · simp only [if_pos hx_on]
      have hm : x ∈ τ₀.movedPos := hx.elim And.left fun h => False.elim (h.2 hx_on)
      exact τ₀.adj_pos x (mem_filter.mp hm).2 (mem_filter.mp (τ₀.movedPos_subset hm)).2
    · simp only [if_neg hx_on]
      have hm : x ∈ τ₁.movedPos := hx.elim (fun h => False.elim (hx_on h.2)) And.left
      exact τ₁.adj_pos x (mem_filter.mp hm).2 (mem_filter.mp (τ₁.movedPos_subset hm)).2

/-- **Canonical alternating-walk double-use resolution**: resolves all double-used endpoints of
`τ₀` and `τ₁` into a single `FactorizationInvolution R S` retaining `τ₀.movedPos` and
`τ₁.movedNeg` simultaneously. -/
def resolveDoubleUse {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) :
    FactorizationInvolution R S :=
  FactorizationInvolution.ofMatching (resolveDoubleUseMatching τ₀ τ₁)

theorem resolveDoubleUse_spec {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (τ₀ τ₁ : FactorizationInvolution R S) :
    τ₀.movedPos ⊆ (resolveDoubleUse τ₀ τ₁).movedPos ∧
      τ₁.movedNeg ⊆ (resolveDoubleUse τ₀ τ₁).movedNeg ∧
      (∀ x ∈ (resolveDoubleUse τ₀ τ₁).movedPos,
        (x ∈ τ₀.movedPos ∧ resolveDoubleUse τ₀ τ₁ x = τ₀ x) ∨
          (x ∈ τ₁.movedPos ∧ resolveDoubleUse τ₀ τ₁ x = τ₁ x)) := by
  let on := switchPos τ₀ τ₁
  have hsrc_eq : (resolveDoubleUse τ₀ τ₁).movedPos =
      (τ₀.movedPos.filter on) ∪ (τ₁.movedPos.filter fun x => ¬ on x) :=
    FactorizationInvolution.ofMatching_movedPos (resolveDoubleUseMatching τ₀ τ₁)
  have hpart : ∀ x ∈ (resolveDoubleUse τ₀ τ₁).movedPos,
      resolveDoubleUse τ₀ τ₁ x = if on x then τ₀ x else τ₁ x := by
    intro x hx
    have hx_src : x ∈ (resolveDoubleUseMatching τ₀ τ₁).sources :=
      (FactorizationInvolution.ofMatching_movedPos (resolveDoubleUseMatching τ₀ τ₁)) ▸ hx
    exact FactorizationInvolution.ofMatching_apply_source hx_src
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hsrc_eq, mem_union, mem_filter, mem_filter]
    by_cases hon : on x
    · exact Or.inl ⟨hx, hon⟩
    · refine Or.inr ⟨?_, hon⟩
      by_contra hx1
      exact hon ⟨x, hx, hx1, 0, .nil⟩
  · intro b hb
    obtain ⟨y, hy1, rfl⟩ := mem_image.mp (τ₁.image_movedPos.symm ▸ hb)
    rw [← (resolveDoubleUse τ₀ τ₁).image_movedPos]
    by_cases hon : on y
    · obtain ⟨a, ha0, ha1, k, hw⟩ := hon
      cases hw with
      | nil => exact False.elim (ha1 hy1)
      | @snoc k' x' _ hw_prev hlast =>
        have hprev_on : on x' := ⟨a, ha0, ha1, k', hw_prev⟩
        have hprev_mem : x' ∈ (resolveDoubleUse τ₀ τ₁).movedPos := by
          rw [hsrc_eq, mem_union, mem_filter]
          exact Or.inl ⟨hlast.1, hprev_on⟩
        refine mem_image.mpr ⟨x', hprev_mem, ?_⟩
        rw [hpart x' hprev_mem, if_pos hprev_on]
        exact hlast.2.2
    · have hy_mem : y ∈ (resolveDoubleUse τ₀ τ₁).movedPos := by
        rw [hsrc_eq, mem_union, mem_filter, mem_filter]
        exact Or.inr ⟨hy1, hon⟩
      refine mem_image.mpr ⟨y, hy_mem, ?_⟩
      rw [hpart y hy_mem, if_neg hon]
  · intro x hx
    have hx' := hx
    rw [hsrc_eq, mem_union, mem_filter, mem_filter] at hx'
    rcases hx' with ⟨hx0, hon⟩ | ⟨hx1, hnoff⟩
    · exact Or.inl ⟨hx0, (hpart x hx).trans (if_pos hon)⟩
    · exact Or.inr ⟨hx1, (hpart x hx).trans (if_neg hnoff)⟩

/-- Ordered-cofactor edge relation inside `GlobalDyadicOneTwoRel`. -/
abbrev OrderedFibreRel (m n : ℕ) : Prop :=
  GlobalDyadicOneTwoRel m n ∧ evenPrefixCofactor m = evenPrefixCofactor n

/-- Every moved positive vertex of an `OrderedFibreRel` involution on `(X, 2X]` drops exactly one
prime factor (`ω(τ₀ x) + 1 = ω(x)`). -/
theorem orderedFibreInvolution_omega_drop {X x : ℕ}
    (τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X)))
    (hx : x ∈ τ₀.movedPos) :
    (τ₀ x).primeFactors.card + 1 = x.primeFactors.card := by
  obtain ⟨hxP, hne⟩ := mem_filter.mp hx
  have hX1 : 1 ≤ X := by
    obtain ⟨hl, hu⟩ := mem_Ioc.mp (mem_filter.mp hxP).1
    omega
  have hadj := τ₀.adj_pos x hne (mem_filter.mp hxP).2
  let a := evenPrefixCofactor x
  have hx_fib : x ∈ fibrePos X a := mem_filter.mpr ⟨hxP, rfl⟩
  have hy_neg := τ₀.movedNeg_subset (τ₀.apply_mem_movedNeg_of_mem_movedPos hx)
  have hy_fib : τ₀ x ∈ fibreNeg X a :=
    mem_filter.mpr ⟨hy_neg, hadj.2.symm⟩
  obtain ⟨_, _, q, r, hqp, hrp, hqr, hxa, hlt_q⟩ := mem_fibrePos_structure hX1 hx_fib
  obtain ⟨_, _, p, hpp, hya, hlt_p⟩ := mem_fibreNeg_structure hX1 hy_fib
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0, zero_mul] at hya
      have := (mem_Ioc.mp (mem_filter.mp hy_neg).1).1
      omega
    · exact hpos
  have hp_not : p ∉ a.primeFactors := fun hm => (hlt_p p hm).false
  have hq_not : q ∉ a.primeFactors := fun hm => (hlt_q q hm).false
  have hr_not_aq : r ∉ insert q a.primeFactors := by
    intro hm
    rcases mem_insert.mp hm with rfl | hm'
    · exact hqr.false
    · exact ((hlt_q r hm').trans hqr).false
  have hpf_y : (τ₀ x).primeFactors = insert p a.primeFactors := by
    rw [hya, Nat.primeFactors_mul ha_pos.ne' hpp.ne_zero, hpp.primeFactors, union_comm,
      singleton_union]
  have hpf_x : x.primeFactors = insert r (insert q a.primeFactors) := by
    rw [hxa, ← mul_assoc,
      Nat.primeFactors_mul (Nat.mul_ne_zero ha_pos.ne' hqp.ne_zero) hrp.ne_zero,
      Nat.primeFactors_mul ha_pos.ne' hqp.ne_zero, hqp.primeFactors, hrp.primeFactors]
    ext d
    simp only [mem_union, mem_singleton, mem_insert]
    tauto
  rw [hpf_y, hpf_x, card_insert_of_notMem hp_not, card_insert_of_notMem hr_not_aq,
    card_insert_of_notMem hq_not]

/-- **Strict factor-count descent along alternating walks**: between an `OrderedFibreRel`
involution `τ₀` and a `(1 → 2)` upward involution `τ₁` (`ω(τ₁ y) = ω(y) + 1`), an alternating walk
of `k` steps strictly decreases `ω` by `2k`, bounding walk length by `ω(a) / 2`. -/
theorem involutionWalk_omega_descent {X : ℕ}
    (τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X)))
    (τ₁ : FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)))
    (hup : ∀ y ∈ τ₁.movedPos, (τ₁ y).primeFactors.card = y.primeFactors.card + 1)
    {a k x : ℕ}
    (hw : InvolutionWalk (τ₀.mono fun h => h.1) τ₁ a k x) :
    x.primeFactors.card + 2 * k = a.primeFactors.card := by
  induction hw with
  | nil => simp
  | snoc hw_prev hstep ih =>
    have hx0 : _ ∈ τ₀.movedPos := hstep.1
    have hy1 : _ ∈ τ₁.movedPos := hstep.2.1
    have heq : τ₀ _ = τ₁ _ := hstep.2.2
    have hdrop := orderedFibreInvolution_omega_drop τ₀ hx0
    have hgain := hup _ hy1
    rw [heq] at hdrop
    omega

/-- **Strict global unmatched-count reduction when clearing root primes**: if `τ₀` is an ordered
involution on `(X, 2X]` and `τ₁` uses only semiprime positive endpoints (`ω = 2`) while covering
all prime targets of `τ₀`, then `resolveDoubleUse` retains every matched vertex of `τ₀` and
strictly decreases `#unmatchedSet` by at least `2 * #(τ₁.movedNeg \ τ₀.movedNeg)`. -/
theorem resolveDoubleUse_unmatched_reduction {X : ℕ}
    (τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X)))
    (τ₁ : FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)))
    (hsemi : ∀ m ∈ τ₁.movedPos, m.primeFactors.card = 2)
    (hprimes : ∀ p ∈ τ₀.movedNeg, p.Prime → p ∈ τ₁.movedNeg) :
    let τ_star := resolveDoubleUse (τ₀.mono fun h => h.1) τ₁
    τ₀.movedPos ⊆ τ_star.movedPos ∧
      τ₀.movedNeg ∪ τ₁.movedNeg ⊆ τ_star.movedNeg ∧
      τ_star.unmatchedSet.card + 2 * (τ₁.movedNeg \ τ₀.movedNeg).card ≤
        τ₀.unmatchedSet.card := by
  set τ₀' := τ₀.mono (R' := GlobalDyadicOneTwoRel) fun h => h.1
  set τ_star := resolveDoubleUse τ₀' τ₁
  obtain ⟨hpos_sub, hneg1_sub, hchoice⟩ := resolveDoubleUse_spec τ₀' τ₁
  have hneg0_sub : τ₀.movedNeg ⊆ τ_star.movedNeg := by
    intro b hb
    by_cases hbp : b.Prime
    · exact hneg1_sub (hprimes b hb hbp)
    · obtain ⟨x, hx0, rfl⟩ := mem_image.mp (τ₀.image_movedPos.symm ▸ hb)
      have hx_star : x ∈ τ_star.movedPos := hpos_sub hx0
      rcases hchoice x hx_star with ⟨_, heq⟩ | ⟨hx1, _⟩
      · rw [← τ_star.image_movedPos]
        exact mem_image.mpr ⟨x, hx_star, heq⟩
      · have hdrop := orderedFibreInvolution_omega_drop τ₀ hx0
        rw [hsemi x hx1] at hdrop
        have hcard1 : (τ₀ x).primeFactors.card = 1 := by omega
        obtain ⟨q, hq⟩ := card_eq_one.mp hcard1
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq]; simp)
        have hsq_b : Squarefree (τ₀ x) :=
          (mem_filter.mp (τ₀.moved_mem_squarefreeOf (mem_filter.mp hb).2)).2
        have hb_eq : τ₀ x = q := by
          rw [← Nat.prod_primeFactors_of_squarefree hsq_b, hq, prod_singleton]
        exact False.elim (hbp (hb_eq ▸ hqp))
  have hunion_neg : τ₀.movedNeg ∪ τ₁.movedNeg ⊆ τ_star.movedNeg :=
    union_subset hneg0_sub hneg1_sub
  refine ⟨hpos_sub, hunion_neg, ?_⟩
  have hextra : (τ₀.movedNeg ∪ τ₁.movedNeg).card =
      τ₀.movedNeg.card + (τ₁.movedNeg \ τ₀.movedNeg).card := by
    rw [← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff_self_right]
  have hneg_ge : τ₀.movedNeg.card + (τ₁.movedNeg \ τ₀.movedNeg).card ≤ τ_star.movedNeg.card :=
    hextra ▸ card_le_card hunion_neg
  have htot₀ := τ₀.card_unmatchedSet_add_movedSet
  have htot_star := τ_star.card_unmatchedSet_add_movedSet
  rw [τ₀.card_movedSet, τ₀.card_movedPos_eq_movedNeg] at htot₀
  rw [τ_star.card_movedSet, τ_star.card_movedPos_eq_movedNeg] at htot_star
  omega

end GaloisForLFunctions.QuantitativeFactorizationMatching
