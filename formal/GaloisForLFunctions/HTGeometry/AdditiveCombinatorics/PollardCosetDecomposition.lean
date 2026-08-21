import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardGrynkiewicz

/-!
# Coset decomposition of the representation counts

Let `K` be a subgroup of a finite commutative group `G`.  Decomposing `A` into its intersections
with the cosets of `K`, the counting functions `rep` and `repSum` split additively:

* `rep_eq_sum_inter_cosets` — `rep A B c` is the sum of `rep (A ∩ u) B c` over the cosets `u`
  meeting `A`; this only needs the fact that the pieces partition `A`.
* `repSum_eq_sum_inter_cosets` — if in addition `B` lies inside a single coset of `K`, then the
  products `(A ∩ u) · B` lie in pairwise distinct cosets, so at most one piece contributes to any
  given representation count and hence `∑_{i≤t} #(A ·_i B)` is also additive.
* `mul_card_le_repSum` — the trivial bound `t · #A ≤ ∑_{i≤t} #(A ·_i B)`, valid whenever
  `t ≤ #B`; it is proved by choosing `t` elements of `B` and counting the translates `A · b`.
* `pollardWeak_of_inter_coset` — combining the two, the weak Pollard bound for a single coset
  piece of `A` upgrades to the weak Pollard bound for `A`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **The trivial lower bound.**  If `#B ≥ t` then `∑_{i=1}^t #(A ·_i B) ≥ t · #A`. -/
theorem mul_card_le_repSum (A B : Finset G) (t : ℕ) (ht : t ≤ B.card) :
    t * A.card ≤ repSum A B t := by
  classical
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq ht
  have hexp : t * A.card = ∑ c : G, (S.filter (fun b => c ∈ b • A)).card := by
    have h1 : ∑ c : G, (S.filter (fun b => c ∈ b • A)).card
        = ∑ b ∈ S, (b • A).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← Finset.card_filter]
      congr 1
      ext c
      simp
    rw [h1, Finset.sum_congr rfl (fun b _ => Finset.card_smul_finset b A), Finset.sum_const,
      hScard, smul_eq_mul]
  rw [hexp, repSum_eq_sum_min]
  refine Finset.sum_le_sum (fun c _ => ?_)
  refine le_min ?_ ?_
  · rw [rep]
    apply Finset.card_le_card_of_injOn (fun b => (c * b⁻¹, b))
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hb ⊢
      obtain ⟨hbS, hbA⟩ := hb
      rw [Finset.mem_smul_finset] at hbA
      obtain ⟨a, ha, hab⟩ := hbA
      simp only [smul_eq_mul] at hab
      refine ⟨⟨?_, hSB hbS⟩, by rw [inv_mul_cancel_right]⟩
      have : c * b⁻¹ = a := by rw [← hab, mul_comm b a, mul_inv_cancel_right]
      rw [this]
      exact ha
    · intro u _ v _ h
      simpa using congrArg Prod.snd h
  · calc (S.filter (fun b => c ∈ b • A)).card ≤ S.card := Finset.card_filter_le _ _
      _ = t := hScard

/-! ### Decomposition along the cosets of a subgroup -/

variable {K : Finset G}

omit [Fintype G] in
/-- A finite set is the disjoint union of its intersections with a family of cosets covering it. -/
theorem card_eq_sum_inter_cosets (hK : IsSubgroupFinset K) (S : Finset (Finset G)) (X : Finset G)
    (hcov : ∀ x ∈ X, x • K ∈ S) (hS : ∀ u ∈ S, ∃ a : G, u = a • K) :
    X.card = ∑ u ∈ S, (X ∩ u).card := by
  classical
  have hcover : X = S.biUnion (fun u => X ∩ u) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hx; exact ⟨x • K, hcov x hx, hx, hK.mem_smul_self x⟩
    · rintro ⟨u, _, hx, _⟩; exact hx
  have hdisj : (S : Set (Finset G)).PairwiseDisjoint (fun u => X ∩ u) := by
    intro u hu v hv huv
    obtain ⟨a, rfl⟩ := hS u hu
    obtain ⟨b, rfl⟩ := hS v hv
    exact Finset.disjoint_left.2 fun z hz hz' =>
      huv (hK.smul_coset_eq_of_mem (Finset.mem_inter.1 hz).2 (Finset.mem_inter.1 hz').2)
  have hcb : (S.biUnion (fun u => X ∩ u)).card = ∑ u ∈ S, (X ∩ u).card :=
    Finset.card_biUnion hdisj
  rw [← hcb]
  exact congrArg Finset.card hcover

omit [Fintype G] in
/-- The representation function splits over a coset decomposition of its first argument. -/
theorem rep_eq_sum_inter_cosets (hK : IsSubgroupFinset K) (A B : Finset G) (c : G) :
    rep A B c = ∑ u ∈ A.image (fun a : G => a • K), rep (A ∩ u) B c := by
  classical
  rw [rep_eq_card_inter]
  have hcov : ∀ x ∈ A ∩ (c • B⁻¹), x • K ∈ A.image (fun a : G => a • K) := by
    intro x hx
    exact Finset.mem_image.2 ⟨x, (Finset.mem_inter.1 hx).1, rfl⟩
  have hS : ∀ u ∈ A.image (fun a : G => a • K), ∃ a : G, u = a • K := by
    intro u hu
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨a, rfl⟩
  rw [card_eq_sum_inter_cosets hK _ _ hcov hS]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [rep_eq_card_inter]
  congr 1
  ext z
  simp only [Finset.mem_inter]
  tauto

omit [Fintype G] in
/-- If `B` lies in a single coset of `K`, the pieces `(A ∩ u) · B` lie in pairwise distinct
cosets of `K`, so at most one piece contributes to any given representation count. -/
theorem inter_coset_unique_of_rep (hK : IsSubgroupFinset K) {A B : Finset G} {b₀ : G}
    (hB : B ⊆ b₀ • K) {c : G} {a a' : G}
    (h : rep (A ∩ a • K) B c ≠ 0) (h' : rep (A ∩ a' • K) B c ≠ 0) :
    a • K = a' • K := by
  classical
  have hmem : ∀ x : G, rep (A ∩ x • K) B c ≠ 0 → c ∈ (x * b₀) • K := by
    intro x hx
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      mem_mul.1 ((rep_pos_iff_mem_mul _ _ c).1 (Nat.pos_of_ne_zero hx))
    obtain ⟨k, hk, hpk⟩ := Finset.mem_smul_finset.1 (Finset.mem_inter.1 hp).2
    obtain ⟨k', hk', hqk⟩ := Finset.mem_smul_finset.1 (hB hq)
    refine Finset.mem_smul_finset.2 ⟨k * k', hK.mul_mem hk hk', ?_⟩
    simp only [smul_eq_mul] at hpk hqk ⊢
    rw [← hpq, ← hpk, ← hqk, mul_mul_mul_comm]
  have h1 := hmem a h
  have h2 := hmem a' h'
  have : (a * b₀) • K = (a' * b₀) • K := hK.smul_coset_eq_of_mem h1 h2
  have hb : b₀ • (a • K) = b₀ • (a' • K) := by
    rw [← mul_smul, ← mul_smul, mul_comm b₀ a, mul_comm b₀ a']
    exact this
  calc a • K = b₀⁻¹ • (b₀ • (a • K)) := (inv_smul_smul b₀ _).symm
    _ = b₀⁻¹ • (b₀ • (a' • K)) := by rw [hb]
    _ = a' • K := inv_smul_smul b₀ _

/-- If `B` lies in a single coset of `K`, then `∑_{i≤t} #(A ·_i B)` is additive over the coset
decomposition of `A`. -/
theorem repSum_eq_sum_inter_cosets (hK : IsSubgroupFinset K) {A B : Finset G} {b₀ : G}
    (hB : B ⊆ b₀ • K) (t : ℕ) :
    repSum A B t = ∑ u ∈ A.image (fun a : G => a • K), repSum (A ∩ u) B t := by
  classical
  have key : ∀ c : G, min (rep A B c) t
      = ∑ u ∈ A.image (fun a : G => a • K), min (rep (A ∩ u) B c) t := by
    intro c
    by_cases hc : rep A B c = 0
    · have hzero : ∀ u ∈ A.image (fun a : G => a • K), min (rep (A ∩ u) B c) t = 0 := by
        intro u _
        have := rep_mono (Finset.inter_subset_left : A ∩ u ⊆ A) (le_refl B) c
        omega
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, hc, Nat.zero_min]
    · obtain ⟨a, ha, b, hb, hab⟩ := mem_mul.1 ((rep_pos_iff_mem_mul _ _ c).1
        (Nat.pos_of_ne_zero hc))
      have hu₀ : a • K ∈ A.image (fun a : G => a • K) := Finset.mem_image.2 ⟨a, ha, rfl⟩
      have hne : rep (A ∩ a • K) B c ≠ 0 := by
        have hcm : c ∈ (A ∩ a • K) * B :=
          mem_mul.2 ⟨a, Finset.mem_inter.2 ⟨ha, hK.mem_smul_self a⟩, b, hb, hab⟩
        exact ((rep_pos_iff_mem_mul _ _ c).2 hcm).ne'
      have hsingle : ∀ u ∈ A.image (fun a : G => a • K), u ≠ a • K → rep (A ∩ u) B c = 0 := by
        intro u hu hune
        by_contra hcon
        obtain ⟨a', _, rfl⟩ := Finset.mem_image.1 hu
        exact hune (inter_coset_unique_of_rep hK hB hcon hne)
      have hsum1 : ∑ u ∈ A.image (fun a : G => a • K), min (rep (A ∩ u) B c) t
          = min (rep (A ∩ a • K) B c) t := by
        refine Finset.sum_eq_single_of_mem _ hu₀ (fun u hu hune => ?_)
        rw [hsingle u hu hune, Nat.zero_min]
      have hsum2 : rep A B c = rep (A ∩ a • K) B c := by
        rw [rep_eq_sum_inter_cosets hK A B c]
        refine Finset.sum_eq_single_of_mem _ hu₀ (fun u hu hune => hsingle u hu hune)
      rw [hsum1, hsum2]
  rw [repSum_eq_sum_min, Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ => (repSum_eq_sum_min _ _ _).symm)

/-- **Transfer of the weak Pollard bound along a coset decomposition.**
If `B` lies in a single coset of `K` and the weak bound holds for one coset piece of `A`, then
it holds for `A`: the remaining pieces are handled by the trivial bound `t · #(A ∩ u)`. -/
theorem pollardWeak_of_inter_coset (hK : IsSubgroupFinset K) {A B : Finset G} {b₀ : G}
    (hB : B ⊆ b₀ • K) {t : ℕ} (ht : t ≤ B.card) {u₀ : Finset G}
    (hu₀ : u₀ ∈ A.image (fun a : G => a • K)) (h : PollardWeak (A ∩ u₀) B t) :
    PollardWeak A B t := by
  classical
  have hcard : A.card = ∑ u ∈ A.image (fun a : G => a • K), (A ∩ u).card :=
    card_eq_sum_inter_cosets hK _ A (fun x hx => Finset.mem_image.2 ⟨x, hx, rfl⟩)
      (fun u hu => by obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hu; exact ⟨a, rfl⟩)
  have hrep : repSum A B t = ∑ u ∈ A.image (fun a : G => a • K), repSum (A ∩ u) B t :=
    repSum_eq_sum_inter_cosets hK hB t
  have h1 : t * (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, (A ∩ u).card)
      ≤ ∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, repSum (A ∩ u) B t := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun u _ => mul_card_le_repSum _ _ t ht)
  have h2 : (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, (A ∩ u).card) + (A ∩ u₀).card
      = A.card := by
    rw [hcard]; exact Finset.sum_erase_add _ _ hu₀
  have h3 : (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, repSum (A ∩ u) B t)
      + repSum (A ∩ u₀) B t = repSum A B t := by
    rw [hrep]; exact Finset.sum_erase_add _ _ hu₀
  rw [PollardWeak] at h ⊢
  rw [← h2, ← h3, Nat.mul_add]
  calc t * (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, (A ∩ u).card)
        + t * (A ∩ u₀).card + t * B.card + 1
      = t * (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, (A ∩ u).card)
        + (t * (A ∩ u₀).card + t * B.card + 1) := by ring
    _ ≤ (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, repSum (A ∩ u) B t)
        + (repSum (A ∩ u₀) B t + 2 * t ^ 2) := Nat.add_le_add h1 h
    _ = (∑ u ∈ (A.image (fun a : G => a • K)).erase u₀, repSum (A ∩ u) B t)
        + repSum (A ∩ u₀) B t + 2 * t ^ 2 := by ring

end GaloisForLFunctions.HTGeometry.AddComb
