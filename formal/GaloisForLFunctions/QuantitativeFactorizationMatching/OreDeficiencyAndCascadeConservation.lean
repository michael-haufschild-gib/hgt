import Mathlib.Combinatorics.Hall.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
# König–Ore Deficiency Decomposition and Layer-Cascade Conservation

Foundational combinatorial identities for opposite-parity matchings of squarefree integers:

1. **Exact cancellation and König–Ore deficiency split**: On any finite set `S ⊆ ℕ`, every
   opposite-parity matching `M` along an edge relation `R ⊆ S₊ × S₋` cancels identically in
   `∑_{n ∈ S} μ(n)`, and the minimum unmatched population across all `R`-matchings equals
   `|∑_{n ∈ S} μ(n)| + 2 · hallExcess R S`, separating the intrinsic Möbius discrepancy from
   the graph-structural Hall bottleneck. Every `R`-isolated subset `I₀ ⊆ squarefreeOf S` lies
   in `M.unmatchedSet` for every matching `M`.
2. **Universal telescoping conservation for adjacent factor-layer cascades**: Any sequence of
   injections `φ_k : U_k ↪ Q_{k+1}(S)` (`U₁ = Q₁(S)`, `U_{k+1} = Q_{k+1}(S) \ φ_k(U_k)`) leaves
   unconsumed remainder `(U_{K+1}).card = (-1)^{K+1} ∑_{n ∈ S, 1 ≤ ω(n) ≤ K+1} μ(n)`,
   independently of `φ₁, …, φ_K`.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Squarefree parity and factor-count layers -/

/-- The squarefree integers in `S`. -/
def squarefreeOf (S : Finset ℕ) : Finset ℕ := by
  classical exact S.filter Squarefree

/-- Positive-Möbius integers (`μ(n) = 1`) in `S`. -/
def posParity (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n => μ n = 1

/-- Negative-Möbius integers (`μ(n) = -1`) in `S`. -/
def negParity (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n => μ n = -1

/-- The `k`-prime squarefree layer `{n ∈ S : Squarefree n ∧ ω(n) = k}`. -/
def factorLayer (S : Finset ℕ) (k : ℕ) : Finset ℕ := by
  classical exact S.filter fun n => Squarefree n ∧ n.primeFactors.card = k

theorem moebius_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    μ (∏ p ∈ T, p) = (-1 : ℤ) ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hpT ih =>
    have hp : p.Prime := hT p (mem_insert_self p T)
    have hT' : ∀ q ∈ T, q.Prime := fun q hq => hT q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ T, q) :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp (hT' q hq)).mpr fun h => hpT (h ▸ hq)
    rw [prod_insert hpT, card_insert_of_notMem hpT, pow_succ',
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ih hT']

/-- On squarefree `n`, `μ(n) = (-1)^{ω(n)}`. -/
theorem moebius_eq_neg_one_pow_omega {n : ℕ} (hn : Squarefree n) :
    μ n = (-1 : ℤ) ^ n.primeFactors.card := by
  have hprod := Nat.prod_primeFactors_of_squarefree hn
  conv_lhs => rw [← hprod]
  exact moebius_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp

theorem moebius_eq_one_or_neg_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    μ n = 1 ∨ μ n = -1 := by
  rw [moebius_eq_neg_one_pow_omega hn]
  rcases Nat.even_or_odd n.primeFactors.card with h | h
  · exact Or.inl (h.neg_one_pow)
  · exact Or.inr (h.neg_one_pow)

theorem squarefree_iff_moebius_ne_zero {n : ℕ} : Squarefree n ↔ μ n ≠ 0 := by
  refine ⟨fun h h0 => ?_, fun h => ?_⟩
  · rcases moebius_eq_one_or_neg_one_of_squarefree h with h1 | h1 <;> omega
  · by_contra hns
    exact h (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns)

theorem disjoint_posParity_negParity (S : Finset ℕ) :
    Disjoint (posParity S) (negParity S) := by
  rw [disjoint_left]
  intro n hp hn
  have h1 := (mem_filter.mp hp).2
  have h2 := (mem_filter.mp hn).2
  omega

theorem squarefreeOf_eq_posParity_union_negParity (S : Finset ℕ) :
    squarefreeOf S = posParity S ∪ negParity S := by
  ext n
  simp only [squarefreeOf, posParity, negParity, mem_union, mem_filter]
  constructor
  · rintro ⟨hnS, hsq⟩
    rcases moebius_eq_one_or_neg_one_of_squarefree hsq with h | h
    · exact Or.inl ⟨hnS, h⟩
    · exact Or.inr ⟨hnS, h⟩
  · rintro (⟨hnS, h⟩ | ⟨hnS, h⟩) <;>
      exact ⟨hnS, squarefree_iff_moebius_ne_zero.mpr (by omega)⟩

theorem card_squarefreeOf (S : Finset ℕ) :
    (squarefreeOf S).card = (posParity S).card + (negParity S).card := by
  rw [squarefreeOf_eq_posParity_union_negParity, card_union_of_disjoint (disjoint_posParity_negParity S)]

/-- The Möbius sum over `S` equals `#S₊ - #S₋`. -/
theorem sum_moebius_eq_card_pos_sub_neg (S : Finset ℕ) :
    ∑ n ∈ S, μ n = ((posParity S).card : ℤ) - ((negParity S).card : ℤ) := by
  have hsplit : ∑ n ∈ S, μ n = ∑ n ∈ squarefreeOf S, μ n := by
    classical
    refine (sum_subset (filter_subset _ S) fun n hnS hnot => ?_).symm
    have hns : ¬ Squarefree n := fun h => hnot (mem_filter.mpr ⟨hnS, h⟩)
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
  rw [hsplit, squarefreeOf_eq_posParity_union_negParity,
    sum_union (disjoint_posParity_negParity S)]
  have hpos : ∑ n ∈ posParity S, μ n = ((posParity S).card : ℤ) := by
    calc ∑ n ∈ posParity S, μ n = ∑ _n ∈ posParity S, (1 : ℤ) :=
          sum_congr rfl fun n hn => (mem_filter.mp hn).2
      _ = ((posParity S).card : ℤ) := by simp
  have hneg : ∑ n ∈ negParity S, μ n = -((negParity S).card : ℤ) := by
    calc ∑ n ∈ negParity S, μ n = ∑ _n ∈ negParity S, (-1 : ℤ) :=
          sum_congr rfl fun n hn => (mem_filter.mp hn).2
      _ = -((negParity S).card : ℤ) := by simp
  omega

/-! ### 2. Disjoint opposite-parity matchings and unmatched bounds -/

/-- A disjoint opposite-parity matching on `S` along an allowed relation `R ⊆ S₊ × S₋`. -/
structure OppositeParityMatching (R : ℕ → ℕ → Prop) (S : Finset ℕ) where
  sources : Finset ℕ
  partner : ℕ → ℕ
  sources_subset : sources ⊆ posParity S
  injOn : Set.InjOn partner ↑sources
  partner_mem : ∀ a ∈ sources, partner a ∈ negParity S
  adj : ∀ a ∈ sources, R a (partner a)

namespace OppositeParityMatching

variable {R : ℕ → ℕ → Prop} {S : Finset ℕ} (M : OppositeParityMatching R S)

/-- Targets consumed by `M` in `negParity S`. -/
def targets : Finset ℕ := M.sources.image M.partner

/-- All squarefree integers of `S` covered by `M`. -/
def matchedSet : Finset ℕ := M.sources ∪ M.targets

/-- Squarefree integers of `S` left unmatched by `M`. -/
def unmatchedSet : Finset ℕ := squarefreeOf S \ M.matchedSet

theorem targets_subset : M.targets ⊆ negParity S := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  exact M.partner_mem a ha

theorem card_targets : M.targets.card = M.sources.card :=
  card_image_of_injOn M.injOn

theorem disjoint_sources_targets : Disjoint M.sources M.targets :=
  Disjoint.mono M.sources_subset M.targets_subset (disjoint_posParity_negParity S)

theorem matchedSet_subset : M.matchedSet ⊆ squarefreeOf S := by
  rw [squarefreeOf_eq_posParity_union_negParity]
  exact union_subset_union M.sources_subset M.targets_subset

theorem card_matchedSet : M.matchedSet.card = 2 * M.sources.card := by
  rw [matchedSet, card_union_of_disjoint M.disjoint_sources_targets, M.card_targets, two_mul]

theorem unmatchedSet_eq_union_sdiff :
    M.unmatchedSet = (posParity S \ M.sources) ∪ (negParity S \ M.targets) := by
  ext n
  simp only [unmatchedSet, matchedSet, squarefreeOf_eq_posParity_union_negParity,
    mem_sdiff, mem_union]
  constructor
  · rintro ⟨hp | hn, hnot⟩
    · exact Or.inl ⟨hp, fun hs => hnot (Or.inl hs)⟩
    · exact Or.inr ⟨hn, fun ht => hnot (Or.inr ht)⟩
  · rintro (⟨hp, hns⟩ | ⟨hn, hnt⟩)
    · refine ⟨Or.inl hp, ?_⟩
      rintro (hs | ht)
      · exact hns hs
      · exact disjoint_left.mp (disjoint_posParity_negParity S) hp (M.targets_subset ht)
    · refine ⟨Or.inr hn, ?_⟩
      rintro (hs | ht)
      · exact disjoint_right.mp (disjoint_posParity_negParity S) hn (M.sources_subset hs)
      · exact hnt ht

theorem card_unmatchedSet_eq :
    M.unmatchedSet.card =
      (posParity S \ M.sources).card + (negParity S \ M.targets).card := by
  rw [M.unmatchedSet_eq_union_sdiff, card_union_of_disjoint]
  exact Disjoint.mono sdiff_subset sdiff_subset (disjoint_posParity_negParity S)

theorem card_unmatchedSet_eq_sub :
    M.unmatchedSet.card = (squarefreeOf S).card - 2 * M.sources.card := by
  have hs := card_sdiff_add_card_eq_card M.matchedSet_subset
  have hm := M.card_matchedSet
  rw [unmatchedSet]
  omega

/-- Matched pairs cancel identically in the unweighted Möbius sum. -/
theorem sum_moebius_matchedSet : ∑ n ∈ M.matchedSet, μ n = 0 := by
  rw [matchedSet, sum_union M.disjoint_sources_targets]
  have h1 : ∑ a ∈ M.sources, μ a = (M.sources.card : ℤ) := by
    calc ∑ a ∈ M.sources, μ a = ∑ _a ∈ M.sources, (1 : ℤ) :=
          sum_congr rfl fun a ha => (mem_filter.mp (M.sources_subset ha)).2
      _ = (M.sources.card : ℤ) := by simp
  have h2 : ∑ b ∈ M.targets, μ b = -(M.sources.card : ℤ) := by
    calc ∑ b ∈ M.targets, μ b = ∑ _b ∈ M.targets, (-1 : ℤ) :=
          sum_congr rfl fun b hb => (mem_filter.mp (M.targets_subset hb)).2
      _ = -(M.targets.card : ℤ) := by simp
      _ = -(M.sources.card : ℤ) := by rw [M.card_targets]
  omega

/-- The unweighted Möbius sum over `S` depends only on the unmatched remainder. -/
theorem sum_moebius_eq_unmatched :
    ∑ n ∈ S, μ n =
      ((posParity S \ M.sources).card : ℤ) - ((negParity S \ M.targets).card : ℤ) := by
  have hs := card_sdiff_add_card_eq_card M.sources_subset
  have ht := card_sdiff_add_card_eq_card M.targets_subset
  have hct := M.card_targets
  rw [sum_moebius_eq_card_pos_sub_neg]
  omega

/-- The absolute Möbius sum is bounded above by the unmatched population. -/
theorem abs_sum_moebius_le_unmatched :
    |∑ n ∈ S, μ n| ≤ (M.unmatchedSet.card : ℤ) := by
  rw [M.sum_moebius_eq_unmatched, M.card_unmatchedSet_eq]
  have h1 : (0 : ℤ) ≤ (posParity S \ M.sources).card := Nat.cast_nonneg _
  have h2 : (0 : ℤ) ≤ (negParity S \ M.targets).card := Nat.cast_nonneg _
  rw [Nat.cast_add]
  exact abs_le.mpr ⟨by omega, by omega⟩

end OppositeParityMatching

/-! ### 3. König–Ore bipartite deficiency decomposition and isolated-source lower bound -/

/-- Neighborhood of `U ⊆ S₊` inside `S₋` under `R`. -/
noncomputable def bipNeighbors (R : ℕ → ℕ → Prop) (S U : Finset ℕ) : Finset ℕ := by
  classical exact U.biUnion fun a => (negParity S).filter (R a ·)

theorem bipNeighbors_subset (R : ℕ → ℕ → Prop) (S U : Finset ℕ) :
    bipNeighbors R S U ⊆ negParity S := by
  classical
  intro b hb
  unfold bipNeighbors at hb
  obtain ⟨a, _, hb'⟩ := mem_biUnion.mp hb
  exact (mem_filter.mp hb').1

@[simp]
theorem bipNeighbors_empty (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    bipNeighbors R S ∅ = ∅ := by
  simp [bipNeighbors]

/-- Hall deficiency `max_{U ⊆ S₊} (#U - #N_R(U))`. -/
noncomputable def hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ) : ℕ :=
  ((posParity S).powerset.image fun U => U.card - (bipNeighbors R S U).card).max'
    (image_nonempty.mpr (powerset_nonempty (posParity S)))

theorem sub_card_bipNeighbors_le_hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ)
    {U : Finset ℕ} (hU : U ⊆ posParity S) :
    U.card - (bipNeighbors R S U).card ≤ hallDeficiency R S :=
  le_max' _ _ (mem_image_of_mem (fun V => V.card - (bipNeighbors R S V).card) (mem_powerset.mpr hU))

theorem card_le_card_bipNeighbors_add_hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ)
    {U : Finset ℕ} (hU : U ⊆ posParity S) :
    U.card ≤ (bipNeighbors R S U).card + hallDeficiency R S := by
  have := sub_card_bipNeighbors_le_hallDeficiency R S hU
  omega

theorem exists_subset_attaining_hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    ∃ U ⊆ posParity S, U.card - (bipNeighbors R S U).card = hallDeficiency R S := by
  have hmem := max'_mem
    ((posParity S).powerset.image fun U => U.card - (bipNeighbors R S U).card)
    (image_nonempty.mpr (powerset_nonempty (posParity S)))
  obtain ⟨U, hUp, hval⟩ := mem_image.mp hmem
  exact ⟨U, mem_powerset.mp hUp, hval⟩

theorem hallDeficiency_le_card_posParity (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    hallDeficiency R S ≤ (posParity S).card := by
  obtain ⟨U, hU, hval⟩ := exists_subset_attaining_hallDeficiency R S
  have hle := card_le_card hU
  omega

theorem card_pos_sub_neg_le_hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    (posParity S).card - (negParity S).card ≤ hallDeficiency R S := by
  have h1 := sub_card_bipNeighbors_le_hallDeficiency R S (Subset.refl (posParity S))
  have h2 := card_le_card (bipNeighbors_subset R S (posParity S))
  omega

/-- Every `R`-matching has size at most `#S₊ - hallDeficiency R S`. -/
theorem OppositeParityMatching.sources_card_le_sub_hallDeficiency
    {R : ℕ → ℕ → Prop} {S : Finset ℕ} (M : OppositeParityMatching R S) :
    M.sources.card ≤ (posParity S).card - hallDeficiency R S := by
  rcases Nat.eq_zero_or_pos (hallDeficiency R S) with hd0 | hdpos
  · rw [hd0, Nat.sub_zero]
    exact card_le_card M.sources_subset
  · classical
    obtain ⟨U, hU, hdef⟩ := exists_subset_attaining_hallDeficiency R S
    have himg : (M.sources ∩ U).image M.partner ⊆ bipNeighbors R S U := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      obtain ⟨haM, haU⟩ := mem_inter.mp ha
      unfold bipNeighbors
      exact mem_biUnion.mpr ⟨a, haU, mem_filter.mpr ⟨M.partner_mem a haM, M.adj a haM⟩⟩
    have hcap : (M.sources ∩ U).card ≤ (bipNeighbors R S U).card := by
      rw [← card_image_of_injOn (M.injOn.mono (coe_subset.mpr inter_subset_left))]
      exact card_le_card himg
    have hcomp : (M.sources \ U).card ≤ (posParity S \ U).card :=
      card_le_card (sdiff_subset_sdiff M.sources_subset (Subset.refl U))
    have hsplitM : (M.sources ∩ U).card + (M.sources \ U).card = M.sources.card :=
      card_inter_add_card_sdiff M.sources U
    have hsplitP : U.card + (posParity S \ U).card = (posParity S).card := by
      rw [add_comm]
      exact card_sdiff_add_card_eq_card hU
    have hNU : (bipNeighbors R S U).card + hallDeficiency R S = U.card := by omega
    omega

/-- **Ore's deficiency attainment theorem**: there exists an `R`-matching of exact cardinality
`#S₊ - hallDeficiency R S`. -/
theorem exists_matching_card_eq_sub_hallDeficiency (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    ∃ M : OppositeParityMatching R S,
      M.sources.card = (posParity S).card - hallDeficiency R S := by
  classical
  set d := hallDeficiency R S
  let t : {a // a ∈ posParity S} → Finset (ℕ ⊕ Fin d) := fun a =>
    (bipNeighbors R S {a.1}).map Function.Embedding.inl ∪
      Finset.univ.map Function.Embedding.inr
  have hall : ∀ s : Finset {a // a ∈ posParity S}, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · let U := s.image Subtype.val
      have hU : U ⊆ posParity S := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := mem_image.mp hx
        exact y.2
      have hcardU : U.card = s.card := card_image_of_injective s Subtype.val_injective
      have hsubL : (bipNeighbors R S U).map Function.Embedding.inl ⊆ s.biUnion t := by
        intro z hz
        obtain ⟨b, hb, rfl⟩ := mem_map.mp hz
        unfold bipNeighbors at hb
        obtain ⟨x, hxU, hbx⟩ := mem_biUnion.mp hb
        obtain ⟨y, hys, rfl⟩ := mem_image.mp hxU
        refine mem_biUnion.mpr ⟨y, hys, mem_union.mpr (Or.inl (mem_map.mpr ⟨b, ?_, rfl⟩))⟩
        unfold bipNeighbors
        exact mem_biUnion.mpr ⟨y.1, mem_singleton_self _, hbx⟩
      have hsubR : (Finset.univ : Finset (Fin d)).map Function.Embedding.inr ⊆ s.biUnion t := by
        obtain ⟨y₀, hy₀⟩ := hne
        intro z hz
        exact mem_biUnion.mpr ⟨y₀, hy₀, mem_union.mpr (Or.inr hz)⟩
      have hdisjLR : Disjoint ((bipNeighbors R S U).map Function.Embedding.inl)
          ((Finset.univ : Finset (Fin d)).map Function.Embedding.inr) := by
        rw [disjoint_left]
        intro z hzL hzR
        obtain ⟨b, _, rfl⟩ := mem_map.mp hzL
        obtain ⟨j, _, hj⟩ := mem_map.mp hzR
        exact Sum.inl_ne_inr hj.symm
      have hsum_le : (bipNeighbors R S U).card + d ≤ (s.biUnion t).card := by
        calc (bipNeighbors R S U).card + d
            = ((bipNeighbors R S U).map Function.Embedding.inl ∪
                (Finset.univ : Finset (Fin d)).map Function.Embedding.inr).card := by
              rw [card_union_of_disjoint hdisjLR, card_map, card_map, card_univ, Fintype.card_fin]
          _ ≤ (s.biUnion t).card := card_le_card (union_subset hsubL hsubR)
      have hdef := card_le_card_bipNeighbors_add_hallDeficiency R S hU
      omega
  obtain ⟨g, hginj, hgmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  let good : Finset {a // a ∈ posParity S} :=
    Finset.univ.filter fun a => (g a).isLeft
  let bad : Finset {a // a ∈ posParity S} :=
    Finset.univ.filter fun a => ¬ (g a).isLeft
  have hgb_sum : good.card + bad.card = (posParity S).card := by
    have := card_filter_add_card_filter_not (s := (Finset.univ : Finset {a // a ∈ posParity S}))
      (p := fun a => (g a).isLeft)
    simpa [good, bad] using this
  have hbad_inr : ∀ x : {a // a ∈ bad}, ∃ j : Fin d, g x.1 = Sum.inr j := by
    intro x
    cases hgx : g x.1 with
    | inl b => exact False.elim ((mem_filter.mp x.2).2 (by simp [hgx]))
    | inr j => exact ⟨j, rfl⟩
  let uninr : {a // a ∈ bad} → Fin d := fun x => (hbad_inr x).choose
  have huninr_inj : Function.Injective uninr := by
    intro x y hxy
    have hx := (hbad_inr x).choose_spec
    have hy := (hbad_inr y).choose_spec
    change (hbad_inr x).choose = (hbad_inr y).choose at hxy
    rw [hxy] at hx
    exact Subtype.ext (hginj (hx.trans hy.symm))
  have hbad_le : bad.card ≤ d := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective uninr huninr_inj
  let sources : Finset ℕ := good.image Subtype.val
  have hsources_card_ge : (posParity S).card - d ≤ sources.card := by
    rw [card_image_of_injective good Subtype.val_injective]
    omega
  let partner : ℕ → ℕ := fun n =>
    if hn : n ∈ posParity S then
      match g ⟨n, hn⟩ with
      | Sum.inl b => b
      | Sum.inr _ => 0
    else 0
  have hsources_sub : sources ⊆ posParity S := by
    intro n hn
    obtain ⟨a, _, rfl⟩ := mem_image.mp hn
    exact a.2
  have hpartner_spec : ∀ n (hn : n ∈ sources), g ⟨n, hsources_sub hn⟩ = Sum.inl (partner n) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    have hleft : (g a).isLeft := (mem_filter.mp ha).2
    cases hga : g a with
    | inr j => simp [hga] at hleft
    | inl b =>
      dsimp only [partner]
      rw [dif_pos a.2]
      simp [hga]
  have hmem_adj : ∀ n ∈ sources, partner n ∈ negParity S ∧ R n (partner n) := by
    intro n hn
    have hgn := hpartner_spec n hn
    have htmem := hgmem ⟨n, hsources_sub hn⟩
    rw [hgn] at htmem
    rcases mem_union.mp htmem with hL | hR
    · obtain ⟨b, hb, hbeq⟩ := mem_map.mp hL
      cases hbeq
      unfold bipNeighbors at hb
      obtain ⟨x, hx, hbx⟩ := mem_biUnion.mp hb
      rw [mem_singleton.mp hx] at hbx
      exact mem_filter.mp hbx
    · obtain ⟨j, _, hj⟩ := mem_map.mp hR
      exact False.elim (Sum.inr_ne_inl hj)
  have hinj : Set.InjOn partner ↑sources := by
    intro x hx y hy hxy
    have hx' : x ∈ sources := hx
    have hy' : y ∈ sources := hy
    have hgx := hpartner_spec x hx'
    have hgy := hpartner_spec y hy'
    rw [hxy] at hgx
    exact congrArg Subtype.val (hginj (hgx.trans hgy.symm))
  let M : OppositeParityMatching R S :=
    { sources := sources
      partner := partner
      sources_subset := hsources_sub
      injOn := hinj
      partner_mem := fun n hn => (hmem_adj n hn).1
      adj := fun n hn => (hmem_adj n hn).2 }
  exact ⟨M, le_antisymm M.sources_card_le_sub_hallDeficiency hsources_card_ge⟩

/-- Graph-structural Hall excess beyond the global Möbius sum `max(0, ∑_{n ∈ S} μ(n))`. -/
noncomputable def hallExcessZ (R : ℕ → ℕ → Prop) (S : Finset ℕ) : ℤ :=
  (hallDeficiency R S : ℤ) - max 0 (∑ n ∈ S, μ n)

theorem hallExcessZ_nonneg (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    0 ≤ hallExcessZ R S := by
  unfold hallExcessZ
  have h1 := card_pos_sub_neg_le_hallDeficiency R S
  rw [sum_moebius_eq_card_pos_sub_neg]
  omega

/-- **Exact König–Ore decomposition of the unmatched population**: every `R`-matching leaves at
least `|∑_{n ∈ S} μ(n)| + 2 · hallExcessZ R S` unmatched squarefree integers, and an optimal
`R`-matching attains this bound with equality. -/
theorem minUnmatched_ore_decomposition (R : ℕ → ℕ → Prop) (S : Finset ℕ) :
    (∀ M : OppositeParityMatching R S,
      |∑ n ∈ S, μ n| + 2 * hallExcessZ R S ≤ (M.unmatchedSet.card : ℤ)) ∧
    (∃ M : OppositeParityMatching R S,
      (M.unmatchedSet.card : ℤ) = |∑ n ∈ S, μ n| + 2 * hallExcessZ R S) := by
  have hident : (((squarefreeOf S).card - 2 * ((posParity S).card - hallDeficiency R S) : ℕ) : ℤ) =
      |∑ n ∈ S, μ n| + 2 * hallExcessZ R S := by
    have hdle := hallDeficiency_le_card_posParity R S
    have hdiff := card_pos_sub_neg_le_hallDeficiency R S
    have hsq := card_squarefreeOf S
    rw [sum_moebius_eq_card_pos_sub_neg, hallExcessZ, sum_moebius_eq_card_pos_sub_neg]
    rcases le_total ((posParity S).card : ℤ) ((negParity S).card : ℤ) with hle | hle
    · have habs : |((posParity S).card : ℤ) - ((negParity S).card : ℤ)| =
          ((negParity S).card : ℤ) - ((posParity S).card : ℤ) := by
        rw [abs_of_nonpos (by omega)]; ring
      have hmax : max (0 : ℤ) (((posParity S).card : ℤ) - ((negParity S).card : ℤ)) = 0 :=
        max_eq_left (by omega)
      rw [habs, hmax]
      omega
    · have habs : |((posParity S).card : ℤ) - ((negParity S).card : ℤ)| =
          ((posParity S).card : ℤ) - ((negParity S).card : ℤ) :=
        abs_of_nonneg (by omega)
      have hmax : max (0 : ℤ) (((posParity S).card : ℤ) - ((negParity S).card : ℤ)) =
          ((posParity S).card : ℤ) - ((negParity S).card : ℤ) :=
        max_eq_right (by omega)
      rw [habs, hmax]
      omega
  constructor
  · intro M
    have hM := M.sources_card_le_sub_hallDeficiency
    have hunm := M.card_unmatchedSet_eq_sub
    have h2le : 2 * M.sources.card ≤ (squarefreeOf S).card := by
      rw [← M.card_matchedSet]
      exact card_le_card M.matchedSet_subset
    have hge : (squarefreeOf S).card - 2 * ((posParity S).card - hallDeficiency R S) ≤
        M.unmatchedSet.card := by omega
    calc |∑ n ∈ S, μ n| + 2 * hallExcessZ R S
        = (((squarefreeOf S).card - 2 * ((posParity S).card - hallDeficiency R S) : ℕ) : ℤ) :=
          hident.symm
      _ ≤ (M.unmatchedSet.card : ℤ) := by exact_mod_cast hge
  · obtain ⟨M, hM⟩ := exists_matching_card_eq_sub_hallDeficiency R S
    refine ⟨M, ?_⟩
    rw [M.card_unmatchedSet_eq_sub, hM, hident]

/-- Squarefree elements of `S` with zero admissible `R`-neighbors in `S`. -/
noncomputable def isolatedVertices (R : ℕ → ℕ → Prop) (S : Finset ℕ) : Finset ℕ := by
  classical
  exact (posParity S).filter (fun a => ∀ b ∈ negParity S, ¬ R a b) ∪
    (negParity S).filter (fun b => ∀ a ∈ posParity S, ¬ R a b)

/-- Every `R`-isolated vertex in `S` is left unmatched by every `R`-matching. -/
theorem isolatedVertices_subset_unmatched {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (M : OppositeParityMatching R S) :
    isolatedVertices R S ⊆ M.unmatchedSet := by
  classical
  intro n hn
  rw [OppositeParityMatching.unmatchedSet, OppositeParityMatching.matchedSet,
    squarefreeOf_eq_posParity_union_negParity, mem_sdiff, mem_union, mem_union]
  rcases mem_union.mp hn with hpos | hneg
  · obtain ⟨hnP, hiso⟩ := mem_filter.mp hpos
    refine ⟨Or.inl hnP, ?_⟩
    rintro (hs | ht)
    · exact hiso (M.partner n) (M.partner_mem n hs) (M.adj n hs)
    · exact disjoint_left.mp (disjoint_posParity_negParity S) hnP (M.targets_subset ht)
  · obtain ⟨hnN, hiso⟩ := mem_filter.mp hneg
    refine ⟨Or.inr hnN, ?_⟩
    rintro (hs | ht)
    · exact disjoint_right.mp (disjoint_posParity_negParity S) hnN (M.sources_subset hs)
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp ht
      exact hiso a (M.sources_subset ha) (M.adj a ha)

theorem card_isolatedVertices_le_unmatched {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (M : OppositeParityMatching R S) :
    (isolatedVertices R S).card ≤ M.unmatchedSet.card :=
  card_le_card (isolatedVertices_subset_unmatched M)

/-! ### 4. Universal telescoping conservation for sequential adjacent-layer cascades -/

/-- Unconsumed layer-`k` sources in a sequential upward cascade `φ_k : U_k → Q_{k+1}(S)`. -/
noncomputable def cascadeUnconsumed (S : Finset ℕ) (φ : ℕ → ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => factorLayer S 1
  | k + 2 => factorLayer S (k + 2) \ (cascadeUnconsumed S φ (k + 1)).image (φ (k + 1))

/-- Validity of a `K`-step sequential upward cascade across layers `1, …, K`. -/
def IsValidLayerCascade (S : Finset ℕ) (φ : ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ K →
    Set.InjOn (φ k) ↑(cascadeUnconsumed S φ k) ∧
      (cascadeUnconsumed S φ k).image (φ k) ⊆ factorLayer S (k + 1)

theorem cascadeUnconsumed_subset_factorLayer (S : Finset ℕ) (φ : ℕ → ℕ → ℕ) :
    ∀ k : ℕ, cascadeUnconsumed S φ k ⊆ factorLayer S k
  | 0 => empty_subset _
  | 1 => Subset.refl _
  | _ + 2 => sdiff_subset

theorem card_cascadeUnconsumed_succ {S : Finset ℕ} {φ : ℕ → ℕ → ℕ} {K k : ℕ}
    (hvalid : IsValidLayerCascade S φ K) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    (cascadeUnconsumed S φ (k + 1)).card =
      (factorLayer S (k + 1)).card - (cascadeUnconsumed S φ k).card := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hinj, hsub⟩ := hvalid (m + 1) hk1 hkK
  change (cascadeUnconsumed S φ (m + 1)).image (φ (m + 1)) ⊆ factorLayer S (m + 2) at hsub
  change (factorLayer S (m + 2) \ (cascadeUnconsumed S φ (m + 1)).image (φ (m + 1))).card =
    (factorLayer S (m + 2)).card - (cascadeUnconsumed S φ (m + 1)).card
  have hsdiff := card_sdiff_add_card_eq_card hsub
  have himg := card_image_of_injOn hinj
  omega

theorem sum_moebius_factorLayer (S : Finset ℕ) (j : ℕ) :
    ∑ n ∈ factorLayer S j, μ n = (-1 : ℤ) ^ j * ((factorLayer S j).card : ℤ) := by
  classical
  have hval : ∀ n ∈ factorLayer S j, μ n = (-1 : ℤ) ^ j := by
    intro n hn
    obtain ⟨_, hsq, hcard⟩ := mem_filter.mp hn
    rw [moebius_eq_neg_one_pow_omega hsq, hcard]
  rw [sum_congr rfl hval, sum_const, nsmul_eq_mul, mul_comm]

theorem filter_omega_Icc_eq_biUnion_factorLayer (S : Finset ℕ) (L : ℕ) :
    S.filter (fun n => Squarefree n ∧ 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ L) =
      (Finset.Icc 1 L).biUnion (factorLayer S) := by
  classical
  ext n
  simp only [mem_filter, mem_biUnion, mem_Icc, factorLayer]
  constructor
  · rintro ⟨hnS, hsq, h1, hL⟩
    exact ⟨n.primeFactors.card, ⟨h1, hL⟩, hnS, hsq, rfl⟩
  · rintro ⟨j, ⟨hj1, hjL⟩, hnS, hsq, rfl⟩
    exact ⟨hnS, hsq, hj1, hjL⟩

theorem disjoint_factorLayer {S : Finset ℕ} {i j : ℕ} (hij : i ≠ j) :
    Disjoint (factorLayer S i) (factorLayer S j) := by
  classical
  rw [disjoint_left]
  intro n hi hj
  exact hij ((mem_filter.mp hi).2.2.symm.trans (mem_filter.mp hj).2.2)

/-- **Universal telescoping law**: in any valid `K`-layer upward cascade, the unconsumed
remainder in layer `K + 1` equals `(-1)^{K+1} ∑_{n ∈ S, 1 ≤ ω(n) ≤ K+1} μ(n)`, independently
of the choice of injections `φ₁, …, φ_K`. -/
theorem intCast_card_cascadeUnconsumed {S : Finset ℕ} {φ : ℕ → ℕ → ℕ} {K : ℕ}
    (hvalid : IsValidLayerCascade S φ K) :
    ∀ k ≤ K,
      ((cascadeUnconsumed S φ (k + 1)).card : ℤ) =
        (-1 : ℤ) ^ (k + 1) *
          ∑ n ∈ S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ k + 1), μ n := by
  have hsq_eq : ∀ L : ℕ,
      ∑ n ∈ S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ L), μ n =
        ∑ j ∈ Finset.Icc 1 L, (-1 : ℤ) ^ j * ((factorLayer S j).card : ℤ) := by
    intro L
    let F := S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ L)
    change ∑ n ∈ F, μ n = _
    classical
    have hsub : S.filter (fun n => Squarefree n ∧ 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ L) ⊆ F :=
      fun n hn => by
        obtain ⟨hnS, _, h1, h2⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨hnS, h1, h2⟩
    rw [← sum_subset hsub (fun n hn hnot => by
      obtain ⟨hnS, h1, h2⟩ := mem_filter.mp hn
      have hns : ¬ Squarefree n := fun hsq => hnot (mem_filter.mpr ⟨hnS, hsq, h1, h2⟩)
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns)]
    rw [filter_omega_Icc_eq_biUnion_factorLayer,
      sum_biUnion (fun i _ j _ hij => disjoint_factorLayer hij)]
    exact sum_congr rfl fun j _ => sum_moebius_factorLayer S j
  intro k hk
  rw [hsq_eq (k + 1)]
  induction k with
  | zero =>
    simp [cascadeUnconsumed]
  | succ m ih =>
    have hmK : m ≤ K := by omega
    have hprev := ih hmK
    have hcard := card_cascadeUnconsumed_succ hvalid (by omega : 1 ≤ m + 1) hk
    have hle : (cascadeUnconsumed S φ (m + 1)).card ≤ (factorLayer S (m + 2)).card := by
      obtain ⟨hinj, hsub⟩ := hvalid (m + 1) (by omega) hk
      rw [← card_image_of_injOn hinj]
      exact card_le_card hsub
    have hIcc : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have hnotMem : m + 2 ∉ Finset.Icc 1 (m + 1) := by simp
    rw [hcard, Nat.cast_sub hle, hIcc, sum_insert hnotMem, mul_add,
      show (-1 : ℤ) ^ (m + 2) * ((-1 : ℤ) ^ (m + 2) * ((factorLayer S (m + 2)).card : ℤ)) =
        ((factorLayer S (m + 2)).card : ℤ) by
        rw [← mul_assoc, ← pow_add, show m + 2 + (m + 2) = 2 * (m + 2) by omega]
        simp [pow_mul],
      show (-1 : ℤ) ^ (m + 2) * ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℤ) ^ j * ((factorLayer S j).card : ℤ) =
        -((-1 : ℤ) ^ (m + 1) * ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℤ) ^ j * ((factorLayer S j).card : ℤ)) by
        rw [pow_succ', neg_one_mul, neg_mul],
      ← hprev]
    ring

/-- Necessary sign-alternation condition for any `K`-step upward cascade, and exact vanishing
criterion when no squarefree elements lie outside `1 ≤ ω(n) ≤ K + 1`. -/
theorem upward_cascade_necessary_and_exhaustion {S : Finset ℕ} {φ : ℕ → ℕ → ℕ} {K : ℕ}
    (hvalid : IsValidLayerCascade S φ K) :
    (∀ k ≤ K,
      0 ≤ (-1 : ℤ) ^ (k + 1) *
        ∑ n ∈ S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ k + 1), μ n) ∧
    (1 ∉ S → (∀ n ∈ S, Squarefree n → n.primeFactors.card ≤ K + 1) →
      (cascadeUnconsumed S φ (K + 1) = ∅ ↔ ∑ n ∈ S, μ n = 0)) := by
  refine ⟨fun k hk => ?_, fun h1 htop => ?_⟩
  · rw [← intCast_card_cascadeUnconsumed hvalid k hk]
    exact Nat.cast_nonneg _
  · have hsum_eq :
        ∑ n ∈ S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ K + 1), μ n =
          ∑ n ∈ S, μ n := by
      let F := S.filter (fun n => 1 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ K + 1)
      have hFsub : F ⊆ S := filter_subset _ S
      change ∑ n ∈ F, μ n = ∑ n ∈ S, μ n
      refine sum_subset hFsub fun n hnS hnot => ?_
      by_cases hsq : Squarefree n
      · have h0 : n ≠ 0 := hsq.ne_zero
        have hn1 : n ≠ 1 := fun heq => h1 (heq ▸ hnS)
        have hpos : 1 ≤ n.primeFactors.card :=
          Finset.card_pos.mpr ⟨n.minFac, Nat.mem_primeFactors.mpr
            ⟨Nat.minFac_prime hn1, Nat.minFac_dvd n, h0⟩⟩
        exact False.elim (hnot (mem_filter.mpr ⟨hnS, hpos, htop n hnS hsq⟩))
      · exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have htel := intCast_card_cascadeUnconsumed hvalid K le_rfl
    rw [hsum_eq] at htel
    constructor
    · intro hemp
      rw [hemp, card_empty, Nat.cast_zero] at htel
      rcases mul_eq_zero.mp htel.symm with hpow | hsum
      · exact False.elim (pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0) hpow)
      · exact hsum
    · intro hsum0
      rw [hsum0, mul_zero] at htel
      exact card_eq_zero.mp (by exact_mod_cast htel)

end GaloisForLFunctions.QuantitativeFactorizationMatching
