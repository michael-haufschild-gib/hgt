import GaloisForLFunctions.RHTower.BeurlingSystemCounting
import GaloisForLFunctions.HTGeometry.PowerHyperbolaConvolution

/-!
# The deletion system `(ℙ ∖ S) ∪ ℙ^{1/β}` and its integer count

For a set `S` of primes and `β > 0`, the Beurling system `deletionSystem S β` has prime labels
`(ℙ ∖ S) ⊕ ℙ`, with norms `p` and `q^{1/β}`.  Its generalized integers are the pairs
`(u, v)` of multisets of kept primes and of primes (`joinEquiv`), with norm `n · m^{1/β}`, where
`n = Π u` runs over the `S`-free integers and `m = Π v` over all positive integers (unique
factorization).  Hence

`N(x) = #{(n, m) : n S-free, m ≥ 1, n m^{1/β} ≤ x} = Σ_{1 ≤ m ≤ x^β} A(x m^{−1/β})`,

`A(t) = #{n ≤ t : n S-free}` (`countBall_eq_hyperbolaCount`), and the system is discrete.
-/

open Finset

noncomputable section

namespace RHTower.BeurlingDeletion

open GaloisForLFunctions.HTGeometry.PowerHyperbola

/-- `n` is positive and has no prime factor in `S`. -/
def SFree (S : Set ℕ) (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∉ S

open Classical in
/-- The indicator of the `S`-free integers. -/
def sFreeR (S : Set ℕ) (n : ℕ) : ℝ := if SFree S n then 1 else 0

theorem sFreeR_zero (S : Set ℕ) : sFreeR S 0 = 0 := by
  classical
  simp [sFreeR, SFree]

theorem abs_sFreeR_le (S : Set ℕ) (n : ℕ) : |sFreeR S n| ≤ 1 := by
  classical
  unfold sFreeR; split_ifs <;> simp

theorem sFreeR_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ sFreeR S n := by
  classical
  unfold sFreeR; split_ifs <;> simp

/-- The primes kept by the deletion of `S`. -/
abbrev KeptPrime (S : Set ℕ) : Type := {p : ℕ // p.Prime ∧ p ∉ S}

/-- **The deletion system** `(ℙ ∖ S) ∪ ℙ^{1/β}`. -/
abbrev deletionSystem (S : Set ℕ) (β : ℝ) (hβ : 0 < β) : BeurlingSystem where
  Label := KeptPrime S ⊕ Nat.Primes
  labelNorm := Sum.elim (fun p => (p.1 : ℝ)) (fun q => ((q : ℕ) : ℝ) ^ (1 / β))
  one_lt_labelNorm := by
    rintro (p | q)
    · show (1 : ℝ) < ((p.1 : ℕ) : ℝ)
      exact_mod_cast p.2.1.one_lt
    · exact Real.one_lt_rpow (by exact_mod_cast q.2.one_lt) (by positivity)

/-! ## Multisets over a sum type -/

section Join

variable {α γ : Type*}

/-- `(u, v) ↦ u ⊕ v`. -/
def join (uv : Multiset α × Multiset γ) : Multiset (α ⊕ γ) := uv.1.map Sum.inl + uv.2.map Sum.inr

/-- The two components of a multiset over `α ⊕ γ`. -/
def split (g : Multiset (α ⊕ γ)) : Multiset α × Multiset γ :=
  (g.filterMap Sum.getLeft?, g.filterMap Sum.getRight?)

theorem filterMap_none {β : Type*} (s : Multiset α) :
    Multiset.filterMap (fun _ => (none : Option β)) s = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih => rw [Multiset.filterMap_cons_none _ _ rfl, ih]

theorem join_split_cons (x : α ⊕ γ) (g : Multiset (α ⊕ γ)) :
    join (split (x ::ₘ g)) = x ::ₘ join (split g) := by
  rcases x with a | c
  · simp only [split, join]
    rw [Multiset.filterMap_cons_some _ _ _ (rfl : Sum.getLeft? (Sum.inl a : α ⊕ γ) = some a),
      Multiset.filterMap_cons_none _ _ (rfl : Sum.getRight? (Sum.inl a : α ⊕ γ) = none),
      Multiset.map_cons, Multiset.cons_add]
  · simp only [split, join]
    rw [Multiset.filterMap_cons_none _ _ (rfl : Sum.getLeft? (Sum.inr c : α ⊕ γ) = none),
      Multiset.filterMap_cons_some _ _ _ (rfl : Sum.getRight? (Sum.inr c : α ⊕ γ) = some c),
      Multiset.map_cons, Multiset.add_cons]

theorem join_split (g : Multiset (α ⊕ γ)) : join (split g) = g := by
  induction g using Multiset.induction_on with
  | empty => simp [join, split]
  | cons x g ih => rw [join_split_cons, ih]

theorem split_join (uv : Multiset α × Multiset γ) : split (join uv) = uv := by
  obtain ⟨u, v⟩ := uv
  simp only [split, join, Multiset.filterMap_add, Multiset.filterMap_map]
  have h1 : (Sum.getLeft? ∘ (Sum.inl : α → α ⊕ γ)) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : γ → α ⊕ γ)) = fun _ => none := rfl
  have h3 : (Sum.getRight? ∘ (Sum.inl : α → α ⊕ γ)) = fun _ => none := rfl
  have h4 : (Sum.getRight? ∘ (Sum.inr : γ → α ⊕ γ)) = some := rfl
  rw [h1, h2, h3, h4, Multiset.filterMap_some, Multiset.filterMap_some, filterMap_none,
    filterMap_none, add_zero, zero_add]

/-- `Multiset (α ⊕ γ) ≃ Multiset α × Multiset γ`. -/
def joinEquiv : Multiset α × Multiset γ ≃ Multiset (α ⊕ γ) where
  toFun := join
  invFun := split
  left_inv := split_join
  right_inv := join_split

end Join

/-! ## Unique factorization -/

theorem prod_primes_injective :
    Function.Injective fun w : Multiset Nat.Primes => (w.map (fun p : Nat.Primes => (p : ℕ))).prod := by
  intro w w' h
  have h' : (PrimeMultiset.prod w : ℕ) = (PrimeMultiset.prod w' : ℕ) := by
    rw [PrimeMultiset.coe_prod, PrimeMultiset.coe_prod]; exact h
  rw [← PrimeMultiset.factorMultiset_prod w, ← PrimeMultiset.factorMultiset_prod w',
    PNat.coe_inj.mp h']

/-- The kept primes as primes. -/
def keptToPrime (S : Set ℕ) (p : KeptPrime S) : Nat.Primes := ⟨p.1, p.2.1⟩

theorem keptToPrime_injective (S : Set ℕ) : Function.Injective (keptToPrime S) := by
  intro p q h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact this

theorem prod_kept_injective (S : Set ℕ) :
    Function.Injective fun u : Multiset (KeptPrime S) => (u.map (fun p : KeptPrime S => p.1)).prod := by
  intro u u' h
  apply Multiset.map_injective (keptToPrime_injective S)
  apply prod_primes_injective
  simp only [Multiset.map_map]
  exact h

theorem prod_primes_pos (w : Multiset Nat.Primes) :
    0 < (w.map (fun p : Nat.Primes => (p : ℕ))).prod := by
  refine Multiset.prod_pos fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hx
  exact p.2.pos

theorem sFree_prod_kept (S : Set ℕ) (u : Multiset (KeptPrime S)) :
    SFree S (u.map (fun p : KeptPrime S => p.1)).prod := by
  have hpos : 0 < (u.map (fun p : KeptPrime S => p.1)).prod := by
    have := prod_primes_pos (u.map (keptToPrime S))
    simpa [Multiset.map_map, keptToPrime] using this
  refine ⟨hpos.ne', fun q hq => ?_⟩
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqd : q ∣ (u.map (fun p : KeptPrime S => p.1)).prod := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨r, hr, hrd⟩ := (Nat.prime_iff.mp hqp).exists_mem_multiset_dvd hqd
  obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
  rw [(Nat.prime_dvd_prime_iff_eq hqp p.2.1).mp hrd]
  exact p.2.2

theorem exists_kept_of_sFree (S : Set ℕ) {n : ℕ} (hn : SFree S n) :
    ∃ u : Multiset (KeptPrime S), (u.map (fun p : KeptPrime S => p.1)).prod = n := by
  have hmem : ∀ p ∈ (n.primeFactorsList : Multiset ℕ), p.Prime ∧ p ∉ S := by
    intro p hp
    have hp' : p ∈ n.primeFactorsList := hp
    refine ⟨Nat.prime_of_mem_primeFactorsList hp', hn.2 p ?_⟩
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_of_mem_primeFactorsList hp', Nat.dvd_of_mem_primeFactorsList hp', hn.1⟩
  refine ⟨(n.primeFactorsList : Multiset ℕ).pmap (fun p hp => (⟨p, hp⟩ : KeptPrime S)) hmem, ?_⟩
  rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id', Multiset.prod_coe,
    Nat.prod_primeFactorsList hn.1]

theorem exists_primes_of_pos {m : ℕ} (hm : 1 ≤ m) :
    ∃ v : Multiset Nat.Primes, (v.map (fun p : Nat.Primes => (p : ℕ))).prod = m := by
  have hm0 : m ≠ 0 := by omega
  have hmem : ∀ p ∈ (m.primeFactorsList : Multiset ℕ), p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactorsList hp
  refine ⟨(m.primeFactorsList : Multiset ℕ).pmap (fun p hp => (⟨p, hp⟩ : Nat.Primes)) hmem, ?_⟩
  rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id', Multiset.prod_coe,
    Nat.prod_primeFactorsList hm0]

/-! ## The integer count -/

/-- The integer pair `(Π u, Π v)` of a generalized integer `u ⊕ v`. -/
def pairMap (S : Set ℕ) (uv : Multiset (KeptPrime S) × Multiset Nat.Primes) : ℕ × ℕ :=
  ((uv.1.map (fun p : KeptPrime S => p.1)).prod, (uv.2.map (fun p : Nat.Primes => (p : ℕ))).prod)

theorem pairMap_injective (S : Set ℕ) : Function.Injective (pairMap S) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [pairMap, Prod.mk.injEq] at h
  rw [prod_kept_injective S h.1, prod_primes_injective h.2]

theorem intNorm_join (S : Set ℕ) {β : ℝ} (hβ : 0 < β) (u : Multiset (KeptPrime S))
    (v : Multiset Nat.Primes) :
    (deletionSystem S β hβ).intNorm (join (u, v)) =
      ((pairMap S (u, v)).1 : ℝ) * ((pairMap S (u, v)).2 : ℝ) ^ (1 / β) := by
  unfold BeurlingSystem.intNorm join pairMap
  simp only
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map,
    Nat.cast_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  exact Real.multiset_prod_map_rpow v (fun q : Nat.Primes => ((q : ℕ) : ℝ))
    (fun q _ => Nat.cast_nonneg _) (1 / β)

theorem mem_range_pairMap (S : Set ℕ) {n m : ℕ} :
    (n, m) ∈ Set.range (pairMap S) ↔ SFree S n ∧ 1 ≤ m := by
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    simp only [pairMap, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]
    exact ⟨sFree_prod_kept S u, prod_primes_pos v⟩
  · rintro ⟨hn, hm⟩
    obtain ⟨u, hu⟩ := exists_kept_of_sFree S hn
    obtain ⟨v, hv⟩ := exists_primes_of_pos hm
    exact ⟨(u, v), by simp [pairMap, hu, hv]⟩

/-- The integer pairs of norm at most `X`. -/
def pairSet (S : Set ℕ) (β X : ℝ) : Set (ℕ × ℕ) :=
  {nm | SFree S nm.1 ∧ 1 ≤ nm.2 ∧ (nm.1 : ℝ) * (nm.2 : ℝ) ^ (1 / β) ≤ X}

theorem ncard_ball_eq_ncard_pairSet (S : Set ℕ) {β : ℝ} (hβ : 0 < β) (X : ℝ) :
    (deletionSystem S β hβ).countBall X = (pairSet S β X).ncard := by
  unfold BeurlingSystem.countBall
  have h1 : {g : Multiset (KeptPrime S ⊕ Nat.Primes) | (deletionSystem S β hβ).intNorm g ≤ X} =
      joinEquiv '' {uv | (deletionSystem S β hβ).intNorm (join uv) ≤ X} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hg
      refine ⟨split g, ?_, join_split g⟩
      show (deletionSystem S β hβ).intNorm (join (split g)) ≤ X
      rw [join_split]; exact hg
    · rintro ⟨uv, huv, rfl⟩
      exact huv
  have h2 : pairSet S β X = pairMap S '' {uv | (deletionSystem S β hβ).intNorm (join uv) ≤ X} := by
    ext ⟨n, m⟩
    simp only [pairSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hn, hm, hX⟩
      obtain ⟨uv, huv⟩ := (mem_range_pairMap S).mpr ⟨hn, hm⟩
      refine ⟨uv, ?_, huv⟩
      obtain ⟨u, v⟩ := uv
      rw [intNorm_join, huv]
      exact hX
    · rintro ⟨⟨u, v⟩, huv, hnm⟩
      have hr := (mem_range_pairMap S).mp ⟨(u, v), hnm⟩
      refine ⟨hr.1, hr.2, ?_⟩
      rw [intNorm_join, hnm] at huv
      exact huv
  change ({g : Multiset (KeptPrime S ⊕ Nat.Primes) | (deletionSystem S β hβ).intNorm g ≤ X}).ncard =
    _
  rw [h1, Set.ncard_image_of_injective _ joinEquiv.injective, h2,
    Set.ncard_image_of_injective _ (pairMap_injective S)]

open Classical in
/-- The finite set of pairs `(n, m)` with `n ≤ X`, `1 ≤ m ≤ X^β`, `n m^{1/β} ≤ X`. -/
def pairFinset (S : Set ℕ) (β X : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 0 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X ^ β⌋₊).filter
    (fun nm => SFree S nm.1 ∧ (nm.1 : ℝ) * (nm.2 : ℝ) ^ (1 / β) ≤ X)

theorem pairSet_eq (S : Set ℕ) {β : ℝ} (hβ : 0 < β) (X : ℝ) :
    pairSet S β X = ↑(pairFinset S β X) := by
  classical
  ext ⟨n, m⟩
  simp only [pairSet, pairFinset, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hn, hm, hnm⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn.1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmp : (1 : ℝ) ≤ (m : ℝ) ^ (1 / β) := Real.one_le_rpow hm1 (by positivity)
    have hnX : (n : ℝ) ≤ X := by nlinarith
    have hmX : (m : ℝ) ^ (1 / β) ≤ X := by nlinarith
    refine ⟨⟨⟨Nat.zero_le _, Nat.le_floor hnX⟩, hm, Nat.le_floor ?_⟩, hn, hnm⟩
    have := Real.rpow_le_rpow (by positivity) hmX hβ.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one] at this
  · rintro ⟨⟨-, hm, -⟩, hn, hnm⟩
    exact ⟨hn, hm, hnm⟩

open Classical in
theorem card_filter_sFree_eq (S : Set ℕ) {β : ℝ} (hβ : 0 < β) {X : ℝ} (hX : 0 < X) {m : ℕ}
    (hm : 1 ≤ m) :
    (((Finset.Icc 0 ⌊X⌋₊).filter
      (fun n => SFree S n ∧ (n : ℝ) * (m : ℝ) ^ (1 / β) ≤ X)).card : ℝ) =
      countFn (sFreeR S) (X * (m : ℝ) ^ (-(1 / β))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos hm0 _
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 / β) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by positivity)
  have hneg : (m : ℝ) ^ (-(1 / β)) = ((m : ℝ) ^ (1 / β))⁻¹ := Real.rpow_neg hm0.le _
  have hiff : ∀ n : ℕ, (n : ℝ) * (m : ℝ) ^ (1 / β) ≤ X ↔ n ≤ ⌊X * (m : ℝ) ^ (-(1 / β))⌋₊ := by
    intro n
    rw [Nat.le_floor_iff (by positivity), hneg, ← div_eq_mul_inv, le_div_iff₀ hmp]
  have hfl : ⌊X * (m : ℝ) ^ (-(1 / β))⌋₊ ≤ ⌊X⌋₊ := by
    apply Nat.floor_le_floor
    rw [hneg, ← div_eq_mul_inv]
    exact div_le_self hX.le hm1
  have hset : (Finset.Icc 0 ⌊X⌋₊).filter
      (fun n => SFree S n ∧ (n : ℝ) * (m : ℝ) ^ (1 / β) ≤ X) =
      (Finset.Icc 0 ⌊X * (m : ℝ) ^ (-(1 / β))⌋₊).filter (fun n => SFree S n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and, hiff]
    constructor
    · rintro ⟨-, hn, hnX⟩; exact ⟨hnX, hn⟩
    · rintro ⟨hnX, hn⟩; exact ⟨hnX.trans hfl, hn, hnX⟩
  unfold countFn sFreeR
  rw [Finset.sum_boole, hset]

/-- **The integer count of the deletion system** is the hyperbola count of the `S`-free
integers. -/
theorem countBall_eq_hyperbolaCount (S : Set ℕ) {β : ℝ} (hβ : 0 < β) {X : ℝ} (hX : 0 < X) :
    ((deletionSystem S β hβ).countBall X : ℝ) = hyperbolaCount (sFreeR S) β X := by
  classical
  rw [ncard_ball_eq_ncard_pairSet, pairSet_eq S hβ, Set.ncard_coe_finset, pairFinset,
    Finset.card_filter, Finset.sum_product_right, hyperbolaCount, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [← card_filter_sFree_eq S hβ hX hm1, Finset.card_filter]

theorem ball_eq_image (S : Set ℕ) {β : ℝ} (hβ : 0 < β) (X : ℝ) :
    {g : Multiset (KeptPrime S ⊕ Nat.Primes) | (deletionSystem S β hβ).intNorm g ≤ X} =
      joinEquiv '' {uv | (deletionSystem S β hβ).intNorm (join uv) ≤ X} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hg
    refine ⟨split g, ?_, join_split g⟩
    show (deletionSystem S β hβ).intNorm (join (split g)) ≤ X
    rw [join_split]; exact hg
  · rintro ⟨uv, huv, rfl⟩
    exact huv

/-- The deletion system is discrete. -/
theorem isDiscrete_deletionSystem (S : Set ℕ) {β : ℝ} (hβ : 0 < β) :
    (deletionSystem S β hβ).IsDiscrete := by
  intro X
  have hX1 : (0 : ℝ) < max X 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : (pairSet S β (max X 1)).Finite := by
    rw [pairSet_eq S hβ]; exact Finset.finite_toSet _
  have hsub : {uv | (deletionSystem S β hβ).intNorm (join uv) ≤ X} ⊆
      pairMap S ⁻¹' pairSet S β (max X 1) := by
    rintro ⟨u, v⟩ huv
    have hr := (mem_range_pairMap S).mp ⟨(u, v), rfl⟩
    simp only [Set.mem_setOf_eq] at huv
    rw [intNorm_join] at huv
    exact ⟨hr.1, hr.2, huv.trans (le_max_left _ _)⟩
  have hfin2 := (hfin.preimage (pairMap_injective S).injOn).subset hsub
  change {g : Multiset (KeptPrime S ⊕ Nat.Primes) | (deletionSystem S β hβ).intNorm g ≤ X}.Finite
  rw [ball_eq_image]
  exact hfin2.image _

end RHTower.BeurlingDeletion
