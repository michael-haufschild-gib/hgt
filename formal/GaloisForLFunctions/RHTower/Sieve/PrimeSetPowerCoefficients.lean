import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIPrimeFactor
import GaloisForLFunctions.RHTower.Sieve.PrimePowerFactorialEnergy

/-!
# Powers of a prime Dirichlet polynomial

For a finite set `B` of primes, `(∑_{p ∈ B} p^{-s})^k = ∑_m c_k(m) m^{-s}` where `c_k(m)` counts
ordered `k`-tuples from `B` with product `m`.  Unique factorization bounds `c_k(m) ≤ k!` (all
tuples with product `m` are rearrangements of one of them), and the support has at most
`binom(|B|+k-1, k)` elements (the product depends only on the multiset of the tuple).  With
`B ⊆ (P, 2P]` the support lies in `(P^k, (2P)^k]`.  This is the amplifier `P₁(s)^k/k!` of
Matomäki–Teräväinen §5.3.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Ordered `k`-tuples from `B` with product `m`. -/
def primeSetTuples (B : Finset ℕ) (k m : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => B).filter fun t => ∏ i, t i = m

/-- Number of ordered `k`-tuples from `B` with product `m`. -/
def primeSetCount (B : Finset ℕ) (k m : ℕ) : ℕ := (primeSetTuples B k m).card

/-- Products of ordered `k`-tuples from `B`. -/
def primeSetSupport (B : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Fintype.piFinset fun _ : Fin k => B).image fun t => ∏ i, t i

theorem mem_primeSetTuples {B : Finset ℕ} {k m : ℕ} {t : Fin k → ℕ} :
    t ∈ primeSetTuples B k m ↔ (∀ i, t i ∈ B) ∧ ∏ i, t i = m := by
  simp [primeSetTuples, Fintype.mem_piFinset]

/-- **The power expansion.** -/
theorem sum_cpow_pow_eq_sum_primeSetCount (B : Finset ℕ) (k : ℕ) (z : ℂ) :
    (∑ p ∈ B, (p : ℂ) ^ z) ^ k =
      ∑ m ∈ primeSetSupport B k, (primeSetCount B k m : ℂ) * (m : ℂ) ^ z := by
  classical
  have hpow : (∑ p ∈ B, (p : ℂ) ^ z) ^ k = ∏ _i : Fin k, ∑ p ∈ B, (p : ℂ) ^ z := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, Finset.prod_univ_sum]
  have h1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => B),
      ∏ i, ((t i : ℕ) : ℂ) ^ z = (((∏ i, t i : ℕ) : ℂ)) ^ z :=
    fun t _ => (natCast_finset_prod_cpow _ t z).symm
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Fin k → ℕ => ∏ i, t i)
    (t := primeSetSupport B k) (fun t ht => Finset.mem_image_of_mem _ ht)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.1 ht).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

theorem primeSetCount_eq_zero_of_not_mem {B : Finset ℕ} {k m : ℕ}
    (hm : m ∉ primeSetSupport B k) : primeSetCount B k m = 0 := by
  rw [primeSetCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨htB, hprod⟩ := mem_primeSetTuples.1 ht
  exact hm (Finset.mem_image.2 ⟨t, Fintype.mem_piFinset.2 htB, hprod⟩)

/-- **Unique factorization bounds each coefficient by `k!`.** -/
theorem primeSetCount_le_factorial {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (k m : ℕ) :
    primeSetCount B k m ≤ k.factorial := by
  classical
  rcases Finset.eq_empty_or_nonempty (primeSetTuples B k m) with hF | ⟨t₀, ht₀⟩
  · rw [primeSetCount, hF]; exact Nat.zero_le _
  have hmemB : ∀ t ∈ primeSetTuples B k m, ∀ i, t i ∈ B := fun t ht => (mem_primeSetTuples.1 ht).1
  let lift : ∀ t ∈ primeSetTuples B k m, Fin k → B := fun t ht i => ⟨t i, hmemB t ht i⟩
  have hperm : ∀ t (ht : t ∈ primeSetTuples B k m),
      List.ofFn (lift t ht) ∈ (List.ofFn (lift t₀ ht₀)).permutations := by
    intro t ht
    rw [List.mem_permutations]
    have hprime : ∀ s ∈ primeSetTuples B k m, ∀ p ∈ List.ofFn s, p.Prime := by
      intro s hs p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
      exact hB _ ((mem_primeSetTuples.1 hs).1 i)
    have hprod : ∀ s ∈ primeSetTuples B k m, (List.ofFn s).prod = m := by
      intro s hs
      rw [List.prod_ofFn]
      exact (mem_primeSetTuples.1 hs).2
    have hval : (List.ofFn t).Perm (List.ofFn t₀) :=
      (Nat.primeFactorsList_unique (hprod t ht) (hprime t ht)).trans
        (Nat.primeFactorsList_unique (hprod t₀ ht₀) (hprime t₀ ht₀)).symm
    apply Multiset.coe_eq_coe.mp
    apply Multiset.map_injective Subtype.val_injective
    rw [Multiset.map_coe, Multiset.map_coe, List.map_ofFn, List.map_ofFn]
    exact Multiset.coe_eq_coe.mpr hval
  let embed : ↑(primeSetTuples B k m) ↪
      {l : List B // l ∈ (List.ofFn (lift t₀ ht₀)).permutations} :=
    { toFun := fun t => ⟨List.ofFn (lift t.1 t.2), hperm t.1 t.2⟩
      inj' := by
        intro s t hst
        apply Subtype.ext
        funext i
        have h := congrFun (List.ofFn_injective (congrArg Subtype.val hst)) i
        exact congrArg Subtype.val h }
  have hcard := Fintype.card_le_of_embedding embed
  rw [Fintype.card_coe] at hcard
  exact hcard.trans (card_permutation_list_subtype_le_factorial (lift t₀ ht₀))

/-- The product of a tuple depends only on its multiset, so the support has at most
`binom(|B|+k-1, k)` elements. -/
theorem card_primeSetSupport_le_choose (B : Finset ℕ) (k : ℕ) :
    (primeSetSupport B k).card ≤ (B.card + k - 1).choose k := by
  classical
  let prodSym : Sym B k → ℕ := fun s => ((s : Multiset B).map Subtype.val).prod
  have hsub : primeSetSupport B k ⊆ (Finset.univ : Finset (Sym B k)).image prodSym := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
    have htB : ∀ i, t i ∈ B := Fintype.mem_piFinset.1 ht
    let s : Sym B k := ⟨(List.ofFn fun i => (⟨t i, htB i⟩ : B) : Multiset B), by simp⟩
    refine Finset.mem_image.2 ⟨s, Finset.mem_univ _, ?_⟩
    change ((List.ofFn fun i => (⟨t i, htB i⟩ : B) : Multiset B).map Subtype.val).prod = _
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
    rfl
  calc (primeSetSupport B k).card ≤ ((Finset.univ : Finset (Sym B k)).image prodSym).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Sym B k)).card := Finset.card_image_le
    _ = (B.card + k - 1).choose k := by
        rw [Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_coe]

/-- Real form: `|supp| · k! ≤ (|B| + k - 1)^k`. -/
theorem card_primeSetSupport_mul_factorial_le (B : Finset ℕ) (k : ℕ) :
    ((primeSetSupport B k).card : ℝ) * k.factorial ≤ ((B.card + k - 1 : ℕ) : ℝ) ^ k := by
  have h1 : ((primeSetSupport B k).card : ℝ) ≤ (((B.card + k - 1).choose k : ℕ) : ℝ) := by
    exact_mod_cast card_primeSetSupport_le_choose B k
  have h2 := Nat.choose_le_pow_div (α := ℝ) k (B.card + k - 1)
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc ((primeSetSupport B k).card : ℝ) * k.factorial
      ≤ ((B.card + k - 1 : ℕ) : ℝ) ^ k / k.factorial * k.factorial :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hf.le
    _ = ((B.card + k - 1 : ℕ) : ℝ) ^ k := div_mul_cancel₀ _ hf.ne'

/-- Support range: products of `k` elements of `(P, 2P]` lie in `(P^k, (2P)^k]` when `k ≥ 1`. -/
theorem mem_primeSetSupport_bounds {B : Finset ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) {m : ℕ}
    (hm : m ∈ primeSetSupport B k) :
    P ^ k < (m : ℝ) ∧ (m : ℝ) ≤ (2 * P) ^ k := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
  have htB : ∀ i, t i ∈ B := Fintype.mem_piFinset.1 ht
  push_cast
  constructor
  · have := Finset.prod_lt_prod_of_nonempty (s := (Finset.univ : Finset (Fin k)))
      (f := fun _ => P) (g := fun i => (t i : ℝ))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    by_cases hP0 : P = 0
    · subst hP0
      rw [zero_pow (by omega)]
      refine Finset.prod_pos fun i _ => ?_
      exact (hB _ (htB i)).1
    · exact this (fun _ _ => lt_of_le_of_ne hP (Ne.symm hP0)) (fun i _ => (hB _ (htB i)).1)
        ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  · calc ∏ i, (t i : ℝ) ≤ ∏ _i : Fin k, 2 * P :=
          Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) fun i _ => (hB _ (htB i)).2
      _ = (2 * P) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem pos_of_mem_primeSetSupport {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {k m : ℕ}
    (hm : m ∈ primeSetSupport B k) : 0 < m := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
  exact Finset.prod_pos fun i _ => (hB _ (Fintype.mem_piFinset.1 ht i)).pos

end

end RHTower.Sieve
