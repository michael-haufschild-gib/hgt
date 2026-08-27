import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCoefficientGrowth

/-!
# Chain products in the finite Matomäki--Teräväinen iteration

Strictly descending, pairwise-disjoint prime blocks make every chosen prime product remember its
whole chain.  Consequently the coefficient after any depth is a sum over a subset of the divisors
of its argument, giving a depth-uniform divisor bound.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Products of exactly `depth` primes selected from strictly descending blocks below `j`. -/
def mtChainProducts {t : ℕ} (data : MTFiniteIterationSourceData t) :
    ℕ → Fin (t + 1) → Finset ℕ
  | 0, _ => {1}
  | depth + 1, j =>
      (mtBlockPrefix j).biUnion fun i =>
        (data.block i).biUnion fun q =>
          (mtChainProducts data depth i.castSucc).image fun d => q * d

theorem mtChainProducts_pos {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) {d : ℕ} (hd : d ∈ mtChainProducts data depth j) :
    0 < d := by
  induction depth generalizing j d with
  | zero =>
      simp only [mtChainProducts, Finset.mem_singleton] at hd
      omega
  | succ depth ih =>
      rw [mtChainProducts] at hd
      obtain ⟨i, hi, q, hq, e, he, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hd
      exact Nat.mul_pos (data.block_prime i q hq).pos (ih i.castSucc he)

/-- Every prime factor of a chain product belongs to a uniquely earlier source block. -/
theorem mtChainProducts_prime_mem_prefix {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) {d p : ℕ}
    (hd : d ∈ mtChainProducts data depth j) (hp : p.Prime) (hpd : p ∣ d) :
    ∃ i ∈ mtBlockPrefix j, p ∈ data.block i := by
  induction depth generalizing j d with
  | zero =>
      simp only [mtChainProducts, Finset.mem_singleton] at hd
      subst d
      simpa using (hp.not_dvd_one hpd)
  | succ depth ih =>
      rw [mtChainProducts] at hd
      obtain ⟨i, hi, q, hq, e, he, hqe⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hd
      subst d
      rcases hp.dvd_mul.mp hpd with hpq | hpe
      · have hpEq : p = q := by
          rcases (Nat.dvd_prime (data.block_prime i q hq)).mp hpq with hp1 | hpqEq
          · exact (hp.ne_one hp1).elim
          · exact hpqEq
        exact ⟨i, hi, hpEq ▸ hq⟩
      · obtain ⟨k, hk, hpk⟩ := ih i.castSucc he hpe
        have hk' : k.1 < i.1 := by
          rw [mem_mtBlockPrefix] at hk
          simpa using hk
        have hi' : i.1 < j.1 := by simpa [mem_mtBlockPrefix] using hi
        exact ⟨k, mem_mtBlockPrefix.mpr (hk'.trans hi'), hpk⟩

/-- A prime in block `i` cannot already occur in a product from strictly earlier blocks. -/
theorem not_dvd_mtChainProducts_of_mem_block {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ) (i : Fin t)
    {q d : ℕ} (hq : q ∈ data.block i)
    (hd : d ∈ mtChainProducts data depth i.castSucc) : ¬q ∣ d := by
  intro hqd
  obtain ⟨k, hk, hqk⟩ := mtChainProducts_prime_mem_prefix data depth i.castSucc hd
    (data.block_prime i q hq) hqd
  rw [mem_mtBlockPrefix] at hk
  have hk' : k.1 < i.1 := by simpa using hk
  have hki : k ≠ i := by
    intro hki
    subst k
    exact (Nat.lt_irrefl i.1) hk'
  exact (Finset.disjoint_left.mp (data.block_disjoint k i hki)) hqk hq

/-- Products obtained from two distinct primes in one block are disjoint. -/
theorem mtChainProducts_images_disjoint_of_ne {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ) (i : Fin t)
    {q r : ℕ} (hq : q ∈ data.block i) (hr : r ∈ data.block i) (hqr : q ≠ r) :
    Disjoint
      ((mtChainProducts data depth i.castSucc).image fun d => q * d)
      ((mtChainProducts data depth i.castSucc).image fun d => r * d) := by
  rw [Finset.disjoint_left]
  intro x hxq hxr
  obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hxq
  obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hxr
  have hqDvd : q ∣ r * e := by
    refine ⟨d, ?_⟩
    omega
  rcases (data.block_prime i q hq).dvd_mul.mp hqDvd with hqrDvd | hqe
  · rcases (Nat.dvd_prime (data.block_prime i r hr)).mp hqrDvd with hq1 | hEq
    · exact (data.block_prime i q hq).ne_one hq1
    · exact hqr hEq
  · exact not_dvd_mtChainProducts_of_mem_block data depth i hq he hqe

/-- Prime-product images within one source block are pairwise disjoint. -/
theorem mtChainProducts_block_pairwiseDisjoint {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ) (i : Fin t) :
    (↑(data.block i) : Set ℕ).PairwiseDisjoint fun q =>
      (mtChainProducts data depth i.castSucc).image fun d => q * d := by
  intro q hq r hr hqr
  exact mtChainProducts_images_disjoint_of_ne data depth i hq hr hqr

/-- Products whose highest selected blocks differ are disjoint. -/
theorem mtChainProducts_blocks_disjoint_of_ne {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    {i k : Fin t} (hik : i ≠ k) :
    Disjoint
      ((data.block i).biUnion fun q =>
        (mtChainProducts data depth i.castSucc).image fun d => q * d)
      ((data.block k).biUnion fun q =>
        (mtChainProducts data depth k.castSucc).image fun d => q * d) := by
  rw [Finset.disjoint_left]
  intro x hxi hxk
  obtain ⟨q, hq, d, hd, hqdx⟩ := by
    simpa only [Finset.mem_biUnion, Finset.mem_image] using hxi
  obtain ⟨r, hr, e, he, hrex⟩ := by
    simpa only [Finset.mem_biUnion, Finset.mem_image] using hxk
  have hikv : i.1 ≠ k.1 := fun h => hik (Fin.ext h)
  rcases lt_or_gt_of_ne hikv with hikv | hkiv
  · have hrDvd : r ∣ q * d := by
      refine ⟨e, ?_⟩
      omega
    rcases (data.block_prime k r hr).dvd_mul.mp hrDvd with hrq | hrd
    · rcases (Nat.dvd_prime (data.block_prime i q hq)).mp hrq with hr1 | hrqEq
      · exact (data.block_prime k r hr).ne_one hr1
      · exact (Finset.disjoint_left.mp (data.block_disjoint k i hik.symm)) hr
          (hrqEq ▸ hq)
    · obtain ⟨u, hu, hru⟩ := mtChainProducts_prime_mem_prefix
        data depth i.castSucc hd (data.block_prime k r hr) hrd
      rw [mem_mtBlockPrefix] at hu
      have hu' : u.1 < i.1 := by simpa using hu
      exact (Finset.disjoint_left.mp (data.block_disjoint k u (by
        intro hku
        have : k.1 = u.1 := congrArg Fin.val hku
        omega))) hr hru
  · have hqDvd : q ∣ r * e := by
      refine ⟨d, ?_⟩
      omega
    rcases (data.block_prime i q hq).dvd_mul.mp hqDvd with hqr | hqe
    · rcases (Nat.dvd_prime (data.block_prime k r hr)).mp hqr with hq1 | hqrEq
      · exact (data.block_prime i q hq).ne_one hq1
      · exact (Finset.disjoint_left.mp (data.block_disjoint i k hik)) hq
          (hqrEq ▸ hr)
    · obtain ⟨u, hu, hqu⟩ := mtChainProducts_prime_mem_prefix
        data depth k.castSucc he (data.block_prime i q hq) hqe
      rw [mem_mtBlockPrefix] at hu
      have hu' : u.1 < k.1 := by simpa using hu
      exact (Finset.disjoint_left.mp (data.block_disjoint i u (by
        intro hiu
        have : i.1 = u.1 := congrArg Fin.val hiu
        omega))) hq hqu

/-- Highest-block product families are pairwise disjoint on every prefix. -/
theorem mtChainProducts_prefix_pairwiseDisjoint {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ) (j : Fin (t + 1)) :
    (↑(mtBlockPrefix j) : Set (Fin t)).PairwiseDisjoint fun i =>
      (data.block i).biUnion fun q =>
        (mtChainProducts data depth i.castSucc).image fun d => q * d := by
  intro i hi k hk hik
  exact mtChainProducts_blocks_disjoint_of_ne data depth hik

/-- Reindex one divisor sum through multiplication by a positive prime. -/
theorem sum_image_mul_ite_dvd (a : ℕ → ℂ) (S : Finset ℕ)
    {q n : ℕ} (hq : 0 < q) :
    (∑ x ∈ S.image (fun d => q * d), if x ∣ n then a (n / x) else 0) =
      if q ∣ n then
        ∑ d ∈ S, if d ∣ n / q then a ((n / q) / d) else 0
      else 0 := by
  rw [Finset.sum_image (by
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left hq hxy)]
  by_cases hqn : q ∣ n
  · simp only [hqn, if_true]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdvd : d ∣ n / q
    · have hmul : q * d ∣ n := (Nat.dvd_div_iff_mul_dvd hqn).mp hdvd
      simp [hdvd, hmul, Nat.div_div_eq_div_mul]
    · have hnotmul : ¬q * d ∣ n := fun hmul =>
        hdvd ((Nat.dvd_div_iff_mul_dvd hqn).mpr hmul)
      simp [hdvd, hnotmul]
  · simp only [hqn, if_false]
    apply Finset.sum_eq_zero
    intro d hd
    have hnot : ¬q * d ∣ n := fun h => hqn (dvd_trans (dvd_mul_right q d) h)
    simp [hnot]

/-- Exact divisor-sum expansion of every iterated coefficient. -/
theorem mtIteratedCoefficientAF_apply_eq_chainProducts {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtIteratedCoefficientAF data a depth j n =
      ∑ d ∈ mtChainProducts data depth j,
        if d ∣ n then a (n / d) else 0 := by
  induction depth generalizing j n with
  | zero => simp [mtIteratedCoefficientAF, mtChainProducts]
  | succ depth ih =>
      rw [mtIteratedCoefficientAF, mtChainProducts, arithmeticFunction_finset_sum_apply]
      rw [Finset.sum_biUnion (mtChainProducts_prefix_pairwiseDisjoint data depth j)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_biUnion (mtChainProducts_block_pairwiseDisjoint data depth i)]
      rw [mtPrimeBlockAF_mul_apply_eq_sum _ _ hn]
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_image_mul_ite_dvd _ _ (data.block_prime i q hq).pos]
      by_cases hqn : q ∣ n
      · simp only [hqn, if_true]
        rw [ih i.castSucc (Nat.div_pos (Nat.le_of_dvd hn hqn)
          (data.block_prime i q hq).pos)]
      · simp [hqn]

/-- Depth-uniform repair of the source coefficient estimate: strict block ordering costs one
ordinary divisor function, not `K^depth`. -/
theorem MTFiniteIterationSourceData.norm_mtIteratedCoefficientAF_le_card_divisors
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    ‖mtIteratedCoefficientAF data a depth j n‖ ≤
      B * (n.divisors.card : ℝ) := by
  rw [mtIteratedCoefficientAF_apply_eq_chainProducts data a depth j hn]
  let S := (mtChainProducts data depth j).filter fun d => d ∣ n
  have hrewrite :
      (∑ d ∈ mtChainProducts data depth j, if d ∣ n then a (n / d) else 0) =
        ∑ d ∈ S, a (n / d) := by
    dsimp [S]
    rw [← Finset.sum_filter]
  rw [hrewrite]
  have hsubset : S ⊆ n.divisors := by
    intro d hd
    simp only [S, Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, hn.ne'⟩
  calc
    ‖∑ d ∈ S, a (n / d)‖ ≤ ∑ d ∈ S, ‖a (n / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ S, B := by
      apply Finset.sum_le_sum
      intro d hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp (hsubset hd)).1
      exact ha (Nat.div_pos (Nat.le_of_dvd hn hdDvd)
        (Nat.pos_of_mem_divisors (hsubset hd)))
    _ = B * (S.card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ B * (n.divisors.card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast Finset.card_le_card hsubset

end

end RHTower.Sieve
