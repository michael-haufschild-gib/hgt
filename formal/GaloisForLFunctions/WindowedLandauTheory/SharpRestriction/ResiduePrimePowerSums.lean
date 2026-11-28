import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Bounds for the sum of the primary parts of the orders of
the base and extension residue multiplicative groups. -/

noncomputable section

namespace WindowedLandauTheory.ConcN

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ 1 ≤ ∏ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    have hfa : 2 ≤ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, by nlinarith⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨b, hb⟩
    · subst hs
      simp
    · have hP2 : 2 ≤ ∏ l ∈ s, f l :=
        (hf b (Finset.mem_insert_of_mem hb)).trans
          (Finset.single_le_prod' (fun l hl => by
            have := hf l (Finset.mem_insert_of_mem hl)
            omega) hb)
      nlinarith

private theorem one_sub_sum_mul_prod_le_prod (q x y z T P : ℕ) (hx : 16 ≤ x) (hy : q ≤ y) (hz : 16 ≤ z) (hqz : q ≤ z)
    (hT : T ≤ P) (hP : 1 ≤ P) : 4 * q * (x + (y + (z + T))) ≤ x * (y * (z * P)) := by
  have h1 : 16 * q ≤ y * z * P := by
    calc 16 * q = q * 16 * 1 := by ring
      _ ≤ y * z * P := Nat.mul_le_mul (Nat.mul_le_mul hy hz) hP
  have h2 : 16 * q ≤ x * z * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * z * P := Nat.mul_le_mul (Nat.mul_le_mul hx hqz) hP
  have h3 : 16 * q ≤ x * y * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * y * P := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hP
  have h4 : 16 * q * T ≤ x * y * z * P := by
    have h5 : 16 * q ≤ x * y * z := by
      calc 16 * q = 16 * q * 1 := by ring
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) (by omega)
    exact Nat.mul_le_mul h5 hT
  nlinarith [Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]

/-- The primary parts of the residue group occupy a small share of its order. -/
theorem prime_power_order_share (g q₁ d : ℕ) (hg : 2 ≤ g) (hq : q₁.Prime) (hd : d.Prime)
    (hqd : q₁ ≠ d) (hq2 : q₁ ≠ 2) (hd2 : d ≠ 2) (hM : 16 ≤ max q₁ d)
    (h16 : 16 ∣ g - 1) (hqn : q₁ ∣ g - 1) (hdn : d ∣ g - 1) :
    (∑ l ∈ (g - 1).primeFactors, ((l ^ padicValNat l (g - 1) : ℕ) : ℝ)) /
      ((g - 1 : ℕ) : ℝ) ≤ 1 / (4 * (min q₁ d : ℕ)) := by
  classical
  set n := g - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∣ n := (show 2 ∣ 16 by norm_num).trans h16
  have hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors := fun l hl hln =>
    Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩
  have hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n := by
    intro l hl hln
    haveI := Fact.mk hl
    have hv : 1 ≤ padicValNat l n := one_le_padicValNat_of_dvd hn0 hln
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ padicValNat l n := Nat.pow_le_pow_right hl.pos hv
  have hf2 : 16 ≤ 2 ^ padicValNat 2 n := by
    haveI := Fact.mk Nat.prime_two
    have hv : 4 ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn0).mp (by norm_num; exact h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hv
  have h2m := hmem 2 Nat.prime_two h2n
  have hqm : q₁ ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩
  have hdm : d ∈ (n.primeFactors.erase 2).erase q₁ :=
    Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩
  have hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n =
      2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
        ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    rw [← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]
  have hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
        ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    have h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl)]
    rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm,
      ← Finset.mul_prod_erase _ _ hdm] at h1
    exact h1.symm
  have hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n := by
    intro l hl
    have hl' : l ∈ n.primeFactors :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
    have hlp := Nat.prime_of_mem_primeFactors hl'
    exact hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))
  obtain ⟨hTP, hP1⟩ := sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2
  have hq16 := hge q₁ hq hqn
  have hd16 := hge d hd hdn
  have hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n := by
    rw [hsum]
    rcases le_total q₁ d with hle | hle
    · rw [min_eq_left hle]
      have key := one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16)
        (hle.trans hd16) hTP hP1
      calc _ = 4 * q₁ * (2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = n := hprod.symm
    · rw [min_eq_right hle]
      have key := one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _
        hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1
      calc _ = 4 * d * (2 ^ padicValNat 2 n + (d ^ padicValNat d n + (q₁ ^ padicValNat q₁ n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
            ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by ring
        _ = n := hprod.symm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))
  rw [← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]
  exact_mod_cast hnat

private theorem prod_pow_factorization_le (s : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (hs : ∀ l ∈ s, l.Prime) :
    ∏ l ∈ s, l ^ n.factorization l ≤ n := by
  classical
  calc ∏ l ∈ s, l ^ n.factorization l ≤ ∏ l ∈ s ∪ n.primeFactors, l ^ n.factorization l := by
        apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
        intro l hl _
        rcases Finset.mem_union.1 hl with h | h
        · exact Nat.one_le_pow _ _ (hs l h).pos
        · exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors h).pos
    _ = ∏ l ∈ n.primeFactors, l ^ n.factorization l := by
        symm
        apply Finset.prod_subset Finset.subset_union_right
        intro l _ hl
        have : n.factorization l = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hl
        rw [this, pow_zero]
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

private theorem lte_val (g δ l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hδ : 1 ≤ δ) (hl : l.Prime)
    (hd : l ∣ g - 1) : padicValNat l (g ^ δ - 1) = padicValNat l (g - 1) + padicValNat l δ := by
  have : Fact l.Prime := ⟨hl⟩
  have hlg : ¬ l ∣ g := by
    intro h
    have : l ∣ 1 := by
      have h2 : l ∣ g - (g - 1) := Nat.dvd_sub h hd
      have : g - (g - 1) = 1 := by omega
      rwa [this] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hgz : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
      rw [← this]; exact_mod_cast h4
    have hg2 : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg
    have key := Int.two_pow_sub_pow' (x := (g : ℤ)) (y := 1) δ hgz hg2
    have hpos : 1 ≤ g ^ δ := Nat.one_le_pow _ _ (by omega)
    have e1 : ((g : ℤ) ^ δ - 1 ^ δ) = ((g ^ δ - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hpos]; ring
    have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
    rw [e1, e2] at key
    have c2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [c2, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have n1 : g ^ δ - 1 ≠ 0 := by
      have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
      simp at this; omega
    rw [← padicValNat_eq_emultiplicity n1, ← padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0),
      ← padicValNat_eq_emultiplicity (by omega : δ ≠ 0)] at key
    exact_mod_cast key
  · have := padicValNat.pow_sub_pow (p := l) hodd (x := g) (y := 1) (by omega) hd hlg (n := δ) (by omega)
    simpa using this

/-- The primary parts in extension degree `δ` split according to whether
their primes divide the base residue group order. -/
theorem prime_power_order_count (g δ : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hδ : 1 ≤ δ) :
    ∑ l ∈ (g ^ δ - 1).primeFactors, l ^ padicValNat l (g ^ δ - 1) ≤
      δ * (g - 1) + (g ^ δ - 1) / (g - 1) := by
  classical
  set A := g - 1 with hA
  have hA0 : A ≠ 0 := by omega
  obtain ⟨B, hB⟩ : A ∣ g ^ δ - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 δ
  have n1 : g ^ δ - 1 ≠ 0 := by
    have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
    simp at this; omega
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB; exact n1 hB
  have hdiv : (g ^ δ - 1) / A = B := by rw [hB]; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, ← Finset.sum_filter_add_sum_filter_not _ (fun l => l ∣ A)]
  apply add_le_add
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ (δ * A).factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [lte_val g δ l hg h4 hδ hp hl.2, Nat.factorization_mul (by omega) hA0,
        Finsupp.add_apply, Nat.factorization_def _ hp, Nat.factorization_def _ hp, add_comm]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _
      (Nat.mul_ne_zero (by omega) hA0) ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have : 1 ≤ (δ * A).factorization l :=
        (hp.dvd_iff_one_le_factorization (Nat.mul_ne_zero (by omega) hA0)).1 (Dvd.dvd.mul_left hl.2 _)
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => ¬ l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ B.factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [← Nat.factorization_def _ hp, hB, Nat.factorization_mul hA0 hB0]
      have : A.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hl.2
      simp [this]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _ hB0 ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have hd : l ∣ B := by
        have := Nat.dvd_of_mem_primeFactors hl.1
        rw [hB] at this
        exact (hp.dvd_mul.1 this).resolve_left hl.2
      have : 1 ≤ B.factorization l := (hp.dvd_iff_one_le_factorization hB0).1 hd
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.prime_power_order_share
#print axioms WindowedLandauTheory.ConcN.prime_power_order_count
