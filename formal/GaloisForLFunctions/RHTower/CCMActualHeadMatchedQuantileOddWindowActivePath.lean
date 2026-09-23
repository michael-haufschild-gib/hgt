import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileActivePathCount
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileActiveGapResonance

namespace RHTower

/-- Completeness of a sorted active path lets a local no-resonance law
propagate across every adjacent pair. -/
theorem sourceActiveNoCoherentPrimeEdge_of_sorted_complete
    (S : Finset ℕ) (P M : ℕ → Prop) (xs : List ℕ) (lo : ℕ)
    (hsorted : xs.Pairwise (· < ·))
    (hcomplete : ∀ k : ℕ, lo < k → k ∈ S → k ∈ xs)
    (hlower : ∀ a ∈ xs, lo < a)
    (hlocal : ∀ a b : ℕ, a < b →
      (∀ k : ℕ, a < k → k < b → k ∉ S) →
      P a → P b → M a ∨ M b) :
    sourceActiveNoCoherentPrimeEdge P M xs := by
  induction xs generalizing lo with
  | nil => trivial
  | cons a tail ih =>
    cases tail with
    | nil => trivial
    | cons b rest =>
      have hsorted' : (b :: rest).Pairwise (· < ·) :=
        (List.pairwise_cons.mp hsorted).2
      have ha_lt : ∀ k ∈ b :: rest, a < k :=
        (List.pairwise_cons.mp hsorted).1
      have hab : a < b := ha_lt b (by simp)
      have hno : ∀ k : ℕ, a < k → k < b → k ∉ S := by
        intro k hak hkb hkS
        have hlo_k : lo < k := (hlower a (by simp)).trans hak
        have hkMem := hcomplete k hlo_k hkS
        simp only [List.mem_cons] at hkMem
        rcases hkMem with hka | hkb' | hkRest
        · omega
        · omega
        · have hbk : b < k :=
            (List.pairwise_cons.mp hsorted').1 k hkRest
          omega
      have hcomplete' : ∀ k : ℕ, a < k → k ∈ S → k ∈ b :: rest := by
        intro k hak hkS
        have hlo_k : lo < k := (hlower a (by simp)).trans hak
        have hkMem := hcomplete k hlo_k hkS
        simp only [List.mem_cons] at hkMem
        rcases hkMem with hka | htail
        · omega
        · simpa only [List.mem_cons] using htail
      change (P a → P b → M a ∨ M b) ∧
        sourceActiveNoCoherentPrimeEdge P M (b :: rest)
      exact ⟨hlocal a b hab hno,
        ih a hsorted' hcomplete' ha_lt⟩

/-- Every adjacent prime pair in the complete, sorted, actual prime-power
window obeys the odd-window resonance exclusion, so one endpoint is a
literal base-displacement mismatch. -/
theorem ccmOddLogWindow_actualActivePath_noCoherentPrimeEdge
    (A B t : ℕ) (hA3 : 3 ≤ A)
    (hAexp : Real.exp 2 ≤ (A : ℝ))
    (hloglo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (A : ℝ))
    (hloghi : (B : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4))
    (herror : ∀ p : ℕ, A ≤ p → p ≤ B →
      Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4) :
    sourceActiveNoCoherentPrimeEdge
      (fun n => n.Prime ∧ A ≤ n ∧ n ≤ B)
      (fun n => ccmActualHeadMatchedQuantilePolarDisplacement n ≠
        ccmActualHeadMatchedQuantilePolarDisplacement 2)
      (((Finset.Icc A B).filter IsPrimePow).sort (· ≤ ·)) := by
  classical
  let S : Finset ℕ := (Finset.Icc A B).filter IsPrimePow
  let P : ℕ → Prop := fun n => n.Prime ∧ A ≤ n ∧ n ≤ B
  let M : ℕ → Prop := fun n =>
    ccmActualHeadMatchedQuantilePolarDisplacement n ≠
      ccmActualHeadMatchedQuantilePolarDisplacement 2
  change sourceActiveNoCoherentPrimeEdge P M (S.sort (· ≤ ·))
  have hsorted : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort S).pairwise
  have hcomplete : ∀ k : ℕ, 0 < k → k ∈ S → k ∈ S.sort (· ≤ ·) := by
    intro k _ hk
    exact (Finset.mem_sort (r := (· ≤ ·))).mpr hk
  have hlower : ∀ a ∈ S.sort (· ≤ ·), 0 < a := by
    intro a ha
    have haS : a ∈ S := (Finset.mem_sort (r := (· ≤ ·))).mp ha
    have hapow : IsPrimePow a := (Finset.mem_filter.mp haS).2
    have ha1 : 1 < a := IsPrimePow.one_lt hapow
    omega
  apply sourceActiveNoCoherentPrimeEdge_of_sorted_complete
    S P M (S.sort (· ≤ ·)) 0 hsorted hcomplete hlower
  intro a b hab hno ha hb
  have haA : A ≤ a := ha.2.1
  have haB : a ≤ B := ha.2.2
  have hbB : b ≤ B := hb.2.2
  have ha2 : a ≠ 2 := by omega
  have haexp : Real.exp 2 ≤ (a : ℝ) :=
    hAexp.trans (by exact_mod_cast haA)
  have haloglo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (a : ℝ) :=
    hloglo.trans (by exact_mod_cast haA)
  have haloghi : (a : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4) := by
    calc
      (a : ℝ) ≤ (B : ℝ) := by exact_mod_cast haB
      _ ≤ _ := hloghi
  have hfree : ∀ k : ℕ, a < k → k < b →
      criticalMellinAtomWeight k = 0 := by
    intro k hak hkb
    by_cases hkpow : IsPrimePow k
    · have hkS : k ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ?_, hkpow⟩
        omega
      exact False.elim (hno k hak hkb hkS)
    · rw [criticalMellinAtomWeight_eq_div_sqrt,
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hkpow]
      simp
  have hneq := ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_exp_window
    ha.1 hb.1 hab ha2 haexp haloglo haloghi
    (herror a haA haB) hfree
  by_cases hMa : M a
  · exact Or.inl hMa
  · right
    intro hMb
    have hea : ccmActualHeadMatchedQuantilePolarDisplacement a =
        ccmActualHeadMatchedQuantilePolarDisplacement 2 :=
      of_not_not hMa
    have heb : ccmActualHeadMatchedQuantilePolarDisplacement b =
        ccmActualHeadMatchedQuantilePolarDisplacement 2 :=
      hMb
    exact hneq (heb.trans hea.symm)

private theorem countP_sortedFinset_eq_card_filter
    (S : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (S.sort (· ≤ ·)).countP (fun n => decide (Q n)) =
      (S.filter Q).card := by
  calc
    (S.sort (· ≤ ·)).countP (fun n => decide (Q n)) =
        Multiset.countP Q ((S.sort (· ≤ ·) : List ℕ) : Multiset ℕ) := by
          rfl
    _ = Multiset.countP Q S.val := by rw [Finset.sort_eq]
    _ = (S.filter Q).card := by
      rw [Multiset.countP_eq_card_filter]
      rfl

/-- Exact finite arithmetic conversion: odd-log active prime windows charge
their full prime count to literal base-displacement mismatches, apart from
proper prime-power separators and one endpoint. -/
theorem ccmOddLogWindow_primeCount_le_twice_baseMismatch_add_properPower
    (A B t : ℕ) (hA3 : 3 ≤ A)
    (hAexp : Real.exp 2 ≤ (A : ℝ))
    (hloglo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (A : ℝ))
    (hloghi : (B : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4))
    (herror : ∀ p : ℕ, A ≤ p → p ≤ B →
      Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4) :
    ((Finset.Icc A B).filter Nat.Prime).card ≤
      2 * (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ccmActualHeadMatchedQuantilePolarDisplacement n ≠
          ccmActualHeadMatchedQuantilePolarDisplacement 2)).card +
      (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card + 1 := by
  classical
  let S : Finset ℕ := (Finset.Icc A B).filter IsPrimePow
  let P : ℕ → Prop := fun n => n.Prime ∧ A ≤ n ∧ n ≤ B
  let M : ℕ → Prop := fun n =>
    ccmActualHeadMatchedQuantilePolarDisplacement n ≠
      ccmActualHeadMatchedQuantilePolarDisplacement 2
  have hchain : sourceActiveNoCoherentPrimeEdge P M (S.sort (· ≤ ·)) :=
    ccmOddLogWindow_actualActivePath_noCoherentPrimeEdge
      A B t hA3 hAexp hloglo hloghi herror
  have hpath := sourceActivePath_prime_count_le_twice_mismatch_add_nonprime
    P M (S.sort (· ≤ ·)) hchain
  have hP := countP_sortedFinset_eq_card_filter S P
  have hM := countP_sortedFinset_eq_card_filter S M
  have hN := countP_sortedFinset_eq_card_filter S (fun n => ¬ P n)
  rw [hP, hM, hN] at hpath
  have hprimeSet : S.filter P = (Finset.Icc A B).filter Nat.Prime := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS, hp⟩ := Finset.mem_filter.mp hn
      have hwin : n ∈ Finset.Icc A B := (Finset.mem_filter.mp hnS).1
      exact Finset.mem_filter.mpr ⟨hwin, hp.1⟩
    · intro hn
      obtain ⟨hwin, hp⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hwin, hp.prime.isPrimePow⟩,
        ⟨hp, (Finset.mem_Icc.mp hwin).1, (Finset.mem_Icc.mp hwin).2⟩⟩
  have hnonprimeSet : S.filter (fun n => ¬ P n) =
      S.filter (fun n => ¬ n.Prime) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      have hwin : n ∈ Finset.Icc A B := (Finset.mem_filter.mp hnS).1
      exact Finset.mem_filter.mpr
        ⟨hnS, fun hp => hnP ⟨hp, (Finset.mem_Icc.mp hwin).1,
          (Finset.mem_Icc.mp hwin).2⟩⟩
    · intro hn
      obtain ⟨hnS, hnprime⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnS, fun hp => hnprime hp.1⟩
  change (S.filter P).card ≤
    2 * (S.filter M).card +
      (S.filter (fun n => ¬ P n)).card + 1 at hpath
  rw [hprimeSet, hnonprimeSet] at hpath
  exact hpath

end RHTower
