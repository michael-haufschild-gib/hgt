import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileOddPrimeDisplacementLower
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileOddWindowActivePath

/-!
# Quantitative actual-source mismatch on odd-log active paths

Each adjacent prime pair on a late odd-log active path has one endpoint whose
matched-quantile displacement differs from the base prime by at least
`1/(8 sqrt B)`. The finite count theorem charges the full prime count to
these quantitative mismatches, proper prime-power separators, and one path
endpoint. No cofinal energy or RH bound is asserted.
-/

namespace RHTower

/-- Actual active atoms whose displacement from the base prime exceeds the
critical quantitative threshold of one odd-log window. -/
noncomputable def ccmOddLogWindowQuantitativeMismatchSet (A B : ℕ) : Finset ℕ :=
  (((Finset.Icc A B).filter IsPrimePow).filter
    (fun n => 1 / (8 * Real.sqrt B) ≤
      |ccmActualHeadMatchedQuantilePolarDisplacement n -
        ccmActualHeadMatchedQuantilePolarDisplacement 2|))

private theorem quantitative_countP_sortedFinset_eq_card_filter
    (S : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (S.sort (· ≤ ·)).countP (fun n => decide (Q n)) =
      (S.filter Q).card := by
  calc
    (S.sort (· ≤ ·)).countP (fun n => decide (Q n)) =
        Multiset.countP Q ((S.sort (· ≤ ·) : List ℕ) : Multiset ℕ) := by rfl
    _ = Multiset.countP Q S.val := by rw [Finset.sort_eq]
    _ = (S.filter Q).card := by
      rw [Multiset.countP_eq_card_filter]
      rfl

/-- The existing odd-window active path has no adjacent prime pair whose two
endpoints are both below the quantitative base-displacement threshold. -/
theorem ccmOddLogWindow_actualActivePath_noSmallPrimeEdge
    (A B t : ℕ) (hA3 : 3 ≤ A)
    (hAexp : Real.exp 2 ≤ (A : ℝ))
    (hloglo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (A : ℝ))
    (hloghi : (B : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4))
    (herror : ∀ p : ℕ, A ≤ p → p ≤ B →
      Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4) :
    sourceActiveNoCoherentPrimeEdge
      (fun n => n.Prime ∧ A ≤ n ∧ n ≤ B)
      (fun n => 1 / (8 * Real.sqrt B) ≤
        |ccmActualHeadMatchedQuantilePolarDisplacement n -
          ccmActualHeadMatchedQuantilePolarDisplacement 2|)
      (((Finset.Icc A B).filter IsPrimePow).sort (· ≤ ·)) := by
  classical
  let S : Finset ℕ := (Finset.Icc A B).filter IsPrimePow
  let P : ℕ → Prop := fun n => n.Prime ∧ A ≤ n ∧ n ≤ B
  let M : ℕ → Prop := fun n => 1 / (8 * Real.sqrt B) ≤
    |ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement 2|
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
  have haloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log a := by
    have haRle : (A : ℝ) ≤ a := by exact_mod_cast haA
    have h := Real.log_le_log (Real.exp_pos _)
      (hloglo.trans haRle)
    simpa only [Real.log_exp] using h
  have haloghi : Real.log a ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4 := by
    have haR : (0 : ℝ) < a := by exact_mod_cast ha.1.pos
    have h := Real.log_le_log haR
      ((by exact_mod_cast haB : (a : ℝ) ≤ B).trans hloghi)
    simpa only [Real.log_exp] using h
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
  have hsep := ccmActualHeadMatchedQuantile_oddActivePrimePair_displacement_lower
    ha.1 hb.1 hab ha2 haexp haloglo haloghi (herror a haA haB) hfree
  have haR : (0 : ℝ) < a := by exact_mod_cast ha.1.pos
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hsA : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr haR
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBR
  have hsle : Real.sqrt (a : ℝ) ≤ Real.sqrt (B : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast haB)
  have hthreshold : 1 / (4 * Real.sqrt (B : ℝ)) ≤
      1 / (4 * Real.sqrt (a : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 < 4 * Real.sqrt (a : ℝ))
    gcongr
  by_cases hMa : M a
  · exact Or.inl hMa
  · right
    by_contra hMb
    have haSmall : |ccmActualHeadMatchedQuantilePolarDisplacement a -
        ccmActualHeadMatchedQuantilePolarDisplacement 2| <
          1 / (8 * Real.sqrt B) := lt_of_not_ge hMa
    have hbSmall : |ccmActualHeadMatchedQuantilePolarDisplacement b -
        ccmActualHeadMatchedQuantilePolarDisplacement 2| <
          1 / (8 * Real.sqrt B) := lt_of_not_ge hMb
    have hupper :
        |ccmActualHeadMatchedQuantilePolarDisplacement b -
          ccmActualHeadMatchedQuantilePolarDisplacement a| <
            1 / (4 * Real.sqrt B) := by
      calc
        _ = |(ccmActualHeadMatchedQuantilePolarDisplacement b -
              ccmActualHeadMatchedQuantilePolarDisplacement 2) -
            (ccmActualHeadMatchedQuantilePolarDisplacement a -
              ccmActualHeadMatchedQuantilePolarDisplacement 2)| := by congr 1 <;> ring
        _ ≤ |ccmActualHeadMatchedQuantilePolarDisplacement b -
              ccmActualHeadMatchedQuantilePolarDisplacement 2| +
            |ccmActualHeadMatchedQuantilePolarDisplacement a -
              ccmActualHeadMatchedQuantilePolarDisplacement 2| := abs_sub _ _
        _ < 1 / (8 * Real.sqrt B) + 1 / (8 * Real.sqrt B) :=
          add_lt_add hbSmall haSmall
        _ = 1 / (4 * Real.sqrt B) := by ring
    exact (not_lt_of_ge hsep) (lt_of_lt_of_le hupper hthreshold)

/-- Prime supply on the literal finite odd-log window forces a quantitative
number of actual base-displacement mismatches after proper-power separators. -/
theorem ccmOddLogWindow_primeCount_le_twice_quantitativeMismatch_add_properPower
    (A B t : ℕ) (hA3 : 3 ≤ A)
    (hAexp : Real.exp 2 ≤ (A : ℝ))
    (hloglo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (A : ℝ))
    (hloghi : (B : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4))
    (herror : ∀ p : ℕ, A ≤ p → p ≤ B →
      Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4) :
    ((Finset.Icc A B).filter Nat.Prime).card ≤
      2 * (ccmOddLogWindowQuantitativeMismatchSet A B).card +
      (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card + 1 := by
  classical
  let S : Finset ℕ := (Finset.Icc A B).filter IsPrimePow
  let P : ℕ → Prop := fun n => n.Prime ∧ A ≤ n ∧ n ≤ B
  let M : ℕ → Prop := fun n => 1 / (8 * Real.sqrt B) ≤
    |ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement 2|
  have hchain : sourceActiveNoCoherentPrimeEdge P M (S.sort (· ≤ ·)) :=
    ccmOddLogWindow_actualActivePath_noSmallPrimeEdge
      A B t hA3 hAexp hloglo hloghi herror
  have hpath := sourceActivePath_prime_count_le_twice_mismatch_add_nonprime
    P M (S.sort (· ≤ ·)) hchain
  rw [quantitative_countP_sortedFinset_eq_card_filter,
    quantitative_countP_sortedFinset_eq_card_filter,
    quantitative_countP_sortedFinset_eq_card_filter] at hpath
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
  simpa only [ccmOddLogWindowQuantitativeMismatchSet] using hpath

end RHTower
