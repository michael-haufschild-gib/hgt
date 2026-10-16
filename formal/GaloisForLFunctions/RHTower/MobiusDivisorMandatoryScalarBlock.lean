import GaloisForLFunctions.RHTower.MobiusDivisorTerminalClockOrder

/-!
# Mandatory scalar insertion with its helper cost paid

A specified isolated prime can be included in a paid block whenever fresh
opposite source mass covers its singleton. The baseline precedes every helper.
The logarithmic reserve is retained at every prefix of the resulting order.
-/

noncomputable section
open Finset
namespace RHTower
namespace PaidExhaustion

private lemma square_paid_cover {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hw : ∀ p ∈ U, 0 ≤ w p) (hcover : h ≤ ∑ p ∈ U, w p) :
    ∃ L ⊆ U, h ≤ ∑ p ∈ L, w p ∧
      ((∑ p ∈ L, w p) - h)^2 ≤ ∑ p ∈ L, (w p)^2 := by
  obtain ⟨L, hLU, hlo, _, hsq⟩ := exists_mass_cover_with_square_reserve U w
    (∑ p ∈ U, w p) (sum_nonneg hw) h hh
    (fun p hp => ⟨hw p hp, single_le_sum hw hp⟩) hcover
  exact ⟨L, hLU, by linarith, hsq⟩

lemma mandatory_scalar_block {α : Type*} [DecidableEq α]
    (a : α → ℝ) (h : ℝ) (p : α) (U V : Finset α)
    (hpU : p ∉ U) (hpV : p ∉ V)
    (hU : ∀ q ∈ U, 0 ≤ a q) (hV : ∀ q ∈ V, a q ≤ 0)
    (hcoverU : |a p| ≤ ∑ q ∈ U, a q)
    (hcoverV : |a p| ≤ ∑ q ∈ V, -a q) :
    ∃ L : Finset α, p ∈ L ∧ L ⊆ insert p (U ∪ V) ∧
      L.card ≤ max U.card V.card + 1 ∧
      2*h*(∑ q ∈ L, a q) + (∑ q ∈ L, a q)^2 ≤ ∑ q ∈ L, (a q)^2 := by
  by_cases hgood : h*a p ≤ 0
  · refine ⟨{p}, by simp, by simp, by simp, ?_⟩
    simp only [sum_singleton]
    nlinarith only [hgood]
  have hbad : 0 < h*a p := lt_of_not_ge hgood
  rcases mul_pos_iff.mp hbad with ⟨hh, ha⟩ | ⟨hh, ha⟩
  · obtain ⟨L, hLV, hmass, hsq⟩ := square_paid_cover V (fun q => -a q) ha.le
      (fun q hq => neg_nonneg.mpr (hV q hq))
      (by simpa only [abs_of_pos ha] using hcoverV)
    have hpL : p ∉ L := fun hp => hpV (hLV hp)
    refine ⟨insert p L, mem_insert_self _ _,
      insert_subset_insert p (hLV.trans subset_union_right), ?_, ?_⟩
    · rw [card_insert_of_notMem hpL]
      exact Nat.add_le_add_right ((card_le_card hLV).trans (le_max_right _ _)) 1
    · simp only [sum_neg_distrib, neg_sq] at hmass hsq
      simp only [sum_insert hpL]
      have hm : h*(a p + ∑ q ∈ L, a q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hh.le (by linarith)
      nlinarith only [hsq, hm, sq_nonneg (a p)]
  · obtain ⟨L, hLU, hmass, hsq⟩ := square_paid_cover U a (neg_nonneg.mpr ha.le) hU
      (by simpa only [abs_of_neg ha] using hcoverU)
    have hpL : p ∉ L := fun hp => hpU (hLU hp)
    refine ⟨insert p L, mem_insert_self _ _,
      insert_subset_insert p (hLU.trans subset_union_left), ?_, ?_⟩
    · rw [card_insert_of_notMem hpL]
      exact Nat.add_le_add_right ((card_le_card hLU).trans (le_max_left _ _)) 1
    · simp only [sum_insert hpL]
      have hm : h*(a p + ∑ q ∈ L, a q) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hh.le (by linarith)
      nlinarith only [hsq, hm, sq_nonneg (a p)]

private lemma clock_reserve (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M P - mobiusDivisorSelectionEnergy M P =
      ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
        Real.log p * (mobiusDivisorSelectionFibre M P {p})^2 := by
  rw [mobiusDivisorFiniteClockEnergy_terminal M P hP,
    mobiusDivisorSelectionEnergy_terminal M P hP]
  simp_rw [add_mul, one_mul]
  rw [sum_add_distrib]
  ring

/-- Terminal insertion spends only additional nonnegative logarithmic reserve. -/
lemma clock_work_le_raw_work (M : ℕ) (P L : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M (P ∪ L) - mobiusDivisorFiniteClockEnergy 1 M P ≤
      mobiusDivisorSelectionEnergy M (P ∪ L) - mobiusDivisorSelectionEnergy M P := by
  have he := clock_reserve M P hP
  have hf := clock_reserve M (P ∪ L) (hP.trans subset_union_left)
  have hsub : mobiusDivisorSelectionPrimes M \ (P ∪ L) ⊆
      mobiusDivisorSelectionPrimes M \ P := by
    intro p hp
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,
      fun h => (mem_sdiff.mp hp).2 (mem_union_left L h)⟩
  have hs : (∑ p ∈ mobiusDivisorSelectionPrimes M \ (P ∪ L),
      Real.log p * (mobiusDivisorSelectionFibre M (P ∪ L) {p})^2) ≤
      ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
        Real.log p * (mobiusDivisorSelectionFibre M P {p})^2 := by
    calc
      _ = ∑ p ∈ mobiusDivisorSelectionPrimes M \ (P ∪ L),
          Real.log p * (mobiusDivisorSelectionFibre M P {p})^2 := by
        apply sum_congr rfl
        intro p hp
        rw [mobiusDivisorSelectionFibre_singleton_union_terminal M P L hP p,
          if_neg (fun h => (mem_sdiff.mp hp).2 (mem_union_right P h))]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (sq_nonneg _))
  linarith only [he, hf, hs]

/-- A mandatory actual prime and all its helpers have one paid prefix order.
Both energy comparisons use the inherited state before any helper insertion. -/
theorem mandatory_prime_block (M : ℕ) (P U V : Finset ℕ) (p n : ℕ)
    (hterminal : mobiusDivisorSmallSelectionPrimes M ⊆ P)
    (hdata : ∀ q ∈ insert p (U ∪ V), q.Prime ∧ q < M ∧ q ∉ P ∧
      mobiusDivisorSelectionPrimes (M/q+1) ⊆ P)
    (hpU : p ∉ U) (hpV : p ∉ V) (hUn : U.card ≤ n) (hVn : V.card ≤ n)
    (hU : ∀ q ∈ U, 0 ≤ mobiusDivisorSelectionFibre M P {q})
    (hV : ∀ q ∈ V, mobiusDivisorSelectionFibre M P {q} ≤ 0)
    (hcoverU : |mobiusDivisorSelectionFibre M P {p}| ≤
      ∑ q ∈ U, mobiusDivisorSelectionFibre M P {q})
    (hcoverV : |mobiusDivisorSelectionFibre M P {p}| ≤
      ∑ q ∈ V, -mobiusDivisorSelectionFibre M P {q}) :
    ∃ l : List ℕ, l.Nodup ∧ p ∈ l ∧ l.length ≤ n+1 ∧
      l.toFinset ⊆ insert p (U ∪ V) ∧
      ∀ j : ℕ, mobiusDivisorSelectionEnergy M (P ∪ (l.take j).toFinset) ≤
        mobiusDivisorSelectionEnergy M P ∧
        mobiusDivisorFiniteClockEnergy 1 M (P ∪ (l.take j).toFinset) ≤
          mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨L, hpL, hL, hLn, hpaid⟩ := mandatory_scalar_block
    (fun q => mobiusDivisorSelectionFibre M P {q})
    (mobiusDivisorSelectionFibre M P ∅) p U V hpU hpV hU hV hcoverU hcoverV
  have hLdata := fun q hq => hdata q (hL hq)
  have hend : mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorSelectionEnergy M P := by
    rw [mobiusDivisorSelectionEnergy_union_isolated M P L hLdata]
    linarith only [hpaid]
  obtain ⟨l, hnd, hset, hbound⟩ := exists_mobiusDivisorIsolatedPrimeOrder M P L hLdata
  refine ⟨l, hnd, List.mem_toFinset.mp (hset.symm ▸ hpL), ?_, hset ▸ hL, ?_⟩
  · have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
    rw [hset] at hcard
    omega
  · intro j
    have hj := hbound j
    rw [max_eq_left hend] at hj
    exact ⟨hj, by
      have hw := clock_work_le_raw_work M P (l.take j).toFinset hterminal
      linarith only [hj, hw]⟩

end PaidExhaustion
end RHTower
