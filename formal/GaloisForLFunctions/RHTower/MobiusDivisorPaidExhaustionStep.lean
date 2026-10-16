import GaloisForLFunctions.RHTower.MobiusDivisorExhaustionSignedSupply

/-!
# A paid extension over every admissible inherited core

The state includes all earlier primes, and its cardinality accounts for every
helper previously consumed. No restriction is imposed on its receiving head.
-/

noncomputable section
open Finset
namespace RHTower.PaidExhaustion

private lemma fresh_subset (U P : Finset ℕ) (n t : ℕ)
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hP : P.card ≤ 2*n*t)
    (hU : 4*n*t ≤ U.card) :
    ∃ S : Finset ℕ, S ⊆ U \ P ∧ S.card = n := by
  have hsub : U ⊆ (U \ P) ∪ P := by
    intro q hq
    by_cases h : q ∈ P
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hq,h⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  apply exists_subset_card_eq
  have hnt : n ≤ n*t := by nlinarith
  nlinarith

private lemma terminal_of_core (A r : ℕ) (P : Finset ℕ) (hAr : A < r)
    (hcore : ∀ q : ℕ, q.Prime → q < r → q ∈ P) :
    mobiusDivisorSmallSelectionPrimes (A*r) ⊆ P := by
  intro q hq
  obtain ⟨hq, hsq⟩ := mem_filter.mp hq
  have hqp := (mem_filter.mp hq).2
  apply hcore q hqp
  by_contra h
  have hqr : r ≤ q := by omega
  have hrr : r*r ≤ q*q := Nat.mul_self_le_mul_self hqr
  nlinarith

private lemma child_core (A r q : ℕ) (P : Finset ℕ) (hr : 0 < r)
    (hAr : A+1 < r) (hrq : r ≤ q)
    (hcore : ∀ s : ℕ, s.Prime → s < r → s ∈ P) :
    mobiusDivisorSelectionPrimes (A*r/q+1) ⊆ P := by
  have hq : 0 < q := hr.trans_le hrq
  have hd : A*r/q < A+1 := (Nat.div_lt_iff_lt_mul hq).mpr
    ((Nat.mul_le_mul_left A hrq).trans_lt
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self A) hq))
  intro s hs
  obtain ⟨hsr, hsp⟩ := mem_filter.mp hs
  have hslt := mem_range.mp hsr
  exact hcore s hsp (by omega)

/-- Either the mandatory prime was already paid by an earlier block, or one
fresh block processes it with every raw and logarithmic prefix paid. -/
theorem paid_extension (w : PrimeCapacity) (r : ℕ) (P : Finset ℕ)
    (hrp : r.Prime) (hr : w.threshold ≤ r)
    (hcore : ∀ q : ℕ, q.Prime → q < r → q ∈ P)
    (hsize : P.card ≤ 2*w.budget*Nat.primeCounting r) :
    ∃ l : List ℕ, l.Nodup ∧ l.length ≤ 2*w.budget ∧
      (∀ q ∈ l, q.Prime ∧ r ≤ q ∧ q < w.factor*r ∧ q ∉ P) ∧
      r ∈ P ∪ l.toFinset ∧
      ∀ j : ℕ, mobiusDivisorSelectionEnergy (w.factor*r) (P ∪ (l.take j).toFinset) ≤
        mobiusDivisorSelectionEnergy (w.factor*r) P ∧
        mobiusDivisorFiniteClockEnergy 1 (w.factor*r) (P ∪ (l.take j).toFinset) ≤
          mobiusDivisorFiniteClockEnergy 1 (w.factor*r) P := by
  classical
  by_cases hrP : r ∈ P
  · refine ⟨[], by simp, by simp, by simp, by simpa using hrP, ?_⟩
    intro j
    simp
  have hAr : w.factor+1 < r := w.threshold_large.trans_le hr
  have hpi : 1 ≤ Nat.primeCounting r := by
    have hne : Nat.primeCounting r ≠ 0 := by
      intro h
      have := Nat.primeCounting_eq_zero_iff.mp h
      have := hrp.two_le
      omega
    omega
  obtain ⟨U,V,hU,hV,hUdata,hVdata⟩ := w.supply r hr
  obtain ⟨S,hS,hSn⟩ := fresh_subset U P w.budget (Nat.primeCounting r)
    w.budget_pos hpi hsize hU
  obtain ⟨T,hT,hTn⟩ := fresh_subset V P w.budget (Nat.primeCounting r)
    w.budget_pos hpi hsize hV
  have hSdata (q : ℕ) (hq : q ∈ S) := hUdata q (mem_sdiff.mp (hS hq)).1
  have hTdata (q : ℕ) (hq : q ∈ T) := hVdata q (mem_sdiff.mp (hT hq)).1
  have hSfresh (q : ℕ) (hq : q ∈ S) := (mem_sdiff.mp (hS hq)).2
  have hTfresh (q : ℕ) (hq : q ∈ T) := (mem_sdiff.mp (hT hq)).2
  have hdata : ∀ q ∈ insert r (S ∪ T), q.Prime ∧ q < w.factor*r ∧ q ∉ P ∧
      mobiusDivisorSelectionPrimes (w.factor*r/q+1) ⊆ P := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · refine ⟨hrp, ?_, hrP, child_core _ _ _ P hrp.pos hAr le_rfl hcore⟩
      have := w.factor_large
      nlinarith [hrp.pos]
    · rcases mem_union.mp hq with hq | hq
      · obtain ⟨hp, hqr, hqM, _⟩ := hSdata q hq
        exact ⟨hp,hqM,hSfresh q hq,child_core _ _ _ P hrp.pos hAr hqr.le hcore⟩
      · obtain ⟨hp, hqr, hqM, _⟩ := hTdata q hq
        exact ⟨hp,hqM,hTfresh q hq,child_core _ _ _ P hrp.pos hAr hqr.le hcore⟩
  have he (q : ℕ) (hq : q ∈ insert r (S ∪ T)) :
      mobiusDivisorSelectionFibre (w.factor*r) P {q} = singletonSource (w.factor*r) q :=
    singleton_eq_source _ P (hdata q hq).1 (hdata q hq).2.2.1 (hdata q hq).2.2.2
  have hrS : r ∉ S := by intro h; exact (hSdata r h).2.1.ne rfl
  have hrT : r ∉ T := by intro h; exact (hTdata r h).2.1.ne rfl
  have hnR : (0:ℝ) < w.budget := by exact_mod_cast (show 0<w.budget from w.budget_pos)
  have hSsign (q : ℕ) (hq : q ∈ S) : 0 ≤ mobiusDivisorSelectionFibre (w.factor*r) P {q} := by
    rw [he q (mem_insert_of_mem (mem_union_left _ hq))]
    have hh := (hSdata q hq).2.2.2
    have habs := abs_nonneg (singletonSource (w.factor*r) r)
    nlinarith only [hh,habs,hnR]
  have hTsign (q : ℕ) (hq : q ∈ T) : mobiusDivisorSelectionFibre (w.factor*r) P {q} ≤ 0 := by
    rw [he q (mem_insert_of_mem (mem_union_right _ hq))]
    have hh := (hTdata q hq).2.2.2
    have habs := abs_nonneg (singletonSource (w.factor*r) r)
    nlinarith only [hh,habs,hnR]
  have hcoverS : |mobiusDivisorSelectionFibre (w.factor*r) P {r}| ≤
      ∑ q ∈ S, mobiusDivisorSelectionFibre (w.factor*r) P {q} := by
    rw [he r (mem_insert_self _ _)]
    have hh := sum_le_sum (fun q hq => (hSdata q hq).2.2.2)
    simp only [sum_const,nsmul_eq_mul,hSn,← mul_sum] at hh
    have heS : (∑ q ∈ S, mobiusDivisorSelectionFibre (w.factor*r) P {q}) =
        ∑ q ∈ S, singletonSource (w.factor*r) q :=
      sum_congr rfl (fun q hq => he q (mem_insert_of_mem (mem_union_left _ hq)))
    rw [heS]
    exact le_of_mul_le_mul_left hh hnR
  have hcoverT : |mobiusDivisorSelectionFibre (w.factor*r) P {r}| ≤
      ∑ q ∈ T, -mobiusDivisorSelectionFibre (w.factor*r) P {q} := by
    rw [he r (mem_insert_self _ _)]
    have hh := sum_le_sum (fun q hq => (hTdata q hq).2.2.2)
    simp only [sum_const,nsmul_eq_mul,hTn,← mul_sum] at hh
    have heT : (∑ q ∈ T, -mobiusDivisorSelectionFibre (w.factor*r) P {q}) =
        ∑ q ∈ T, -singletonSource (w.factor*r) q :=
      sum_congr rfl (fun q hq => congrArg Neg.neg
        (he q (mem_insert_of_mem (mem_union_right _ hq))))
    rw [heT]
    exact le_of_mul_le_mul_left hh hnR
  obtain ⟨l,hnd,hrl,hln,hl,hpaid⟩ := mandatory_prime_block (w.factor*r) P S T r w.budget
    (terminal_of_core _ _ P (by omega) hcore) hdata hrS hrT hSn.le hTn.le
    hSsign hTsign hcoverS hcoverT
  refine ⟨l,hnd,by have := w.budget_pos; omega,?_,mem_union_right _ (List.mem_toFinset.mpr hrl),hpaid⟩
  intro q hql
  have hq := hl (List.mem_toFinset.mpr hql)
  have hd := hdata q hq
  refine ⟨hd.1,?_,hd.2.1,hd.2.2.1⟩
  rcases mem_insert.mp hq with rfl | hq
  · exact le_rfl
  · exact (mem_union.mp hq).elim (fun h => (hSdata q h).2.1.le)
      (fun h => (hTdata q h).2.1.le)

end RHTower.PaidExhaustion
