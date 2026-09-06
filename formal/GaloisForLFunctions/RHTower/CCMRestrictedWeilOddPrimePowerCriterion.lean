import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimePowerGap

/-!
# Genuine prime-power checkpoint criterion for the odd Weil pole

The nearest prime-power entries bracket every positive radius above two.
Exact comparison across their gap removes all zero-Mangoldt integer checks
from the odd tail. The resulting RH criterion retains the even inequalities
and the initial odd range, with no assumption on the desired checkpoint signs.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- The whole odd tail above radius two is controlled exactly by its starting
value and genuine prime-power entry values; zero-Mangoldt integers are dispensable. -/
theorem ccmWeilOddPole_nonneg_tail_iff_primePower_entries (a : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) :
    (∀ c : SuzukiPositiveAperture, a.1 ≤ c.1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1))) ↔
    0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n), IsPrimePow n → a.1 ≤ (ccmWeilIntegerEntry n hn).1 →
        0 ≤ ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
          (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1)) := by
  classical
  constructor
  · intro h
    exact ⟨h a le_rfl,fun n hn _ hle => h _ hle⟩
  · rintro ⟨hQa,hE⟩ c hac
    let N := ⌊Real.exp (2*c.1)⌋₊
    have hN : 2 ≤ N := Nat.le_floor (by
      have := Real.add_one_le_exp (2*c.1)
      norm_num at ⊢
      linarith)
    let p := Nat.findGreatest IsPrimePow N
    have hp : IsPrimePow p := Nat.findGreatest_spec hN Nat.prime_two.isPrimePow
    have hp2 : 2 ≤ p := Nat.le_findGreatest hN Nat.prime_two.isPrimePow
    have hpN : p ≤ N := Nat.findGreatest_le _
    have hex : ∃ q : ℕ, N < q ∧ IsPrimePow q := by
      obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (N+1)
      exact ⟨q,by omega,hprime.isPrimePow⟩
    let q := Nat.find hex
    have hq : N < q ∧ IsPrimePow q := Nat.find_spec hex
    have hq2 : 2 ≤ q := by omega
    let l := ccmWeilIntegerEntry p hp2
    let r := ccmWeilIntegerEntry q hq2
    have hel : Real.exp (2*l.1) = p := exp_two_mul_ccmWeilIntegerEntry _ _
    have her : Real.exp (2*r.1) = q := exp_two_mul_ccmWeilIntegerEntry _ _
    have hlc : l.1 ≤ c.1 := by
      have hx : Real.exp (2*l.1) ≤ Real.exp (2*c.1) := by
        rw [hel]
        exact (show (p:ℝ) ≤ (N:ℝ) by exact_mod_cast hpN).trans (Nat.floor_le (Real.exp_pos _).le)
      have := Real.exp_le_exp.mp hx
      linarith
    have hcr : c.1 < r.1 := by
      have hx : Real.exp (2*c.1) < Real.exp (2*r.1) := by
        rw [her]
        exact Nat.lt_of_floor_lt hq.1
      have := Real.exp_lt_exp.mp hx
      linarith
    have hfree : ∀ n : ℕ, 2 ≤ n → l.1 < Real.log n/2 → Real.log n/2 < r.1 → ¬IsPrimePow n := by
      intro n hn hln hnr hnprime
      have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hpn : p < n := by
        have hh := Real.exp_lt_exp.mpr (show 2*l.1 < Real.log n by linarith)
        rw [hel,Real.exp_log hnpos] at hh
        exact_mod_cast hh
      have hnq : n < q := by
        have hh := Real.exp_lt_exp.mpr (show Real.log n < 2*r.1 by linarith)
        rw [her,Real.exp_log hnpos] at hh
        exact_mod_cast hh
      by_cases hnN : n ≤ N
      · exact Nat.findGreatest_is_greatest hpn hnN hnprime
      · exact Nat.find_min hex hnq ⟨by omega,hnprime⟩
    have hQr := hE q hq2 hq.2 (hac.trans hcr.le)
    by_cases hal : a.1 ≤ l.1
    · exact (ccmWeilOddPole_nonneg_primePower_gap_iff_endpoints l r
        (ha.trans hal) (hlc.trans hcr.le) hfree).mpr ⟨hE p hp2 hp hal,hQr⟩ c ⟨hlc,hcr.le⟩
    · have hla : l.1 ≤ a.1 := le_of_not_ge hal
      have hfree' : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < r.1 → ¬IsPrimePow n := by
        intro n hn hna hnr
        exact hfree n hn (hla.trans_lt hna) hnr
      exact (ccmWeilOddPole_nonneg_primePower_gap_iff_endpoints a r
        ha (hac.trans hcr.le) hfree').mpr ⟨hQa,hQr⟩ c ⟨hac,hcr.le⟩

/-- Exact RH criterion retaining only genuine prime-power checkpoints on the odd
tail, together with all even inequalities and the initial odd range. -/
theorem riemannHypothesis_iff_even_and_odd_primePower_entries :
    RiemannHypothesis ↔
    (∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1)) ∧
    (∀ a : SuzukiPositiveAperture, a.1 ≤ 2 →
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n), IsPrimePow n → 2 ≤ (ccmWeilIntegerEntry n hn).1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
        (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1))) := by
  rw [riemannHypothesis_iff_parityPole_nonneg]
  constructor
  · intro h
    exact ⟨fun a => (h a).1,fun a _ => (h a).2,fun n hn _ _ => (h _).2⟩
  · rintro ⟨heven,hsmall,hentry⟩ a
    refine ⟨heven a,?_⟩
    by_cases ha : a.1 ≤ 2
    · exact hsmall a ha
    · let b : SuzukiPositiveAperture := ⟨2,by norm_num⟩
      exact (ccmWeilOddPole_nonneg_tail_iff_primePower_entries b le_rfl).mpr
        ⟨hsmall b le_rfl,hentry⟩ a (le_of_not_ge ha)

/-- Every negative odd tail witness forces a negative starting value or a
negative value at an actual prime-power entry. -/
theorem ccmWeilOddPole_negative_tail_iff_primePower_entry (a : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) :
    (∃ c : SuzukiPositiveAperture, a.1 ≤ c.1 ∧
      ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) < 0) ↔
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) < 0 ∨
      ∃ (n : ℕ) (hn : 2 ≤ n), IsPrimePow n ∧ a.1 ≤ (ccmWeilIntegerEntry n hn).1 ∧
        ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
          (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1)) < 0 := by
  have h := not_congr (ccmWeilOddPole_nonneg_tail_iff_primePower_entries a ha)
  push Not at h
  simpa only [imp_iff_not_or,not_le] using h

end RHTower
