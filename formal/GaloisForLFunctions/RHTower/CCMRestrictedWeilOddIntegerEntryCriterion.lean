import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimeEntryComparison
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleCompressionRHCriterion

/-!
# Discrete integer-entry criterion for the odd Weil pole

Exact handoff and the chamber minimum principle reduce every odd inequality
above radius two to the starting value and integer-entry values. Combining
this reduction with the two-pole criterion gives an exact RH equivalence
retaining all even inequalities and the initial odd range.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- The positive aperture at which the integer `n≥2` enters the prime cutoff. -/
def ccmWeilIntegerEntry (n : ℕ) (hn : 2 ≤ n) : SuzukiPositiveAperture :=
  ⟨Real.log n/2,div_pos (Real.log_pos (by exact_mod_cast hn.trans_lt' (by norm_num : (1:ℕ) < 2))) (by norm_num)⟩

/-- Exact exponential coordinate of every integer-entry aperture. -/
theorem exp_two_mul_ccmWeilIntegerEntry (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (2*(ccmWeilIntegerEntry n hn).1) = n := by
  change Real.exp (2*(Real.log n/2)) = n
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  exact Real.exp_log (by exact_mod_cast (by omega : 0 < n))

/-- Exact integer cutoff at an entry aperture. -/
theorem floor_exp_two_mul_ccmWeilIntegerEntry (n : ℕ) (hn : 2 ≤ n) :
    ⌊Real.exp (2*(ccmWeilIntegerEntry n hn).1)⌋₊ = n := by
  rw [exp_two_mul_ccmWeilIntegerEntry,Nat.floor_natCast]

/-- Above any starting radius at least two, the continuum of actual odd-pole
inequalities is exactly its starting value and its integer-entry values. -/
theorem ccmWeilOddPole_nonneg_tail_iff_integer_entries (a : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) :
    (∀ c : SuzukiPositiveAperture, a.1 ≤ c.1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1))) ↔
    0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n), a.1 ≤ (ccmWeilIntegerEntry n hn).1 →
        0 ≤ ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
          (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1)) := by
  constructor
  · intro h
    exact ⟨h a le_rfl,fun n hn hle => h _ hle⟩
  · rintro ⟨hQa,hE⟩ c hac
    let N := ⌊Real.exp (2*c.1)⌋₊
    have hN : 2 ≤ N := Nat.le_floor (by
      have := Real.add_one_le_exp (2*c.1)
      norm_num at ⊢
      linarith)
    let l := ccmWeilIntegerEntry N hN
    let r := ccmWeilIntegerEntry (N+1) (by omega)
    have hel : Real.exp (2*l.1) = N := exp_two_mul_ccmWeilIntegerEntry _ _
    have her : Real.exp (2*r.1) = (N+1:ℕ) := exp_two_mul_ccmWeilIntegerEntry _ _
    have hlc : l.1 ≤ c.1 := by
      have := Nat.floor_le (Real.exp_pos (2*c.1)).le
      have hx : Real.exp (2*l.1) ≤ Real.exp (2*c.1) := by simpa only [hel] using this
      have := Real.exp_le_exp.mp hx
      linarith
    have hcr : c.1 < r.1 := by
      have hx : Real.exp (2*c.1) < Real.exp (2*r.1) := by
        rw [her,Nat.cast_add,Nat.cast_one]
        exact Nat.lt_floor_add_one _
      have := Real.exp_lt_exp.mp hx
      linarith
    have hQr := hE (N+1) (by omega) (le_trans hac hcr.le)
    by_cases hal : a.1 ≤ l.1
    · have hQl := hE N hN hal
      have hb : Real.exp (2*r.1) ≤ (⌊Real.exp (2*l.1)⌋₊:ℝ)+1 := by
        rw [her,hel,Nat.floor_natCast,Nat.cast_add,Nat.cast_one]
      exact (ccmWeilOddPole_nonneg_until_next_entry_iff_endpoints l r
        (ha.trans hal) (hlc.trans hcr.le) hb).mpr ⟨hQl,hQr⟩ c ⟨hlc,hcr.le⟩
    · have hla : l.1 ≤ a.1 := le_of_not_ge hal
      have hfloor : ⌊Real.exp (2*a.1)⌋₊ = N := by
        apply (Nat.floor_eq_iff (Real.exp_pos _).le).mpr
        constructor
        · rw [← hel]
          exact Real.exp_le_exp.mpr (by linarith)
        · exact (Real.exp_le_exp.mpr (show 2*a.1 ≤ 2*c.1 by linarith)).trans_lt
            (Nat.lt_floor_add_one _)
      have hb : Real.exp (2*r.1) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ)+1 := by
        rw [her,hfloor,Nat.cast_add,Nat.cast_one]
      exact (ccmWeilOddPole_nonneg_until_next_entry_iff_endpoints a r
        ha (hac.trans hcr.le) hb).mpr ⟨hQa,hQr⟩ c ⟨hac,hcr.le⟩

/-- The odd half of the exact pole criterion needs only the compact initial
range and the discrete integer-entry inequalities above radius two. -/
theorem ccmWeilOddPole_nonneg_iff_small_and_integer_entries :
    (∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ↔
    (∀ a : SuzukiPositiveAperture, a.1 ≤ 2 →
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n), 2 ≤ (ccmWeilIntegerEntry n hn).1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
        (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1))) := by
  constructor
  · intro h
    exact ⟨fun a _ => h a,fun n hn _ => h _⟩
  · rintro ⟨hsmall,hentry⟩ a
    by_cases ha : a.1 ≤ 2
    · exact hsmall a ha
    · let b : SuzukiPositiveAperture := ⟨2,by norm_num⟩
      apply (ccmWeilOddPole_nonneg_tail_iff_integer_entries b le_rfl).mpr
        ⟨hsmall b le_rfl,hentry⟩ a (le_of_not_ge ha)

/-- Exact RH criterion with the odd tail reduced to integer-entry inequalities.
The even inequalities and the initial odd range are retained explicitly. -/
theorem riemannHypothesis_iff_even_and_odd_integer_entries :
    RiemannHypothesis ↔
    (∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1)) ∧
    (∀ a : SuzukiPositiveAperture, a.1 ≤ 2 →
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n), 2 ≤ (ccmWeilIntegerEntry n hn).1 →
      0 ≤ ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
        (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1))) := by
  rw [riemannHypothesis_iff_parityPole_nonneg,forall_and,
    ccmWeilOddPole_nonneg_iff_small_and_integer_entries]

/-- Every negative actual odd-pole value on a tail above radius two forces a
negative starting value or a negative value at an integer-entry aperture. -/
theorem ccmWeilOddPole_negative_tail_iff_integer_entry (a : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) :
    (∃ c : SuzukiPositiveAperture, a.1 ≤ c.1 ∧
      ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c (-1)) < 0) ↔
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) < 0 ∨
      ∃ (n : ℕ) (hn : 2 ≤ n), a.1 ≤ (ccmWeilIntegerEntry n hn).1 ∧
        ccmRestrictedWeilSourceQuadratic (ccmWeilIntegerEntry n hn)
          (ccmPolarParityFormVector (ccmWeilIntegerEntry n hn) (-1)) < 0 := by
  have h := not_congr (ccmWeilOddPole_nonneg_tail_iff_integer_entries a ha)
  push Not at h
  simpa only [imp_iff_not_or,not_le] using h

end RHTower
