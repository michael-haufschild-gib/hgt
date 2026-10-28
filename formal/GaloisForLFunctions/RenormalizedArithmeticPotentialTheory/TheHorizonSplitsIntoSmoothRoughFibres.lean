import GaloisForLFunctions.RHTower.SteinhausSmoothRoughSum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicMeasureTensorizesOverPrimes

/-!
# Smooth and rough fibres of the integer horizon

The literal smooth part fixes a fibre whose remaining coordinate is a rough
interval. The existing smooth/rough sum decomposition supplies the partition;
absorbing its product cutoff gives the exact quotient horizon on each fibre.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

theorem roughInterval_eq_prefix_filter (Q X : ℕ) :
    roughInterval Q X = (Icc 1 X).filter (fun k => ∀ p ∈ Nat.primesBelow Q, ¬p ∣ k) := by
  ext k
  rw [mem_roughInterval, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hk1, hkX, hrough⟩
    refine ⟨⟨hk1, hkX⟩, fun p hp hd => ?_⟩
    have hpp := Nat.mem_primesBelow.mp hp
    have := hrough p hpp.2 hd
    omega
  · rintro ⟨⟨hk1, hkX⟩, hrough⟩
    refine ⟨hk1, hkX, fun p hp hd => ?_⟩
    by_contra h
    exact hrough p (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩) hd

/-- Every finite real sum splits into its actual smooth-part fibres. -/
theorem sum_Icc_eq_smoothRough_fibres (Q N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, F n) =
      ∑ d ∈ Nat.smoothNumbersUpTo N Q, ∑ k ∈ roughInterval Q (N / d), F (d * k) := by
  classical
  have h := congrArg Complex.re
    (RHTower.sum_Icc_eq_smoothRough_sum Q N (fun n => (F n : ℂ)))
  have hreal : (∑ n ∈ Icc 1 N, F n) =
      ∑ k ∈ (Icc 1 N).filter (fun k => ∀ p ∈ Nat.primesBelow Q, ¬p ∣ k),
        ∑ d ∈ Nat.smoothNumbersUpTo N Q, if d * k ≤ N then F (d * k) else 0 := by
    simpa only [Complex.re_sum, apply_ite, Complex.ofReal_re, Complex.zero_re] using h
  rw [hreal, Finset.sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp hd).2)
  rw [← sum_filter]
  have hset : ((Icc 1 N).filter (fun k => ∀ p ∈ Nat.primesBelow Q, ¬p ∣ k)).filter
      (fun k => d * k ≤ N) = roughInterval Q (N / d) := by
    ext k
    rw [roughInterval_eq_prefix_filter]
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨hk1, _⟩, hkr⟩, hdk⟩
      exact ⟨⟨hk1, (Nat.le_div_iff_mul_le hd0).mpr (by simpa only [mul_comm] using hdk)⟩, hkr⟩
    · rintro ⟨⟨hk1, hkN⟩, hkr⟩
      exact ⟨⟨⟨hk1, hkN.trans (Nat.div_le_self _ _)⟩, hkr⟩,
        by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkN⟩
  rw [hset]

/-- Each rough coordinate has exactly the stated smooth part. -/
theorem smoothPart_mul_of_mem_rough_fibre {Q N d k : ℕ}
    (hd : d ∈ Nat.smoothNumbersUpTo N Q) (hk : k ∈ roughInterval Q (N / d)) :
    RHTower.Sieve.smoothPart (Q - 1) (d * k) = d := by
  have hk' := mem_filter.mp (roughInterval_eq_prefix_filter Q (N / d) ▸ hk)
  exact RHTower.sieveSmoothPart_mul_of_smooth_rough
    (Nat.mem_smoothNumbersUpTo.mp hd).2
    (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk'.1).1) hk'.2

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

