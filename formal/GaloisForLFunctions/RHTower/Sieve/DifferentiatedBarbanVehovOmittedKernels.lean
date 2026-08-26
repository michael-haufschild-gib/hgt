import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedLcmExpansion

/-!
# Standard long-kernel form of the omitted detector-head boundary

The two boundary inequalities `L*q < k` and `L*r < k` are one lower endpoint
`L * max q r < k`. Thus every omitted-boundary kernel is an existing differentiated
Barban--Vehov long kernel with a pair-dependent lower endpoint.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Two complementary-divisor boundary inequalities collapse to their maximum endpoint. -/
theorem omittedBoundary_pair_iff_max (L q r k : ℕ) :
    (L * q < k ∧ L * r < k) ↔ L * max q r < k := by
  constructor
  · rintro ⟨hqk, hrk⟩
    rcases le_total q r with hqr | hrq
    · simpa [max_eq_right hqr] using hrk
    · simpa [max_eq_left hrq] using hqk
  · intro hk
    exact ⟨(Nat.mul_le_mul_left L (Nat.le_max_left q r)).trans_lt hk,
      (Nat.mul_le_mul_left L (Nat.le_max_right q r)).trans_lt hk⟩

/-- A doubly truncated lcm fibre is the standard fibre above the maximum lower endpoint. -/
theorem sum_omittedBoundary_lcm_eq_maxEndpoint
    {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    (L U q r : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
      if L * q < k ∧ L * r < k then f k else 0) =
      ∑ k ∈ (Finset.Ioc (L * max q r) U).filter
        (fun k => Nat.lcm q r ∣ k), f k := by
  simp_rw [omittedBoundary_pair_iff_max]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hLk, hkU⟩, hlcm⟩, hmaxk⟩
      exact ⟨⟨hmaxk, hkU⟩, hlcm⟩
    · rintro ⟨⟨hmaxk, hkU⟩, hlcm⟩
      have hLle : L ≤ L * max q r := by
        have hqmax : 1 ≤ max q r := hq.trans (Nat.le_max_left q r)
        simpa using Nat.mul_le_mul_left L hqmax
      exact ⟨⟨⟨hLle.trans_lt hmaxk, hkU⟩, hlcm⟩, hmaxk⟩
  · intro k hk
    rfl

theorem barbanVehovOmittedLongHarmonicKernel_eq_maxEndpoint
    (L U q r : ℕ) (hq : 1 ≤ q) :
    barbanVehovOmittedLongHarmonicKernel L U q r =
      barbanVehovLongHarmonicKernel (L * max q r) U q r := by
  exact sum_omittedBoundary_lcm_eq_maxEndpoint
    (fun k => 1 / (k : ℝ)) L U q r hq

theorem barbanVehovOmittedLongFirstLogKernel_eq_maxEndpoint
    (L U q r : ℕ) (hq : 1 ≤ q) :
    barbanVehovOmittedLongFirstLogKernel L U q r =
      barbanVehovLongFirstLogKernel (L * max q r) U q r := by
  exact sum_omittedBoundary_lcm_eq_maxEndpoint
    (fun k => Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)) L U q r hq

theorem barbanVehovOmittedLongSecondLogKernel_eq_maxEndpoint
    (L U q r : ℕ) (hq : 1 ≤ q) :
    barbanVehovOmittedLongSecondLogKernel L U q r =
      barbanVehovLongSecondLogKernel (L * max q r) U q r := by
  exact sum_omittedBoundary_lcm_eq_maxEndpoint
    (fun k => Real.log (((k / q : ℕ) : ℝ)) *
      Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)) L U q r hq

end

end RHTower.Sieve
