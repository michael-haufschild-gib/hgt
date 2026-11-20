import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence

/-!
# Exponential moments of the energy radiated in unit time

The right tail is the sum of the nonnegative unit-step decrements.
Consequently a pointwise exponential bound for the radiated energy has
exactly the same rate as a bound for the entire tail. Exponential moments
of the decrements detect the open range of rates, including for pulses
with arbitrarily long stalls.
-/

noncomputable section
open Finset Filter
open scoped Topology

namespace GaloisForLFunctions.BlackHoleRingdown

/-- The full reflected tail is recovered by summing the subsequent, disjoint
unit intervals. The starting time can be any real number. -/
theorem unit_decrements_have_sum (h : CompactPulse) (T : ℝ) :
    HasSum (fun n : ℕ => stepDecrement h (T+n) 1) (tailEnergy h T) := by
  have hT : Tendsto (fun n : ℕ => T+(n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T tendsto_natCast_atTop_atTop
  have ht := tendsto_const_nhds (x := tailEnergy h T) |>.sub ((tendsto_tailEnergy_atTop h).comp hT)
  rw [sub_zero] at ht
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => stepDecrement_nonneg h (T+n) 1) _).mpr
  exact ht.congr fun k => by
    have he (n : ℕ) : stepDecrement h (T+n) 1 =
        tailEnergy h (T+n) - tailEnergy h (T+((n+1:ℕ):ℝ)) := by
      rw [← tailEnergy_sub_step h _ zero_le_one, Nat.cast_succ, add_assoc]
    simp_rw [he]
    simpa only [Function.comp_apply, Nat.cast_zero, add_zero] using
      (sum_range_sub' (fun n : ℕ => tailEnergy h (T+n)) k).symm

/-- Interpolation of a unit-grid upper bound for a decreasing tail. -/
private theorem tail_from_samples (h : CompactPulse) {b C : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hgrid : ∀ n : ℕ, tailEnergy h n ≤ C * Real.exp (-b*n)) (T : ℝ) (hT : 0 ≤ T) :
    tailEnergy h T ≤ (C*Real.exp b) * Real.exp (-b*T) := by
  let n := ⌊T⌋₊
  have hn : T < (n:ℝ)+1 := Nat.lt_floor_add_one T
  have he := Real.exp_le_exp.mpr (show -b*(n:ℝ) ≤ b+(-b*T) by
    linarith only [mul_le_mul_of_nonneg_left hn.le hb])
  rw [Real.exp_add] at he
  exact ((tailEnergy_anti h (Nat.floor_le hT)).trans (hgrid n)).trans
    ((mul_le_mul_of_nonneg_left he hC).trans_eq (mul_assoc ..).symm)

/-- A uniform exponential envelope on the unit releases recovers the
whole continuous-time envelope at exactly the same positive exponent. -/
theorem tail_decay_iff_unit_decrement_decay (h : CompactPulse) {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → tailEnergy h T ≤ C*Real.exp (-b*T)) ↔
      ∃ C : ℝ, ∀ n : ℕ, stepDecrement h n 1 ≤ C*Real.exp (-b*n) := by
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨C, fun n => ?_⟩
    rw [←tailEnergy_sub_step h _ zero_le_one]
    exact (sub_le_self _ (tailEnergy_nonneg _ _)).trans (hC _ (Nat.cast_nonneg _))
  · rintro ⟨C,hC⟩
    let q := Real.exp (-b)
    have hq : 0 ≤ q := (Real.exp_pos _).le
    have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)
    have hC₀ : 0 ≤ C := by
      exact (stepDecrement_nonneg h 0 1).trans (by simpa using hC 0)
    let D := C*(1-q)⁻¹
    have hD : 0 ≤ D := mul_nonneg hC₀ (inv_nonneg.mpr (sub_nonneg.mpr hq₁.le))
    refine ⟨D*Real.exp b, tail_from_samples h hb.le hD (fun n => ?_)⟩
    have hs := (unit_decrements_have_sum h n)
    let A := C*Real.exp (-b*(n:ℝ))
    have hgeom := (summable_geometric_of_lt_one hq hq₁).mul_left A
    have hterm (i : ℕ) : stepDecrement h ((n:ℝ)+i) 1 ≤ A*q^i := by
      have hi := hC (n+i)
      rw [Nat.cast_add, mul_add, Real.exp_add] at hi
      dsimp only [q,A]
      rwa [←Real.exp_nat_mul, mul_comm (i:ℝ) (-b), mul_assoc]
    have hw := hs.summable.tsum_le_tsum hterm hgeom
    rw [hs.tsum_eq, tsum_mul_left, tsum_geometric_of_lt_one hq hq₁] at hw
    exact hw.trans_eq (by dsimp only [A,D]; ring)

/-- A release envelope at b gives finite exponential moment at every smaller
exponent c. This is the geometric-series case of the subcritical integral
comparison used by Fino and Majdoub (arXiv:2611.24340, Lemma 2.1). -/
theorem summable_weighted_decrements_of_envelope (h : CompactPulse) {b c : ℝ}
    (hcb : c < b) (henv : ∃ C : ℝ, ∀ n : ℕ, stepDecrement h n 1 ≤ C*Real.exp (-b*n)) :
    Summable (fun n : ℕ => Real.exp (c*n)*stepDecrement h n 1) := by
  obtain ⟨C,hC⟩ := henv
  apply ((Real.summable_exp_nat_mul_iff.mpr (sub_neg.mpr hcb)).mul_left C).of_nonneg_of_le
    (fun n : ℕ => mul_nonneg (Real.exp_pos (c*n)).le (stepDecrement_nonneg h n 1))
  intro n
  calc _ ≤ Real.exp (c*n)*(C*Real.exp (-b*n)) := mul_le_mul_of_nonneg_left (hC n) (Real.exp_pos _).le
       _ = C*Real.exp ((n:ℝ)*(c-b)) := by
         rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- The actual exponential moment itself bounds each weighted release. -/
theorem release_le_weighted_moment (h : CompactPulse) {c : ℝ}
    (hs : Summable (fun n : ℕ => Real.exp (c*n)*stepDecrement h n 1)) (n : ℕ) :
    stepDecrement h n 1 ≤ (∑' j : ℕ, Real.exp (c*j)*stepDecrement h j 1)*Real.exp (-c*n) := by
  have hb := hs.sum_le_tsum {n} (fun i _ => mul_nonneg (Real.exp_pos _).le (stepDecrement_nonneg h i 1))
  simp only [sum_singleton] at hb
  have hw := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-c*(n:ℝ))).le
  rwa [mul_right_comm _ (stepDecrement h n 1), ←Real.exp_add,
    show c*(n:ℝ)+ -c*n = 0 by ring, Real.exp_zero, one_mul] at hw

/-- RH is equivalent to convergence of the positive generating series for
the energy released in unit intervals at every exponent below one half. -/
theorem rh_iff_unit_radiation_moments :
    RiemannHypothesis ↔ ∀ h : CompactPulse, ∀ b : ℝ, b < 1/2 →
      Summable (fun n : ℕ => Real.exp (b*n)*stepDecrement h n 1) := by
  rw [riemannHypothesis_iff_tailEnergy_decay.1]
  constructor
  · intro hr h b hb
    obtain ⟨c,hbc,hc⟩ := exists_between (max_lt hb (by norm_num : (0:ℝ)<1/2))
    have hc₀ := (le_max_right b 0).trans_lt hbc
    have hε : 0 < (1/2-c)/2 := by linarith only [hc]
    obtain ⟨C,hC⟩ := hr _ hε h
    apply summable_weighted_decrements_of_envelope h ((le_max_left ..).trans_lt hbc)
    apply (tail_decay_iff_unit_decrement_decay h hc₀).mp
    refine ⟨C,fun T hT => ?_⟩
    convert hC T hT using 3 <;> ring
  · intro hm ε hε h
    let b := 1/2-2*ε
    by_cases hb : 0 < b
    · have hs := hm h b (by dsimp only [b]; linarith only [hε])
      exact (tail_decay_iff_unit_decrement_decay h hb).mpr ⟨_,release_le_weighted_moment h hs⟩
    · refine ⟨tailEnergy h 0,fun T hT => ?_⟩
      apply (tailEnergy_anti h hT).trans
      apply le_mul_of_one_le_right (tailEnergy_nonneg _ _)
      exact Real.one_le_exp (mul_nonneg (neg_nonneg.mpr (le_of_not_gt hb)) hT)

end GaloisForLFunctions.BlackHoleRingdown
