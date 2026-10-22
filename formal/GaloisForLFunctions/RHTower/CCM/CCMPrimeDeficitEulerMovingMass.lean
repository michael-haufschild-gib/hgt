import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerCriticalMass
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerPrimeCausality
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Large moving critical mass before surviving-prime force enters

At cutoff `m = n^2`, primes between `n^2` and `n^3` give rough critical
mass at least `n/6`, once `n` exceeds a fixed Mertens threshold. Their
product square gives renewal mass at least `n^2/36` at horizon `n^6`.
This horizon is still inside the cubic causal window, where the surviving
prime force is exactly zero. Thus that causal cancellation alone does not
give a positive critical contraction, even for moving factorial moduli.

The signed deficit estimate and the TG source-to-zero bound remain open.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmEulerMovingMassLogThreshold : ℝ :=
  4 * ((Real.log 4 + 4) + (8 + Mertens.mertensTail))

/-- A growing prime window survives the moving factorial cutoff. -/
theorem ccmEulerCriticalMass_factorial_square_cube_lower (n : ℕ)
    (hn : 2 ≤ n) (hlog : ccmEulerMovingMassLogThreshold ≤ Real.log n) :
    (n : ℝ) / 6 ≤ ccmEulerCriticalMass (n ^ 2).factorial (n ^ 3) := by
  classical
  let A := (Finset.Icc 1 (n ^ 2)).filter Nat.Prime
  let B := (Finset.Icc 1 (n ^ 3)).filter Nat.Prime
  let W := B \ A
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hpow : n ^ 2 ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul_left (n ^ 2) hn1]
  have hAB : A ⊆ B := by
    intro p hp
    simp only [A, B, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hpow⟩, hp.2⟩
  have hsplit :
      (∑ p ∈ W, Real.log p / (p : ℝ)) +
        (∑ p ∈ A, Real.log p / (p : ℝ)) =
          ∑ p ∈ B, Real.log p / (p : ℝ) := Finset.sum_sdiff hAB
  have hA := (abs_le.mp (Mertens.mertens_first_prime (n ^ 2)
    (by have hpos := pow_pos hn0 2; omega))).2
  have hB := (abs_le.mp (Mertens.mertens_first_prime (n ^ 3)
    (by have hpos := pow_pos hn0 3; omega))).1
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hA hB
  have hwindow : Real.log (n : ℝ) / 2 ≤ ∑ p ∈ W, Real.log p / (p : ℝ) := by
    change ccmEulerMovingMassLogThreshold ≤ _ at hlog
    unfold ccmEulerMovingMassLogThreshold at hlog
    change (∑ p ∈ A, Real.log p / (p : ℝ)) - 2 * Real.log n ≤ _ at hA
    change _ ≤ (∑ p ∈ B, Real.log p / (p : ℝ)) - 3 * Real.log n at hB
    linarith
  have hW : W ⊆ Finset.Icc 1 (n ^ 3) := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
  have hterm (p : ℕ) (hp : p ∈ W) :
      (n : ℝ) * (Real.log p / p) ≤
        (3 * Real.log n) * (ccmEulerRough (n ^ 2).factorial p / Real.sqrt p) := by
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hpB
    have hplow : n ^ 2 < p := by
      by_contra h
      exact hpA (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpI).1, by omega⟩, hpprime⟩)
    have hcop : p.Coprime (n ^ 2).factorial :=
      hpprime.coprime_iff_not_dvd.mpr (fun h =>
        (not_le_of_gt hplow) (hpprime.dvd_factorial.mp h))
    have hrough : ccmEulerRough (n ^ 2).factorial p = 1 :=
      if_pos ⟨hpprime.one_lt, hcop⟩
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
    have hns : (n : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by exact_mod_cast hplow.le)
    have hlp : Real.log (p : ℝ) ≤ 3 * Real.log n := by
      have h := Real.log_le_log hpR
        (show (p : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast (Finset.mem_Icc.mp hpI).2)
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    rw [hrough]
    calc
      (n : ℝ) * (Real.log p / p) =
          ((n : ℝ) / Real.sqrt p) * (Real.log p / Real.sqrt p) := by
        rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hpR.le]
        ring
      _ ≤ 1 * (Real.log p / Real.sqrt p) :=
        mul_le_mul_of_nonneg_right ((div_le_one hs).mpr hns)
          (div_nonneg (Real.log_natCast_nonneg p) hs.le)
      _ ≤ (3 * Real.log n) * (1 / Real.sqrt p) := by
        simpa only [one_mul, mul_one_div] using div_le_div_of_nonneg_right hlp hs.le
  have hupper :
      (n : ℝ) * (∑ p ∈ W, Real.log p / (p : ℝ)) ≤
        (3 * Real.log n) * ccmEulerCriticalMass (n ^ 2).factorial (n ^ 3) := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum hterm).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg hW
      (fun p _ _ => div_nonneg (ccmEulerRough_nonneg _ _) (Real.sqrt_nonneg _))
  apply (mul_le_mul_iff_right₀ hln).mp
  have hlower := mul_le_mul_of_nonneg_left hwindow (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hupper, hlower]

/-- The complete ordered prime-pair square lies below the cubic causal boundary. -/
theorem ccmEulerRenewalCriticalMass_factorial_square_six_lower (n : ℕ)
    (hn : 2 ≤ n) (hlog : ccmEulerMovingMassLogThreshold ≤ Real.log n) :
    (n : ℝ) ^ 2 / 36 ≤ ccmEulerRenewalCriticalMass (n ^ 2).factorial (n ^ 6) := by
  have hmass := ccmEulerCriticalMass_factorial_square_cube_lower n hn hlog
  have hsq : ((n : ℝ) / 6) ^ 2 ≤
      ccmEulerCriticalMass (n ^ 2).factorial (n ^ 3) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hmass 2
  have hprod := ccmEulerCriticalMass_sq_le_renewalCriticalMass (n ^ 2).factorial (n ^ 3)
  have heq : (n ^ 3) ^ 2 = n ^ 6 := by ring
  rw [heq] at hprod
  nlinarith only [hsq, hprod]

/-- Arbitrarily large positive critical mass coexists with exactly zero surviving-prime
work, for actual moving factorial cutoffs inside their cubic causal windows. -/
theorem exists_ccmEulerMoving_cubic_window_large_mass (B : ℝ) :
    ∃ m N : ℕ, 0 < m ∧ 0 < N ∧ N < (m + 1) ^ 3 ∧
      B < ccmEulerRenewalCriticalMass m.factorial N ∧
      ccmEulerSurvivingWork m.factorial (Real.log N) = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (2 : ℝ) (max (Real.exp ccmEulerMovingMassLogThreshold) (36 * (|B| + 1))))
  have hnR : (2 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn2 : 2 ≤ n := by exact_mod_cast hnR.le
  have hn0 : 0 < n := by omega
  have hnexp : Real.exp ccmEulerMovingMassLogThreshold ≤ (n : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn.le
  have hlog : ccmEulerMovingMassLogThreshold ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log
      (Real.exp_pos ccmEulerMovingMassLogThreshold) hnexp
  have hnB : 36 * (|B| + 1) < (n : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hn
  have hB : B < (n : ℝ) ^ 2 / 36 := by nlinarith [le_abs_self B]
  have hwindow : n ^ 6 < (n ^ 2 + 1) ^ 3 := by
    have h := Nat.pow_lt_pow_left (Nat.lt_succ_self (n ^ 2)) (by decide : 3 ≠ 0)
    convert h using 1
    ring
  refine ⟨n ^ 2, n ^ 6, by positivity, by positivity, hwindow,
    hB.trans_le (ccmEulerRenewalCriticalMass_factorial_square_six_lower n hn2 hlog), ?_⟩
  apply ccmEulerSurvivingWork_factorial_eq_zero_before_cubic
  rw [Real.exp_log (by positivity : (0 : ℝ) < (n ^ 6 : ℕ)), Nat.floor_natCast]
  exact hwindow

end RHTower
