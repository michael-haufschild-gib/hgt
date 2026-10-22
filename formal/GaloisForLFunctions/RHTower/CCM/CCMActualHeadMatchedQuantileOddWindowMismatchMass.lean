import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileOddWindowCofinalCount
import GaloisForLFunctions.RHTower.Sieve.ProperPrimePowerCount

namespace RHTower

/-- Literal prime-power vertices in a window whose completed-source
displacement differs from the base prime. -/
noncomputable def ccmOddLogWindowMismatchSet (A B : ℕ) : Finset ℕ :=
  (((Finset.Icc A B).filter IsPrimePow).filter
    (fun n => ccmActualHeadMatchedQuantilePolarDisplacement n ≠
      ccmActualHeadMatchedQuantilePolarDisplacement 2))

private theorem mismatch_weight_ge
    {B n : ℕ} (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : n ≤ B)
    (hpow : IsPrimePow n) :
    Real.log 2 / Real.sqrt B ≤ criticalMellinAtomWeight n := by
  have hmin : 2 ≤ Nat.minFac n :=
    (Nat.minFac_prime (IsPrimePow.ne_one hpow)).two_le
  have hv : Real.log 2 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpow]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hmin)
  have hsN : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hsB : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < B))
  have hsLe : Real.sqrt (n : ℝ) ≤ Real.sqrt (B : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnB)
  have hl0 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  apply (div_le_div_iff₀ hsB hsN).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hv) (le_of_lt hsB),
    mul_nonneg hl0 (sub_nonneg.mpr hsLe)]

private theorem mismatch_mass_ge_count
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ((ccmOddLogWindowMismatchSet A B).card : ℝ) * (Real.log 2 / Real.sqrt B) ≤
      ∑ n ∈ ccmOddLogWindowMismatchSet A B, criticalMellinAtomWeight n := by
  classical
  calc
    ((ccmOddLogWindowMismatchSet A B).card : ℝ) * (Real.log 2 / Real.sqrt B) =
        ∑ _n ∈ ccmOddLogWindowMismatchSet A B,
          Real.log 2 / Real.sqrt B := by simp
    _ ≤ ∑ n ∈ ccmOddLogWindowMismatchSet A B,
        criticalMellinAtomWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS : n ∈ (Finset.Icc A B).filter IsPrimePow :=
        (Finset.mem_filter.mp hn).1
      have hnI : n ∈ Finset.Icc A B := (Finset.mem_filter.mp hnS).1
      exact mismatch_weight_ge (hA.trans hAB)
        (hA.trans (Finset.mem_Icc.mp hnI).1)
        (Finset.mem_Icc.mp hnI).2 (Finset.mem_filter.mp hnS).2

/-- Finite arithmetic weight law: abundant primes force literal
completed-source mismatch mass after paying proper prime-power separators. -/
theorem odd_window_prime_count_weight_le_mismatch_mass_add_separators
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hcount : ((Finset.Icc A B).filter Nat.Prime).card ≤
      2 * (ccmOddLogWindowMismatchSet A B).card +
      (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card + 1) :
    (((Finset.Icc A B).filter Nat.Prime).card : ℝ) *
        (Real.log 2 / Real.sqrt B) ≤
      2 * (∑ n ∈ ccmOddLogWindowMismatchSet A B,
        criticalMellinAtomWeight n) +
        ((((Finset.Icc A B).filter IsPrimePow).filter
          (fun n => ¬ n.Prime)).card : ℝ) *
          (Real.log 2 / Real.sqrt B) +
        Real.log 2 / Real.sqrt B := by
  have hc : (((Finset.Icc A B).filter Nat.Prime).card : ℝ) ≤
      2 * ((ccmOddLogWindowMismatchSet A B).card : ℝ) +
        ((((Finset.Icc A B).filter IsPrimePow).filter
          (fun n => ¬ n.Prime)).card : ℝ) + 1 := by
    exact_mod_cast hcount
  have hcoef : 0 ≤ Real.log 2 / Real.sqrt B := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hcoef
  have hmass := mismatch_mass_ge_count hA hAB
  nlinarith

/-- The proper-prime-power separator cost at critical-Mellin scale is at
most logarithmic, by the exact von Mangoldt defect estimate. -/
theorem odd_window_proper_power_separator_cost_le_log
    {A B : ℕ} (hB : 2 ≤ B) :
    ((((Finset.Icc A B).filter IsPrimePow).filter
      (fun n => ¬ n.Prime)).card : ℝ) *
      (Real.log 2 / Real.sqrt B) ≤ 2 * Real.log (B : ℝ) := by
  classical
  have hsubset :
      (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)) ⊆
      ((Finset.range (B + 1)).filter
        (fun n => IsPrimePow n ∧ ¬ n.Prime)) := by
    intro n hn
    have hnS : n ∈ (Finset.Icc A B).filter IsPrimePow :=
      (Finset.mem_filter.mp hn).1
    have hnI : n ∈ Finset.Icc A B := (Finset.mem_filter.mp hnS).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hnI).2),
        (Finset.mem_filter.mp hnS).2, (Finset.mem_filter.mp hn).2⟩
  have hcard :
      ((((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card : ℝ) ≤
      ((((Finset.range (B + 1)).filter
        (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hlog2 : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hdefect := RHTower.Sieve.properPrimePower_count_mul_log_two_le_sqrt_log
    (show 1 ≤ B by omega)
  have hnumer :
      ((((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card : ℝ) * Real.log 2 ≤
        2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) :=
    (mul_le_mul_of_nonneg_right hcard hlog2).trans hdefect
  have hsB : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < B))
  calc
    _ = ((((Finset.Icc A B).filter IsPrimePow).filter
          (fun n => ¬ n.Prime)).card : ℝ) *
          Real.log 2 / Real.sqrt B := by ring
    _ ≤ (2 * Real.sqrt B * Real.log B) / Real.sqrt B :=
      div_le_div_of_nonneg_right hnumer hsB.le
    _ = 2 * Real.log (B : ℝ) := by
      field_simp [ne_of_gt hsB]

/-- Finite source law: prime supply forces literal mismatch mass at the
critical-Mellin scale, with only a logarithmic proper-power debit. -/
theorem odd_window_prime_count_weight_le_two_mismatch_mass_add_log
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hcount : ((Finset.Icc A B).filter Nat.Prime).card ≤
      2 * (ccmOddLogWindowMismatchSet A B).card +
      (((Finset.Icc A B).filter IsPrimePow).filter
        (fun n => ¬ n.Prime)).card + 1) :
    (((Finset.Icc A B).filter Nat.Prime).card : ℝ) *
        (Real.log 2 / Real.sqrt B) ≤
      2 * (∑ n ∈ ccmOddLogWindowMismatchSet A B,
        criticalMellinAtomWeight n) +
        2 * Real.log (B : ℝ) + Real.log 2 / Real.sqrt B := by
  have hmass := odd_window_prime_count_weight_le_mismatch_mass_add_separators
    hA hAB hcount
  have hsep := odd_window_proper_power_separator_cost_le_log
    (A := A) (B := B) (hA.trans hAB)
  linarith

/-- Every sufficiently late canonical odd-log window obeys the exact
critical-Mellin prime-count/mismatch-mass inequality. -/
theorem eventually_odd_window_prime_count_weight_le_two_mismatch_mass_add_log :
    ∀ᶠ t : ℕ in Filter.atTop,
      (((Finset.Icc (ccmOddLogWindowLower t)
        (ccmOddLogWindowUpper t)).filter Nat.Prime).card : ℝ) *
          (Real.log 2 / Real.sqrt (ccmOddLogWindowUpper t)) ≤
        2 * (∑ n ∈ ccmOddLogWindowMismatchSet
          (ccmOddLogWindowLower t) (ccmOddLogWindowUpper t),
          criticalMellinAtomWeight n) +
        2 * Real.log (ccmOddLogWindowUpper t : ℝ) +
          Real.log 2 / Real.sqrt (ccmOddLogWindowUpper t) := by
  let K : ℝ := Real.exp (1 / 4 : ℝ)
  have hK : 1 < K := by
    dsimp [K]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hlin : Filter.Tendsto
      (fun t : ℕ => ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono
      (fun t : ℕ => by exact_mod_cast (show t ≤ 2 * t + 1 by omega))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxTop : Filter.Tendsto
      (fun t : ℕ => Real.exp ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hlin
  filter_upwards
    [eventually_ccmOddLogWindow_primeCount_le_twice_baseMismatch_add_properPower,
      hxTop.eventually_ge_atTop (1 / (K - 1))] with t hcount hlarge
  let x : ℝ := Real.exp ((2 * t + 1 : ℕ) : ℝ)
  let A : ℕ := ccmOddLogWindowLower t
  let B : ℕ := ccmOddLogWindowUpper t
  have hx0 : 0 < x := Real.exp_pos _
  have hx2 : (2 : ℝ) ≤ x := by
    have ht1 : (1 : ℝ) ≤ ((2 * t + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * t + 1 by omega)
    calc
      (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ x := Real.exp_le_exp.mpr ht1
  have hA2 : 2 ≤ A := by
    have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx2
    change 2 ≤ ⌊x⌋₊ + 1
    omega
  have hAreal : (A : ℝ) ≤ x + 1 := by
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    change ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1
    push_cast
    linarith
  have hgap : x + 1 ≤ K * x := by
    have hKdiff : 0 < K - 1 := by linarith
    have hlarge' : 1 / (K - 1) ≤ x := hlarge
    have hh : (1 : ℝ) ≤ x * (K - 1) :=
      (div_le_iff₀ hKdiff).mp hlarge'
    nlinarith
  have hAB : A ≤ B := by
    dsimp only [B, ccmOddLogWindowUpper]
    apply Nat.le_floor
    rw [Real.exp_add]
    simpa only [x, K, mul_comm] using hAreal.trans hgap
  exact odd_window_prime_count_weight_le_two_mismatch_mass_add_log
    hA2 hAB (by simpa only [A, B, ccmOddLogWindowMismatchSet] using hcount)

end RHTower
