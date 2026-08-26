import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

noncomputable section

/-- Public cubic-log envelope for the Möbius harmonic partial sums. -/
theorem exists_abs_deningerHarmonicPartial_le_const_div_log_cube :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |RHTower.deningerHarmonicPartial N| ≤ C / Real.log (N : ℝ) ^ 3 := by
  obtain ⟨B, hB, hrate⟩ := exists_abs_deningerHarmonicPartial_log_rate
  let C : ℝ := 2 * B + B / 3
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have hevent : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)
    filter_upwards [hevent] with N hN
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hN
  filter_upwards [hrate, hlog] with N hrateN hlogN
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have hp3 : 0 < Real.log (N : ℝ) ^ 3 := pow_pos hlogpos 3
  have hp34 : Real.log (N : ℝ) ^ 3 ≤ Real.log (N : ℝ) ^ 4 := by
    calc
      Real.log (N : ℝ) ^ 3 ≤ Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) :=
        le_mul_of_one_le_right (pow_nonneg hlogpos.le 3) hlogN
      _ = Real.log (N : ℝ) ^ 4 := by ring
  have hfirst : 2 * B / Real.log (N : ℝ) ^ 4 ≤
      2 * B / Real.log (N : ℝ) ^ 3 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using one_div_le_one_div_of_le hp3 hp34)
      (mul_nonneg (by norm_num) hB)
  exact hrateN.trans (by
    calc
      2 * B / Real.log (N : ℝ) ^ 4 + B / (3 * Real.log (N : ℝ) ^ 3) ≤
          2 * B / Real.log (N : ℝ) ^ 3 + B / (3 * Real.log (N : ℝ) ^ 3) :=
        add_le_add hfirst le_rfl
      _ = C / Real.log (N : ℝ) ^ 3 := by dsimp [C]; ring)

/-- The coefficient `μ(n) log²(n) / n`. -/
def moebiusLogSqHarmonicTerm (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2 / (n : ℝ)

/-- Partial sums of `μ(n) log²(n) / n`. -/
def moebiusLogSqHarmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), moebiusLogSqHarmonicTerm n

@[simp] theorem moebiusLogSqHarmonicTerm_zero : moebiusLogSqHarmonicTerm 0 = 0 := by
  simp [moebiusLogSqHarmonicTerm]

private theorem summable_deningerHarmonic_logSqIncrement :
    Summable fun n : ℕ => RHTower.deningerHarmonicPartial n *
      (Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2) := by
  obtain ⟨C, hC, hpartial⟩ :=
    exists_abs_deningerHarmonicPartial_le_const_div_log_cube
  rw [eventually_atTop] at hpartial
  obtain ⟨K, hK⟩ := hpartial
  have hevent : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)
  rw [eventually_atTop] at hevent
  obtain ⟨L, hL⟩ := hevent
  let M := max (max K L) 1
  have hMK : K ≤ M := le_trans (le_max_left K L) (le_max_left _ 1)
  have hML : L ≤ M := le_trans (le_max_right K L) (le_max_left _ 1)
  have hM1 : 1 ≤ M := le_max_right _ 1
  have hMe : Real.exp 1 ≤ (M : ℝ) := hL M hML
  have hbase : Summable fun n : ℕ =>
      3 * C * (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) :=
    RHTower.burnolSummable_one_div_mul_log_sq.mul_left (3 * C)
  have hmajor : Summable fun i : ℕ =>
      3 * C / (((i + (M + 1) : ℕ) : ℝ) *
        Real.log ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by
    have hshift := (summable_nat_add_iff (M + 1)).mpr hbase
    simpa [div_eq_mul_inv, mul_assoc] using hshift
  have hshift : Summable fun i : ℕ =>
      RHTower.deningerHarmonicPartial (i + (M + 1)) *
        (Real.log (((i + (M + 1) : ℕ) : ℝ) + 1) ^ 2 -
          Real.log ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by
    refine Summable.of_norm_bounded hmajor fun i => ?_
    let n := i + (M + 1)
    have hnM : M ≤ n := by dsimp [n]; omega
    have hnK : K ≤ n := hMK.trans hnM
    have hne : Real.exp 1 ≤ (n : ℝ) := hMe.trans (by exact_mod_cast hnM)
    have hn1 : 1 ≤ n := hM1.trans hnM
    have hlog : 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hne
    have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
    have hpart := hK n hnK
    have hdiff0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
      exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
    have hdiff := log_natCast_succ_sub_log_natCast_le_inv n hn1
    have hlogSucc : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      have hinc : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 / (n : ℝ) := by
        linarith
      have hinv : 1 / (n : ℝ) ≤ Real.log (n : ℝ) := by
        have hinvOne : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (show 0 < n by omega))]
          exact_mod_cast hn1
        exact hinvOne.trans hlog
      linarith
    have hsumLog : Real.log ((n : ℝ) + 1) + Real.log (n : ℝ) ≤
        3 * Real.log (n : ℝ) := by linarith
    have hsqDiff : Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2 ≤
        3 * Real.log (n : ℝ) / (n : ℝ) := by
      have hsumLog0 : 0 ≤
          Real.log ((n : ℝ) + 1) + Real.log (n : ℝ) := by
        have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hnreal0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hnreal
        have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
        have hlogsucc0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
          Real.log_nonneg (by linarith)
        linarith
      rw [show Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2 =
        (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) *
          (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ)) by ring]
      calc
        (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) *
            (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ)) ≤
            (1 / (n : ℝ)) * (3 * Real.log (n : ℝ)) :=
          mul_le_mul hdiff hsumLog hsumLog0 (by positivity)
        _ = 3 * Real.log (n : ℝ) / (n : ℝ) := by ring
    have hsqDiff0 : 0 ≤
        Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2 := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith [hdiff0, Real.log_nonneg hnreal]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsqDiff0]
    calc
      |RHTower.deningerHarmonicPartial n| *
          (Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2) ≤
          (C / Real.log (n : ℝ) ^ 3) *
            (3 * Real.log (n : ℝ) / (n : ℝ)) :=
        mul_le_mul hpart hsqDiff hsqDiff0 (by positivity)
      _ = 3 * C / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
        field_simp [hlogpos.ne']
      _ = 3 * C / (((i + (M + 1) : ℕ) : ℝ) *
          Real.log ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by rfl
  exact (summable_nat_add_iff (M + 1)).mp (by
    simpa only [Nat.add_comm] using hshift)

/-- The quadratic logarithmic Möbius partial sums converge. -/
theorem exists_tendsto_moebiusLogSqHarmonicPartial :
    ∃ S : ℝ, Tendsto moebiusLogSqHarmonicPartial atTop (𝓝 S) := by
  let t : ℕ → ℝ := fun n => RHTower.deningerHarmonicPartial n *
    (Real.log ((n : ℝ) + 1) ^ 2 - Real.log (n : ℝ) ^ 2)
  have ht : Summable t := summable_deningerHarmonic_logSqIncrement
  refine ⟨-(∑' n : ℕ, t n), ?_⟩
  have hboundary : Tendsto (fun N : ℕ =>
      RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ 2) atTop (𝓝 0) := by
    obtain ⟨C, hC, hpartial⟩ :=
      exists_abs_deningerHarmonicPartial_le_const_div_log_cube
    have hbound : Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (𝓝 0) := by
      have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      simpa only [zero_div] using tendsto_const_nhds.div_atTop hlog
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ (by
      simpa only [norm_zero] using hbound.norm)
    filter_upwards [hpartial] with N hN
    by_cases hlog : Real.log (N : ℝ) = 0
    · simp [hlog]
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc
      |RHTower.deningerHarmonicPartial N| * |Real.log (N : ℝ)| ^ 2 ≤
          (C / Real.log (N : ℝ) ^ 3) * |Real.log (N : ℝ)| ^ 2 :=
        mul_le_mul_of_nonneg_right hN (sq_nonneg _)
      _ = C / Real.log (N : ℝ) := by
        have hlogpos : 0 ≤ Real.log (N : ℝ) := by
          rcases eq_or_lt_of_le (Nat.zero_le N) with hzero | hpos
          · subst N; simp
          · exact Real.log_nonneg (by exact_mod_cast hpos)
        rw [abs_of_nonneg hlogpos]
        field_simp
      _ ≤ |C / Real.log (N : ℝ)| := le_abs_self _
  have hseries := ht.hasSum.tendsto_sum_nat.neg
  have hadd := hboundary.add hseries
  rw [zero_add] at hadd
  refine hadd.congr fun N => ?_
  have habel := RHTower.deningerAbelSummation
    (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))
    (fun n : ℕ => Real.log (n : ℝ) ^ 2) N
  calc
    RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ 2 -
        ∑ i ∈ Finset.range N, t i =
      RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ 2 +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (Real.log (i : ℝ) ^ 2 - Real.log ((i + 1 : ℕ) : ℝ) ^ 2) := by
      rw [sub_eq_add_neg]
      apply congrArg (fun x =>
        RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ 2 + x)
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [t]
      push_cast
      ring
    _ = ∑ n ∈ Finset.range (N + 1),
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) *
          Real.log (n : ℝ) ^ 2 := habel.symm
    _ = moebiusLogSqHarmonicPartial N := by
      rw [moebiusLogSqHarmonicPartial]
      apply Finset.sum_congr rfl
      intro n hn
      rw [moebiusLogSqHarmonicTerm]
      ring

/-- Quadratic logarithmic Möbius kernel. -/
def moebiusDoubleLogKernel (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
      Real.log ((N : ℝ) / (n : ℝ)) ^ 2

private theorem moebiusDoubleLogKernel_expansion (N : ℕ) (hN : 1 ≤ N) :
    moebiusDoubleLogKernel N =
      Real.log (N : ℝ) ^ 2 * RHTower.deningerHarmonicPartial N +
        2 * Real.log (N : ℝ) * moebiusLogHarmonicPartial N +
          moebiusLogSqHarmonicPartial N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpartial : RHTower.deningerHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) N using 1
    all_goals push_cast
    all_goals ring
  have hlogsum : moebiusLogHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        -(((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (d : ℝ)) := by
    rw [moebiusLogHarmonicPartial, Finset.sum_range_succ']
    simp only [moebiusLogHarmonicTerm_zero, add_zero]
    rw [RHTower.sum_range_succ_eq_sum_Icc moebiusLogHarmonicTerm N]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      simp only [Finset.mem_Icc] at hd
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
    rw [moebiusLogHarmonicTerm, Real.rpow_neg_one]
    field_simp
  have hlogsq : moebiusLogSqHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (d : ℝ) ^ 2 := by
    rw [moebiusLogSqHarmonicPartial, Finset.sum_range_succ']
    simp only [moebiusLogSqHarmonicTerm_zero, add_zero]
    rw [RHTower.sum_range_succ_eq_sum_Icc moebiusLogSqHarmonicTerm N]
    apply Finset.sum_congr rfl
    intro d hd
    rw [moebiusLogSqHarmonicTerm]
    ring
  rw [moebiusDoubleLogKernel, hpartial, hlogsum, hlogsq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < (d : ℝ) := by
    simp only [Finset.mem_Icc] at hd
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
  rw [Real.log_div hNR.ne' hdR.ne']
  ring

/-- The double-logarithmic Möbius kernel has leading coefficient two. -/
theorem tendsto_moebiusDoubleLogKernel_div_log_two :
    Tendsto (fun N : ℕ => moebiusDoubleLogKernel N / Real.log N) atTop (𝓝 2) := by
  obtain ⟨S, hS⟩ := exists_tendsto_moebiusLogSqHarmonicPartial
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSq : Tendsto (fun N : ℕ =>
      moebiusLogSqHarmonicPartial N / Real.log (N : ℝ)) atTop (𝓝 0) :=
    hS.div_atTop hlog
  have hlinear : Tendsto (fun N : ℕ => 2 * moebiusLogHarmonicPartial N)
      atTop (𝓝 (2 * 1)) :=
    tendsto_moebiusLogHarmonicPartial_one.const_mul 2
  have hadd := tendsto_log_mul_deningerHarmonicPartial_zero.add
    (hlinear.add hSq)
  have htarget : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N +
        (2 * moebiusLogHarmonicPartial N +
          moebiusLogSqHarmonicPartial N / Real.log (N : ℝ)))
      atTop (𝓝 2) := by
    simpa only [zero_add, mul_one, add_zero] using hadd
  refine htarget.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : 1 ≤ N := by omega
  have hlogpos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hN)
  rw [moebiusDoubleLogKernel_expansion N hN1]
  field_simp [hlogpos.ne']
  ring

end

end RHTower.Sieve
