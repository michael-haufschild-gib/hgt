import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.Matveev.PerturbedPower

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- The coefficient `μ(n) log(n)^p / n`. -/
def moebiusLogPowerHarmonicTerm (p n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ p / (n : ℝ)

/-- Partial sums of `μ(n) log(n)^p / n`. -/
def moebiusLogPowerHarmonicPartial (p N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), moebiusLogPowerHarmonicTerm p n

@[simp] theorem moebiusLogPowerHarmonicTerm_zero (p : ℕ) :
    moebiusLogPowerHarmonicTerm p 0 = 0 := by
  simp [moebiusLogPowerHarmonicTerm]

private theorem summable_deningerHarmonic_logPowerIncrement (p : ℕ) :
    Summable fun n : ℕ => RHTower.deningerHarmonicPartial n *
      (Real.log ((n : ℝ) + 1) ^ p - Real.log (n : ℝ) ^ p) := by
  rcases p with _ | q
  · simp
  obtain ⟨C, hC, hpartial⟩ :=
    exists_abs_deningerHarmonicPartial_le_const_div_log_pow (q + 2) (by omega)
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
  let D : ℝ := ((q + 1 : ℕ) : ℝ) * 2 ^ q * C
  have hbase : Summable fun n : ℕ =>
      D * (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) :=
    RHTower.burnolSummable_one_div_mul_log_sq.mul_left D
  have hmajor : Summable fun i : ℕ =>
      D / (((i + (M + 1) : ℕ) : ℝ) *
        Real.log ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by
    have hshift := (summable_nat_add_iff (M + 1)).mpr hbase
    simpa [div_eq_mul_inv, mul_assoc] using hshift
  have hshift : Summable fun i : ℕ =>
      RHTower.deningerHarmonicPartial (i + (M + 1)) *
        (Real.log (((i + (M + 1) : ℕ) : ℝ) + 1) ^ (q + 1) -
          Real.log ((i + (M + 1) : ℕ) : ℝ) ^ (q + 1)) := by
    refine Summable.of_norm_bounded hmajor fun i => ?_
    let n := i + (M + 1)
    have hnM : M ≤ n := by dsimp [n]; omega
    have hnK : K ≤ n := hMK.trans hnM
    have hne : Real.exp 1 ≤ (n : ℝ) := hMe.trans (by exact_mod_cast hnM)
    have hn1 : 1 ≤ n := hM1.trans hnM
    have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hne
    have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
    have hpart := hK n hnK
    have hdiff0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
      exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
    have hdiff := log_natCast_succ_sub_log_natCast_le_inv n hn1
    have hlogSucc0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    have hlogSucc : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      have hinc : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 / (n : ℝ) := by
        linarith
      have hinv : 1 / (n : ℝ) ≤ Real.log (n : ℝ) := by
        have hinvOne : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one hn0]
          exact_mod_cast hn1
        exact hinvOne.trans hlog
      linarith
    have hxAbs : |Real.log (n : ℝ)| ≤ 2 * Real.log (n : ℝ) := by
      rw [abs_of_nonneg hlogpos.le]
      linarith
    have hyAbs : |Real.log ((n : ℝ) + 1)| ≤ 2 * Real.log (n : ℝ) := by
      rw [abs_of_nonneg hlogSucc0]
      exact hlogSucc
    have hpowDiff := GaloisForLFunctions.RHTower.Matveev.abs_pow_sub_pow_le
      hyAbs hxAbs (q + 1)
    have hdiffAbs : |Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)| ≤
        1 / (n : ℝ) := by
      rw [abs_of_nonneg hdiff0]
      exact hdiff
    have hpowDiff' :
        |Real.log ((n : ℝ) + 1) ^ (q + 1) - Real.log (n : ℝ) ^ (q + 1)| ≤
          ((q + 1 : ℕ) : ℝ) * (2 * Real.log (n : ℝ)) ^ q *
            (1 / (n : ℝ)) := by
      exact hpowDiff.trans (mul_le_mul_of_nonneg_left hdiffAbs (by positivity))
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |RHTower.deningerHarmonicPartial n| *
          |Real.log ((n : ℝ) + 1) ^ (q + 1) - Real.log (n : ℝ) ^ (q + 1)| ≤
          (C / Real.log (n : ℝ) ^ (q + 2)) *
            (((q + 1 : ℕ) : ℝ) * (2 * Real.log (n : ℝ)) ^ q *
              (1 / (n : ℝ))) :=
        mul_le_mul hpart hpowDiff' (abs_nonneg _) (by positivity)
      _ = D / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
        dsimp [D]
        rw [mul_pow, pow_add]
        field_simp [hlogpos.ne', hn0.ne']
      _ = D / (((i + (M + 1) : ℕ) : ℝ) *
          Real.log ((i + (M + 1) : ℕ) : ℝ) ^ 2) := by rfl
  exact (summable_nat_add_iff (M + 1)).mp (by
    simpa only [Nat.add_comm] using hshift)

/-- Every logarithmic Möbius moment has a finite limiting value. -/
theorem exists_tendsto_moebiusLogPowerHarmonicPartial (p : ℕ) :
    ∃ S : ℝ, Tendsto (moebiusLogPowerHarmonicPartial p) atTop (𝓝 S) := by
  let t : ℕ → ℝ := fun n => RHTower.deningerHarmonicPartial n *
    (Real.log ((n : ℝ) + 1) ^ p - Real.log (n : ℝ) ^ p)
  have ht : Summable t := summable_deningerHarmonic_logPowerIncrement p
  refine ⟨-(∑' n : ℕ, t n), ?_⟩
  have hboundary : Tendsto (fun N : ℕ =>
      RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ p) atTop (𝓝 0) := by
    simpa only [mul_comm] using tendsto_log_pow_mul_deningerHarmonicPartial_zero p
  have hseries := ht.hasSum.tendsto_sum_nat.neg
  have hadd := hboundary.add hseries
  rw [zero_add] at hadd
  refine hadd.congr fun N => ?_
  have habel := RHTower.deningerAbelSummation
    (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))
    (fun n : ℕ => Real.log (n : ℝ) ^ p) N
  calc
    RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ p -
        ∑ i ∈ Finset.range N, t i =
      RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ p +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (Real.log (i : ℝ) ^ p - Real.log ((i + 1 : ℕ) : ℝ) ^ p) := by
      rw [sub_eq_add_neg]
      apply congrArg (fun x =>
        RHTower.deningerHarmonicPartial N * Real.log (N : ℝ) ^ p + x)
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [t]
      push_cast
      ring
    _ = ∑ n ∈ Finset.range (N + 1),
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) *
          Real.log (n : ℝ) ^ p := habel.symm
    _ = moebiusLogPowerHarmonicPartial p N := by
      rw [moebiusLogPowerHarmonicPartial]
      apply Finset.sum_congr rfl
      intro n hn
      rw [moebiusLogPowerHarmonicTerm]
      ring

/-- Möbius kernel with an arbitrary integral logarithmic power. -/
def moebiusLogPowerKernel (p N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
      Real.log ((N : ℝ) / (n : ℝ)) ^ p

private theorem moebiusLogPowerHarmonicPartial_eq_Icc
    (p N : ℕ) :
    moebiusLogPowerHarmonicPartial p N =
      ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (d : ℝ) ^ p := by
  rw [moebiusLogPowerHarmonicPartial, Finset.sum_range_succ']
  simp only [moebiusLogPowerHarmonicTerm_zero, add_zero]
  rw [RHTower.sum_range_succ_eq_sum_Icc (moebiusLogPowerHarmonicTerm p) N]
  apply Finset.sum_congr rfl
  intro d hd
  rw [moebiusLogPowerHarmonicTerm]
  ring

/-- Exact finite binomial expansion of every logarithmic Möbius kernel into its moments. -/
theorem moebiusLogPowerKernel_expansion (p N : ℕ) (hN : 1 ≤ N) :
    moebiusLogPowerKernel p N =
      ∑ m ∈ Finset.range (p + 1),
        (-1 : ℝ) ^ (m + p) * Real.log (N : ℝ) ^ m *
          moebiusLogPowerHarmonicPartial (p - m) N * (p.choose m : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [moebiusLogPowerKernel]
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
          Real.log ((N : ℝ) / (n : ℝ)) ^ p) =
      ∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
          (Real.log (N : ℝ) - Real.log (n : ℝ)) ^ p := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnR : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
        rw [Real.log_div hNR.ne' hnR.ne']
    _ = ∑ n ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.range (p + 1),
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
            ((-1 : ℝ) ^ (m + p) * Real.log (N : ℝ) ^ m *
              Real.log (n : ℝ) ^ (p - m) * (p.choose m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [sub_pow, Finset.mul_sum]
    _ = ∑ m ∈ Finset.range (p + 1),
        ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) *
            ((-1 : ℝ) ^ (m + p) * Real.log (N : ℝ) ^ m *
              Real.log (n : ℝ) ^ (p - m) * (p.choose m : ℝ)) := by
        rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range (p + 1),
        (-1 : ℝ) ^ (m + p) * Real.log (N : ℝ) ^ m *
          moebiusLogPowerHarmonicPartial (p - m) N * (p.choose m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [moebiusLogPowerHarmonicPartial_eq_Icc]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring

/-- Moment-indexed form of the finite binomial expansion. -/
theorem moebiusLogPowerKernel_expansion_by_moment (p N : ℕ) (hN : 1 ≤ N) :
    moebiusLogPowerKernel p N =
      ∑ j ∈ Finset.range (p + 1),
        (-1 : ℝ) ^ j * (p.choose j : ℝ) * Real.log (N : ℝ) ^ (p - j) *
          moebiusLogPowerHarmonicPartial j N := by
  rw [moebiusLogPowerKernel_expansion p N hN]
  rw [← Finset.sum_range_reflect
    (fun j => (-1 : ℝ) ^ j * (p.choose j : ℝ) *
      Real.log (N : ℝ) ^ (p - j) *
        moebiusLogPowerHarmonicPartial j N) (p + 1)]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ p := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hm
  have hidx : p + 1 - 1 - m = p - m := by omega
  rw [hidx, Nat.choose_symm hmle]
  have hpowidx : p - (p - m) = m := by omega
  rw [hpowidx]
  have hpdecomp : p = m + (p - m) := by omega
  have hsign : (-1 : ℝ) ^ (m + p) = (-1 : ℝ) ^ (p - m) := by
    calc
      (-1 : ℝ) ^ (m + p) = (-1 : ℝ) ^ m * (-1 : ℝ) ^ p := by
        rw [pow_add]
      _ =
          (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * (-1 : ℝ) ^ (p - m)) := by
        congr 1
        calc
          (-1 : ℝ) ^ p = (-1 : ℝ) ^ (m + (p - m)) :=
            congrArg (fun e : ℕ => (-1 : ℝ) ^ e) hpdecomp
          _ = (-1 : ℝ) ^ m * (-1 : ℝ) ^ (p - m) := pow_add _ _ _
      _ = (((-1 : ℝ) ^ m) * (-1 : ℝ) ^ m) * (-1 : ℝ) ^ (p - m) := by ring
      _ = (-1 : ℝ) ^ (p - m) := by
        rw [← pow_add, show m + m = 2 * m by omega, pow_mul]
        norm_num
  rw [hsign]
  ring

@[simp] theorem moebiusLogPowerHarmonicPartial_zeroPower (N : ℕ) :
    moebiusLogPowerHarmonicPartial 0 N = RHTower.deningerHarmonicPartial N := by
  rw [moebiusLogPowerHarmonicPartial, RHTower.deningerHarmonicPartial]
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebiusLogPowerHarmonicTerm]
  simp

theorem moebiusLogPowerHarmonicPartial_onePower (N : ℕ) :
    moebiusLogPowerHarmonicPartial 1 N = -moebiusLogHarmonicPartial N := by
  rw [moebiusLogPowerHarmonicPartial, moebiusLogHarmonicPartial,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebiusLogPowerHarmonicTerm, moebiusLogHarmonicTerm,
    Real.rpow_neg_one]
  ring

private theorem tendsto_normalized_moebiusLogPowerMomentTerm
    (p j : ℕ) (hj : j ≤ p + 1) :
    Tendsto (fun N : ℕ =>
      ((-1 : ℝ) ^ j * ((p + 1).choose j : ℝ) *
          Real.log (N : ℝ) ^ (p + 1 - j) *
            moebiusLogPowerHarmonicPartial j N) /
        Real.log (N : ℝ) ^ p) atTop
      (𝓝 (if j = 1 then ((p + 1 : ℕ) : ℝ) else 0)) := by
  rcases j with _ | j
  · have hzero := tendsto_log_pow_mul_deningerHarmonicPartial_zero 1
    have htarget : Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N) atTop (𝓝 0) := by
      simpa only [pow_one] using hzero
    simpa only [Nat.zero_ne_one, ↓reduceIte] using htarget.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      rw [moebiusLogPowerHarmonicPartial_zeroPower]
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      rw [show p + 1 - 0 = p + 1 by omega, pow_succ]
      field_simp [hlog])
  rcases j with _ | j
  · have hlinear := tendsto_moebiusLogHarmonicPartial_one.const_mul
      (((p + 1 : ℕ) : ℝ))
    have htarget : Tendsto (fun N : ℕ =>
        ((p + 1 : ℕ) : ℝ) * moebiusLogHarmonicPartial N)
        atTop (𝓝 (((p + 1 : ℕ) : ℝ))) := by
      simpa only [mul_one] using hlinear
    simpa only [ite_true] using htarget.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      rw [moebiusLogPowerHarmonicPartial_onePower]
      have hpowidx : p + 1 - 1 = p := by omega
      have hchoose : (p + 1).choose 1 = p + 1 := by simp
      rw [hpowidx, hchoose]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hlog]
      ring)
  have hjtwo : 2 ≤ j + 2 := by omega
  obtain ⟨S, hS⟩ :=
    exists_tendsto_moebiusLogPowerHarmonicPartial (j + 2)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hlog)
  have hvanish : Tendsto (fun N : ℕ =>
      moebiusLogPowerHarmonicPartial (j + 2) N *
        (1 / Real.log (N : ℝ)) ^ (j + 1)) atTop (𝓝 0) := by
    simpa [zero_pow (by omega : j + 1 ≠ 0)] using hS.mul (hinv.pow (j + 1))
  have hconst := hvanish.const_mul
    ((-1 : ℝ) ^ (j + 2) * (((p + 1).choose (j + 2) : ℕ) : ℝ))
  rw [if_neg (by omega : j + 2 ≠ 1)]
  simpa only [mul_zero] using hconst.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlogN : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      have hdecomp : p = (p + 1 - (j + 2)) + (j + 1) := by omega
      have hratio : Real.log (N : ℝ) ^ (p + 1 - (j + 2)) /
          Real.log (N : ℝ) ^ p =
          (1 / Real.log (N : ℝ)) ^ (j + 1) := by
        have hpowdecomp : Real.log (N : ℝ) ^ p =
            Real.log (N : ℝ) ^ (p + 1 - (j + 2)) *
              Real.log (N : ℝ) ^ (j + 1) := by
          calc
            Real.log (N : ℝ) ^ p =
                Real.log (N : ℝ) ^ ((p + 1 - (j + 2)) + (j + 1)) :=
              congrArg (fun e : ℕ => Real.log (N : ℝ) ^ e) hdecomp
            _ = _ := pow_add _ _ _
        rw [hpowdecomp, one_div, inv_pow]
        field_simp [hlogN]
      rw [show j + 1 + 1 = j + 2 by omega]
      calc
        (-1 : ℝ) ^ (j + 2) * (((p + 1).choose (j + 2) : ℕ) : ℝ) *
            (moebiusLogPowerHarmonicPartial (j + 2) N *
              (1 / Real.log (N : ℝ)) ^ (j + 1)) =
          (-1 : ℝ) ^ (j + 2) * (((p + 1).choose (j + 2) : ℕ) : ℝ) *
            moebiusLogPowerHarmonicPartial (j + 2) N *
              (Real.log (N : ℝ) ^ (p + 1 - (j + 2)) /
                Real.log (N : ℝ) ^ p) := by rw [hratio]; ring
        _ = ((-1 : ℝ) ^ (j + 2) * (((p + 1).choose (j + 2) : ℕ) : ℝ) *
            Real.log (N : ℝ) ^ (p + 1 - (j + 2)) *
              moebiusLogPowerHarmonicPartial (j + 2) N) /
                Real.log (N : ℝ) ^ p := by ring)

/-- Every positive logarithmic Möbius kernel has its classical leading coefficient. -/
theorem tendsto_moebiusLogPowerKernel_div_log_pow (p : ℕ) :
    Tendsto (fun N : ℕ =>
      moebiusLogPowerKernel (p + 1) N / Real.log (N : ℝ) ^ p)
      atTop (𝓝 ((p + 1 : ℕ) : ℝ)) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.range (p + 2),
        (((-1 : ℝ) ^ j * ((p + 1).choose j : ℝ) *
            Real.log (N : ℝ) ^ (p + 1 - j) *
              moebiusLogPowerHarmonicPartial j N) /
          Real.log (N : ℝ) ^ p)) atTop
      (𝓝 (∑ j ∈ Finset.range (p + 2),
        if j = 1 then ((p + 1 : ℕ) : ℝ) else 0)) := by
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_normalized_moebiusLogPowerMomentTerm p j (by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj)
  have hlimit : (∑ j ∈ Finset.range (p + 2),
      if j = 1 then ((p + 1 : ℕ) : ℝ) else 0) = ((p + 1 : ℕ) : ℝ) := by
    simp [show 1 < p + 2 by omega]
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [moebiusLogPowerKernel_expansion_by_moment (p + 1) N (by omega),
    Finset.sum_div]

end


end RHTower.Sieve
