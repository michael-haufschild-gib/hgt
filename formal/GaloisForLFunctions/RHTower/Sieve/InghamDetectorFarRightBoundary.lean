import GaloisForLFunctions.RHTower.Sieve.InghamDetectorPoleGaugeCancellation
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.RHTower.EulerHellingerLocalGrowthBounds
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorCenterLogMoment
import Mathlib.NumberTheory.LSeries.Deriv

open Complex Filter MeasureTheory intervalIntegral Set Topology ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

theorem inghamRightEdgeAbsoluteTail_four_le
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRightEdgeAbsoluteTail 4 X ≤ (X : ℝ) ^ (-2 : ℝ) / 2 := by
  let major : ℕ → ℝ := fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ (-4 : ℝ)
  have hmajor : Summable major := summable_card_divisors_mul_rpow (by norm_num)
  have hterm : ∀ k : ℕ,
      major (k + X + 1) ≤ (((k + X + 1 : ℕ) : ℝ)) ^ (-3 : ℝ) := by
    intro k
    have hn : (0 : ℕ) < k + X + 1 := by omega
    have hnR : (0 : ℝ) < ((k + X + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have hd : ((((k + X + 1 : ℕ)).divisors.card : ℕ) : ℝ) ≤
        ((k + X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (k + X + 1)
    calc
      major (k + X + 1) ≤
          ((k + X + 1 : ℕ) : ℝ) * ((k + X + 1 : ℕ) : ℝ) ^ (-4 : ℝ) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hnR.le _)
      _ = ((k + X + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
        calc
          ((k + X + 1 : ℕ) : ℝ) * ((k + X + 1 : ℕ) : ℝ) ^ (-4 : ℝ) =
              ((k + X + 1 : ℕ) : ℝ) ^ (1 : ℝ) *
                ((k + X + 1 : ℕ) : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_one]
          _ = ((k + X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) + (-4 : ℝ)) :=
            (Real.rpow_add hnR 1 (-4)).symm
          _ = ((k + X + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by norm_num
  have hmajorShift : Summable (fun k => major (k + X + 1)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmajor
  have hp : Summable (fun k : ℕ => (((k + X + 1 : ℕ) : ℝ)) ^ (-3 : ℝ)) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (X + 1)).mpr
        (summable_nat_rpow_neg (by norm_num : (1 : ℝ) < 3))
  calc
    inghamRightEdgeAbsoluteTail 4 X = ∑' k : ℕ, major (k + X + 1) := by
      rfl
    _ ≤ ∑' k : ℕ, (((k + X + 1 : ℕ) : ℝ)) ^ (-3 : ℝ) :=
      Summable.tsum_le_tsum hterm hmajorShift hp
    _ ≤ (X : ℝ) ^ (1 - (3 : ℝ)) / ((3 : ℝ) - 1) :=
      tsum_tail_rpow_neg_le (by norm_num) hX
    _ = (X : ℝ) ^ (-2 : ℝ) / 2 := by norm_num

private theorem norm_LSeriesTerm_logMul_moebiusZetaDefect_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) (n : ℕ) :
    ‖LSeries.term
        (LSeries.logMul (complexCoeff (moebiusZetaDefect X)))
        ((4 : ℂ) + (t : ℂ) * I) n‖ ≤ (n : ℝ) ^ (-2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [LSeries.term_def, Real.zero_rpow]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1R
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := by
      exact (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
    have hcoeff := norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
    have hdiv : (n.divisors.card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self n
    have hlogNorm : ‖Complex.log (n : ℂ)‖ = Real.log (n : ℝ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnR.le,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hcoeffLog :
        ‖LSeries.logMul (complexCoeff (moebiusZetaDefect X)) n‖ ≤
          (n : ℝ) ^ 2 := by
      rw [LSeries.logMul, norm_mul, hlogNorm]
      calc
        Real.log (n : ℝ) * ‖complexCoeff (moebiusZetaDefect X) n‖ ≤
            (n : ℝ) * (n.divisors.card : ℝ) :=
          mul_le_mul hlog hcoeff (norm_nonneg _) hnR.le
        _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hdiv hnR.le
        _ = (n : ℝ) ^ 2 := by ring
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    have hre : (((4 : ℂ) + (t : ℂ) * I)).re = (4 : ℝ) := by simp
    rw [hre, div_eq_mul_inv, ← Real.rpow_neg hnR.le]
    calc
      ‖LSeries.logMul (complexCoeff (moebiusZetaDefect X)) n‖ *
          (n : ℝ) ^ (-4 : ℝ) ≤
          (n : ℝ) ^ 2 * (n : ℝ) ^ (-4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeffLog (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast ((n : ℝ)) 2, ← Real.rpow_add hnR]
        norm_num

theorem norm_LSeries_logMul_moebiusZetaDefect_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖LSeries (LSeries.logMul (complexCoeff (moebiusZetaDefect X)))
        ((4 : ℂ) + (t : ℂ) * I)‖ ≤ (X : ℝ) ^ (-1 : ℝ) := by
  let s : ℂ := (4 : ℂ) + (t : ℂ) * I
  let coeff : ℕ → ℂ := LSeries.logMul (complexCoeff (moebiusZetaDefect X))
  let major : ℕ → ℝ := fun n => (n : ℝ) ^ (-2 : ℝ)
  have hmajor : Summable major := summable_nat_rpow_neg (by norm_num)
  have htermLe : ∀ n, ‖LSeries.term coeff s n‖ ≤ major n := by
    intro n
    exact norm_LSeriesTerm_logMul_moebiusZetaDefect_four_le hX t n
  have hterm : Summable (fun n => ‖LSeries.term coeff s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htermLe hmajor
  have hshiftTerm :
      ∑' n, ‖LSeries.term coeff s n‖ =
        ∑' k, ‖LSeries.term coeff s (k + X + 1)‖ := by
    have hsplit := hterm.sum_add_tsum_nat_add (X + 1)
    have hzero : ∑ n ∈ Finset.range (X + 1), ‖LSeries.term coeff s n‖ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hc0 : coeff n = 0 := by
        dsimp only [coeff, LSeries.logMul]
        rw [complexCoeff_apply,
          moebiusZetaDefect_vanishesBelow X n (Finset.mem_range.mp hn)]
        simp
      simp only [LSeries.term_def, hc0, norm_eq_zero]
      split_ifs <;> simp
    rw [hzero, zero_add] at hsplit
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm
  have hmajorShift : Summable (fun k => major (k + X + 1)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmajor
  have htermShift : Summable (fun k => ‖LSeries.term coeff s (k + X + 1)‖) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hterm
  have htailBound :
      (∑' k, ‖LSeries.term coeff s (k + X + 1)‖) ≤
        ∑' k, major (k + X + 1) := by
    exact Summable.tsum_le_tsum (fun k => htermLe (k + X + 1))
      htermShift hmajorShift
  calc
    ‖LSeries coeff s‖ = ‖∑' n, LSeries.term coeff s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term coeff s n‖ := norm_tsum_le_tsum_norm hterm
    _ = ∑' k, ‖LSeries.term coeff s (k + X + 1)‖ := hshiftTerm
    _ ≤ ∑' k, major (k + X + 1) := htailBound
    _ ≤ (X : ℝ) ^ (1 - (2 : ℝ)) / ((2 : ℝ) - 1) :=
      tsum_tail_rpow_neg_le (by norm_num) hX
    _ = (X : ℝ) ^ (-1 : ℝ) := by norm_num

theorem norm_deriv_inghamMollifiedError_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖deriv (fun z : ℂ => riemannZeta z * inghamMollifier X z - 1)
        ((4 : ℂ) + (t : ℂ) * I)‖ ≤ (X : ℝ) ^ (-1 : ℝ) := by
  let s : ℂ := (4 : ℂ) + (t : ℂ) * I
  let coeff : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  let raw : ℂ → ℂ := fun z => riemannZeta z * inghamMollifier X z - 1
  have hsumNorm := summable_norm_complexCoeff_moebiusZetaDefect_damped hX
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hsum : LSeriesSummable coeff ((3 / 2 : ℝ) : ℂ) := by
    rw [LSeriesSummable, ← summable_norm_iff]
    apply hsumNorm.congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_def]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [LSeries.norm_term_eq, if_neg hn.ne']
      simp only [Complex.ofReal_re]
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _)]
      dsimp only [coeff]
      rw [Real.rpow_neg hnR.le]
      exact (div_eq_mul_inv _ _).symm
  have habs : LSeries.abscissaOfAbsConv coeff < s.re := by
    refine hsum.abscissaOfAbsConv_le.trans_lt ?_
    norm_num [s]
  have hopen : {z : ℂ | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [s])
  have heq : raw =ᶠ[nhds s] fun z => -LSeries coeff z := by
    filter_upwards [hopen] with z hz
    dsimp only [raw, coeff]
    rw [LSeries_complexCoeff_moebiusZetaDefect_eq X hz]
    ring
  have hL := LSeries_hasDerivAt habs
  calc
    ‖deriv raw s‖ =
        ‖LSeries (LSeries.logMul coeff) s‖ := by
      rw [heq.deriv_eq]
      change ‖deriv (-LSeries coeff) s‖ = _
      rw [hL.neg.deriv]
      simp
    _ ≤ (X : ℝ) ^ (-1 : ℝ) := by
      simpa only [s, coeff] using
        norm_LSeries_logMul_moebiusZetaDefect_four_le hX t

theorem norm_inghamMollifiedError_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖riemannZeta ((4 : ℂ) + (t : ℂ) * I) *
        inghamMollifier X ((4 : ℂ) + (t : ℂ) * I) - 1‖ ≤
      (X : ℝ) ^ (-2 : ℝ) / 2 := by
  exact (norm_inghamMollifiedError_right_le_absoluteTail (by norm_num) hX t).trans
    (inghamRightEdgeAbsoluteTail_four_le hX)

theorem inghamClassicalDetector_ne_zero_four
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let e : ℂ := riemannZeta ((4 : ℂ) + (t : ℂ) * I) *
    inghamMollifier X ((4 : ℂ) + (t : ℂ) * I) - 1
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have he : ‖e‖ ≤ (1 : ℝ) / 2 := by
    have hthis : ‖e‖ ≤ (X : ℝ) ^ (-2 : ℝ) / 2 := by
      simpa only [e] using norm_inghamMollifiedError_four_le hX t
    linarith
  intro hz
  have heq : e ^ 2 = 1 := by
    simpa only [inghamClassicalDetector, e] using (sub_eq_zero.mp hz).symm
  have hn := congrArg norm heq
  rw [norm_pow, norm_one] at hn
  nlinarith [norm_nonneg e]

theorem neg_log_norm_inghamClassicalDetector_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    -Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖ ≤
      2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2 := by
  let e : ℂ := riemannZeta ((4 : ℂ) + (t : ℂ) * I) *
    inghamMollifier X ((4 : ℂ) + (t : ℂ) * I) - 1
  let A : ℝ := (X : ℝ) ^ (-2 : ℝ) / 2
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hAhalf : A ≤ (1 : ℝ) / 2 := by dsimp only [A]; linarith
  have he : ‖e‖ ≤ A := by
    simpa only [e, A] using norm_inghamMollifiedError_four_le hX t
  have hehalf : ‖e‖ ≤ (1 : ℝ) / 2 := he.trans hAhalf
  have hu0 : 0 ≤ ‖e‖ ^ 2 := sq_nonneg _
  have huhalf : ‖e‖ ^ 2 ≤ (1 : ℝ) / 2 := by
    nlinarith [norm_nonneg e]
  have hlower : 1 - ‖e‖ ^ 2 ≤ ‖1 - e ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (e ^ 2)
    simpa only [norm_one, norm_pow] using h
  have hpos : 0 < 1 - ‖e‖ ^ 2 := by nlinarith
  have hlog : Real.log (1 - ‖e‖ ^ 2) ≤ Real.log ‖1 - e ^ 2‖ :=
    Real.log_le_log hpos hlower
  have hneg := RHTower.neg_log_one_sub_le_of_le hu0 huhalf
    (by norm_num : (1 : ℝ) / 2 < 1)
  have heSq : ‖e‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg e) he 2
  calc
    -Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖ =
        -Real.log ‖1 - e ^ 2‖ := by rfl
    _ ≤ -Real.log (1 - ‖e‖ ^ 2) := neg_le_neg hlog
    _ ≤ (1 - (1 : ℝ) / 2)⁻¹ * ‖e‖ ^ 2 := hneg
    _ = 2 * ‖e‖ ^ 2 := by norm_num
    _ ≤ 2 * A ^ 2 := mul_le_mul_of_nonneg_left heSq (by norm_num)
    _ = 2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2 := rfl

theorem norm_logDeriv_inghamClassicalDetector_four_le
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    ‖logDeriv (inghamClassicalDetector X) ((4 : ℂ) + (t : ℂ) * I)‖ ≤
      4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ) := by
  let s : ℂ := (4 : ℂ) + (t : ℂ) * I
  let raw : ℂ → ℂ := fun z => riemannZeta z * inghamMollifier X z - 1
  let A : ℝ := (X : ℝ) ^ (-2 : ℝ) / 2
  let B : ℝ := (X : ℝ) ^ (-1 : ℝ)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hAhalf : A ≤ (1 : ℝ) / 2 := by dsimp only [A]; linarith
  have hraw : ‖raw s‖ ≤ A := by
    simpa only [raw, s, A] using norm_inghamMollifiedError_four_le hX t
  have hrawDeriv : ‖deriv raw s‖ ≤ B := by
    simpa only [raw, s, B] using norm_deriv_inghamMollifiedError_four_le hX t
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s] at hre
  have hrawAnalytic : AnalyticAt ℂ raw s :=
    (((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const)
  have hdetHas : HasDerivAt (inghamClassicalDetector X)
      (-(2 * raw s * deriv raw s)) s := by
    have h := (hasDerivAt_const s (1 : ℂ)).sub
      (hrawAnalytic.differentiableAt.hasDerivAt.pow 2)
    change HasDerivAt (fun z => 1 - raw z ^ 2) (-(2 * raw s * deriv raw s)) s
    have hfun : ((fun _ : ℂ => (1 : ℂ)) - raw ^ 2) =
        (fun z => 1 - raw z ^ 2) := by
      funext z
      rfl
    rw [hfun] at h
    have hscalar : (0 : ℂ) - (2 : ℂ) * raw s ^ (2 - 1) * deriv raw s =
        -(2 * raw s * deriv raw s) := by
      norm_num
    exact h.congr_deriv hscalar
  have hdetDeriv :
      ‖deriv (inghamClassicalDetector X) s‖ ≤ 2 * A * B := by
    rw [hdetHas.deriv, norm_neg, norm_mul, norm_mul, norm_ofNat]
    have hmul := mul_le_mul hraw hrawDeriv (norm_nonneg _) hA0
    nlinarith
  have hdetLower : (1 : ℝ) / 2 ≤ ‖inghamClassicalDetector X s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((raw s) ^ 2)
    have hrawHalf : ‖raw s‖ ≤ (1 : ℝ) / 2 := hraw.trans hAhalf
    simp only [norm_one, norm_pow] at h
    change (1 : ℝ) / 2 ≤ ‖1 - raw s ^ 2‖
    nlinarith [norm_nonneg (raw s)]
  have hdetPos : 0 < ‖inghamClassicalDetector X s‖ := lt_of_lt_of_le (by norm_num) hdetLower
  rw [logDeriv_apply, norm_div]
  apply (div_le_iff₀ hdetPos).2
  have hscale : 2 * A * B ≤
      (4 * A * B) * ‖inghamClassicalDetector X s‖ := by
    nlinarith [mul_nonneg hA0 hB0]
  exact hdetDeriv.trans hscale

private theorem analyticAt_inghamClassicalDetector_four
    (X : ℕ) (t : ℝ) :
    AnalyticAt ℂ (inghamClassicalDetector X) ((4 : ℂ) + (t : ℂ) * I) := by
  have hs1 : (4 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num at hre
  exact analyticAt_const.sub ((((analyticAt_riemannZeta_of_ne_one hs1).mul
    (analyticAt_inghamMollifier X _)).sub analyticAt_const).pow 2)

private theorem analyticAt_logDeriv_inghamClassicalDetector_four
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    AnalyticAt ℂ (logDeriv (inghamClassicalDetector X))
      ((4 : ℂ) + (t : ℂ) * I) := by
  let s : ℂ := (4 : ℂ) + (t : ℂ) * I
  have hf : AnalyticAt ℂ (inghamClassicalDetector X) s := by
    simpa only [s] using analyticAt_inghamClassicalDetector_four X t
  have hn : inghamClassicalDetector X s ≠ 0 := by
    simpa only [s] using inghamClassicalDetector_ne_zero_four hX t
  have hq := hf.deriv.div hf hn
  exact hq.congr (by
    filter_upwards with z
    simp only [Pi.div_apply, logDeriv_apply])

private theorem continuous_log_norm_inghamClassicalDetector_four
    {X : ℕ} (hX : 1 ≤ X) :
    Continuous fun t : ℝ =>
      Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖ := by
  apply Continuous.log
  · rw [continuous_iff_continuousAt]
    intro t
    have hpath : ContinuousAt (fun u : ℝ => (4 : ℂ) + (u : ℂ) * I) t := by
      fun_prop
    exact (analyticAt_inghamClassicalDetector_four X t).continuousAt.comp_of_eq
      hpath rfl |>.norm
  · intro t
    exact norm_ne_zero_iff.mpr (inghamClassicalDetector_ne_zero_four hX t)

private theorem continuous_re_logDeriv_inghamClassicalDetector_four
    {X : ℕ} (hX : 1 ≤ X) :
    Continuous fun t : ℝ =>
      (logDeriv (inghamClassicalDetector X) ((4 : ℂ) + (t : ℂ) * I)).re := by
  rw [continuous_iff_continuousAt]
  intro t
  have hpath : ContinuousAt (fun u : ℝ => (4 : ℂ) + (u : ℂ) * I) t := by
    fun_prop
  have hcomp : ContinuousAt (fun u : ℝ =>
      logDeriv (inghamClassicalDetector X) ((4 : ℂ) + (u : ℂ) * I)) t :=
    (analyticAt_logDeriv_inghamClassicalDetector_four hX t).continuousAt.comp_of_eq
      hpath rfl
  exact Complex.continuous_re.continuousAt.comp hcomp

theorem neg_intervalIntegral_log_norm_inghamClassicalDetector_four_le
    {X : ℕ} (hX : 1 ≤ X) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    -(∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖) ≤
      (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) := by
  let C : ℝ := 2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2
  have hf := (continuous_log_norm_inghamClassicalDetector_four hX).neg
  have hconst : Continuous (fun _ : ℝ => C) := continuous_const
  have hmono :
      (∫ t in T₁..T₂,
          -Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖) ≤
        ∫ _t in T₁..T₂, C := by
    apply intervalIntegral.integral_mono_on hT
      (hf.intervalIntegrable _ _) (hconst.intervalIntegrable _ _)
    intro t _
    change -Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖ ≤ C
    simpa only [C] using neg_log_norm_inghamClassicalDetector_four_le hX t
  calc
    -(∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖) =
        ∫ t in T₁..T₂,
          -Real.log ‖inghamClassicalDetector X ((4 : ℂ) + (t : ℂ) * I)‖ := by
      rw [intervalIntegral.integral_neg]
    _ ≤ ∫ _t in T₁..T₂, C := hmono
    _ = (T₂ - T₁) * C := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    _ = (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) := rfl

theorem intervalIntegral_re_logDeriv_inghamClassicalDetector_four_le
    {X : ℕ} (hX : 1 ≤ X) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ t in T₁..T₂,
        (logDeriv (inghamClassicalDetector X)
          ((4 : ℂ) + (t : ℂ) * I)).re) ≤
      (T₂ - T₁) *
        (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)) := by
  let C : ℝ := 4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)
  have hf := continuous_re_logDeriv_inghamClassicalDetector_four hX
  have hconst : Continuous (fun _ : ℝ => C) := continuous_const
  have hmono :
      (∫ t in T₁..T₂,
          (logDeriv (inghamClassicalDetector X)
            ((4 : ℂ) + (t : ℂ) * I)).re) ≤
        ∫ _t in T₁..T₂, C := by
    apply intervalIntegral.integral_mono_on hT
      (hf.intervalIntegrable _ _) (hconst.intervalIntegrable _ _)
    intro t _
    calc
      (logDeriv (inghamClassicalDetector X)
          ((4 : ℂ) + (t : ℂ) * I)).re ≤
          |(logDeriv (inghamClassicalDetector X)
            ((4 : ℂ) + (t : ℂ) * I)).re| := le_abs_self _
      _ ≤ ‖logDeriv (inghamClassicalDetector X)
          ((4 : ℂ) + (t : ℂ) * I)‖ := abs_re_le_norm _
      _ ≤ C := by
        simpa only [C] using norm_logDeriv_inghamClassicalDetector_four_le hX t
  calc
    (∫ t in T₁..T₂,
        (logDeriv (inghamClassicalDetector X)
          ((4 : ℂ) + (t : ℂ) * I)).re) ≤ ∫ _t in T₁..T₂, C := hmono
    _ = (T₂ - T₁) * C := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    _ = (T₂ - T₁) *
        (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)) := rfl

/-- Exact horizontal argument-variation remainder after the movable far-right edge is separated. -/
noncomputable def inghamClassicalHorizontalBoundary
    (X : ℕ) (c d T₁ T₂ : ℝ) : ℝ :=
  (∫ x in c..d,
      (x - c) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im) -
    ∫ x in c..d,
      (x - c) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im

theorem inghamClassicalLittlewoodBoundary_four_le
    {X : ℕ} (hX : 1 ≤ X) {c T₁ T₂ : ℝ}
    (hc : c ≤ 4) (hT : T₁ ≤ T₂) :
    inghamClassicalLittlewoodBoundary X c 4 T₁ T₂ ≤
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X ((c : ℂ) + (t : ℂ) * I)‖) +
      (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
      (4 - c) * ((T₂ - T₁) *
        (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
      inghamClassicalHorizontalBoundary X c 4 T₁ T₂ := by
  have hlog := neg_intervalIntegral_log_norm_inghamClassicalDetector_four_le hX hT
  have hderiv := intervalIntegral_re_logDeriv_inghamClassicalDetector_four_le hX hT
  have hderivMul := mul_le_mul_of_nonneg_left hderiv (by linarith : 0 ≤ 4 - c)
  unfold inghamClassicalLittlewoodBoundary weightedLittlewoodBoundary
  dsimp only [inghamClassicalHorizontalBoundary]
  norm_num at hlog hderiv hderivMul ⊢
  linarith

theorem farRightFour_verticalLoss_le_one
    {X : ℕ} (hX : 4 ≤ X) {T₁ T₂ : ℝ}
    (hT : T₁ ≤ T₂) (hlen : T₂ - T₁ ≤ 2 * (X : ℝ)) :
    (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
      (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
        (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) ≤ 1 := by
  let x : ℝ := X
  have hx4 : (4 : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast hX
  change T₂ - T₁ ≤ 2 * x at hlen
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx4
  have hx1 : 1 ≤ x := by linarith
  have hlen0 : 0 ≤ T₂ - T₁ := sub_nonneg.mpr hT
  have hneg2 : x ^ (-2 : ℝ) ≤ (1 : ℝ) / 16 := by
    have h := Real.rpow_le_rpow_of_nonpos (x := (4 : ℝ)) (y := x) (z := (-2 : ℝ))
      (by norm_num) hx4 (by norm_num)
    norm_num at h ⊢
    exact h
  have hneg3 : x ^ (-3 : ℝ) ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsq : (x ^ (-2 : ℝ)) ^ (2 : ℕ) = x ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hlogEq :
      (2 * x) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) = x ^ (-3 : ℝ) := by
    calc
      (2 * x) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) =
          x * (x ^ (-2 : ℝ)) ^ 2 := by ring
      _ = x * x ^ (-4 : ℝ) := by rw [hsq]
      _ = x ^ (-3 : ℝ) := by
        calc
          x * x ^ (-4 : ℝ) = x ^ (1 : ℝ) * x ^ (-4 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + (-4 : ℝ)) := (Real.rpow_add hx 1 (-4)).symm
          _ = x ^ (-3 : ℝ) := by norm_num
  have hmix : x * x ^ (-2 : ℝ) * x ^ (-1 : ℝ) = x ^ (-2 : ℝ) := by
    calc
      x * x ^ (-2 : ℝ) * x ^ (-1 : ℝ) =
          (x ^ (1 : ℝ) * x ^ (-2 : ℝ)) * x ^ (-1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-2 : ℝ)) * x ^ (-1 : ℝ) := by
        rw [Real.rpow_add hx]
      _ = x ^ (-1 : ℝ) * x ^ (-1 : ℝ) := by norm_num
      _ = x ^ ((-1 : ℝ) + (-1 : ℝ)) := (Real.rpow_add hx (-1) (-1)).symm
      _ = x ^ (-2 : ℝ) := by norm_num
  have hderivEq :
      (4 - inghamFixedGabrielSigma) * ((2 * x) *
        (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) =
        4 * (4 - inghamFixedGabrielSigma) * x ^ (-2 : ℝ) := by
    rw [show (2 * x) * (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ)) =
        4 * (x * x ^ (-2 : ℝ) * x ^ (-1 : ℝ)) by ring, hmix]
    ring
  have hlogMono :
      (T₂ - T₁) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) ≤ x ^ (-3 : ℝ) := by
    calc
      (T₂ - T₁) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) ≤
          (2 * x) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) := by
        gcongr
      _ = x ^ (-3 : ℝ) := hlogEq
  have hcoef : 0 ≤ 4 - inghamFixedGabrielSigma := by
    norm_num [inghamFixedGabrielSigma]
  have hderivMono :
      (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
        (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) ≤
        4 * (4 - inghamFixedGabrielSigma) * x ^ (-2 : ℝ) := by
    calc
      (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
          (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) ≤
          (4 - inghamFixedGabrielSigma) * ((2 * x) *
            (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) := by
        gcongr
      _ = 4 * (4 - inghamFixedGabrielSigma) * x ^ (-2 : ℝ) := hderivEq
  change (T₂ - T₁) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) +
      (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
        (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) ≤ 1
  have hsum :
      (T₂ - T₁) * (2 * (x ^ (-2 : ℝ) / 2) ^ 2) +
          (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
            (4 * (x ^ (-2 : ℝ) / 2) * x ^ (-1 : ℝ))) ≤
        (1 + 4 * (4 - inghamFixedGabrielSigma)) * x ^ (-2 : ℝ) := by
    calc
      _ ≤ x ^ (-3 : ℝ) + 4 * (4 - inghamFixedGabrielSigma) * x ^ (-2 : ℝ) :=
        add_le_add hlogMono hderivMono
      _ ≤ x ^ (-2 : ℝ) + 4 * (4 - inghamFixedGabrielSigma) * x ^ (-2 : ℝ) :=
        add_le_add hneg3 (le_refl _)
      _ = (1 + 4 * (4 - inghamFixedGabrielSigma)) * x ^ (-2 : ℝ) := by ring
  calc
    _ ≤ (1 + 4 * (4 - inghamFixedGabrielSigma)) * x ^ (-2 : ℝ) := hsum
    _ ≤ (1 + 4 * (4 - inghamFixedGabrielSigma)) * ((1 : ℝ) / 16) := by
      gcongr
    _ ≤ 1 := by norm_num [inghamFixedGabrielSigma]

theorem eventually_exists_zetaZeroMass_le_inghamClassicalBoundary_farRightFour :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            inghamClassicalLittlewoodBoundary X inghamFixedGabrielSigma
              4 T₁ T₂ + 4 * Real.pi * (1 - inghamFixedGabrielSigma) := by
  filter_upwards [eventually_exists_inghamDetector_admissibleContour_at_rightEdge
    (c := inghamFixedGabrielSigma) (beta := 4)
    (by norm_num [inghamFixedGabrielSigma]) (by norm_num)] with X hcontour
  intro H
  obtain ⟨T₁, hT₁, T₂, hT₂, hbot, htop, hright, hmass⟩ := hcontour H
  have hT₁neg : T₁ < 0 := by
    have := abs_nonneg H
    linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := lt_of_le_of_lt (abs_nonneg H) hT₂.1
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamFixedGabrielSigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) (by norm_num)
    hT₁neg hT₂pos hbot htop hright
  rw [hgauge] at hmass
  exact ⟨T₁, hT₁, T₂, hT₂, hmass⟩

/-- Selected-contour Route T inequality with every non-horizontal boundary contribution explicit. -/
theorem eventually_exists_zetaZeroMass_le_center_horizontal_farRightFour :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            (∫ t in T₁..T₂,
              Real.log ‖inghamClassicalDetector X
                ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖) +
            (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
            inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ +
            4 * Real.pi * (1 - inghamFixedGabrielSigma) := by
  filter_upwards [eventually_exists_zetaZeroMass_le_inghamClassicalBoundary_farRightFour,
    eventually_ge_atTop (1 : ℕ)] with X hcontour hX
  intro H
  obtain ⟨T₁, hT₁, T₂, hT₂, hmass⟩ := hcontour H
  have hT : T₁ ≤ T₂ := by
    have := abs_nonneg H
    linarith [hT₁.2, hT₂.1]
  have hboundary := inghamClassicalLittlewoodBoundary_four_le hX
    (c := inghamFixedGabrielSigma) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) hT
  refine ⟨T₁, hT₁, T₂, hT₂, hmass.trans ?_⟩
  linarith

/-- Route T after center, pole, contour, and vertical-right closure.  Only horizontal argument
variation remains unestimated; both right-edge losses are displayed with their decaying powers. -/
theorem exists_eventually_zetaZeroMass_le_centerMoment_horizontal_farRightFour :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∃ T₁ ∈ Set.Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Set.Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            C * (X : ℝ) ^ inghamFixedGabrielRouteTExponent +
            (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
            inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ +
            4 * Real.pi * (1 - inghamFixedGabrielSigma) := by
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_fixedGabrielCenter_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_exists_zetaZeroMass_le_center_horizontal_farRightFour,
    eventually_ge_atTop (4 : ℕ)] with X hcontour hX
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hH0 : 0 ≤ (X : ℝ) - 2 := by linarith
  have habs : |(X : ℝ) - 2| = (X : ℝ) - 2 := abs_of_nonneg hH0
  obtain ⟨T₁, hT₁, T₂, hT₂, hmass⟩ := hcontour ((X : ℝ) - 2)
  have hT₁' : T₁ ∈ Set.Ioo (-(X : ℝ)) (-(X : ℝ) + 1) := by
    rw [habs] at hT₁
    constructor <;> linarith [hT₁.1, hT₁.2]
  have hT₂' : T₂ ∈ Set.Ioo ((X : ℝ) - 2) ((X : ℝ) - 1) := by
    rw [habs] at hT₂
    constructor <;> linarith [hT₂.1, hT₂.2]
  have hT : T₁ ≤ T₂ := by linarith [hT₁'.2, hT₂'.1]
  have hleft := hcenter hX (le_of_lt hT₁'.1) hT (by linarith [hT₂'.2])
  have hleft' :
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X
          ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖) ≤
        C * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
    simpa only [inghamClassicalDetector] using hleft
  refine ⟨T₁, hT₁', T₂, hT₂', hmass.trans ?_⟩
  linarith [hleft']

/-- Complete Route T boundary reduction: fixed center power plus horizontal argument variation.
Contour selection, pole charge, and both vertical edges are absorbed into one unconditional
constant. -/
theorem exists_eventually_zetaZeroMass_le_fixedPower_add_horizontalFarRightFour :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∃ T₁ ∈ Set.Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Set.Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            K * (X : ℝ) ^ inghamFixedGabrielRouteTExponent +
              inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_zetaZeroMass_le_centerMoment_horizontal_farRightFour
  let P : ℝ := 4 * Real.pi * (1 - inghamFixedGabrielSigma)
  let K : ℝ := C + 1 + P
  have hP : 0 ≤ P := by
    dsimp only [P]
    have hpi := Real.pi_pos.le
    have hc : 0 ≤ 1 - inghamFixedGabrielSigma := by
      norm_num [inghamFixedGabrielSigma]
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (4 : ℕ)] with X hselected hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hmass⟩ := hselected
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hT : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1, hXR]
  have hlen : T₂ - T₁ ≤ 2 * (X : ℝ) := by linarith [hT₁.1, hT₂.2]
  have hvertical := farRightFour_verticalLoss_le_one hX hT hlen
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hq : 0 ≤ inghamFixedGabrielRouteTExponent := by
    rw [inghamFixedGabrielRouteTExponent_eq]
    norm_num
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ inghamFixedGabrielRouteTExponent :=
    Real.one_le_rpow hX1 hq
  have hconst : 1 + P ≤ (1 + P) *
      (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
    exact le_mul_of_one_le_right (by positivity) hpow1
  refine ⟨T₁, hT₁, T₂, hT₂, hmass.trans ?_⟩
  dsimp only [K, P]
  dsimp only [P] at hconst
  linarith

end

end RHTower.Sieve
