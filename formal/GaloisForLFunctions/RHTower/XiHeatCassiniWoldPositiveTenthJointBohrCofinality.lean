import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelAbelRenormalization
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinOrderedPrimeGap
import GaloisForLFunctions.RHTower.ExponentialSumMeanSquareLower
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Positive-height joint Bohr cofinality for the T2 Wold residual

The separate Wold and prime-log-mesh currents diverge on the positive Borel ray.  Keeping the
terminal, edge, and holonomy pieces together exposes Abel increment coefficients

`(R_(n+1) - R_n) exp(h_(n+1)/10)`.

The ordered-prime Hoheisel estimate and the depth-one Wold majorant make these exact increments
square summable.  Finite Bohr--Cesàro Parseval then proves that the original cancellation-preserving
positive-height cutoffs are Cauchy in mean square.  No pointwise evaluation or RH input is used.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem exp_oneFifth_xiMassNthPrimeLogHeight_eq_rpow (N : ℕ) :
    Real.exp (xiMassNthPrimeLogHeight N / 5) =
      (nthPrimeSubtype N : ℝ) ^ (1 / 5 : ℝ) := by
  rw [Real.rpow_def_of_pos (nthPrimeSubtype_pos N)]
  unfold xiMassNthPrimeLogHeight
  congr 1
  ring

theorem exp_neg_nineHundredth_xiMassNthPrimeLogHeight_eq_rpow (N : ℕ) :
    Real.exp (-(9 / 100 : ℝ) * xiMassNthPrimeLogHeight N) =
      (nthPrimeSubtype N : ℝ) ^ (-(9 / 100 : ℝ)) := by
  rw [Real.rpow_def_of_pos (nthPrimeSubtype_pos N)]
  unfold xiMassNthPrimeLogHeight
  congr 1
  ring

theorem summable_xiHeatCassiniOrderedPrimeLogGap_sq_mul_positiveFifthHeight :
    Summable (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLogGap N ^ 2 *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5)) := by
  let C : ℝ := 2 * (2 : ℝ) ^ (1 / 5 : ℝ)
  have hmajor : Summable (fun N : ℕ =>
      C * (xiHeatCassiniOrderedPrimeLogGap N *
        Real.exp (-(9 / 100 : ℝ) * xiMassNthPrimeLogHeight N))) :=
    (summable_primeLogGap_mul_exp_neg_height
      (by norm_num : (0 : ℝ) < 9 / 100)).mul_left C
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Sieve.eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase]
      with N hgap
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  let gap : ℝ := q - p
  let rel : ℝ := gap / p
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hp : 0 < p := by simpa [p] using nthPrimeSubtype_pos N
  have hq : 0 < q := by simpa [q] using nthPrimeSubtype_pos (N + 1)
  have hgap0 : 0 ≤ gap := by
    dsimp only [gap, p, q]
    exact sub_nonneg.mpr (by
      exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N))
  have hrel0 : 0 ≤ rel := div_nonneg hgap0 hp.le
  have hdelta0 : 0 ≤ delta := by
    simpa [delta] using xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdeltaRel : delta ≤ rel := by
    simpa [delta, rel, gap, p, q, xiHeatCassiniOrderedPrimeGap] using
      xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
  have hrelLog : rel ≤ 2 * delta := by
    have hbase := primeGap_div_two_prime_le_primeLogGap N
    dsimp only [rel, gap, p, q, delta, xiHeatCassiniOrderedPrimeGap] at hbase ⊢
    have hpne : (nthPrimeSubtype N : ℝ) ≠ 0 := (nthPrimeSubtype_pos N).ne'
    calc
      ((nthPrimeSubtype (N + 1) : ℝ) - (nthPrimeSubtype N : ℝ)) /
          (nthPrimeSubtype N : ℝ) =
        2 * (((nthPrimeSubtype (N + 1) : ℝ) - (nthPrimeSubtype N : ℝ)) /
          (2 * (nthPrimeSubtype N : ℝ))) := by field_simp
      _ ≤ 2 * xiHeatCassiniOrderedPrimeLogGap N := by gcongr
  have hrelPow : rel ≤ p ^ (-(29 / 100 : ℝ)) := by
    have hgap' : gap ≤ p ^ (71 / 100 : ℝ) := by
      simpa [gap, p, q, Sieve.routeTHoheiselEveryBaseExponent] using hgap
    apply (div_le_iff₀ hp).2
    change gap ≤ p ^ (-(29 / 100 : ℝ)) * p
    calc
      gap ≤ p ^ (71 / 100 : ℝ) := hgap'
      _ = p ^ (-(29 / 100 : ℝ)) * p := by
        rw [show -(29 / 100 : ℝ) = 71 / 100 - 1 by norm_num,
          Real.rpow_sub hp, Real.rpow_one]
        field_simp
  have hqTwo : q ≤ 2 * p := by
    change ((nthPrimeSubtype (N + 1) : ℕ) : ℝ) ≤
      2 * ((nthPrimeSubtype N : ℕ) : ℝ)
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hqPow : q ^ (1 / 5 : ℝ) ≤
      (2 : ℝ) ^ (1 / 5 : ℝ) * p ^ (1 / 5 : ℝ) := by
    calc
      q ^ (1 / 5 : ℝ) ≤ (2 * p) ^ (1 / 5 : ℝ) := by
        exact Real.rpow_le_rpow hq.le hqTwo (by norm_num)
      _ = (2 : ℝ) ^ (1 / 5 : ℝ) * p ^ (1 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hp.le]
  have htarget : delta ^ 2 * q ^ (1 / 5 : ℝ) ≤
      C * (delta * p ^ (-(9 / 100 : ℝ))) := by
    calc
      delta ^ 2 * q ^ (1 / 5 : ℝ) ≤ rel ^ 2 * q ^ (1 / 5 : ℝ) := by
        gcongr
      _ ≤ rel ^ 2 * ((2 : ℝ) ^ (1 / 5 : ℝ) * p ^ (1 / 5 : ℝ)) := by
        gcongr
      _ ≤ (p ^ (-(29 / 100 : ℝ)) * (2 * delta)) *
          ((2 : ℝ) ^ (1 / 5 : ℝ) * p ^ (1 / 5 : ℝ)) := by
        gcongr
        calc
          rel ^ 2 = rel * rel := by ring
          _ ≤ p ^ (-(29 / 100 : ℝ)) * (2 * delta) := by gcongr
      _ = C * (delta * p ^ (-(9 / 100 : ℝ))) := by
        dsimp only [C]
        calc
          p ^ (-(29 / 100 : ℝ)) * (2 * delta) *
              ((2 : ℝ) ^ (1 / 5 : ℝ) * p ^ (1 / 5 : ℝ)) =
            2 * (2 : ℝ) ^ (1 / 5 : ℝ) * delta *
              (p ^ (-(29 / 100 : ℝ)) * p ^ (1 / 5 : ℝ)) := by ring
          _ = 2 * (2 : ℝ) ^ (1 / 5 : ℝ) * delta *
              p ^ (-(9 / 100 : ℝ)) := by
            rw [← Real.rpow_add hp]
            norm_num
          _ = 2 * (2 : ℝ) ^ (1 / 5 : ℝ) *
              (delta * p ^ (-(9 / 100 : ℝ))) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (Real.exp_nonneg _)), exp_oneFifth_xiMassNthPrimeLogHeight_eq_rpow,
    exp_neg_nineHundredth_xiMassNthPrimeLogHeight_eq_rpow]
  simpa [p, q, delta] using htarget

theorem summable_woldCoeff_sq_mul_positiveFifthHeight :
    Summable (fun N : ℕ =>
      woldCoeff 1 (nthPrimeSubtype (N + 1)) ^ 2 *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5)) := by
  have hinj : Function.Injective
      (fun N : ℕ => (nthPrimeSubtype (N + 1) : ℕ)) := by
    intro M N hMN
    have hindex : M + 1 = N + 1 :=
      nthPrimeSubtype_strictMono.injective hMN
    omega
  have hmajor : Summable (fun N : ℕ =>
      primeLogPowWeight 2 (nthPrimeSubtype (N + 1) : ℕ) *
        ((nthPrimeSubtype (N + 1) : ℝ) ^ (-(4 / 5 : ℝ)))) :=
    (summable_primeLogPowWeight_rpow 1
      (by norm_num : (0 : ℝ) < 4 / 5)).comp_injective hinj
  apply hmajor.of_nonneg_of_le
  · intro N
    exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · intro N
    let q : ℝ := nthPrimeSubtype (N + 1)
    let h : ℝ := xiMassNthPrimeLogHeight (N + 1)
    let w : ℝ := woldCoeff 1 (nthPrimeSubtype (N + 1))
    have hq : 0 < q := by simpa [q] using nthPrimeSubtype_pos (N + 1)
    have hh : h = Real.log q := by rfl
    have hw0 : 0 ≤ w := by
      simpa [w] using woldCoeff_nonneg 1 (nthPrimeSubtype (N + 1))
    have hw : w ≤ h / q := by
      have hbase :=
        (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one
          (nthPrimeSubtype (N + 1))).1
      rw [xiMassPrimeHarmonicRealCoefficient] at hbase
      change w ≤ Real.log q / q
      simpa [w, h, q, xiMassNthPrimeLogHeight] using hbase
    have hw' : w ≤ Real.log q / q := by simpa [hh] using hw
    have hweight : Real.exp (h / 5) = q ^ (1 / 5 : ℝ) := by
      simpa [h, q] using exp_oneFifth_xiMassNthPrimeLogHeight_eq_rpow (N + 1)
    have hbound : w ^ 2 * Real.exp (h / 5) ≤
        (Real.log q) ^ 2 * q ^ (-(9 / 5 : ℝ)) := by
      rw [hweight]
      calc
        w ^ 2 * q ^ (1 / 5 : ℝ) ≤ (Real.log q / q) ^ 2 * q ^ (1 / 5 : ℝ) := by
          gcongr
        _ = (Real.log q) ^ 2 * q ^ (-(9 / 5 : ℝ)) := by
          rw [div_pow]
          have hquot : q ^ (1 / 5 : ℝ) / q ^ 2 =
              q ^ (-(9 / 5 : ℝ)) := by
            calc
              q ^ (1 / 5 : ℝ) / q ^ 2 =
                  q ^ (1 / 5 : ℝ) / q ^ (2 : ℝ) := by norm_num
              _ = q ^ ((1 / 5 : ℝ) - 2) :=
                (Real.rpow_sub hq (1 / 5 : ℝ) 2).symm
              _ = q ^ (-(9 / 5 : ℝ)) := by norm_num
          calc
            (Real.log q) ^ 2 / q ^ 2 * q ^ (1 / 5 : ℝ) =
                (Real.log q) ^ 2 * (q ^ (1 / 5 : ℝ) / q ^ 2) := by ring
            _ = (Real.log q) ^ 2 * q ^ (-(9 / 5 : ℝ)) := by rw [hquot]
    calc
      woldCoeff 1 (nthPrimeSubtype (N + 1)) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) =
        w ^ 2 * Real.exp (h / 5) := by rfl
      _ ≤ (Real.log q) ^ 2 * q ^ (-(9 / 5 : ℝ)) := hbound
      _ = primeLogPowWeight 2 (nthPrimeSubtype (N + 1) : ℕ) *
          ((nthPrimeSubtype (N + 1) : ℝ) ^ (-(4 / 5 : ℝ))) := by
        rw [primeLogPowWeight, if_pos (nthPrimeSubtype (N + 1)).prop]
        change (Real.log q) ^ 2 * q ^ (-(9 / 5 : ℝ)) =
          ((Real.log q) ^ 2 / q) * q ^ (-(4 / 5 : ℝ))
        have hpow : q ^ (-(9 / 5 : ℝ)) =
            q ^ (-(4 / 5 : ℝ)) / q := by
          calc
            q ^ (-(9 / 5 : ℝ)) = q ^ (-(4 / 5 : ℝ) - 1) := by norm_num
            _ = q ^ (-(4 / 5 : ℝ)) / q ^ (1 : ℝ) :=
              Real.rpow_sub hq (-(4 / 5 : ℝ)) 1
            _ = q ^ (-(4 / 5 : ℝ)) / q := by rw [Real.rpow_one]
        rw [hpow]
        field_simp [ne_of_gt hq]

/-- Abel increment of the terminal-plus-edge current at positive height `1/10`. -/
def xiHeatCassiniWoldPositiveTenthJointCoefficient (N : ℕ) : ℂ :=
  ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
    (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ)

/-- Ordered prime-log frequency belonging to the `N`th Abel increment. -/
def xiHeatCassiniWoldPositiveTenthJointFrequency (N : ℕ) : ℝ :=
  xiMassNthPrimeLogHeight (N + 1)

theorem xiHeatCassiniOrderedPrimeComplexNegativePhase_positiveTenth
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniOrderedPrimeComplexNegativePhase N
        ((x : ℂ) + Complex.I * ((1 / 10 : ℝ) : ℂ)) =
      (Real.exp (xiMassNthPrimeLogHeight N / 10) : ℂ) *
        Complex.exp (-Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * (x : ℂ)) := by
  unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
  rw [show (Real.exp (xiMassNthPrimeLogHeight N / 10) : ℂ) =
      Complex.exp ((xiMassNthPrimeLogHeight N / 10 : ℝ) : ℂ) by simp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    rw [pow_two, Complex.I_mul_I]]
  ring

/-- Abel coordinates of the finite cancellation-preserving current. -/
def xiHeatCassiniWoldPositiveTenthJointAbelCurrent (N : ℕ) (x : ℝ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
      xiHeatCassiniOrderedPrimeComplexNegativePhase 0
        ((x : ℂ) + Complex.I * ((1 / 10 : ℝ) : ℂ)) +
    expSum (Finset.range N) xiHeatCassiniWoldPositiveTenthJointCoefficient
      xiHeatCassiniWoldPositiveTenthJointFrequency x

theorem xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_positiveTenth_eq_abel
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) N =
      xiHeatCassiniWoldPositiveTenthJointAbelCurrent N x := by
  rw [← integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace_eq_renormalized,
    integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace]
  rw [xiHeatCassiniWoldResidualComplexFiniteAbel]
  unfold xiHeatCassiniWoldPositiveTenthJointAbelCurrent expSum
  apply congrArg₂ (fun a b : ℂ => a + b) rfl
  apply Finset.sum_congr rfl
  intro n hn
  rw [xiHeatCassiniWoldPositiveTenthJointCoefficient,
    xiHeatCassiniWoldPositiveTenthJointFrequency,
    xiHeatCassiniOrderedPrimeComplexNegativePhase_positiveTenth]
  push_cast
  ring

/-- Exact positive-height residual increments are square summable. -/
theorem summable_norm_sq_xiHeatCassiniWoldPositiveTenthJointCoefficient :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldPositiveTenthJointCoefficient N‖ ^ 2) := by
  have hmajor : Summable (fun N : ℕ =>
      2 * (woldCoeff 1 (nthPrimeSubtype (N + 1)) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) +
        xiHeatCassiniOrderedPrimeLogGap N ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5))) :=
    (summable_woldCoeff_sq_mul_positiveFifthHeight.add
      summable_xiHeatCassiniOrderedPrimeLogGap_sq_mul_positiveFifthHeight).mul_left 2
  apply hmajor.of_nonneg_of_le
  · intro N
    positivity
  · intro N
    let d : ℝ :=
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
    let w : ℝ := woldCoeff 1 (nthPrimeSubtype (N + 1))
    let g : ℝ := xiHeatCassiniOrderedPrimeLogGap N
    let e : ℝ := Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10)
    have hd : d = w - g := by
      simpa [d, w, g, xiHeatCassiniOrderedPrimeLogGap] using
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub N
    have hsq : d ^ 2 ≤ 2 * (w ^ 2 + g ^ 2) := by
      rw [hd]
      nlinarith [sq_nonneg (w + g)]
    have he2 : e ^ 2 =
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) := by
      dsimp only [e]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    change ‖(d : ℂ) * (e : ℂ)‖ ^ 2 ≤
      2 * (w ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) +
        g ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5))
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, sq_abs]
    change d ^ 2 * e ^ 2 ≤
      2 * (w ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) +
        g ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5))
    rw [he2]
    have hmul : d ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) ≤
        (2 * (w ^ 2 + g ^ 2)) *
          Real.exp (xiMassNthPrimeLogHeight (N + 1) / 5) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    nlinarith

theorem xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_positiveTenth_sub_eq_expSum
    {L M : ℕ} (hLM : L ≤ M) (x : ℝ) :
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) M -
        xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) L =
      expSum (Finset.Ico L M) xiHeatCassiniWoldPositiveTenthJointCoefficient
        xiHeatCassiniWoldPositiveTenthJointFrequency x := by
  rw [
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_positiveTenth_eq_abel,
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_positiveTenth_eq_abel]
  unfold xiHeatCassiniWoldPositiveTenthJointAbelCurrent expSum
  let f : ℕ → ℂ := fun j =>
    xiHeatCassiniWoldPositiveTenthJointCoefficient j *
      Complex.exp (-Complex.I *
        (xiHeatCassiniWoldPositiveTenthJointFrequency j : ℂ) * (x : ℂ))
  have hsplit :
      (∑ j ∈ Finset.range L, f j) + (∑ j ∈ Finset.Ico L M, f j) =
        ∑ j ∈ Finset.range M, f j := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le L) hLM
  change (_ + ∑ j ∈ Finset.range M, f j) -
      (_ + ∑ j ∈ Finset.range L, f j) =
    ∑ j ∈ Finset.Ico L M, f j
  linear_combination -hsplit

theorem xiHeatCassiniWoldPositiveTenthJointFrequency_injective :
    Function.Injective xiHeatCassiniWoldPositiveTenthJointFrequency := by
  intro L M hLM
  have hsucc : L + 1 = M + 1 := by
    apply nthPrimeSubtype_log_strictMono.injective
    simpa [xiHeatCassiniWoldPositiveTenthJointFrequency,
      xiMassNthPrimeLogHeight] using hLM
  omega

/-- Exact Bohr mean-square law for every tail of the positive-height joint current. -/
theorem tendsto_xiHeatCassiniWoldPositiveTenthJointCurrent_tail_cesaro_normSq
    {L M : ℕ} (hLM : L ≤ M) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ x in (1 : ℝ)..T,
      ‖xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) M -
        xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) L‖ ^ 2)
      atTop
      (𝓝 (∑ j ∈ Finset.Ico L M,
        ‖xiHeatCassiniWoldPositiveTenthJointCoefficient j‖ ^ 2)) := by
  have hparseval := tendsto_cesaro_normSq_expSum
    (Finset.Ico L M) xiHeatCassiniWoldPositiveTenthJointCoefficient
      xiHeatCassiniWoldPositiveTenthJointFrequency
      xiHeatCassiniWoldPositiveTenthJointFrequency_injective.injOn
  simpa only [
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_positiveTenth_sub_eq_expSum
      hLM] using hparseval

/-- The cancellation-preserving positive-height T2 current is Cauchy in Bohr mean square. -/
theorem xiHeatCassiniWoldPositiveTenthJointCurrent_bohrCauchy :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ L M : ℕ, N ≤ L → L ≤ M →
        (∑ j ∈ Finset.Ico L M,
          ‖xiHeatCassiniWoldPositiveTenthJointCoefficient j‖ ^ 2) < ε ∧
        Tendsto (fun T : ℝ => (1 / T) * ∫ x in (1 : ℝ)..T,
          ‖xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) M -
            xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x (1 / 10) L‖ ^ 2)
          atTop
          (𝓝 (∑ j ∈ Finset.Ico L M,
            ‖xiHeatCassiniWoldPositiveTenthJointCoefficient j‖ ^ 2)) := by
  intro ε hε
  let c : ℕ → ℝ := fun j =>
    ‖xiHeatCassiniWoldPositiveTenthJointCoefficient j‖ ^ 2
  have hc : Summable c :=
    summable_norm_sq_xiHeatCassiniWoldPositiveTenthJointCoefficient
  let S : ℝ := ∑' j, c j
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, c j)
      atTop (𝓝 S) := by
    simpa [S] using hc.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ N in atTop, S - ε < ∑ j ∈ Finset.range N, c j := by
    apply htend.eventually
    exact eventually_gt_nhds (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro L M hNL hLM
  have hlow : S - ε < ∑ j ∈ Finset.range L, c j := hN L hNL
  have hupper : (∑ j ∈ Finset.range M, c j) ≤ S := by
    exact Summable.sum_le_tsum (Finset.range M) (fun j hj => sq_nonneg _) hc
  have hsplit :
      (∑ j ∈ Finset.range L, c j) + (∑ j ∈ Finset.Ico L M, c j) =
        ∑ j ∈ Finset.range M, c j := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le L) hLM
  constructor
  · change (∑ j ∈ Finset.Ico L M, c j) < ε
    linarith
  · exact tendsto_xiHeatCassiniWoldPositiveTenthJointCurrent_tail_cesaro_normSq hLM

end

end RHTower
