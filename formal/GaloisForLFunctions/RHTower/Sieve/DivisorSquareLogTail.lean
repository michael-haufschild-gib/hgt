import GaloisForLFunctions.RHTower.Sieve.DivisorSquareTail
import GaloisForLFunctions.RHTower.FourthMomentDiagonal
import Mathlib.NumberTheory.AbelSummation

namespace RHTower.Sieve

open Finset MeasureTheory

private noncomputable def divisorSquareLogCoeff (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ 2

@[simp] private theorem divisorSquareLogCoeff_zero : divisorSquareLogCoeff 0 = 0 := by
  simp [divisorSquareLogCoeff]

private theorem divisorSquareLogPartialSum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 0 N, divisorSquareLogCoeff n ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons, divisorSquareLogCoeff_zero, zero_add,
    ← Icc_add_one_left_eq_Ioc]
  simpa [divisorSquareLogCoeff] using sum_card_divisors_pow_le_polylog 2 N hN

private noncomputable def logSquareInverseSquare (t : ℝ) : ℝ :=
  Real.log t ^ 2 / t ^ 2

private theorem hasDerivAt_logSquareInverseSquare {t : ℝ} (ht : 0 < t) :
    HasDerivAt logSquareInverseSquare
      (2 * Real.log t * (1 - Real.log t) / t ^ 3) t := by
  unfold logSquareInverseSquare
  convert ((Real.hasDerivAt_log ht.ne').pow 2).div
      ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne') using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht.ne']
  ring_nf

private theorem logSquareInverseSquare_differentiableAt {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ logSquareInverseSquare t := by
  exact (hasDerivAt_logSquareInverseSquare ht).differentiableAt

private theorem logSquareInverseSquare_deriv {t : ℝ} (ht : 0 < t) :
    deriv logSquareInverseSquare t =
      2 * Real.log t * (1 - Real.log t) / t ^ 3 := by
  exact (hasDerivAt_logSquareInverseSquare ht).deriv

private noncomputable def logQuinticTailPrimitive (t : ℝ) : ℝ :=
  (Real.log t ^ 5 + 10 * Real.log t ^ 4 + 50 * Real.log t ^ 3 +
      160 * Real.log t ^ 2 + 325 * Real.log t + 326) / t

private theorem hasDerivAt_logQuinticTailPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt logQuinticTailPrimitive
      (-((1 + Real.log t) ^ 5 / t ^ 2)) t := by
  unfold logQuinticTailPrimitive
  have hlog := Real.hasDerivAt_log ht.ne'
  have h5 := hlog.pow 5
  have h4 := (hasDerivAt_const (x := t) (c := (10 : ℝ))).mul (hlog.pow 4)
  have h3 := (hasDerivAt_const (x := t) (c := (50 : ℝ))).mul (hlog.pow 3)
  have h2 := (hasDerivAt_const (x := t) (c := (160 : ℝ))).mul (hlog.pow 2)
  have h1 := (hasDerivAt_const (x := t) (c := (325 : ℝ))).mul hlog
  have h0 := hasDerivAt_const (x := t) (c := (326 : ℝ))
  have hnum := ((((h5.add h4).add h3).add h2).add h1).add h0
  convert hnum.div (hasDerivAt_id t) ht.ne' using 1 <;> try rfl
  simp
  field_simp [ht.ne']
  ring_nf

private noncomputable def logQuinticKernel (t : ℝ) : ℝ :=
  (1 + Real.log t) ^ 5 / t ^ 2

private theorem logQuinticKernel_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn logQuinticKernel (Set.Icc a b) := by
  unfold logQuinticKernel
  apply ContinuousOn.div
    ((continuousOn_const.add (Real.continuousOn_log.mono (fun t ht => by
      exact ne_of_gt (lt_of_lt_of_le ha ht.1)))).pow 5)
    (continuousOn_id.pow 2)
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha ht.1))

private theorem integral_logQuinticKernel (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, logQuinticKernel t =
      logQuinticTailPrimitive a - logQuinticTailPrimitive b := by
  have hcont := logQuinticKernel_continuousOn (b := b) ha
  have hpcont : ContinuousOn logQuinticTailPrimitive (Set.Icc a b) := by
    intro t ht
    exact (hasDerivAt_logQuinticTailPrimitive
      (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  have hkint : IntervalIntegrable (fun t => -logQuinticKernel t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hcont.neg.integrableOn_Icc
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hpcont
    (fun t ht => hasDerivAt_logQuinticTailPrimitive (lt_of_lt_of_le ha ht.1.le))
    (by simpa [logQuinticKernel] using hkint)
  rw [intervalIntegral.integral_neg] at hfund
  simpa [logQuinticKernel] using congrArg Neg.neg hfund

private theorem logQuintic_le_tailNumerator {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ 5 ≤
      Real.log t ^ 5 + 10 * Real.log t ^ 4 + 50 * Real.log t ^ 3 +
        160 * Real.log t ^ 2 + 325 * Real.log t + 326 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  ring_nf
  nlinarith [pow_nonneg hlog 2, pow_nonneg hlog 3, pow_nonneg hlog 4,
    pow_nonneg hlog 5]

private theorem tailNumerator_le_threeHundredTwentySix_logQuintic
    {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ^ 5 + 10 * Real.log t ^ 4 + 50 * Real.log t ^ 3 +
        160 * Real.log t ^ 2 + 325 * Real.log t + 326 ≤
      326 * (1 + Real.log t) ^ 5 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  ring_nf
  nlinarith [pow_nonneg hlog 2, pow_nonneg hlog 3, pow_nonneg hlog 4,
    pow_nonneg hlog 5]

private theorem logQuinticTailPrimitive_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ logQuinticTailPrimitive t := by
  unfold logQuinticTailPrimitive
  exact div_nonneg
    ((pow_nonneg (by linarith [Real.log_nonneg ht]) 5).trans
      (logQuintic_le_tailNumerator ht))
    (zero_le_one.trans ht)

private theorem logQuinticTailPrimitive_le {t : ℝ} (ht : 1 ≤ t) :
    logQuinticTailPrimitive t ≤
      326 * (1 + Real.log t) ^ 5 / t := by
  unfold logQuinticTailPrimitive
  exact (div_le_div_iff_of_pos_right (lt_of_lt_of_le zero_lt_one ht)).mpr
    (tailNumerator_le_threeHundredTwentySix_logQuintic ht)

private theorem divisorSquareLogPartialSum_floor_le {t : ℝ} (ht : 1 ≤ t) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n ≤
      t * (1 + Real.log t) ^ 3 := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hbaseFloor : 0 ≤ 1 + Real.log (⌊t⌋₊ : ℝ) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ⌊t⌋₊ by exact_mod_cast hfloor1)]
  have hbase : 0 ≤ 1 + Real.log t := by linarith [Real.log_nonneg ht]
  have hfloorCast : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hlog : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn
      (show (⌊t⌋₊ : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ⌊t⌋₊
        exact_mod_cast hfloor1)
      (show t ∈ Set.Ioi 0 by exact lt_of_lt_of_le zero_lt_one ht)
      hfloorCast
  calc
    ∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n
        ≤ (⌊t⌋₊ : ℝ) * (1 + Real.log (⌊t⌋₊ : ℝ)) ^ 3 :=
          divisorSquareLogPartialSum_le ⌊t⌋₊ hfloor1
    _ ≤ t * (1 + Real.log t) ^ 3 :=
      mul_le_mul hfloorCast (pow_le_pow_left₀ hbaseFloor (by linarith) 3)
        (pow_nonneg hbaseFloor 3) (zero_le_one.trans ht)

private theorem abelLogIntegrand_le_logQuinticKernel {t : ℝ} (ht : 1 ≤ t) :
    -deriv logSquareInverseSquare t *
        (∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n) ≤
      2 * logQuinticKernel t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hsum0 : 0 ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n :=
    sum_nonneg fun n _ => by unfold divisorSquareLogCoeff; positivity
  have hfactor :
      -deriv logSquareInverseSquare t ≤
        2 * (1 + Real.log t) ^ 2 / t ^ 3 := by
    rw [logSquareInverseSquare_deriv ht0]
    have ht30 : 0 < t ^ 3 := by positivity
    calc
      -(2 * Real.log t * (1 - Real.log t) / t ^ 3) =
          (- (2 * Real.log t * (1 - Real.log t))) / t ^ 3 := by ring
      _ ≤ 2 * (1 + Real.log t) ^ 2 / t ^ 3 :=
        (div_le_div_iff₀ ht30 ht30).2 (by
          nlinarith [sq_nonneg (Real.log t), sq_nonneg (1 + Real.log t)])
  calc
    -deriv logSquareInverseSquare t *
          (∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n)
        ≤ (2 * (1 + Real.log t) ^ 2 / t ^ 3) *
          (∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff n) :=
            mul_le_mul_of_nonneg_right hfactor hsum0
    _ ≤ (2 * (1 + Real.log t) ^ 2 / t ^ 3) *
          (t * (1 + Real.log t) ^ 3) := by
            exact mul_le_mul_of_nonneg_left
              (divisorSquareLogPartialSum_floor_le ht) (by positivity)
    _ = 2 * logQuinticKernel t := by
      unfold logQuinticKernel
      field_simp [ht0.ne']

private theorem logSquareInverseSquare_boundary_le (M : ℕ) (hM : 1 ≤ M) :
    logSquareInverseSquare M *
        (∑ n ∈ Icc 0 M, divisorSquareLogCoeff n) ≤
      logQuinticTailPrimitive M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hw0 : 0 ≤ logSquareInverseSquare (M : ℝ) := by
    unfold logSquareInverseSquare
    positivity
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlog_le : Real.log (M : ℝ) ≤ 1 + Real.log (M : ℝ) := by linarith
  calc
    logSquareInverseSquare M *
          (∑ n ∈ Icc 0 M, divisorSquareLogCoeff n)
        ≤ logSquareInverseSquare M *
          ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_left (divisorSquareLogPartialSum_le M hM) hw0
    _ = Real.log (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 3 / (M : ℝ) := by
      unfold logSquareInverseSquare
      field_simp [hM0.ne']
    _ ≤ (1 + Real.log (M : ℝ)) ^ 5 / (M : ℝ) := by
      apply (div_le_div_iff_of_pos_right hM0).2
      calc
        Real.log (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 3
            ≤ (1 + Real.log (M : ℝ)) ^ 2 *
                (1 + Real.log (M : ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 hlog_le 2)
            (pow_nonneg (by linarith) 3)
        _ = (1 + Real.log (M : ℝ)) ^ 5 := by ring
    _ ≤ logQuinticTailPrimitive M := by
      unfold logQuinticTailPrimitive
      exact (div_le_div_iff_of_pos_right hM0).mpr
        (logQuintic_le_tailNumerator (by exact_mod_cast hM))

private theorem logSquareInverseSquare_deriv_continuousOn
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv logSquareInverseSquare) (Set.Icc a b) := by
  apply ContinuousOn.congr
    (((continuousOn_const.mul
      (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le ha ht.1))).mul
      (continuousOn_const.sub
        (Real.continuousOn_log.mono fun t ht =>
          ne_of_gt (lt_of_lt_of_le ha ht.1)))).div
      (continuousOn_id.pow 3) fun t ht =>
        pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le ha ht.1)))
  intro t ht
  exact logSquareInverseSquare_deriv (lt_of_lt_of_le ha ht.1)

private theorem divisorSquareLog_abel_identity (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Ioc N M,
        logSquareInverseSquare k * divisorSquareLogCoeff k =
      logSquareInverseSquare M *
          (∑ k ∈ Icc 0 M, divisorSquareLogCoeff k) -
        logSquareInverseSquare N *
          (∑ k ∈ Icc 0 N, divisorSquareLogCoeff k) -
          ∫ t in Set.Ioc (N : ℝ) M,
            deriv logSquareInverseSquare t *
              ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff k := by
  apply sum_mul_eq_sub_sub_integral_mul' (c := divisorSquareLogCoeff) hNM
  · intro t ht
    exact logSquareInverseSquare_differentiableAt
      (lt_of_lt_of_le (by exact_mod_cast hN) ht.1)
  · exact (logSquareInverseSquare_deriv_continuousOn
      (b := (M : ℝ)) (by exact_mod_cast hN)).integrableOn_Icc

private theorem finite_divisorSquareLog_tail_le_primitive (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Ioc N M,
        logSquareInverseSquare k * divisorSquareLogCoeff k ≤
      2 * logQuinticTailPrimitive N := by
  have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 1 ≤ M := hN.trans hNM
  let F : ℝ → ℝ := fun t =>
    -deriv logSquareInverseSquare t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff k
  have hderivInt : IntegrableOn (-deriv logSquareInverseSquare) (Set.Icc (N : ℝ) M) :=
    (logSquareInverseSquare_deriv_continuousOn
      (b := (M : ℝ)) hNreal).neg.integrableOn_Icc
  have hFIntOn : IntegrableOn F (Set.Icc (N : ℝ) M) := by
    exact integrableOn_mul_sum_Icc divisorSquareLogCoeff hNreal.le hderivInt
  have hFInt : IntervalIntegrable F volume (N : ℝ) M := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNMreal]
    exact hFIntOn
  have hkernelInt : IntervalIntegrable
      (fun t => 2 * logQuinticKernel t) volume (N : ℝ) M := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNMreal]
    exact (continuousOn_const.mul
      (logQuinticKernel_continuousOn (b := (M : ℝ)) hNreal)).integrableOn_Icc
  have hintegral :
      ∫ t in (N : ℝ)..M, F t ≤
        ∫ t in (N : ℝ)..M, 2 * logQuinticKernel t := by
    exact intervalIntegral.integral_mono_on hNMreal hFInt hkernelInt
      (fun t ht => abelLogIntegrand_le_logQuinticKernel
        (le_trans (by exact_mod_cast hN) ht.1))
  have hkernelEval :
      ∫ t in (N : ℝ)..M, 2 * logQuinticKernel t =
        2 * (logQuinticTailPrimitive N - logQuinticTailPrimitive M) := by
    rw [intervalIntegral.integral_const_mul,
      integral_logQuinticKernel (N : ℝ) M hNreal hNMreal]
  have habel := divisorSquareLog_abel_identity N M hN hNM
  rw [← intervalIntegral.integral_of_le hNMreal] at habel
  have habel' :
      ∑ k ∈ Ioc N M,
          logSquareInverseSquare k * divisorSquareLogCoeff k =
        logSquareInverseSquare M *
            (∑ k ∈ Icc 0 M, divisorSquareLogCoeff k) -
          logSquareInverseSquare N *
            (∑ k ∈ Icc 0 N, divisorSquareLogCoeff k) +
            ∫ t in (N : ℝ)..M, F t := by
    rw [habel]
    have hnegInt :
        ∫ t in (N : ℝ)..M, F t =
          -(∫ t in (N : ℝ)..M,
            deriv logSquareInverseSquare t *
              ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareLogCoeff k) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [F]
      ring
    rw [hnegInt]
    ring
  rw [habel']
  have hboundary := logSquareInverseSquare_boundary_le M hM
  have hnegative :
      0 ≤ logSquareInverseSquare N *
        (∑ k ∈ Icc 0 N, divisorSquareLogCoeff k) := by
    apply mul_nonneg
    · unfold logSquareInverseSquare
      positivity
    · exact sum_nonneg fun k _ => by unfold divisorSquareLogCoeff; positivity
  have hprimitiveM :=
    logQuinticTailPrimitive_nonneg (t := (M : ℝ)) (by exact_mod_cast hM)
  rw [hkernelEval] at hintegral
  linarith

private theorem sum_range_shift_log_eq_sum_Ioc (N M : ℕ) :
    ∑ k ∈ range M,
        logSquareInverseSquare (N + 1 + k) *
          divisorSquareLogCoeff (N + 1 + k) =
      ∑ k ∈ Ioc N (N + M),
        logSquareInverseSquare k * divisorSquareLogCoeff k := by
  apply Finset.sum_bij (fun k _hk => N + 1 + k)
  · intro k hk
    rw [mem_range] at hk
    rw [mem_Ioc]
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    rw [mem_Ioc] at hb
    refine ⟨b - (N + 1), ?_, ?_⟩
    · rw [mem_range]
      omega
    · omega
  · intro k hk
    norm_cast

/-- Sharp logarithmically weighted divisor-square tail. -/
theorem tsum_shift_divisorSquare_log_sq_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' k : ℕ,
        (((N + 1 + k).divisors.card : ℝ) ^ 2 *
          Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 2) ≤
      652 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ) := by
  have hraw :
      ∑' k : ℕ,
          logSquareInverseSquare (N + 1 + k) *
            divisorSquareLogCoeff (N + 1 + k) ≤
        2 * logQuinticTailPrimitive N := by
    apply Real.tsum_le_of_sum_range_le
      (fun k => mul_nonneg
        (by unfold logSquareInverseSquare; positivity)
        (by unfold divisorSquareLogCoeff; positivity))
    intro M
    rw [sum_range_shift_log_eq_sum_Ioc]
    exact finite_divisorSquareLog_tail_le_primitive N (N + M) hN (by omega)
  have hp := logQuinticTailPrimitive_le
    (t := (N : ℝ)) (by exact_mod_cast hN)
  calc
    ∑' k : ℕ,
          (((N + 1 + k).divisors.card : ℝ) ^ 2 *
            Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
            ((N + 1 + k : ℕ) : ℝ) ^ 2) =
        ∑' k : ℕ,
          logSquareInverseSquare (N + 1 + k) *
            divisorSquareLogCoeff (N + 1 + k) := by
              apply tsum_congr
              intro k
              unfold logSquareInverseSquare divisorSquareLogCoeff
              push_cast
              ring
    _ ≤ 2 * logQuinticTailPrimitive N := hraw
    _ ≤ 2 * (326 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 652 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ) := by ring

/-- Cubic logarithmically weighted divisor-square tail. -/
theorem tsum_shift_divisorSquare_log_sq_div_cube_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' k : ℕ,
        (((N + 1 + k).divisors.card : ℝ) ^ 2 *
          Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 3) ≤
      652 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ) ^ 2 := by
  let sq : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2) * Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2
  let cube : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2) * Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 3
  have hinj : Function.Injective (fun k : ℕ => N + 1 + k) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hsummableSq : Summable (fun k : ℕ => sq (N + 1 + k)) := by
    have hbase := RHTower.summable_divisor_sq_log_rpow (σ := (1 : ℝ)) (by norm_num)
    apply (hbase.comp_injective hinj).congr
    intro k
    unfold sq
    simp only [Function.comp_apply]
    have hk : (0 : ℝ) < ((N + 1 + k : ℕ) : ℝ) := by positivity
    rw [show (-2 * (1 : ℝ)) = (-2 : ℝ) by norm_num, Real.rpow_neg hk.le]
    norm_num [one_div]
    ring
  have hsummableCube : Summable (fun k : ℕ => cube (N + 1 + k)) := by
    have hbase := RHTower.summable_divisor_sq_log_rpow (σ := (3 / 2 : ℝ)) (by norm_num)
    apply (hbase.comp_injective hinj).congr
    intro k
    unfold cube
    simp only [Function.comp_apply]
    have hk : (0 : ℝ) < ((N + 1 + k : ℕ) : ℝ) := by positivity
    rw [show (-2 * (3 / 2 : ℝ)) = (-3 : ℝ) by norm_num, Real.rpow_neg hk.le]
    norm_num [one_div]
    ring
  have hpoint : ∀ k : ℕ,
      cube (N + 1 + k) ≤ (1 / (N + 1 : ℝ)) * sq (N + 1 + k) := by
    intro k
    have hNk : (N + 1 : ℝ) ≤ (N + 1 + k : ℕ) := by exact_mod_cast (by omega : N + 1 ≤ N + 1 + k)
    have hNp : (0 : ℝ) < N + 1 := by positivity
    have hkp : (0 : ℝ) < (N + 1 + k : ℕ) := by positivity
    unfold cube sq
    have hd : 0 ≤ ((N + 1 + k).divisors.card : ℝ) ^ 2 *
        Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 := by positivity
    field_simp [hNp.ne', hkp.ne']
    nlinarith
  have hcompare := hsummableCube.tsum_le_tsum hpoint
    (hsummableSq.mul_left (1 / (N + 1 : ℝ)))
  have hsqBound := tsum_shift_divisorSquare_log_sq_div_sq_le N hN
  rw [hsummableSq.tsum_mul_left] at hcompare
  change (∑' k : ℕ, cube (N + 1 + k)) ≤ _
  apply le_trans hcompare
  apply le_trans (mul_le_mul_of_nonneg_left hsqBound (by positivity))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ (1 + Real.log (N : ℝ)) ^ 5 := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    positivity
  field_simp [hNpos.ne']
  nlinarith

end RHTower.Sieve
