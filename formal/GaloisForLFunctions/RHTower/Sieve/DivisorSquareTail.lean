import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSummability
import Mathlib.NumberTheory.AbelSummation

namespace RHTower.Sieve

open Finset MeasureTheory


private noncomputable def divisorSquareCoeff (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ 2

@[simp] private theorem divisorSquareCoeff_zero : divisorSquareCoeff 0 = 0 := by
  simp [divisorSquareCoeff]

private theorem divisorSquarePartialSum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 0 N, divisorSquareCoeff n ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons, divisorSquareCoeff_zero, zero_add,
    ← Icc_add_one_left_eq_Ioc]
  simpa [divisorSquareCoeff] using sum_card_divisors_pow_le_polylog 2 N hN

private noncomputable def inverseSquare (t : ℝ) : ℝ := t ^ (-2 : ℤ)

private theorem inverseSquare_differentiableAt {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ inverseSquare t := by
  unfold inverseSquare
  exact (hasDerivAt_zpow (-2) t (Or.inl ht)).differentiableAt

private theorem inverseSquare_deriv (t : ℝ) :
    deriv inverseSquare t = (-2 : ℝ) * t ^ (-3 : ℤ) := by
  unfold inverseSquare
  rw [deriv_zpow]
  norm_num

private noncomputable def logCubeTailPrimitive (t : ℝ) : ℝ :=
  (Real.log t ^ 3 + 6 * Real.log t ^ 2 + 15 * Real.log t + 16) / t

private theorem hasDerivAt_logCubeTailPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt logCubeTailPrimitive (-((1 + Real.log t) ^ 3 / t ^ 2)) t := by
  unfold logCubeTailPrimitive
  convert (((Real.hasDerivAt_log ht.ne').pow 3).add
      ((hasDerivAt_const (x := t) (c := (6 : ℝ))).mul
        ((Real.hasDerivAt_log ht.ne').pow 2)) |>.add
      ((hasDerivAt_const (x := t) (c := (15 : ℝ))).mul
        (Real.hasDerivAt_log ht.ne')) |>.add
      (hasDerivAt_const (x := t) (c := (16 : ℝ)))).div (hasDerivAt_id t) ht.ne'
      using 1 <;> try rfl
  simp
  field_simp [ht.ne']
  ring

private noncomputable def logCubeKernel (t : ℝ) : ℝ :=
  (1 + Real.log t) ^ 3 / t ^ 2

private theorem logCubeKernel_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn logCubeKernel (Set.Icc a b) := by
  unfold logCubeKernel
  apply ContinuousOn.div
    ((continuousOn_const.add (Real.continuousOn_log.mono (fun t ht => by
      exact ne_of_gt (lt_of_lt_of_le ha ht.1)))).pow 3)
    (continuousOn_id.pow 2)
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha ht.1))

private theorem integral_logCubeKernel (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, logCubeKernel t =
      logCubeTailPrimitive a - logCubeTailPrimitive b := by
  have hcont := logCubeKernel_continuousOn (b := b) ha
  have hpcont : ContinuousOn logCubeTailPrimitive (Set.Icc a b) := by
    intro t ht
    exact (hasDerivAt_logCubeTailPrimitive
      (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  have hkint : IntervalIntegrable (fun t => -logCubeKernel t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hcont.neg.integrableOn_Icc
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hpcont
    (fun t ht => hasDerivAt_logCubeTailPrimitive (lt_of_lt_of_le ha ht.1.le))
    (by simpa [logCubeKernel] using hkint)
  rw [intervalIntegral.integral_neg] at hfund
  simpa [logCubeKernel] using congrArg Neg.neg hfund

private theorem logCube_le_tailNumerator {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ 3 ≤
      Real.log t ^ 3 + 6 * Real.log t ^ 2 + 15 * Real.log t + 16 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  nlinarith [sq_nonneg (Real.log t)]

private theorem tailNumerator_le_sixteen_logCube {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ^ 3 + 6 * Real.log t ^ 2 + 15 * Real.log t + 16 ≤
      16 * (1 + Real.log t) ^ 3 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  nlinarith [sq_nonneg (Real.log t), mul_nonneg (sq_nonneg (Real.log t)) hlog]

private theorem logCubeTailPrimitive_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ logCubeTailPrimitive t := by
  unfold logCubeTailPrimitive
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  exact div_nonneg
    ((pow_nonneg (by linarith) 3).trans (logCube_le_tailNumerator ht))
    (zero_le_one.trans ht)

private theorem logCubeTailPrimitive_le {t : ℝ} (ht : 1 ≤ t) :
    logCubeTailPrimitive t ≤ 16 * (1 + Real.log t) ^ 3 / t := by
  unfold logCubeTailPrimitive
  exact (div_le_div_iff_of_pos_right (lt_of_lt_of_le zero_lt_one ht)).mpr
    (tailNumerator_le_sixteen_logCube ht)

private theorem divisorSquarePartialSum_floor_le {t : ℝ} (ht : 1 ≤ t) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff n ≤
      t * (1 + Real.log t) ^ 3 := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hbaseFloor : 0 ≤ 1 + Real.log (⌊t⌋₊ : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ⌊t⌋₊ by exact_mod_cast hfloor1)
    linarith
  have hbase : 0 ≤ 1 + Real.log t := by
    have := Real.log_nonneg ht
    linarith
  have hfloorCast : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hlog : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn
      (show (⌊t⌋₊ : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ⌊t⌋₊
        exact_mod_cast hfloor1)
      (show t ∈ Set.Ioi 0 by
        change 0 < t
        exact lt_of_lt_of_le zero_lt_one ht)
      hfloorCast
  calc
    ∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff n
        ≤ (⌊t⌋₊ : ℝ) * (1 + Real.log (⌊t⌋₊ : ℝ)) ^ 3 :=
          divisorSquarePartialSum_le ⌊t⌋₊ hfloor1
    _ ≤ t * (1 + Real.log t) ^ 3 :=
      mul_le_mul hfloorCast
        (pow_le_pow_left₀ hbaseFloor (by linarith) 3)
        (pow_nonneg hbaseFloor 3) (zero_le_one.trans ht)

private theorem abelIntegrand_le_logCubeKernel {t : ℝ} (ht : 1 ≤ t) :
    -deriv inverseSquare t *
        (∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff n) ≤
      2 * logCubeKernel t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hderiv : deriv inverseSquare t = (-2 : ℝ) * t ^ (-3 : ℤ) :=
    inverseSquare_deriv t
  have hfactor : 0 ≤ -deriv inverseSquare t := by
    rw [hderiv]
    have hz : 0 < t ^ (-3 : ℤ) := zpow_pos ht0 (-3)
    nlinarith
  calc
    -deriv inverseSquare t *
          (∑ n ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff n)
        ≤ -deriv inverseSquare t * (t * (1 + Real.log t) ^ 3) :=
          mul_le_mul_of_nonneg_left (divisorSquarePartialSum_floor_le ht) hfactor
    _ = 2 * logCubeKernel t := by
      rw [hderiv]
      unfold logCubeKernel
      field_simp [ht0.ne']

private theorem inverseSquare_boundary_le (M : ℕ) (hM : 1 ≤ M) :
    inverseSquare M * (∑ n ∈ Icc 0 M, divisorSquareCoeff n) ≤
      logCubeTailPrimitive M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hinv : 0 ≤ inverseSquare (M : ℝ) := by
    unfold inverseSquare
    exact (zpow_pos hM0 (-2)).le
  calc
    inverseSquare M * (∑ n ∈ Icc 0 M, divisorSquareCoeff n)
        ≤ inverseSquare M * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 3) :=
          mul_le_mul_of_nonneg_left (divisorSquarePartialSum_le M hM) hinv
    _ = (1 + Real.log (M : ℝ)) ^ 3 / (M : ℝ) := by
      unfold inverseSquare
      field_simp [hM0.ne']
    _ ≤ logCubeTailPrimitive M := by
      unfold logCubeTailPrimitive
      exact (div_le_div_iff_of_pos_right hM0).mpr
        (logCube_le_tailNumerator (by exact_mod_cast hM))

private theorem inverseSquare_deriv_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv inverseSquare) (Set.Icc a b) := by
  apply ContinuousOn.congr
    (continuousOn_const.mul (ContinuousOn.zpow₀ continuousOn_id (-3) (fun t ht => by
      have : 0 < t := lt_of_lt_of_le ha ht.1
      exact Or.inl (ne_of_gt this))))
  intro t ht
  exact inverseSquare_deriv t

private theorem divisorSquare_abel_identity (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Ioc N M, inverseSquare k * divisorSquareCoeff k =
      inverseSquare M * (∑ k ∈ Icc 0 M, divisorSquareCoeff k) -
        inverseSquare N * (∑ k ∈ Icc 0 N, divisorSquareCoeff k) -
          ∫ t in Set.Ioc (N : ℝ) M,
            deriv inverseSquare t *
              ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff k := by
  apply sum_mul_eq_sub_sub_integral_mul' (c := divisorSquareCoeff) hNM
  · intro t ht
    exact inverseSquare_differentiableAt (by
      have : 0 < t := lt_of_lt_of_le (by exact_mod_cast hN) ht.1
      positivity)
  · exact (inverseSquare_deriv_continuousOn (b := (M : ℝ)) (by exact_mod_cast hN)).integrableOn_Icc

private theorem finite_divisorSquare_tail_le_primitive (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Ioc N M, inverseSquare k * divisorSquareCoeff k ≤
      2 * logCubeTailPrimitive N := by
  have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 1 ≤ M := hN.trans hNM
  let F : ℝ → ℝ := fun t =>
    -deriv inverseSquare t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff k
  have hderivInt : IntegrableOn (-deriv inverseSquare) (Set.Icc (N : ℝ) M) :=
    (inverseSquare_deriv_continuousOn (b := (M : ℝ)) hNreal).neg.integrableOn_Icc
  have hFIntOn : IntegrableOn F (Set.Icc (N : ℝ) M) := by
    exact integrableOn_mul_sum_Icc divisorSquareCoeff hNreal.le hderivInt
  have hFInt : IntervalIntegrable F volume (N : ℝ) M := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNMreal]
    exact hFIntOn
  have hkernelInt : IntervalIntegrable (fun t => 2 * logCubeKernel t) volume (N : ℝ) M := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNMreal]
    exact (continuousOn_const.mul (logCubeKernel_continuousOn (b := (M : ℝ)) hNreal)).integrableOn_Icc
  have hintegral :
      ∫ t in (N : ℝ)..M, F t ≤
        ∫ t in (N : ℝ)..M, 2 * logCubeKernel t := by
    exact intervalIntegral.integral_mono_on hNMreal hFInt hkernelInt (fun t ht =>
      abelIntegrand_le_logCubeKernel (by
        exact le_trans (by exact_mod_cast hN) ht.1))
  have hkernelEval :
      ∫ t in (N : ℝ)..M, 2 * logCubeKernel t =
        2 * (logCubeTailPrimitive N - logCubeTailPrimitive M) := by
    rw [intervalIntegral.integral_const_mul,
      integral_logCubeKernel (N : ℝ) M hNreal hNMreal]
  have habel := divisorSquare_abel_identity N M hN hNM
  rw [← intervalIntegral.integral_of_le hNMreal] at habel
  have habel' :
      ∑ k ∈ Ioc N M, inverseSquare k * divisorSquareCoeff k =
        inverseSquare M * (∑ k ∈ Icc 0 M, divisorSquareCoeff k) -
          inverseSquare N * (∑ k ∈ Icc 0 N, divisorSquareCoeff k) +
            ∫ t in (N : ℝ)..M, F t := by
    rw [habel]
    have hnegInt :
        ∫ t in (N : ℝ)..M, F t =
          -(∫ t in (N : ℝ)..M,
            deriv inverseSquare t *
              ∑ k ∈ Icc 0 ⌊t⌋₊, divisorSquareCoeff k) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [F]
      ring
    rw [hnegInt]
    ring
  rw [habel']
  have hboundary := inverseSquare_boundary_le M hM
  have hnegative :
      0 ≤ inverseSquare N * (∑ k ∈ Icc 0 N, divisorSquareCoeff k) := by
    apply mul_nonneg
    · unfold inverseSquare
      exact (zpow_pos hNreal (-2)).le
    · exact sum_nonneg (fun k _ => by
        unfold divisorSquareCoeff
        positivity)
  have hprimitiveM := logCubeTailPrimitive_nonneg (t := (M : ℝ)) (by exact_mod_cast hM)
  rw [hkernelEval] at hintegral
  linarith

private theorem sum_range_shift_eq_sum_Ioc (N M : ℕ) :
    ∑ k ∈ range M,
        inverseSquare (N + 1 + k) * divisorSquareCoeff (N + 1 + k) =
      ∑ k ∈ Ioc N (N + M), inverseSquare k * divisorSquareCoeff k := by
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

/-- Quantitative shifted tail for the inverse-square divisor mass.  The `N⁻¹ log³ N` scale is
the sharp scale needed after the large-argument moving-carrier derivative estimate. -/
private theorem tsum_shift_divisorSquare_inverseSquare_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' k : ℕ,
        inverseSquare (N + 1 + k) * divisorSquareCoeff (N + 1 + k) ≤
      32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  apply le_trans (Real.tsum_le_of_sum_range_le
    (fun k => mul_nonneg
      (by
        unfold inverseSquare
        exact (zpow_pos (by positivity) (-2)).le)
      (by
        unfold divisorSquareCoeff
        positivity))
    (fun M => by
      rw [sum_range_shift_eq_sum_Ioc]
      exact finite_divisorSquare_tail_le_primitive N (N + M) hN (by omega)))
  have hp := logCubeTailPrimitive_le (t := (N : ℝ)) (by exact_mod_cast hN)
  calc
    2 * logCubeTailPrimitive (N : ℝ)
        ≤ 2 * (16 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by ring

/-- **Sharp divisor-square tail.**  Uniformly for `N ≥ 1`, the inverse-square tail is at most
`32 (1 + log N)^3 / N`. -/
theorem tsum_shift_divisorSquare_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' k : ℕ,
        (((N + 1 + k).divisors.card : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 2) ≤
      32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  convert tsum_shift_divisorSquare_inverseSquare_le N hN using 1
  apply tsum_congr
  intro k
  unfold inverseSquare divisorSquareCoeff
  have hk : (0 : ℝ) < (N + 1 + k : ℕ) := by positivity
  field_simp [hk.ne']
  norm_cast

/-- Cubic companion tail.  One extra inverse factor improves the tail by one full power of `N`. -/
theorem tsum_shift_divisorSquare_div_cube_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' k : ℕ,
        (((N + 1 + k).divisors.card : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 3) ≤
      32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2 := by
  let sq : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2) / ((n : ℝ) ^ 2)
  let cube : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2) / ((n : ℝ) ^ 3)
  have hinj : Function.Injective (fun k : ℕ => N + 1 + k) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hsq : Summable (fun k : ℕ => sq (N + 1 + k)) := by
    apply (summable_divisorSquare_div_sq.comp_injective hinj).congr
    intro k
    unfold sq
    norm_cast
  have hcube : Summable (fun k : ℕ => cube (N + 1 + k)) := by
    apply (summable_divisorSquare_div_cube.comp_injective hinj).congr
    intro k
    unfold cube
    norm_cast
  have hpoint : ∀ k : ℕ,
      cube (N + 1 + k) ≤ (1 / (N + 1 : ℝ)) * sq (N + 1 + k) := by
    intro k
    have hNk : (N + 1 : ℝ) ≤ (N + 1 + k : ℕ) := by exact_mod_cast (by omega : N + 1 ≤ N + 1 + k)
    have hNp : (0 : ℝ) < N + 1 := by positivity
    have hkp : (0 : ℝ) < (N + 1 + k : ℕ) := by positivity
    unfold cube sq
    have hd : 0 ≤ (((N + 1 + k).divisors.card : ℝ) ^ 2) := by positivity
    field_simp [hNp.ne', hkp.ne']
    nlinarith
  have hcompare := hcube.tsum_le_tsum hpoint (hsq.mul_left (1 / (N + 1 : ℝ)))
  have hsqBound := tsum_shift_divisorSquare_div_sq_le N hN
  rw [hsq.tsum_mul_left] at hcompare
  change (∑' k : ℕ, cube (N + 1 + k)) ≤ _
  apply le_trans hcompare
  apply le_trans (mul_le_mul_of_nonneg_left hsqBound (by positivity))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ (1 + Real.log (N : ℝ)) ^ 3 := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    positivity
  field_simp [hNpos.ne']
  nlinarith

end RHTower.Sieve
