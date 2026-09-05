import GaloisForLFunctions.RHTower.SoninRegularizedDiagonalTail

/-!
# Exact prime-labelled diagonal Sonin head and tail budgets

The original weighted blocks, including prime/depth labels, are retained. The discarded
Hilbert--Schmidt mass equals that of the common-input column without identifying the operators.
No Xi, moment-matching, or RH premise is used.
-/

open Filter Topology ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem schattenOnePrefix_soninAllPrimeResidual_le_sourceHeadTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    schattenPowerPartialSum 1 (soninAllPrimeResidualOperator a ha) N ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        (∑ pk ∈ s, ‖soninLogPrimePowerCoefficient pk‖) +
      Real.sqrt ((N : ℝ) * ((128 * a ^ 2) * ∑' pk : Nat.Primes × ℕ,
        if pk ∈ s then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ 2)) := by
  have h := schattenOnePrefix_le_traceClassHead_add_hilbertSchmidtTail
    (soninAllPrimeResidualOperator_isCompactOperator a ha)
    (soninAllPrimeDiagonalFiniteHead_memSchattenClass_one a ha s)
    (soninAllPrimeDiagonalTail_isHilbertSchmidt a ha s) N
  exact h.trans (add_le_add (traceNorm_soninAllPrimeDiagonalFiniteHead_le_source a ha s)
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (hsNormSq_soninAllPrimeDiagonalTail_le_coefficientTail a ha s) (Nat.cast_nonneg N))))

/-- The literal block-diagonal regularized source retains its prime labels and coefficients,
but has only logarithmic singular-prefix mass. No moment-weld or Xi hypothesis is assumed. -/
theorem schattenOnePrefix_soninAllPrimeResidual_le_log
    (a : ℝ) (ha : 0 < a) (N : ℕ) :
    schattenPowerPartialSum 1 (soninAllPrimeResidualOperator a ha) N ≤
      8 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        (1 + Real.log (N + 1 : ℕ)) + Real.sqrt (512 * a ^ 2) := by
  let M := N + 1
  have hM : 0 < M := Nat.succ_pos N
  have h := schattenOnePrefix_soninAllPrimeResidual_le_sourceHeadTail a ha
    (soninPrimeDepthBox M) N
  have hhead := mul_le_mul_of_nonneg_left
    (sum_norm_soninLogPrimePowerCoefficient_box_le_log M)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (traceNorm_nonneg (centralSoninProjectionCorrection a)))
  have htail := mul_le_mul_of_nonneg_left
    (sum_sq_soninLogPrimePowerCoefficient_boxTail_le M hM)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) (sq_nonneg a))
  have hscale : (N : ℝ) * ((128 * a ^ 2) * (4 / (M : ℝ))) ≤ 512 * a ^ 2 := by
    have hpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have hNM : (N : ℝ) ≤ M := by exact_mod_cast Nat.le_succ N
    have hfrac : (N : ℝ) / M ≤ 1 := (div_le_one hpos).mpr hNM
    calc
      _ = (512 * a ^ 2) * ((N : ℝ) / M) := by ring
      _ ≤ (512 * a ^ 2) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := mul_one _
  have hroot := Real.sqrt_le_sqrt
    ((mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N)).trans hscale)
  exact h.trans ((add_le_add hhead hroot).trans_eq (by dsimp [M]; ring))

theorem tendsto_schattenOnePrefix_soninAllPrimeResidual_div_logSq
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      schattenPowerPartialSum 1 (soninAllPrimeResidualOperator a ha) N /
        Real.log ((N : ℝ) + 1) ^ 2) atTop (nhds 0) := by
  let C := 8 * traceNorm SoninL2 (centralSoninProjectionCorrection a)
  let D := Real.sqrt (512 * a ^ 2)
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hq : Tendsto (fun N : ℕ => 1 / Real.log ((N : ℝ) + 1)) atTop (nhds 0) :=
    hlog.const_div_atTop 1
  have hzero : Tendsto (fun N : ℕ =>
      (C + D) * (1 / Real.log ((N : ℝ) + 1)) ^ 2 +
        C * (1 / Real.log ((N : ℝ) + 1))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hq.pow 2)).add (tendsto_const_nhds.mul hq)
  apply squeeze_zero_norm' _ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hL : 0 < Real.log ((N : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hN)
  have hsum : 0 ≤ schattenPowerPartialSum 1 (soninAllPrimeResidualOperator a ha) N := by
    simp only [schattenPowerPartialSum, Real.rpow_one]
    exact Finset.sum_nonneg fun n _ => approxNumber_nonneg _ n
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum (sq_nonneg _))]
  have hbound := schattenOnePrefix_soninAllPrimeResidual_le_log a ha N
  simp only [Nat.cast_add, Nat.cast_one] at hbound
  refine (div_le_div_of_nonneg_right hbound (sq_nonneg _)).trans_eq ?_
  dsimp [C, D]
  field_simp
  ring

end
end RHTower
