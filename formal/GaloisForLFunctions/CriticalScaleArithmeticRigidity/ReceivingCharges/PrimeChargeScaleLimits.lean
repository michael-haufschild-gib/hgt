import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Logarithmic scales of coherent prime charge

The prime Mertens mass is asymptotic to the logarithm. The reciprocal-prime
mass grows more slowly than every positive power of that logarithm. Together
these facts make both moments of a coherent charge negligible under the
overlap costs occurring in the complete form.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

private theorem prime_filter_eq (N : ℕ) :
    (Icc 1 N).filter Nat.Prime = Nat.primesLE N := by
  ext p
  simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.one_le, h.1⟩, h.2⟩⟩

private theorem log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The exact prime-charge normalizer has leading coefficient one. -/
theorem tendsto_log_div_primePoleScale :
    Tendsto (fun N : ℕ => Real.log N / primePoleScale N) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (primePoleScale_tendsto_atTop.const_div_atTop
      ((Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)))
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hB := primePoleScale_pos hN
  have heq : Real.log N / primePoleScale N - 1 =
      (Real.log N - primePoleScale N) / primePoleScale N := by
    field_simp [hB.ne']
  rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hB, abs_sub_comm]
  exact div_le_div_of_nonneg_right (primePoleScale_logarithmic (by omega)) hB.le

private theorem log_rpow_div_rpow_limit (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.log x ^ p / x ^ q) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p q hq).comp
    Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.rpow_def_of_pos hx,
    div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Logarithmic overlap has vanishing physical width. -/
theorem tendsto_log_rpow_div_nat (p : ℝ) :
    Tendsto (fun N : ℕ => Real.log N ^ p / (N : ℝ)) atTop (𝓝 0) := by
  simpa only [Real.rpow_one, Function.comp_def] using
    (log_rpow_div_rpow_limit p zero_lt_one).comp tendsto_natCast_atTop_atTop

/-- Every positive critical multiple eventually has overlap at least one and width at most one third. -/
theorem eventually_primeCharge_criticalOverlap_facts {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ 2 * K * Real.log N ^ (1 / 8 : ℝ) ∧
        (2 * K * Real.log N ^ (1 / 8 : ℝ)) / N ≤ 1 / 3 := by
  have hpower := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp log_nat_atTop
  have hwidth : Tendsto (fun N : ℕ =>
      (2 * K * Real.log N ^ (1 / 8 : ℝ)) / N) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using (tendsto_log_rpow_div_nat (1 / 8)).const_mul (2 * K)
  filter_upwards [hpower.eventually_ge_atTop (1 / (2 * K)),
    hwidth.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with N hlarge hsmall
  refine ⟨?_, hsmall⟩
  have h := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ 2 * K)
  simpa only [Function.comp_def,
    mul_one_div_cancel (by positivity : (2 * K : ℝ) ≠ 0)] using h

/-- Reciprocal-prime mass is smaller than every positive logarithmic power. -/
theorem tendsto_primeReciprocal_div_log_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ)) /
        Real.log N ^ q) atTop (𝓝 0) := by
  let C := 1 + 2 * (_root_.RHTower.Sieve.mertensFirstConst / Real.log 2) -
    _root_.RHTower.Sieve.logLog 2
  have hlim : Tendsto (fun N : ℕ =>
      (Real.log (Real.log N) + C) / Real.log N ^ q) atTop (𝓝 0) := by
    have h1 := (log_rpow_div_rpow_limit 1 hq).comp log_nat_atTop
    have h2 := ((tendsto_rpow_atTop hq).comp log_nat_atTop).const_div_atTop C
    simpa only [Function.comp_def, Real.rpow_one, zero_add, ← add_div] using h1.add h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hS0 : 0 ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ) :=
    sum_nonneg fun p _ => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hS0
    (Real.rpow_nonneg (Real.log_natCast_nonneg N) q))]
  apply div_le_div_of_nonneg_right _
    (Real.rpow_nonneg (Real.log_natCast_nonneg N) q)
  simpa only [prime_filter_eq, _root_.RHTower.Sieve.mertensS,
    _root_.RHTower.Sieve.logLog, C] using _root_.RHTower.Sieve.mertensSecond_upper hN

/-- The quadratic reciprocal-prime moment also loses to every logarithmic power. -/
theorem tendsto_primeReciprocal_quadratic_div_log_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ =>
      (4 * (∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
        2 * ∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ)) /
          Real.log N ^ q) atTop (𝓝 0) := by
  have hsq := (tendsto_primeReciprocal_div_log_rpow (q := q / 2)
    (by linarith only [hq])).pow 2
  have hlin := tendsto_primeReciprocal_div_log_rpow hq
  have h := (hsq.const_mul 4).add (hlin.const_mul 2)
  simp only [zero_pow two_ne_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [log_nat_atTop.eventually_gt_atTop 0] with N hN
  have hp : (Real.log (N : ℝ) ^ (q / 2)) ^ (2 : ℕ) = Real.log N ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
  simp only [div_pow, hp]
  ring

/-- Both coherent moments absorb every overlap power strictly below one logarithm. -/
theorem tendsto_primeChargeMoment_cost (t : ℝ) {r : ℝ} (hr : r < 1) :
    Tendsto (fun N : ℕ =>
      Real.log N ^ r * (Real.log N + 1) * (t / primePoleScale N) ^ 2 *
        (4 * (∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ))) atTop (𝓝 0) := by
  have hlog := log_nat_atTop.const_div_atTop 1
  have hfactor : Tendsto (fun N : ℕ =>
      (t * (Real.log N / primePoleScale N)) ^ 2 * (1 + 1 / Real.log N))
      atTop (𝓝 (t ^ 2)) := by
    simpa only [mul_one, add_zero] using
      ((tendsto_log_div_primePoleScale.const_mul t).pow 2).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add hlog)
  have h := hfactor.mul
    (tendsto_primeReciprocal_quadratic_div_log_rpow (sub_pos.mpr hr))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [log_nat_atTop.eventually_gt_atTop 0, eventually_ge_atTop 2] with N hN hNat
  rw [Real.rpow_sub hN, Real.rpow_one]
  field_simp [hN.ne', (Real.rpow_pos_of_pos hN r).ne', (primePoleScale_pos hNat).ne']

#print axioms tendsto_log_div_primePoleScale
#print axioms tendsto_primeReciprocal_quadratic_div_log_rpow
#print axioms tendsto_primeChargeMoment_cost

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
