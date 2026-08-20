import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Lie–Trotter product formula

In a Banach algebra the exponential of a sum is the limit of the products of the exponentials of
the scaled summands:

```text
(exp (A / n) * exp (B / n)) ^ n → exp (A + B).
```

The proof is the standard two-line estimate made quantitative.  The difference
`exp (t A) exp (t B) - exp (t (A + B))` vanishes to first order at `t = 0`, because both factors
have derivative `A + B` there, so it is `o (t)`; and `‖x ^ n - y ^ n‖ ≤ n M ^ n ‖x - y‖` for
`‖x‖, ‖y‖ ≤ M` with `1 ≤ M`, by a telescoping induction.  Taking `M = exp ((‖A‖ + ‖B‖) / n)`, whose
`n`-th power is the constant `exp (‖A‖ + ‖B‖)`, converts the `o (1/n)` into `o (1)`.
-/

namespace GaloisForLFunctions.HTGeometry

open NormedSpace Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ## The exponential is bounded by the exponential of the norm -/

omit [CompleteSpace 𝔸] in
theorem norm_exp_le_exp_norm (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hsum : Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹ : ℝ) • x ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have hbound : ∀ n : ℕ, ‖((n.factorial : ℝ)⁻¹ : ℝ) • x ^ n‖ ≤ ((n.factorial : ℝ)⁻¹ : ℝ) * ‖x‖ ^ n := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)
  have hsum' : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹ : ℝ) * ‖x‖ ^ n := by
    have := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (‖x‖ : ℝ)
    refine this.congr fun n => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  calc ‖NormedSpace.exp x‖
      = ‖∑' n : ℕ, ((n.factorial : ℝ)⁻¹ : ℝ) • x ^ n‖ := by rw [NormedSpace.exp_eq_tsum ℝ]
    _ ≤ ∑' n : ℕ, ‖((n.factorial : ℝ)⁻¹ : ℝ) • x ^ n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ : ℝ) * ‖x‖ ^ n := hsum.tsum_le_tsum hbound hsum'
    _ = Real.exp ‖x‖ := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
        exact tsum_congr fun n => by rw [smul_eq_mul]

/-! ## A telescoping bound for powers -/

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
private theorem norm_pow_sub_pow_le {x y : 𝔸} {M : ℝ} (hM : 1 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ∀ n : ℕ, ‖x ^ n - y ^ n‖ ≤ n * M ^ n * ‖x - y‖ := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : ‖x ^ n‖ ≤ M ^ n := le_trans (norm_pow_le x n) (pow_le_pow_left₀ (norm_nonneg _) hx n)
    have hsplit : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    calc ‖x ^ (n + 1) - y ^ (n + 1)‖
        ≤ ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ M ^ n * ‖x - y‖ + (n * M ^ n * ‖x - y‖) * M := by
          refine add_le_add ?_ ?_
          · exact le_trans (norm_mul_le _ _)
              (mul_le_mul_of_nonneg_right hxn (norm_nonneg _))
          · exact le_trans (norm_mul_le _ _)
              (mul_le_mul ih hy (norm_nonneg _) (by positivity))
      _ ≤ (n + 1 : ℕ) * M ^ (n + 1) * ‖x - y‖ := by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hxy : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
          have hMn : (0 : ℝ) ≤ M ^ n := by positivity
          rw [pow_succ]
          push_cast
          nlinarith [mul_nonneg (mul_nonneg hMn hxy) (sub_nonneg.2 hM)]

/-! ## The product formula -/

/-- **The Lie–Trotter product formula.** -/
theorem tendsto_pow_exp_smul_inv (A B : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n)
      atTop (𝓝 (NormedSpace.exp (A + B))) := by
  set C : ℝ := ‖A‖ + ‖B‖ with hC
  have hC0 : 0 ≤ C := by positivity
  -- the first-order defect
  set g : ℝ → 𝔸 := fun t =>
    NormedSpace.exp (t • A) * NormedSpace.exp (t • B) - NormedSpace.exp (t • (A + B)) with hgdef
  have hderiv : HasDerivAt g 0 0 := by
    have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
      simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B)) B 0 := by
      simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
    have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (A + B))) (A + B) 0 := by
      simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (A + B) (0 : ℝ)
    have h12 : HasDerivAt
        (fun t : ℝ => NormedSpace.exp (t • A) * NormedSpace.exp (t • B)) (A + B) 0 := by
      have h := h1.mul h2
      simp only [zero_smul, NormedSpace.exp_zero, mul_one, one_mul] at h
      exact h
    have hsub := h12.sub h3
    rw [sub_self] at hsub
    exact hsub
  have hlo : (fun t : ℝ => g t) =o[𝓝 0] fun t : ℝ => t := by
    have h := hasDerivAt_iff_isLittleO.1 hderiv
    simpa [hgdef] using h
  -- along the sequence
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcomp : (fun n : ℕ => ‖g ((n : ℝ)⁻¹)‖) =o[atTop] fun n : ℕ => ((n : ℝ))⁻¹ :=
    (hlo.norm_left).comp_tendsto hseq
  have hzero : Tendsto (fun n : ℕ => (n : ℝ) * ‖g ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
    have h := hcomp.tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  -- the estimate
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero'
    (g := fun n : ℕ => Real.exp C * ((n : ℝ) * ‖g ((n : ℝ)⁻¹)‖)) ?_ ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with n _ using norm_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hM : (1 : ℝ) ≤ Real.exp (C / n) := Real.one_le_exp (by positivity)
    have hX : ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)‖
        ≤ Real.exp (C / n) := by
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _)
        (norm_nonneg _) (Real.exp_nonneg _)) ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      rw [norm_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn0, hC,
        div_eq_inv_mul, mul_add]
    have hY : ‖NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖ ≤ Real.exp (C / n) := by
      refine le_trans (norm_exp_le_exp_norm _) (Real.exp_le_exp.2 ?_)
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn0]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le A B) (by positivity)
    have hYpow : (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) ^ n = NormedSpace.exp (A + B) := by
      letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
      rw [← NormedSpace.exp_nsmul]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (ne_of_gt hn0), one_smul]
    have hpow : (Real.exp (C / n)) ^ n = Real.exp C := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    calc ‖(NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n
            - NormedSpace.exp (A + B)‖
        = ‖(NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n
            - (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) ^ n‖ := by rw [hYpow]
      _ ≤ n * (Real.exp (C / n)) ^ n * ‖g ((n : ℝ)⁻¹)‖ :=
          norm_pow_sub_pow_le hM hX hY n
      _ = Real.exp C * ((n : ℝ) * ‖g ((n : ℝ)⁻¹)‖) := by rw [hpow]; ring
  · have := hzero.const_mul (Real.exp C)
    simpa using this

end GaloisForLFunctions.HTGeometry
