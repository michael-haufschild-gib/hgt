import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseUniformDivisibility
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationEndpoints
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticParityVariance

/-!
# Uniform tightness of the actual valuation ratios

One radial neighborhood controls every divisibility ratio. Taking adjacent
differences gives geometric control of all valuation ratios. No coefficient
sign or multiplicativity is assumed.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

/-- The finite valuation partition retains its exact divisibility tail. -/
theorem sum_range_valuation_LSeries {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (p N : ℕ) :
    (∑ k ∈ Finset.range N, LSeries (valuationPart p k f) s) =
      LSeries f s - LSeries (divisibilityPart (p ^ N) f) s := by
  induction N with
  | zero =>
    have he : divisibilityPart 1 f = f := by
      funext n
      simp [divisibilityPart, divisibilityMask]
    simp [he]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, valuationPart_eq_sub_divisibilityPart,
      LSeries_sub (summable_divisibilityPart _ hf) (summable_divisibilityPart _ hf)]
    ring

/-- Divisibility ratios decay with the square root of the modulus, uniformly
before taking any endpoint. -/
theorem exists_forward_divisibility_ratio_bound {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ q : ℕ, q ≠ 0 →
      ‖LSeries (divisibilityPart q (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)‖ ≤ D / Real.sqrt q := by
  obtain ⟨C, eta, hC, heta, hbound⟩ := exists_forward_divisibility_near_one hW
  let B := ‖sourceCompletion hW 1‖
  have hB : 0 < B := norm_pos_iff.mpr (sourceCompletion_one_ne_zero hW)
  have hden := (forward_source_residue hW).norm.eventually
    (lt_mem_nhds (show B / 2 < ‖sourceCompletion hW 1‖ by dsimp [B]; linarith))
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 1 + eta :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + eta))
  refine ⟨Real.sqrt C / (B / 2), by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hnear, hden] with s hs hset hden q hq
  have hscaled : ‖((s : ℂ) - 1) *
      LSeries (divisibilityPart q (sourceCoeff lam)) (s : ℂ)‖ ≤
      Real.sqrt C / Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt (hbound q hq s hs hset)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_div hC] using hh
  have hne : (s : ℂ) - 1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at he'
    change 1 < s at hs
    linarith
  rw [← mul_div_mul_left _ _ hne, norm_div]
  calc
    _ ≤ (Real.sqrt C / Real.sqrt q) / (B / 2) :=
      div_le_div₀ (by positivity) hscaled (by positivity) hden.le
    _ = (Real.sqrt C / (B / 2)) / Real.sqrt q := by ring

theorem sqrt_nat_pow (p k : ℕ) :
    Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt (p : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Every exact valuation ratio obeys one geometric envelope on a common
radial neighborhood. -/
theorem exists_forward_valuation_ratio_geometric {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ k : ℕ,
      ‖LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)‖ ≤ C * (Real.sqrt (p : ℝ))⁻¹ ^ k := by
  obtain ⟨D, hD, hbound⟩ := exists_forward_divisibility_ratio_bound hW
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp1
  have hr0 : 0 ≤ (Real.sqrt (p : ℝ))⁻¹ := by positivity
  have hr1 : (Real.sqrt (p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
  refine ⟨2 * D, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hbound] with s hs hb k
  have h0 := hb (p ^ k) (pow_ne_zero _ hp.ne_zero)
  have h1 := hb (p ^ (k + 1)) (pow_ne_zero _ hp.ne_zero)
  rw [sqrt_nat_pow] at h0 h1
  simp only [div_eq_mul_inv, ← inv_pow] at h0 h1
  rw [valuationPart_eq_sub_divisibilityPart,
    LSeries_sub (summable_divisibilityPart _ (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1)
      (summable_divisibilityPart _ (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1), sub_div]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D * (Real.sqrt (p : ℝ))⁻¹ ^ k +
        D * (Real.sqrt (p : ℝ))⁻¹ ^ (k + 1) := add_le_add h0 h1
    _ ≤ D * (Real.sqrt (p : ℝ))⁻¹ ^ k +
        D * (Real.sqrt (p : ℝ))⁻¹ ^ k :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0 hr1 (Nat.le_succ k)) hD)
    _ = _ := by ring

end RHTower.WeilSingularArithmetic
