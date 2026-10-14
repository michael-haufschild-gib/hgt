import GaloisForLFunctions.RHTower.ModularArcWhittakerPositivity
import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrincipleLevel

/-!
# Stability of the Whittaker arc rigidity

For `c_n = 2π(n+1)` let `v(u, y) = Σ_{n<N} K₀(c_n y)(a_n cos c_n u + b_n sin c_n u)` be a decaying
Whittaker sum (`whittakerArcSum`).  `whittakerArc_coeff_eq_zero` says that `v ≥ 0` on the bottom
arc `{u² + y² = 1, |u| ≤ ½}` forces every coefficient to vanish.

**Theorem** (`abs_coeff_le_of_ge_on_arc`).  If `v ≥ −ε` on the bottom arc (`ε ≥ 0`), then

`|a_m|, |b_m| ≤ 4ε / K₀(c_m)`   for every `m < N`.

Proof.  The minimum principle at the level `−ε` (`le_of_le_on_modularArc`) gives `v(u, 1) ≥ −ε`
for every `u`.  The horocycle `y = 1` has no constant mode (`∫₀¹ v(u, 1) du = 0`), so
`|v| ≤ v + 2ε` integrates to `∫₀¹ |v(u, 1)| du ≤ 2ε`.  The Fourier coefficient
`∫₀¹ v(u, 1) cos(c_m u) du = K₀(c_m) a_m/2` (and the sine analogue) is therefore at most `2ε`.

So the qualitative rigidity behind the twisted arc witness has an explicit modulus: a Whittaker
combination that is almost nonnegative on the arc has coefficients `O(ε e^{c_m})`.
-/

open MeasureTheory Set Filter Topology
open scoped Interval
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The minimum principle at level `−ε` for a Whittaker sum. -/
theorem neg_le_whittakerArcSum_of_ge_on_arc (N : ℕ) (a b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 → -ε ≤ whittakerArcSum N a b u y)
    {u y₀ : ℝ} (hy₀ : 1 ≤ y₀) : -ε ≤ whittakerArcSum N a b u y₀ :=
  le_of_le_on_modularArc (v := whittakerArcSum N a b)
    (vu := fun u y => ∑ n ∈ Finset.range N,
      kMoment 0 (arcFreq n * y) * arcTrigDeriv a b n u)
    (vuu := fun u y => ∑ n ∈ Finset.range N,
      kMoment 0 (arcFreq n * y) * -(arcFreq n ^ 2 * arcTrig a b n u))
    (vy := fun u y => ∑ n ∈ Finset.range N,
      -kMoment 1 (arcFreq n * y) * arcFreq n * arcTrig a b n u)
    (vyy := fun u y => ∑ n ∈ Finset.range N,
      kMoment 2 (arcFreq n * y) * arcFreq n ^ 2 * arcTrig a b n u)
    (fun u y _ => HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_arcTrig a b n u).const_mul _)
    (fun u y _ => HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_arcTrigDeriv a b n u).const_mul _)
    (fun u y hy => HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_kMoment_comp 0 n hy).mul_const _)
    (fun u y hy => HasDerivAt.fun_sum fun n _ => by
      have h := ((hasDerivAt_kMoment_comp 1 n hy).neg.mul_const (arcFreq n)).mul_const
        (arcTrig a b n u)
      refine h.congr_deriv ?_
      ring)
    (fun u y hy => whittakerArcSum_eq N a b hy u)
    (continuousOn_whittakerArcSum N a b) (whittakerArcSum_periodic N a b)
    (whittakerArcSum_decay N a b) (by linarith) harc hy₀

/-- On the horocycle `y = 1` a Whittaker sum bounded below by `−ε` has `L¹` mass at most `2ε`,
measured against any weight bounded by `1`. -/
theorem abs_integral_whittakerArcSum_mul_le (N : ℕ) (a b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hlow : ∀ u, -ε ≤ whittakerArcSum N a b u 1) {g : ℝ → ℝ} (hg : Continuous g)
    (hg1 : ∀ u, |g u| ≤ 1) :
    |∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 1 * g u| ≤ 2 * ε := by
  have hcont : Continuous fun u => whittakerArcSum N a b u 1 := by
    unfold whittakerArcSum arcTrig; fun_prop
  calc |∫ u in (0 : ℝ)..1, whittakerArcSum N a b u 1 * g u|
      ≤ ∫ u in (0 : ℝ)..1, |whittakerArcSum N a b u 1 * g u| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ u in (0 : ℝ)..1, (whittakerArcSum N a b u 1 + 2 * ε) := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((hcont.mul hg).abs.intervalIntegrable 0 1)
          ((hcont.add continuous_const).intervalIntegrable 0 1) fun u _ => ?_
        have h1 := hlow u
        rw [abs_mul]
        have h2 : |whittakerArcSum N a b u 1| ≤ whittakerArcSum N a b u 1 + 2 * ε := by
          rcases le_or_gt 0 (whittakerArcSum N a b u 1) with h | h
          · rw [abs_of_nonneg h]; linarith
          · rw [abs_of_neg h]; linarith
        calc |whittakerArcSum N a b u 1| * |g u| ≤ |whittakerArcSum N a b u 1| * 1 :=
              mul_le_mul_of_nonneg_left (hg1 u) (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact h2
    _ = 2 * ε := by
        rw [intervalIntegral.integral_add (hcont.intervalIntegrable 0 1)
          intervalIntegrable_const, integral_whittakerArcSum, intervalIntegral.integral_const]
        simp

/-- **Stability of the Whittaker arc rigidity.**  A Whittaker sum that is at least `−ε` on the
bottom arc has `|a_m|, |b_m| ≤ 4ε / K₀(c_m)`. -/
theorem abs_coeff_le_of_ge_on_arc (N : ℕ) (a b : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 → -ε ≤ whittakerArcSum N a b u y)
    {m : ℕ} (hm : m < N) :
    |a m| ≤ 4 * ε / kMoment 0 (arcFreq m) ∧ |b m| ≤ 4 * ε / kMoment 0 (arcFreq m) := by
  have hlow : ∀ u, -ε ≤ whittakerArcSum N a b u 1 := fun u =>
    neg_le_whittakerArcSum_of_ge_on_arc N a b hε harc le_rfl
  have hK := kMoment_zero_pos_of_pos (arcFreq_pos m)
  have hcos := integral_whittakerArcSum_mul_cos N a b 1 hm
  have hsin := integral_whittakerArcSum_mul_sin N a b 1 hm
  rw [mul_one] at hcos hsin
  have hc := abs_integral_whittakerArcSum_mul_le N a b hε hlow (g := fun u => Real.cos (arcFreq m * u))
    (by fun_prop) fun u => Real.abs_cos_le_one _
  have hs := abs_integral_whittakerArcSum_mul_le N a b hε hlow (g := fun u => Real.sin (arcFreq m * u))
    (by fun_prop) fun u => Real.abs_sin_le_one _
  rw [hcos, abs_mul, abs_of_pos hK, abs_div, abs_two] at hc
  rw [hsin, abs_mul, abs_of_pos hK, abs_div, abs_two] at hs
  constructor
  · rw [le_div_iff₀ hK]; nlinarith
  · rw [le_div_iff₀ hK]; nlinarith

end

end RHTower
