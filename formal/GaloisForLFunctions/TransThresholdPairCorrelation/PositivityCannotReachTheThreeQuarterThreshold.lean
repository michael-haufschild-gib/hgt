import GaloisForLFunctions.TransThresholdPairCorrelation.FormFactorThresholdAndShiftInequality
import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing

/-!
# Positivity cannot reach the three-quarter threshold

Montgomery's form factor `F` is the Fourier transform of the pair-correlation measure of the zeros,
whose off-diagonal part has density `p = 1 + 𝓕(F − 1)` (Mathlib's convention
`𝓕g(ξ) = ∫ e^{−2πiαξ} g(α) dα`; the term `T^{−2|α|} log T` of `F` contributes the constant `1`).
The `3/4` certificate `frobeniusFormFactor F (4/3) ≤ 5/4` is equivalent to
`I = ∫₁^{4/3} (4/3 − α) F(α) dα ≤ 1/9`.

Upper bounds for `I` by positivity (shift inequalities, nonnegative majorants with nonnegative
Fourier transform, Fejér kernels as in `fejer_shifted_bound_gap`) use only

* `F(α) = α` on `[0, 1]` (Montgomery's theorem),
* `F ≥ 0`,
* `p ≥ 0` (the pair measure `δ₀ + p(ξ) dξ` is a positive measure).

So each such bound also holds for every model form factor with these properties. This module
constructs one with `I > 1/9` (`positivity_does_not_reach_three_quarters`): GUE plus a narrow spike
pair of mass `1/5` at `±101/100`,

`F(α) = min(|α|, 1) + 20 (Λ(α − 101/100) + Λ(α + 101/100))`, `Λ(u) = (1 − 100|u|)₊`,

with pair density `p(ξ) = 1 − sinc(πξ)² + (2/5) cos(2π · (101/100) ξ) sinc(πξ/100)²`. Hence no
positivity argument certifies `3/4`; the best positivity bound lies in `[1/18 + 47/750, 8/27]`, and
the target needs signed (arithmetic) information about `F` beyond `α = 1`.

`p ≥ 0` reduces (`spikedPairDensity_nonneg`) to `t² − 2 + 2 cos t + (2/5) t² cos(101t/100) ≥ 0`,
proved by the two-step double-angle bound `cos y ≥ 2(2(1 − y²/32)² − 1)² − 1` on rational
subintervals of `[31/20, 13/5]` and crude bounds outside.
-/

open MeasureTheory Real Set FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## The trigonometric core -/

/-- Lower bound for `cos y` from `cos(y/4) ≥ 1 − y²/32` and two double-angle steps. -/
def cosLower (y : ℝ) : ℝ := 2 * (2 * (1 - y ^ 2 / 32) ^ 2 - 1) ^ 2 - 1

theorem cosLower_le_cos {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 3) : cosLower y ≤ cos y := by
  have h4 : 1 - y ^ 2 / 32 ≤ cos (y / 4) := by
    have := one_sub_sq_div_two_le_cos (x := y / 4)
    linarith [show (y / 4) ^ 2 / 2 = y ^ 2 / 32 by ring]
  have hL : 23 / 32 ≤ 1 - y ^ 2 / 32 := by nlinarith
  have h2 : 2 * (1 - y ^ 2 / 32) ^ 2 - 1 ≤ cos (y / 2) := by
    have e : cos (y / 2) = 2 * cos (y / 4) ^ 2 - 1 := by
      rw [← cos_two_mul]; congr 1; ring
    rw [e]
    nlinarith [pow_le_pow_left₀ (by linarith) h4 2]
  have hM : 0 ≤ 2 * (1 - y ^ 2 / 32) ^ 2 - 1 := by nlinarith
  have e : cos y = 2 * cos (y / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  unfold cosLower
  rw [e]
  nlinarith [pow_le_pow_left₀ hM h2 2]

/-- `t²` times the pair density of the spike model at frequency `t/(2π)`, with the spike width
dropped (`spikedPairDensity_nonneg`). -/
def spikeTrig (t : ℝ) : ℝ :=
  t ^ 2 - 2 + 2 * cos t + 2 / 5 * (t ^ 2 * cos (101 / 100 * t))

theorem spikeTrig_neg (t : ℝ) : spikeTrig (-t) = spikeTrig t := by
  unfold spikeTrig
  rw [cos_neg, mul_neg, cos_neg, neg_sq]

/-- On `[p, q]` the core is at least `p² − 2 + 2 cosLower q + (2/5) q² cosLower(101q/100)`:
`cos` decreases on `[0, π]`, and `t² cos(101t/100) ≥ q² cosLower(101q/100)` once the latter is
`≤ 0`. -/
theorem spikeTrig_nonneg_of_mem {p q t : ℝ} (hp : 0 ≤ p) (hpt : p ≤ t) (htq : t ≤ q)
    (hq : 101 / 100 * q ≤ 3) (hQ : cosLower (101 / 100 * q) ≤ 0)
    (hb : 0 ≤ p ^ 2 - 2 + 2 * cosLower q + 2 / 5 * (q ^ 2 * cosLower (101 / 100 * q))) :
    0 ≤ spikeTrig t := by
  have hπ : (3 : ℝ) < π := pi_gt_three
  have ht0 : 0 ≤ t := hp.trans hpt
  have hq0 : 0 ≤ q := ht0.trans htq
  have hc1 : cosLower q ≤ cos t :=
    (cosLower_le_cos hq0 (by linarith)).trans
      (cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith) htq)
  have hc2 : cosLower (101 / 100 * q) ≤ cos (101 / 100 * t) :=
    (cosLower_le_cos (by positivity) hq).trans
      (cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith))
  have hsq : t ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ ht0 htq 2
  have hp2 : p ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hp hpt 2
  have key : q ^ 2 * cosLower (101 / 100 * q) ≤ t ^ 2 * cos (101 / 100 * t) := by
    rcases le_or_gt 0 (cos (101 / 100 * t)) with h | h
    · have h1 : q ^ 2 * cosLower (101 / 100 * q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q) hQ
      have h2 : 0 ≤ t ^ 2 * cos (101 / 100 * t) := mul_nonneg (sq_nonneg t) h
      linarith
    · calc q ^ 2 * cosLower (101 / 100 * q) ≤ q ^ 2 * cos (101 / 100 * t) :=
            mul_le_mul_of_nonneg_left hc2 (sq_nonneg q)
        _ ≤ t ^ 2 * cos (101 / 100 * t) := mul_le_mul_of_nonpos_right hsq h.le
  unfold spikeTrig
  linarith

/-- **The trigonometric core.** `t² − 2 + 2 cos t + (2/5) t² cos(101t/100) ≥ 0` for all real `t`.
Below `31/20` both cosine terms are harmless (`101t/100 ≤ π/2`, `cos t ≥ 1 − t²/2`); above `13/5`,
`(3/5) t² ≥ 4`; in between, eleven rational subintervals. -/
theorem spikeTrig_nonneg (t : ℝ) : 0 ≤ spikeTrig t := by
  wlog ht : 0 ≤ t generalizing t
  · simpa [spikeTrig_neg] using this (-t) (by linarith)
  rcases le_or_gt t (31 / 20) with h0 | h0
  · have hπ : (157 / 50 : ℝ) < π := by have := pi_gt_d2; norm_num at this ⊢; linarith
    have hc : 0 ≤ cos (101 / 100 * t) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have h1 := one_sub_sq_div_two_le_cos (x := t)
    unfold spikeTrig
    nlinarith [mul_nonneg (sq_nonneg t) hc]
  rcases le_or_gt (13 / 5) t with h1 | h1
  · have hc1 := neg_one_le_cos t
    have hc2 : 0 ≤ cos (101 / 100 * t) + 1 := by linarith [neg_one_le_cos (101 / 100 * t)]
    unfold spikeTrig
    nlinarith [mul_nonneg (sq_nonneg t) hc2]
  have J := fun (p q : ℝ) (hp : 0 ≤ p) (hpt : p ≤ t) (htq : t ≤ q) (hq : 101 / 100 * q ≤ 3)
    (hQ : cosLower (101 / 100 * q) ≤ 0)
    (hb : 0 ≤ p ^ 2 - 2 + 2 * cosLower q + 2 / 5 * (q ^ 2 * cosLower (101 / 100 * q))) =>
    spikeTrig_nonneg_of_mem hp hpt htq hq hQ hb
  rcases le_total t (42 / 25) with h2 | h2
  · exact J (31 / 20) (42 / 25) (by norm_num) h0.le h2 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (9 / 5) with h3 | h3
  · exact J (42 / 25) (9 / 5) (by norm_num) h2 h3 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (191 / 100) with h4 | h4
  · exact J (9 / 5) (191 / 100) (by norm_num) h3 h4 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (201 / 100) with h5 | h5
  · exact J (191 / 100) (201 / 100) (by norm_num) h4 h5 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (421 / 200) with h6 | h6
  · exact J (201 / 100) (421 / 200) (by norm_num) h5 h6 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (439 / 200) with h7 | h7
  · exact J (421 / 200) (439 / 200) (by norm_num) h6 h7 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (457 / 200) with h8 | h8
  · exact J (439 / 200) (457 / 200) (by norm_num) h7 h8 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (19 / 8) with h9 | h9
  · exact J (457 / 200) (19 / 8) (by norm_num) h8 h9 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (247 / 100) with h10 | h10
  · exact J (19 / 8) (247 / 100) (by norm_num) h9 h10 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  rcases le_total t (129 / 50) with h11 | h11
  · exact J (247 / 100) (129 / 50) (by norm_num) h10 h11 (by norm_num) (by norm_num [cosLower])
      (by norm_num [cosLower])
  exact J (129 / 50) (13 / 5) (by norm_num) h11 h1.le (by norm_num) (by norm_num [cosLower])
    (by norm_num [cosLower])

/-! ## The spike model and its pair density -/

/-- GUE form factor plus a spike pair of mass `1/5` at `±101/100` with half-width `1/100`. -/
def spikedFormFactor (α : ℝ) : ℝ :=
  min |α| 1 + 20 * (triangleFn (1 / 100) (α - 101 / 100) + triangleFn (1 / 100) (α + 101 / 100))

/-- The off-diagonal pair density `1 + 𝓕(F − 1)` of the spike model. -/
def spikedPairDensity (ξ : ℝ) : ℝ :=
  1 - sinc (π * ξ) ^ 2 + 2 / 5 * cos (2 * π * (101 / 100) * ξ) * sinc (π * (1 / 100) * ξ) ^ 2

/-- **The spike model has a positive pair measure.** Where the cosine is negative the spike width
only helps (`sinc² ≤ 1`), and `4(πξ)² (1 − sinc(πξ)² + (2/5) cos(2π·101ξ/100)) = spikeTrig(2πξ)`. -/
theorem spikedPairDensity_nonneg (ξ : ℝ) : 0 ≤ spikedPairDensity ξ := by
  unfold spikedPairDensity
  have hs1 : sinc (π * ξ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
  have hs2 : sinc (π * (1 / 100) * ξ) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
  have hs2' : 0 ≤ sinc (π * (1 / 100) * ξ) ^ 2 := sq_nonneg _
  rcases le_or_gt 0 (cos (2 * π * (101 / 100) * ξ)) with hC | hC
  · nlinarith [mul_nonneg hC hs2']
  have hξ : ξ ≠ 0 := by
    rintro rfl
    simp at hC
    linarith
  have hx : π * ξ ≠ 0 := mul_ne_zero pi_ne_zero hξ
  have hlow : 2 / 5 * cos (2 * π * (101 / 100) * ξ) ≤
      2 / 5 * cos (2 * π * (101 / 100) * ξ) * sinc (π * (1 / 100) * ξ) ^ 2 := by
    nlinarith
  suffices h : 0 ≤ 1 - sinc (π * ξ) ^ 2 + 2 / 5 * cos (2 * π * (101 / 100) * ξ) by linarith
  have hid : spikeTrig (2 * (π * ξ)) =
      4 * (π * ξ) ^ 2 * (1 - sinc (π * ξ) ^ 2 + 2 / 5 * cos (2 * π * (101 / 100) * ξ)) := by
    have e1 : cos (2 * (π * ξ)) = 1 - 2 * sin (π * ξ) ^ 2 := by rw [cos_two_mul, cos_sq']; ring
    have e2 : cos (101 / 100 * (2 * (π * ξ))) = cos (2 * π * (101 / 100) * ξ) := by
      congr 1; ring
    unfold spikeTrig
    rw [sinc_of_ne_zero hx, e1, e2]
    field_simp
    ring
  have hT := spikeTrig_nonneg (2 * (π * ξ))
  rw [hid] at hT
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hT

/-! ## Fourier transform of the spike model -/

theorem triangleFn_sub_eq_zero {w b α : ℝ} (hw : 0 < w) (hα : α ∉ Icc (b - w) (b + w)) :
    triangleFn w (α - b) = 0 := by
  apply triangleFn_eq_zero hw
  rw [mem_Icc, not_and_or, not_le, not_le] at hα
  rcases hα with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_triangleFn_sub {w : ℝ} (hw : 0 < w) (b : ℝ) :
    Integrable fun α : ℝ => triangleFn w (α - b) :=
  ((continuous_triangleFn w).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ hα => triangleFn_sub_eq_zero hw hα)

theorem integrable_cexp_mul_triangleFn_sub {w : ℝ} (hw : 0 < w) (b ξ : ℝ) :
    Integrable fun α : ℝ =>
      Complex.exp (↑(-2 * π * α * ξ) * Complex.I) * ((triangleFn w (α - b) : ℝ) : ℂ) := by
  have hΛ := continuous_triangleFn w
  have hc : Continuous fun α : ℝ =>
      Complex.exp (↑(-2 * π * α * ξ) * Complex.I) * ((triangleFn w (α - b) : ℝ) : ℂ) := by
    fun_prop
  refine hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := b - w) (b := b + w)) fun α hα => ?_)
  rw [triangleFn_sub_eq_zero hw hα, Complex.ofReal_zero, mul_zero]

/-- Translated triangle: `∫ e^{−2πiαξ} Λ_w(α − b) dα = e^{−2πibξ} · w sinc(πwξ)²`. -/
theorem integral_cexp_mul_triangleFn_sub {w : ℝ} (hw : 0 < w) (b ξ : ℝ) :
    ∫ α : ℝ, Complex.exp (↑(-2 * π * α * ξ) * Complex.I) * ((triangleFn w (α - b) : ℝ) : ℂ) =
      Complex.exp (↑(-2 * π * b * ξ) * Complex.I) * ((w * sinc (π * w * ξ) ^ 2 : ℝ) : ℂ) := by
  have h0 := fourier_triangleFn hw ξ
  rw [fourier_real_eq_integral_exp_smul] at h0
  simp only [smul_eq_mul] at h0
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun α : ℝ => Complex.exp (↑(-2 * π * α * ξ) * Complex.I) * ((triangleFn w (α - b) : ℝ) : ℂ)) b
  simp only [add_sub_cancel_right] at hshift
  rw [← hshift, ← h0, ← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem spikedFormFactor_sub_one (α : ℝ) :
    spikedFormFactor α - 1 = -triangleFn 1 (α - 0) + 20 * triangleFn (1 / 100) (α - 101 / 100) +
      20 * triangleFn (1 / 100) (α - -(101 / 100)) := by
  have hmin : min |α| 1 - 1 = -triangleFn 1 α := by
    unfold triangleFn
    rcases le_total |α| 1 with h | h
    · rw [min_eq_left h, div_one, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, div_one, max_eq_right (by linarith)]; ring
  unfold spikedFormFactor
  rw [sub_zero, sub_neg_eq_add]
  linarith

/-- **Fourier transform of the spike model.** `𝓕(F − 1)(ξ) = p(ξ) − 1`, real-valued. -/
theorem fourier_spikedFormFactor_sub_one (ξ : ℝ) :
    𝓕 (fun α => ((spikedFormFactor α - 1 : ℝ) : ℂ)) ξ = ((spikedPairDensity ξ - 1 : ℝ) : ℂ) := by
  have hA := integrable_cexp_mul_triangleFn_sub one_pos 0 ξ
  have hB := integrable_cexp_mul_triangleFn_sub (by norm_num : (0 : ℝ) < 1 / 100) (101 / 100) ξ
  have hC := integrable_cexp_mul_triangleFn_sub (by norm_num : (0 : ℝ) < 1 / 100) (-(101 / 100)) ξ
  rw [fourier_real_eq_integral_exp_smul]
  refine (integral_congr_ae (g := fun α : ℝ =>
      -(Complex.exp (↑(-2 * π * α * ξ) * Complex.I) * ((triangleFn 1 (α - 0) : ℝ) : ℂ)) +
        20 * (Complex.exp (↑(-2 * π * α * ξ) * Complex.I) *
          ((triangleFn (1 / 100) (α - 101 / 100) : ℝ) : ℂ)) +
        20 * (Complex.exp (↑(-2 * π * α * ξ) * Complex.I) *
          ((triangleFn (1 / 100) (α - -(101 / 100)) : ℝ) : ℂ)))
      (Filter.Eventually.of_forall fun α => ?_)).trans ?_
  · simp only [smul_eq_mul]
    rw [spikedFormFactor_sub_one]
    push_cast
    ring
  rw [integral_add, integral_add, integral_neg, integral_const_mul, integral_const_mul,
    integral_cexp_mul_triangleFn_sub one_pos,
    integral_cexp_mul_triangleFn_sub (w := 1 / 100) (by norm_num),
    integral_cexp_mul_triangleFn_sub (w := 1 / 100) (by norm_num)]
  rotate_left
  · exact hA.neg
  · exact hB.const_mul 20
  · exact hA.neg.add (hB.const_mul 20)
  · exact hC.const_mul 20
  have hcos : Complex.exp (↑(-2 * π * (101 / 100) * ξ) * Complex.I) +
      Complex.exp (↑(-2 * π * -(101 / 100) * ξ) * Complex.I) =
      ((2 * cos (2 * π * (101 / 100) * ξ) : ℝ) : ℂ) := by
    have e1 : (-2 * π * (101 / 100) * ξ : ℝ) = -(2 * π * (101 / 100) * ξ) := by ring
    have e2 : (-2 * π * -(101 / 100) * ξ : ℝ) = 2 * π * (101 / 100) * ξ := by ring
    rw [e1, e2, Complex.ofReal_neg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    push_cast
    ring
  have h0 : Complex.exp (↑(-2 * π * 0 * ξ) * Complex.I) = 1 := by simp
  unfold spikedPairDensity
  rw [h0]
  simp only [mul_one]
  push_cast at hcos ⊢
  linear_combination (20 * (1 / 100) * ((sinc (π * (1 / 100) * ξ) : ℂ)) ^ 2) * hcos

/-! ## Sub-threshold agreement and the trans-threshold excess -/

theorem continuous_spikedFormFactor : Continuous spikedFormFactor := by
  have hΛ := continuous_triangleFn (1 / 100)
  unfold spikedFormFactor
  fun_prop

theorem spikedFormFactor_of_mem_Icc {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : spikedFormFactor α = α := by
  have h1 : triangleFn (1 / 100) (α - 101 / 100) = 0 :=
    triangleFn_eq_zero (by norm_num) (by rw [abs_of_neg (by linarith [hα.2])]; linarith [hα.2])
  have h2 : triangleFn (1 / 100) (α + 101 / 100) = 0 :=
    triangleFn_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith [hα.1])]; linarith [hα.1])
  unfold spikedFormFactor
  rw [h1, h2, abs_of_nonneg hα.1, min_eq_left hα.2]
  ring

/-- `I(F) ≥ 1/18 + 47/750 > 1/9`: the spike carries mass `1/5` where `4/3 − α ≥ 47/150`. -/
theorem transThresholdIntegral_spikedFormFactor :
    1 / 18 + 47 / 750 ≤ transThresholdIntegral spikedFormFactor (4 / 3) := by
  unfold transThresholdIntegral
  have hΛc : Continuous fun α : ℝ => triangleFn (1 / 100) (α - 101 / 100) :=
    (continuous_triangleFn _).comp (continuous_id.sub continuous_const)
  have hbase : ∫ α in (1 : ℝ)..4 / 3, (4 / 3 - α) = 1 / 18 := by
    have h := transThresholdIntegral_four_thirds_one
    unfold transThresholdIntegral at h
    simpa only [mul_one] using h
  have hmass : ∫ α in (1 : ℝ)..4 / 3, triangleFn (1 / 100) (α - 101 / 100) = 1 / 100 := by
    rw [intervalIntegral.integral_comp_sub_right (triangleFn (1 / 100)) (101 / 100),
      show (1 : ℝ) - 101 / 100 = -(1 / 100) by norm_num,
      show (4 / 3 : ℝ) - 101 / 100 = 97 / 300 by norm_num]
    have hcont := continuous_triangleFn (1 / 100)
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 100)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have hcore : ∫ u in -(1 / 100 : ℝ)..1 / 100, triangleFn (1 / 100) u = 1 / 100 := by
      have h := integral_triangleFn (a := (1 / 100 : ℝ)) (by norm_num)
      rw [intervalIntegral.integral_ofReal] at h
      exact_mod_cast h
    have htail : ∫ u in (1 / 100 : ℝ)..97 / 300, triangleFn (1 / 100) u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
      · simp
      rw [uIcc_of_le (by norm_num)] at hu
      exact triangleFn_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith [hu.1])]; exact hu.1)
    rw [hcore, htail, add_zero]
  have hpt : ∀ α ∈ Icc (1 : ℝ) (4 / 3),
      (4 / 3 - α) + 94 / 15 * triangleFn (1 / 100) (α - 101 / 100) ≤
        (4 / 3 - α) * spikedFormFactor α := by
    intro α hα
    have hfar : triangleFn (1 / 100) (α + 101 / 100) = 0 :=
      triangleFn_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith [hα.1])]; linarith [hα.1])
    have hΛ0 := triangleFn_nonneg (1 / 100) (α - 101 / 100)
    unfold spikedFormFactor
    rw [hfar, abs_of_pos (by linarith [hα.1]), min_eq_right hα.1, add_zero]
    rcases le_or_gt α (51 / 50) with h | h
    · nlinarith [hα.2]
    · rw [triangleFn_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith)]
      linarith
  have hlhs : IntervalIntegrable
      (fun α : ℝ => (4 / 3 - α) + 94 / 15 * triangleFn (1 / 100) (α - 101 / 100)) volume 1 (4 / 3) :=
    (by fun_prop : Continuous fun α : ℝ => (4 / 3 - α)).intervalIntegrable _ _ |>.add
      ((hΛc.const_mul _).intervalIntegrable _ _)
  have hrhs : IntervalIntegrable (fun α : ℝ => (4 / 3 - α) * spikedFormFactor α) volume 1 (4 / 3) :=
    ((continuous_const.sub continuous_id).mul continuous_spikedFormFactor).intervalIntegrable _ _
  calc (1 / 18 + 47 / 750 : ℝ)
      = ∫ α in (1 : ℝ)..4 / 3, ((4 / 3 - α) + 94 / 15 * triangleFn (1 / 100) (α - 101 / 100)) := by
        rw [intervalIntegral.integral_add
            ((by fun_prop : Continuous fun α : ℝ => (4 / 3 - α)).intervalIntegrable _ _)
            ((hΛc.const_mul _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, hbase, hmass]
        norm_num
    _ ≤ ∫ α in (1 : ℝ)..4 / 3, (4 / 3 - α) * spikedFormFactor α :=
        intervalIntegral.integral_mono_on (by norm_num) hlhs hrhs hpt

/-! ## The no-go -/

/-- **Positivity cannot certify the `3/4` threshold.** Some continuous, even, nonnegative form
factor equals `α` on `[0, 1]`, has `F − 1` integrable with real Fourier transform `p − 1` for a
nonnegative pair density `p`, and still has trans-threshold integral above `1/9`, so its Frobenius
norm at bandwidth `4/3` exceeds `5/4`. Any upper bound for `I` derived only from these properties
is therefore weaker than `I ≤ 1/9`. -/
theorem positivity_does_not_reach_three_quarters :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ α, F (-α) = F α) ∧ (∀ α, 0 ≤ F α) ∧
      (∀ α ∈ Icc (0 : ℝ) 1, F α = α) ∧ Integrable (fun α => F α - 1) ∧
      (∀ ξ : ℝ, ∃ p : ℝ, 0 ≤ p ∧ 𝓕 (fun α => ((F α - 1 : ℝ) : ℂ)) ξ = ((p - 1 : ℝ) : ℂ)) ∧
      1 / 9 < transThresholdIntegral F (4 / 3) ∧ 5 / 4 < frobeniusFormFactor F (4 / 3) := by
  have hI : 1 / 9 < transThresholdIntegral spikedFormFactor (4 / 3) :=
    lt_of_lt_of_le (by norm_num) transThresholdIntegral_spikedFormFactor
  refine ⟨spikedFormFactor, continuous_spikedFormFactor, fun α => ?_, fun α => ?_,
    fun α hα => spikedFormFactor_of_mem_Icc hα, ?_,
    fun ξ => ⟨spikedPairDensity ξ, spikedPairDensity_nonneg ξ, fourier_spikedFormFactor_sub_one ξ⟩,
    hI, ?_⟩
  · have hneg : ∀ w u : ℝ, triangleFn w (-u) = triangleFn w u := fun w u => by
      unfold triangleFn; rw [abs_neg]
    unfold spikedFormFactor
    rw [abs_neg, show -α - 101 / 100 = -(α + 101 / 100) by ring,
      show -α + 101 / 100 = -(α - 101 / 100) by ring, hneg, hneg, add_comm (triangleFn _ _)]
  · unfold spikedFormFactor
    have := triangleFn_nonneg (1 / 100) (α - 101 / 100)
    have := triangleFn_nonneg (1 / 100) (α + 101 / 100)
    have : 0 ≤ min |α| 1 := le_min (abs_nonneg α) zero_le_one
    positivity
  · rw [funext spikedFormFactor_sub_one]
    exact ((integrable_triangleFn_sub one_pos 0).neg.add
      ((integrable_triangleFn_sub (by norm_num) _).const_mul 20)).add
      ((integrable_triangleFn_sub (by norm_num) _).const_mul 20)
  · rw [← not_le, frobeniusFormFactor_four_thirds_le_five_fourths_iff continuous_spikedFormFactor
      fun α hα => spikedFormFactor_of_mem_Icc hα, not_le]
    exact hI

end GaloisForLFunctions.TransThresholdPairCorrelation
