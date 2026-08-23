import GaloisForLFunctions.RHTower.SoninExtendedMellinCrude
import GaloisForLFunctions.RHTower.SoninExtendedFunctionalEquation
import GaloisForLFunctions.RHTower.MellinHardyClasses
import GaloisForLFunctions.HTGeometry.HardyLineIsometry

/-!
# Edge estimates for the continued Mellin transform

Phragmén--Lindelöf needs *bounded* edges, not merely polynomially bounded ones: the conclusion
inherits the edge exponents, so an exponent `1` on the right edge would swamp Burnol's target
`max(1/2-a,0)+ε` whenever that is smaller.  Right of the critical line the bound is the Hardy one:
the tail transform of an `L²(a,∞)` datum is an element of `A^s H²`, and a Hardy function of the
right half-plane obeys `‖F(w)‖ ≤ ‖φ‖(2 Re w)^{-1/2}`, which is uniform in the height.

Left of the critical line the functional equation moves the point to the right, so this module also
records the identification of the two continuations across `0 < Re s < 1/2`.

## Main results

* `exists_norm_mellinTail_bounded` — the Hardy bound for the tail transform
* `exists_norm_extendedMellinRight_bounded` — bounded on a closed substrip of `Re s > 1/2`
* `extendedMellinRight_eq_left` — the functional equation for the continuations
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **The Hardy bound for the tail transform.** -/
theorem exists_norm_mellinTail_bounded {a : ℝ} (ha : 0 < a) (f : SoninL2) {σ₁ b : ℝ}
    (hσ₁ : 1 / 2 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ b →
      ‖∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t‖ ≤ C := by
  obtain ⟨M, hM⟩ := isMellinTailHardy_mellinTail ha ((Lp.memLp f).restrict (Ioi a))
  set K : ℝ := rayL2Norm (hardyDatum _ hM) with hK
  have hK0 : 0 ≤ K := rayL2Norm_nonneg _
  set Apow : ℝ := max (a ^ ((1 : ℝ) / 2 - b)) (a ^ ((1 : ℝ) / 2 - σ₁)) with hApow
  have hApow0 : 0 ≤ Apow := le_trans (Real.rpow_nonneg ha.le _) (le_max_left _ _)
  refine ⟨Apow * (K / Real.sqrt (2 * σ₁ - 1)), by positivity, ?_⟩
  intro s hs hsb
  have hs0 : 0 < s.re := by linarith
  set w : ℂ := s - 1 / 2 with hw
  have hwre : w.re = s.re - 1 / 2 := by
    rw [hw, Complex.sub_re]
    have : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [this]
  have hwpos : 0 < w.re := by rw [hwre]; linarith
  have hbound := norm_le_of_isHalfPlaneHardy hM hwpos
  have hval : ((a : ℝ) : ℂ) ^ w * (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-(w + 1 / 2)) *
      (f : ℝ → ℂ) t) = ((a : ℝ) : ℂ) ^ w * ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
    have : w + 1 / 2 = s := by rw [hw]; ring
    rw [this]
  rw [hval] at hbound
  -- strip the `a^w` factor
  have hnormpow : ‖((a : ℝ) : ℂ) ^ w‖ = a ^ w.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ha w
  have hpowpos : (0 : ℝ) < a ^ w.re := Real.rpow_pos_of_pos ha _
  rw [norm_mul, hnormpow] at hbound
  have hstep : ‖∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t‖
      ≤ (a ^ w.re)⁻¹ * (K / Real.sqrt (2 * w.re)) := by
    rw [← le_div_iff₀' hpowpos] at hbound
    rw [inv_mul_eq_div]
    exact hbound
  refine hstep.trans ?_
  have hinv : (a ^ w.re)⁻¹ = a ^ ((1 : ℝ) / 2 - s.re) := by
    rw [hwre, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [hinv]
  have hApowle : a ^ ((1 : ℝ) / 2 - s.re) ≤ Apow := by
    rw [hApow]
    exact rpow_le_max_of_mem_Icc ha (by linarith) (by linarith)
  have hsqrt : Real.sqrt (2 * σ₁ - 1) ≤ Real.sqrt (2 * w.re) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hwre]
    linarith
  have hsq0 : 0 < Real.sqrt (2 * σ₁ - 1) := Real.sqrt_pos.2 (by linarith)
  have hdiv : K / Real.sqrt (2 * w.re) ≤ K / Real.sqrt (2 * σ₁ - 1) := by
    exact div_le_div_of_nonneg_left hK0 hsq0 hsqrt
  have hnn : (0 : ℝ) ≤ K / Real.sqrt (2 * w.re) := by positivity
  exact mul_le_mul hApowle hdiv hnn hApow0

/-- **The continued transform is bounded on a closed substrip right of the critical line.** -/
theorem exists_norm_extendedMellinRight_bounded {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    {σ₁ b : ℝ} (hσ₁ : 1 / 2 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖extendedMellinRight a c d f s‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_mellinTail_bounded ha f (σ₁ := σ₁) (b := b) hσ₁
  set Bpow : ℝ := max (a ^ ((1 : ℝ) - b)) (a ^ ((1 : ℝ) - σ₁)) with hBpow
  have hBpow0 : 0 ≤ Bpow := le_trans (Real.rpow_nonneg ha.le _) (le_max_left _ _)
  refine ⟨C₀ + ‖d‖ * Bpow, by positivity, ?_⟩
  intro s hs hsb ht
  have hs2 : 1 / 2 < s.re := lt_of_lt_of_le hσ₁ hs
  have htail : ‖extendedTailMellin a c f s‖ ≤ C₀ := by
    rw [extendedTailMellin_eq ha hc hs2]
    exact hC₀ s hs hsb
  have hhead : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ ≤ ‖d‖ * Bpow := by
    have hnum : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)‖ = ‖d‖ * a ^ ((1 : ℝ) - s.re) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      congr 2
    have hden : (1 : ℝ) ≤ ‖(1 : ℂ) - s‖ := by
      have him : ((1 : ℂ) - s).im = -s.im := by simp
      calc (1 : ℝ) ≤ |s.im| := ht
        _ = |((1 : ℂ) - s).im| := by rw [him, abs_neg]
        _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
    have hBpowle : a ^ ((1 : ℝ) - s.re) ≤ Bpow := by
      rw [hBpow]
      exact rpow_le_max_of_mem_Icc ha (by linarith) (by linarith)
    have hdn : (0 : ℝ) ≤ ‖d‖ := norm_nonneg d
    rw [norm_div, hnum, div_le_iff₀ (by linarith : (0:ℝ) < ‖(1 : ℂ) - s‖)]
    have hA : ‖d‖ * a ^ ((1 : ℝ) - s.re) ≤ ‖d‖ * Bpow :=
      mul_le_mul_of_nonneg_left hBpowle hdn
    nlinarith [mul_nonneg hdn hBpow0]
  calc ‖extendedMellinRight a c d f s‖
      ≤ ‖extendedTailMellin a c f s‖ + ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ := by
        rw [extendedMellinRight]
        exact norm_add_le _ _
    _ ≤ C₀ + ‖d‖ * Bpow := by linarith

/-- **The functional equation for the two continuations.** -/
theorem extendedMellinRight_eq_left {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs0 : 0 < s.re) (hs : s.re < 1 / 2) :
    extendedMellinRight a c d f s
      = burnolChiFactor s * extendedMellinRight a d c (fourierUnitary f) (1 - s) := by
  have hs1 : s.re < 1 := by linarith
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hdF : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
    rw [hff]
    exact hd
  have hzre : 1 / 2 < ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hzre1 : ((1 : ℂ) - s).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  -- the head of `f`
  have hhead : (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      = d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact integral_head_of_mem_extended ha hd hs1
  -- the right-hand side of the functional equation
  have hsplit := integral_split_extendedMellin (f := fourierUnitary f) ha hc hzre hzre1
  have hone : (1 : ℂ) - ((1 : ℂ) - s) = s := by ring
  rw [hone] at hsplit
  have htail := extendedTailMellin_eq (f := fourierUnitary f) ha hdF hzre
  have hRHS : soninMellinIntegral (fourierUnitary f) (1 - s)
      = extendedMellinRight a d c (fourierUnitary f) (1 - s) := by
    rw [soninMellinIntegral, hsplit, extendedMellinRight, htail, hone]
    ring
  have hFE := extendedFullMellin_functional_equation ha hev hc hs0 hs
  rw [hRHS, extendedFullMellin, hhead] at hFE
  rw [extendedMellinRight]
  exact hFE

end RHTower

end
