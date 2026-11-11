import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine

/-!
# Weyl growth on arbitrarily thin strips about the critical line

Right-strip interpolation and the functional equation give
`|ζ(s)| ≤ C |Im s|^(1/6+ε)` on a sufficiently thin two-sided strip,
with one constant for the entire strip and both signs of the height.
-/

open Complex Set
open scoped ComplexConjugate

namespace RHTower

private theorem exists_norm_zeta_right_strip_le_abs_rpow {η : ℝ}
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ C > 0, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 + η → 8 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (1 / 6 + η) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_riemannZeta_le_subconvex hη hηhalf
  have hpos : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (1 / 6 + η) := by
    intro σ t hσ hση ht
    refine (hbound σ t hσ hση ht).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith only [ht])
    apply (div_le_iff₀ (by linarith only [hη] : 0 < 1 / 2 + η)).mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [hσ]) (by linarith only [hη])
  refine ⟨C, hC, fun s hs hsη ht => ?_⟩
  rcases le_or_gt 0 s.im with him | him
  · have hb := hpos s.re s.im hs hsη (by simpa only [abs_of_nonneg him] using ht)
    simpa only [Complex.re_add_im, abs_of_nonneg him] using hb
  · have hb := hpos s.re (-s.im) hs hsη (by simpa only [abs_of_neg him] using ht)
    have heq : (s.re : ℂ) + ((-s.im : ℝ) : ℂ) * I = conj s := by
      apply Complex.ext <;> simp
    rw [heq, riemannZeta_conj, Complex.norm_conj] at hb
    simpa only [abs_of_neg him] using hb

/-- For every exponent above `1/6`, zeta has that uniform power bound on
some two-sided strip about the critical line. -/
theorem exists_norm_zeta_thin_strip_le_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0, ∀ s : ℂ,
      |s.re - 1 / 2| ≤ r → 8 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (1 / 6 + ε) := by
  let r := min (ε / 4) (1 / 8)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrε : r ≤ ε / 4 := min_le_left _ _
  have hr8 : r ≤ 1 / 8 := min_le_right _ _
  have hrhalf : r < 1 / 2 := by linarith only [hr8]
  obtain ⟨C, hC, hright⟩ := exists_norm_zeta_right_strip_le_abs_rpow hr hrhalf.le
  obtain ⟨K, hK, hchi⟩ := exists_norm_zetaChi_moving_left_line_le_rpow hr.le hrhalf
  refine ⟨r, hr, hrhalf, C * (K + 1), by positivity, fun s hs ht => ?_⟩
  have hs' := abs_le.mp hs
  have ht1 : 1 ≤ |s.im| := by linarith only [ht]
  have ht0 : 0 < |s.im| := by linarith only [ht]
  by_cases hhalf : 1 / 2 ≤ s.re
  · have hz := hright s hhalf (by linarith only [hs'.2]) ht
    calc
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (1 / 6 + r) := hz
      _ ≤ C * |s.im| ^ (1 / 6 + ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hrε, hε])) hC.le
      _ ≤ C * (K + 1) * |s.im| ^ (1 / 6 + ε) :=
        mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right hC.le (by linarith only [hK])) (Real.rpow_nonneg ht0.le _)
  · have hsr : s.re < 1 / 2 := lt_of_not_ge hhalf
    have hd0 : 0 ≤ 1 / 2 - s.re := by linarith only [hsr]
    have hdr : 1 / 2 - s.re ≤ r := by linarith only [hs'.1]
    have hc := hchi (1 / 2 - s.re) hd0 hdr s.im
    have heq : (((1 / 2 - (1 / 2 - s.re) : ℝ) : ℂ) + (s.im : ℂ) * I) = s := by
      rw [show (1 / 2 : ℝ) - (1 / 2 - s.re) = s.re by ring]
      exact Complex.re_add_im s
    rw [heq, max_eq_right ht1] at hc
    have hz := hright (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hsr])
      (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hs'.1, hr8])
      (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using ht)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hz
    have hs0 : 0 < s.re := by linarith only [hs'.1, hrhalf]
    have hs1 : s.re < 1 := by linarith only [hsr]
    have hsne0 : s ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hs0
    have hsne1 : s ≠ 1 := by intro h; simpa only [h, Complex.one_re, lt_self_iff_false] using hs1
    have hgamma : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [hs1])
    rw [zeta_eq_zetaChi_mul hsne0 hsne1 hgamma, norm_mul]
    calc
      ‖zetaChi s‖ * ‖riemannZeta (1 - s)‖ ≤
          (K * |s.im| ^ (1 / 2 - s.re)) * (C * |s.im| ^ (1 / 6 + r)) :=
        mul_le_mul hc hz (norm_nonneg _) (mul_nonneg hK (Real.rpow_nonneg ht0.le _))
      _ = K * C * |s.im| ^ ((1 / 2 - s.re) + (1 / 6 + r)) := by
        rw [Real.rpow_add ht0 (1 / 2 - s.re) (1 / 6 + r)]
        ring
      _ ≤ K * C * |s.im| ^ (1 / 6 + ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hdr, hrε, hε]))
        (mul_nonneg hK hC.le)
      _ ≤ C * (K + 1) * |s.im| ^ (1 / 6 + ε) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hC]) (Real.rpow_nonneg ht0.le _)

/-- Compactness fills bounded heights in the thin-strip Weyl estimate. -/
theorem exists_global_norm_zeta_thin_strip_le_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0, ∀ s : ℂ,
      |s.re - 1 / 2| ≤ r →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (1 / 6 + ε) := by
  obtain ⟨r, hr, hrhalf, C₀, hC₀, hlarge⟩ := exists_norm_zeta_thin_strip_le_weyl hε
  let box : Set (ℝ × ℝ) := Icc (1 / 2 - r) (1 / 2 + r) ×ˢ Icc (-8) 8
  let pt : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * I
  have hcont : ContinuousOn (fun p => riemannZeta (pt p)) box := by
    intro p hp
    have hp1 : pt p ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [pt, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero, Complex.one_re] at hre
      have hup : p.1 ≤ 1 / 2 + r := hp.1.2
      linarith only [hre, hup, hrhalf]
    exact ((differentiableAt_riemannZeta hp1).continuousAt.comp
      (show ContinuousAt pt p by dsimp [pt]; fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  let C := max C₀ B + 1
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith only [le_max_left C₀ B]
  have hBC : B ≤ C := by dsimp [C]; linarith only [le_max_right C₀ B]
  have hC : 0 < C := hC₀.trans_le hC₀C
  have he : 0 ≤ (1 / 6 : ℝ) + ε := by linarith only [hε]
  refine ⟨r, hr, hrhalf, C, hC, fun s hs => ?_⟩
  by_cases ht : |s.im| ≤ 8
  · have hs' := abs_le.mp hs
    have hmem : (s.re, s.im) ∈ box :=
      ⟨⟨by linarith only [hs'.1], by linarith only [hs'.2]⟩, abs_le.mp ht⟩
    have hsmall : ‖riemannZeta s‖ ≤ B := by
      simpa only [pt, Complex.re_add_im] using hB (s.re, s.im) hmem
    exact (hsmall.trans hBC).trans (le_mul_of_one_le_right hC.le
      (Real.one_le_rpow (by linarith only [abs_nonneg s.im]) he))
  · exact (hlarge s hs (le_of_not_ge ht)).trans
      (mul_le_mul hC₀C
        (Real.rpow_le_rpow (abs_nonneg _) (by linarith only [abs_nonneg s.im]) he)
        (Real.rpow_nonneg (abs_nonneg _) _) hC.le)

end RHTower
