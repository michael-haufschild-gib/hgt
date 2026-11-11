import GaloisForLFunctions.RHTower.ZetaDiscLowerBoundsAtTypicalHeights
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingRightLine

/-!
# Typical-height zeta floors on both sides of the critical line

The functional-equation factor is uniformly bounded on each closed substrip
right of the critical line. Reflection therefore transfers the typical-height
disc floor to the left half of the critical strip, at the same heights.
-/

open Complex Filter Topology Set Metric MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace RHTower

/-- Reflection from a closed left substrip costs only a fixed factor. -/
theorem exists_norm_zeta_reflect_le {a : ℝ} (ha : 0 < a) (hahalf : a < 1 / 2) :
    ∃ C > 0, ∀ s : ℂ, a ≤ s.re → s.re ≤ 1 / 2 →
      ‖riemannZeta (1 - conj s)‖ ≤ C * ‖riemannZeta s‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_zetaChi_moving_right_line_le_rpow
    (d₀ := 1 / 2 - a) (by linarith) (by linarith)
  refine ⟨K + 1, by linarith, fun s hs hshalf => ?_⟩
  let v := 1 - conj s
  have hvre : v.re = 1 - s.re := by simp only [v, Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hvhalf : 1 / 2 ≤ v.re := by rw [hvre]; linarith
  have hvone : v.re < 1 := by rw [hvre]; linarith
  have hχ := hK (v.re - 1 / 2) (by linarith) (by rw [hvre]; linarith) v.im
  have heq : (((1 / 2 + (v.re - 1 / 2) : ℝ) : ℂ) + (v.im : ℂ) * I) = v := by
    rw [show (1 / 2 : ℝ) + (v.re - 1 / 2) = v.re by ring]
    exact Complex.re_add_im v
  rw [heq] at hχ
  have hχbound : ‖zetaChi v‖ ≤ K + 1 := by
    refine (hχ.trans (div_le_self hK0 ?_)).trans (by linarith)
    exact Real.one_le_rpow (le_max_left _ _) (by linarith)
  have hv0 : v ≠ 0 := by intro h; rw [h, Complex.zero_re] at hvhalf; linarith
  have hv1 : v ≠ 1 := by intro h; rw [h, Complex.one_re] at hvone; exact lt_irrefl _ hvone
  have hg : Gammaℝ (1 - v) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  rw [zeta_eq_zetaChi_mul hv0 hv1 hg, norm_mul]
  have hpartner : 1 - v = conj s := by dsimp [v]; ring
  rw [hpartner, riemannZeta_conj, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right hχbound (norm_nonneg _)

/-- The typical-height disc floor on the left follows from the right floor by
the functional equation and conjugation. -/
theorem exists_zeta_left_disc_floor_at_typical_heights {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 0 < c.re - 2 * r) (hhalf : c.re + 2 * r < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b > 0, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ∃ z ∈ closedBall c r, ‖riemannZeta (z + τ * I)‖ < b} ∩ Icc 0 T)
        ≤ ENNReal.ofReal (δ * T) := by
  let c' := 1 - conj c
  have hc're : c'.re = 1 - c.re := by simp only [c', Complex.sub_re, Complex.one_re, Complex.conj_re]
  obtain ⟨b, hb, hfloor⟩ := exists_zeta_disc_floor_at_typical_heights (c := c') hr
    (by rw [hc're]; linarith) (by rw [hc're]; linarith) hδ
  obtain ⟨C, hC, hreflect⟩ := exists_norm_zeta_reflect_le h0 (by linarith)
  refine ⟨b / C, div_pos hb hC, ?_⟩
  filter_upwards [hfloor] with T hT
  refine le_trans (measure_mono ?_) hT
  rintro τ ⟨⟨z, hz, hsmall⟩, hτ⟩
  refine ⟨⟨1 - conj z, ?_, ?_⟩, hτ⟩
  · rw [mem_closedBall, dist_eq_norm]
    have heq : 1 - conj z - c' = -conj (z - c) := by
      dsimp [c']
      rw [map_sub]
      ring
    rw [heq, norm_neg, RCLike.norm_conj]
    exact mem_closedBall_iff_norm.mp hz
  · have hzre := abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans (mem_closedBall_iff_norm.mp hz))
    simp only [Complex.sub_re] at hzre
    have hsre : (z + τ * I).re = z.re := by simp
    have hbound := hreflect (z + τ * I) (by rw [hsre]; linarith [hzre.1])
      (by rw [hsre]; linarith [hzre.2])
    have heq : 1 - conj (z + τ * I) = 1 - conj z + τ * I := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [heq] at hbound
    have hsmall' := (lt_div_iff₀ hC).mp hsmall
    exact hbound.trans_lt (by nlinarith only [hsmall'])

/-- Every off-line point of the critical strip has a disc on which zeta is
uniformly bounded away from zero at all but any prescribed small density. -/
theorem exists_zeta_offLine_disc_floor {c : ℂ} (h0 : 0 < c.re) (h1 : c.re < 1)
    (hne : c.re ≠ 1 / 2) :
    ∃ r > 0, ∀ δ > 0, ∃ b > 0, ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ∃ z ∈ closedBall c r, ‖riemannZeta (z + τ * I)‖ < b} ∩ Icc 0 T)
        ≤ ENNReal.ofReal (δ * T) := by
  rcases lt_or_gt_of_ne hne with hleft | hright
  · let r := min (c.re / 4) ((1 / 2 - c.re) / 4)
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hr0 : r ≤ c.re / 4 := min_le_left _ _
    have hrhalf : r ≤ (1 / 2 - c.re) / 4 := min_le_right _ _
    exact ⟨r, hr, fun δ hδ => exists_zeta_left_disc_floor_at_typical_heights hr
      (by linarith) (by linarith) hδ⟩
  · let r := min ((c.re - 1 / 2) / 4) ((1 - c.re) / 4)
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hrhalf : r ≤ (c.re - 1 / 2) / 4 := min_le_left _ _
    have hr1 : r ≤ (1 - c.re) / 4 := min_le_right _ _
    exact ⟨r, hr, fun δ hδ => exists_zeta_disc_floor_at_typical_heights hr
      (by linarith) (by linarith) hδ⟩

end RHTower
