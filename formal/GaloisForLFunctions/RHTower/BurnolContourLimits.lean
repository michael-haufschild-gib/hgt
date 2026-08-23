import GaloisForLFunctions.RHTower.BurnolRectangleSum
import GaloisForLFunctions.RHTower.BurnolEdgeIntegrability
import GaloisForLFunctions.RHTower.ResidueContourEdges
import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal

/-!
# The four edges of Burnol's rectangle in the limit

At a fixed abscissa `A`, as the selected heights `T k` tend to infinity, the two horizontal edges
vanish (Proposition 5.1 plus the quick decrease of `G`) and the two vertical edges converge to the
integrals over the full vertical lines `Re s = 1/2 ± A`.

## Main results

* `tendsto_hIntegral_burnolIntegrand` — a horizontal edge tends to `0`.
* `tendsto_vIntegral_burnolIntegrand` — a vertical edge tends to the line integral.
* `tendsto_rectangleIntegral'_burnolIntegrand` — the rectangle integral tends to
  `(1/2π)·(right line − left line)`.
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The horizontal edges -/

theorem hIntegral_burnolIntegrand (G : ℂ → ℂ) (Z : ℂ) (x₁ x₂ y : ℝ) :
    HIntegral (burnolIntegrand G Z) x₁ x₂ y
      = riemannZeta Z * ∫ σ in x₁..x₂, burnolEdgeIntegrand G Z ((σ : ℂ) + (y : ℂ) * I) := by
  rw [HIntegral, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun σ _ => burnolIntegrand_eq_smul_edge G Z _

/-- **A horizontal edge vanishes** along the selected heights. -/
theorem tendsto_hIntegral_burnolIntegrand {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    {C A b : ℝ} {k₀ : ℕ} (hC : 0 < C) (hA : 0 < A) (hb : 2 ≤ b)
    {ε : ℝ} (hε : |ε| = 1)
    (hzeta : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A)
    {x₁ x₂ : ℝ} (hx₁ : -b ≤ x₁) (hx₁' : x₁ ≤ b) (hx₂ : -b ≤ x₂) (hx₂' : x₂ ≤ b)
    (Z : ℂ) :
    Tendsto (fun k : ℕ => HIntegral (burnolIntegrand G Z) x₁ x₂ (ε * T k)) atTop (𝓝 0) := by
  have hedge := tendsto_norm_horizontal_edge_zero hG htop hT1 hC hA hb hε hzeta
    hx₁ hx₁' hx₂ hx₂' Z
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrw : ∀ k : ℕ, ‖HIntegral (burnolIntegrand G Z) x₁ x₂ (ε * T k)‖
      = ‖riemannZeta Z‖ * ‖∫ σ in x₁..x₂,
          G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I)
            * (riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹
            * (Z - ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖ := by
    intro k
    rw [hIntegral_burnolIntegrand, norm_mul]
    simp only [burnolEdgeIntegrand]
  refine Tendsto.congr (fun k => (hrw k).symm) ?_
  have := hedge.const_mul ‖riemannZeta Z‖
  simpa using this

/-! ## The vertical edges -/

theorem vIntegral_burnolIntegrand (G : ℂ → ℂ) (Z : ℂ) (x y₁ y₂ : ℝ) :
    VIntegral (burnolIntegrand G Z) x y₁ y₂
      = I • (riemannZeta Z * ∫ y in y₁..y₂, burnolEdgeIntegrand G Z ((x : ℂ) + (y : ℂ) * I)) := by
  rw [VIntegral, ← intervalIntegral.integral_const_mul]
  congr 1
  exact intervalIntegral.integral_congr fun y _ => burnolIntegrand_eq_smul_edge G Z _

/-- **A vertical edge converges to the line integral.** -/
theorem tendsto_vIntegral_burnolIntegrand {G : ℂ → ℂ} {Z : ℂ} {x : ℝ}
    (hint : Integrable (fun y : ℝ => burnolEdgeIntegrand G Z ((x : ℂ) + (y : ℂ) * I)) volume)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) :
    Tendsto (fun k : ℕ => VIntegral (burnolIntegrand G Z) x (-T k) (T k)) atTop
      (𝓝 (I • (riemannZeta Z * ∫ y : ℝ, burnolEdgeIntegrand G Z ((x : ℂ) + (y : ℂ) * I)))) := by
  have hbot : Tendsto (fun k : ℕ => -T k) atTop atBot := tendsto_neg_atTop_atBot.comp htop
  have hlim := intervalIntegral_tendsto_integral (μ := (volume : Measure ℝ)) hint hbot htop
  have h2 := (hlim.const_mul (riemannZeta Z)).const_smul I
  refine Tendsto.congr (fun k => ?_) h2
  rw [vIntegral_burnolIntegrand]

/-! ## The whole rectangle -/

/-- **The rectangle integral converges to the difference of the two line integrals.** -/
theorem tendsto_rectangleIntegral'_burnolIntegrand {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    {C Aexp b : ℝ} {k₀ : ℕ} (hC : 0 < C) (hAexp : 0 < Aexp) (hb : 2 ≤ b)
    (hzetaPos : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + (((1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp)
    (hzetaNeg : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + (((-1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp)
    {A : ℝ} (hA1 : -b ≤ 1 / 2 - A) (hA2 : 1 / 2 + A ≤ b) (hA0 : 0 ≤ A)
    {Z : ℂ}
    (hintR : Integrable
      (fun y : ℝ => burnolEdgeIntegrand G Z (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I)) volume)
    (hintL : Integrable
      (fun y : ℝ => burnolEdgeIntegrand G Z (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)) volume) :
    Tendsto (fun k : ℕ => RectangleIntegral' (burnolIntegrand G Z)
        (burnolRectLow A (T k)) (burnolRectHigh A (T k))) atTop
      (𝓝 ((1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
        ((∫ y : ℝ, burnolEdgeIntegrand G Z (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I))
          - ∫ y : ℝ, burnolEdgeIntegrand G Z (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)))) := by
  have hAb1 : -b ≤ 1 / 2 - A := hA1
  have hAb2 : 1 / 2 - A ≤ b := by linarith
  have hAb3 : -b ≤ 1 / 2 + A := by linarith
  have hAb4 : 1 / 2 + A ≤ b := hA2
  have hεpos : |(1 : ℝ)| = 1 := by norm_num
  have hεneg : |(-1 : ℝ)| = 1 := by norm_num
  have hH2 : Tendsto (fun k : ℕ =>
      HIntegral (burnolIntegrand G Z) (1 / 2 - A) (1 / 2 + A) (T k)) atTop (𝓝 0) := by
    have h := tendsto_hIntegral_burnolIntegrand hG htop hT1 hC hAexp hb hεpos hzetaPos
      hAb1 hAb2 hAb3 hAb4 Z
    refine Tendsto.congr (fun k => ?_) h
    rw [one_mul]
  have hH1 : Tendsto (fun k : ℕ =>
      HIntegral (burnolIntegrand G Z) (1 / 2 - A) (1 / 2 + A) (-T k)) atTop (𝓝 0) := by
    have h := tendsto_hIntegral_burnolIntegrand hG htop hT1 hC hAexp hb hεneg hzetaNeg
      hAb1 hAb2 hAb3 hAb4 Z
    refine Tendsto.congr (fun k => ?_) h
    rw [neg_one_mul]
  have hV1 := tendsto_vIntegral_burnolIntegrand (G := G) (Z := Z) hintR htop
  have hV2 := tendsto_vIntegral_burnolIntegrand (G := G) (Z := Z) hintL htop
  have hR : Tendsto (fun k : ℕ => RectangleIntegral (burnolIntegrand G Z)
      (burnolRectLow A (T k)) (burnolRectHigh A (T k))) atTop
      (𝓝 (0 - 0
        + I • (riemannZeta Z * ∫ y : ℝ,
            burnolEdgeIntegrand G Z (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I))
        - I • (riemannZeta Z * ∫ y : ℝ,
            burnolEdgeIntegrand G Z (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)))) := by
    refine Tendsto.congr (fun k => ?_) (((hH1.sub hH2).add hV1).sub hV2)
    rw [RectangleIntegral, burnolRectLow_re, burnolRectLow_im, burnolRectHigh_re,
      burnolRectHigh_im]
  have hsmul := hR.const_smul (1 / (2 * (Real.pi : ℂ) * I))
  have hconst : (1 / (2 * (Real.pi : ℂ) * I)) • ((0 : ℂ) - 0
        + I • (riemannZeta Z * ∫ y : ℝ,
            burnolEdgeIntegrand G Z (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I))
        - I • (riemannZeta Z * ∫ y : ℝ,
            burnolEdgeIntegrand G Z (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)))
      = (1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
        ((∫ y : ℝ, burnolEdgeIntegrand G Z (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I))
          - ∫ y : ℝ, burnolEdgeIntegrand G Z (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [← hconst]
  exact hsmul

end

end RHTower
