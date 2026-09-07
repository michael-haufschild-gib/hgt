import GaloisForLFunctions.RHTower.ProductAFEDual
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualReflection

/-!
# The exact Gaussian approximate functional equation for `ζ(s₁)ζ(s₂)`

Reflecting the two-ratio dual cutoff to the positive line and assembling the right edge, the left
edge, and the two shifted residues gives, for `0 < Re s₁, Re s₂ < 1` and `s₁ ≠ s₂`, the exact
identity

  `ζ(s₁)ζ(s₂) = Σ'_{m,n} (m+1)^{-s₁}(n+1)^{-s₂} V((m+1)(n+1)/x)`
  `           + χ(s₁)χ(s₂) Σ'_{m,n} (m+1)^{s₁-1}(n+1)^{s₂-1} W_{s₁,s₂}((m+1)(n+1)x)`
  `           − x^{1-s₁}e^{(1-s₁)²}ζ(s₂+1-s₁)/(1-s₁) − x^{1-s₂}e^{(1-s₂)²}ζ(s₁+1-s₂)/(1-s₂)`,

valid for every scale `x > 0`.  Here `V` is the canonical Gaussian cutoff and `W` the exact dual
weight carrying the product of the two shifted archimedean ratios.  With `s₁ = ½+α+it`,
`s₂ = ½+β−it` this is the degree-two approximate functional equation whose only `t`-oscillation
is the twist `(m/n)^{-it}`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- Positive-line exact two-ratio dual weight after `w ↦ -w`. -/
def productAFEDualWeight (s₁ s₂ : ℂ) (Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio s₁ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEZetaChiShiftRatio s₂ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem productAFEDualCutoff_eq_neg_dualWeight {y : ℝ} (hy : 0 < y) (s₁ s₂ : ℂ) :
    productAFEDualCutoff s₁ s₂ y = -productAFEDualWeight s₁ s₂ y⁻¹ := by
  unfold productAFEDualCutoff productAFEDualWeight
  let f : ℝ → ℂ := fun v =>
    productAFEDualRatioIntegrand s₁ s₂ y (((-1 : ℝ) : ℂ) + (v : ℂ) * I)
  rw [← MeasureTheory.integral_neg_eq_self f volume]
  rw [Complex.real_smul, Complex.real_smul]
  have hpoint : ∀ v : ℝ,
      f (-v) =
        -(smoothAFEZetaChiShiftRatio s₁ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEZetaChiShiftRatio s₂ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand y⁻¹ (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
    intro v
    let w : ℂ := ((1 : ℝ) : ℂ) + (v : ℂ) * I
    have hw : w ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      dsimp only [w] at hre
      norm_num at hre
    have harg : (((-1 : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) = -w := by
      dsimp only [w]
      push_cast
      ring
    rw [show f (-v) = productAFEDualRatioIntegrand s₁ s₂ y (-w) by
          unfold f
          rw [harg]]
    unfold productAFEDualRatioIntegrand
    rw [smoothAFEMellinIntegrand_neg_eq_neg_inv hy w hw]
    ring
  rw [show (fun v : ℝ => f (-v)) =
      (fun v : ℝ => -(smoothAFEZetaChiShiftRatio s₁ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEZetaChiShiftRatio s₂ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand y⁻¹ (((1 : ℝ) : ℂ) + (v : ℂ) * I))) by
        funext v
        exact hpoint v]
  rw [integral_neg]
  ring

/-- The left edge as the positive-line dual weight series. -/
theorem productAFEDualMellinAt_eq_neg_tsum_dualWeight {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) :
    productAFEDualMellinAt s₁ s₂ x =
      -(∑' p : ℕ × ℕ,
        (zetaChi s₁ * zetaChi s₂ * (p.1 + 1 : ℂ) ^ (s₁ - 1) * (p.2 + 1 : ℂ) ^ (s₂ - 1)) *
          productAFEDualWeight s₁ s₂ ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x)) := by
  rw [productAFEDualMellinAt_eq_tsum hx h₁0 h₁1 h₂0 h₂1, ← tsum_neg]
  apply tsum_congr
  intro p
  have hpos : 0 < (p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x := by positivity
  rw [productAFEDualCutoff_eq_neg_dualWeight (one_div_pos.mpr hpos), one_div, inv_inv]
  ring

/-- **The exact Gaussian product approximate functional equation.** -/
theorem riemannZeta_mul_eq_productAFE {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) (hne : s₁ ≠ s₂) :
    riemannZeta s₁ * riemannZeta s₂ =
      (∑' p : ℕ × ℕ, (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂) *
          smoothAFECutoff (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x)) +
      (∑' p : ℕ × ℕ,
          (zetaChi s₁ * zetaChi s₂ * (p.1 + 1 : ℂ) ^ (s₁ - 1) * (p.2 + 1 : ℂ) ^ (s₂ - 1)) *
            productAFEDualWeight s₁ s₂ ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x)) -
      productAFEShiftedResidue s₁ s₂ x - productAFEShiftedResidue s₂ s₁ x := by
  have hs₁ : s₁ ≠ 1 := by
    intro h
    rw [h] at h₁1
    norm_num at h₁1
  have hs₂ : s₂ ≠ 1 := by
    intro h
    rw [h] at h₂1
    norm_num at h₂1
  have hcontour := productAFE_infinite_contour_shift hx hs₁ hs₂ hne h₁0 (by linarith) h₂0
    (by linarith)
  set R : ℂ := ∫ v : ℝ, productAFEIntegrand s₁ s₂ x (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hR
  set L : ℂ := ∫ v : ℝ, productAFEIntegrand s₁ s₂ x (((-1 : ℝ) : ℂ) + (v : ℂ) * I) with hL
  set Z : ℂ := riemannZeta s₁ * riemannZeta s₂ + productAFEShiftedResidue s₁ s₂ x +
    productAFEShiftedResidue s₂ s₁ x with hZdef
  have hcancel : R - L = (2 * Real.pi : ℂ) * Z := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, Z, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hcontour
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hZ : productAFEMellinAt 1 s₁ s₂ x - productAFEDualMellinAt s₁ s₂ x = Z := by
    show (1 / (2 * Real.pi)) • R - (1 / (2 * Real.pi)) • L = Z
    rw [← smul_sub, hcancel, Complex.real_smul]
    push_cast
    field_simp
  have hdirect := productAFEMellinAt_eq_tsum_smoothAFECutoff (s₁ := s₁) (s₂ := s₂) (x := x)
    hx one_pos (by linarith) (by linarith)
  have hdual := productAFEDualMellinAt_eq_neg_tsum_dualWeight hx h₁0 h₁1 h₂0 h₂1
  have hsplit : riemannZeta s₁ * riemannZeta s₂ =
      Z - productAFEShiftedResidue s₁ s₂ x - productAFEShiftedResidue s₂ s₁ x := by
    rw [hZdef]
    ring
  rw [hsplit, ← hZ, hdirect, hdual]
  ring

end RHTower

end
