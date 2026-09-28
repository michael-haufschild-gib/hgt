import GaloisForLFunctions.RHTower.TiltedKernelResolventTest
import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# `Ξ` near an on-line zero

Write `Ξ(z) = riemannPhiTransform(1/2 + iz)`.  Near the real axis:

* `norm_riemannPhiTransform_conj`: `|Ξ(z̄)| = |Ξ(z)|` (functional equation and reality);
* `norm_riemannPhiTransform_le_near_line`: `|Ξ(z)| ≤ K₁ (1 + Re z)³ e^{-π Re z/4}` for
  `|Im z| ≤ 1/2`, `Re z ≥ 2` (right-strip zeta bound and the Gamma ratio on `[Re s/2, 1/2]`);
* `norm_riemannPhiTransform_ge_near_line`: `|Ξ(z)| ≥ c (Re z)²/(1 + Re z) e^{-π Re z/4}
  exp(-(3/2) C log Re z / δ')` when the horizontal path from `1/2 + iz` to `Re s = 2` avoids every
  zero by `δ'` (path bound for `ζ`, the digamma increase from `1/4` to `Re s/2`, and the sharp
  quarter-line Gamma bound).

At an on-line zero `ρ₀ = 1/2 + iγ₀` of multiplicity `m₀`, `δ`-separated in ordinate from all
other zeros, the resolvent-divided tilted kernel `F = D_{γ₀}^{m₀} Φ_θ` has
`|F̂(γ₀)| ≥ m_V` (minimum modulus on the circle of radius `δ/2`) and `F̂` varies by a relative
amount `≤ 4 (log(M_V/m_V) + 1) r/(δ/2 - r)` on `|τ - γ₀| ≤ r` (Borel–Carathéodory for the analytic
logarithm), where `M_V` bounds `F̂` on the disc of radius `3δ/4`
(`divided_tilted_kernel_near_zero`).
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-! ## Symmetry -/

theorem norm_riemannPhiTransform_conj (z : ℂ) :
    ‖riemannPhiTransform (1 / 2 + I * (starRingEnd ℂ) z)‖ =
      ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
  rw [riemannPhiTransform_eq_xi, riemannPhiTransform_eq_xi]
  have e : 1 / 2 + I * (starRingEnd ℂ) z = 1 - (starRingEnd ℂ) (1 / 2 + I * z) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [e, xi_one_sub, xi_conj, Complex.norm_conj]

/-- `|ξ-unit(s)| = |s||s - 1|/2 · |π^{-s/2}| |Γ(s/2)|`. -/
theorem norm_xiUnit_eq (s : ℂ) :
    ‖xiUnit s‖ = ‖s‖ * ‖s - 1‖ / 2 * (‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖) := by
  unfold xiUnit
  rw [Complex.Gammaℝ_def, norm_mul, norm_div, norm_mul, norm_mul]
  norm_num

/-! ## Upper bound near the critical line -/

/-- `K₁ = 10 e² √(2π)`. -/
def xiNearLineUpperConst : ℝ := 10 * Real.exp 2 * Real.sqrt (2 * π)

theorem xiNearLineUpperConst_pos : 0 < xiNearLineUpperConst := by
  unfold xiNearLineUpperConst; have := Real.pi_pos; positivity

theorem norm_riemannPhiTransform_le_near_line_of_im_nonpos {z : ℂ} (hz : -(1 / 2) ≤ z.im)
    (hneg : z.im ≤ 0) (hre : 2 ≤ z.re) :
    ‖riemannPhiTransform (1 / 2 + I * z)‖ ≤
      xiNearLineUpperConst * (1 + z.re) ^ 3 * Real.exp (-(π * z.re / 4)) := by
  set s : ℂ := 1 / 2 + I * z with hs
  have hsre : s.re = 1 / 2 - z.im := by simp [hs]; ring
  have hsim : s.im = z.re := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hsre0 : 0 < s.re := by rw [hsre]; linarith
  rw [riemannPhiTransform_eq_xi, xi_eq_xiUnit_mul_zeta hs0 hs1 hsre0, norm_mul]
  have hζ : ‖riemannZeta s‖ ≤ 5 * (4 + z.re) := by
    have h := norm_riemannZeta_le_right_smoothAFE_strip (σ := s.re) (t := s.im)
      (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hsim, abs_of_pos (by linarith)]; linarith)
    rw [Complex.re_add_im, hsim, abs_of_pos (by linarith)] at h
    exact h
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤
      Real.exp 2 * Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4)) := by
    have hs2 : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp
      · simp [hs]
    have hrat := norm_Gamma_vertical_ratio_le_exp_two (a := s.re / 2) (b := 1 / 2) (y := z.re / 2)
      (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by linarith)
    have hhalf := (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_bounds (z.re / 2)).2
    have hhalf' : ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I)‖ ≤
        Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4)) := by
      have e : (((1 / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I) = 1 / 2 + ((z.re / 2 : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [e]
      refine hhalf.trans (le_of_eq ?_)
      rw [abs_of_pos (by linarith : (0 : ℝ) < z.re / 2)]
      congr 2; ring
    have hB : 0 < ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I)‖ := by
      apply norm_pos_iff.mpr
      apply Complex.Gamma_ne_zero
      intro m h
      have him := congrArg Complex.im h
      simp at him; linarith
    rw [div_le_iff₀ hB] at hrat
    rw [hs2]
    calc ‖Complex.Gamma (((s.re / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I)‖
        ≤ Real.exp 2 * ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I)‖ := hrat
      _ ≤ Real.exp 2 * (Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4))) :=
          mul_le_mul_of_nonneg_left hhalf' (Real.exp_pos _).le
      _ = _ := by ring
  have hss : ‖s‖ * ‖s - 1‖ ≤ (1 + z.re) ^ 2 := by
    have h1 : ‖s‖ ≤ 1 + z.re := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsre, hsim, abs_of_pos (by linarith : (0 : ℝ) < z.re)]
      have : |1 / 2 - z.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have h2 : ‖s - 1‖ ≤ 1 + z.re := by
      refine (Complex.norm_le_abs_re_add_abs_im (s - 1)).trans ?_
      rw [Complex.sub_re, Complex.sub_im, hsre, hsim, Complex.one_re, Complex.one_im, sub_zero,
        abs_of_pos (by linarith : (0 : ℝ) < z.re)]
      have : |1 / 2 - z.im - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    calc ‖s‖ * ‖s - 1‖ ≤ (1 + z.re) * (1 + z.re) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      _ = (1 + z.re) ^ 2 := by ring
  have hU : ‖xiUnit s‖ ≤ (1 + z.re) ^ 2 / 2 *
      (Real.exp 2 * Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4))) := by
    rw [norm_xiUnit_eq]
    have hpi : ‖(π : ℂ) ^ (-s / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      have : (-s / 2).re = -(s.re / 2) := by simp; ring
      rw [this, hsre]; linarith
    calc ‖s‖ * ‖s - 1‖ / 2 * (‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖)
        ≤ (1 + z.re) ^ 2 / 2 * (1 * (Real.exp 2 * Real.sqrt (2 * π) *
            Real.exp (-(π * z.re / 4)))) := by
          gcongr
      _ = _ := by ring
  have hE : 0 ≤ Real.exp 2 * Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4)) := by positivity
  calc ‖xiUnit s‖ * ‖riemannZeta s‖
      ≤ ((1 + z.re) ^ 2 / 2 * (Real.exp 2 * Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4)))) *
          (5 * (4 + z.re)) := mul_le_mul hU hζ (norm_nonneg _) (by positivity)
    _ ≤ ((1 + z.re) ^ 2 / 2 * (Real.exp 2 * Real.sqrt (2 * π) * Real.exp (-(π * z.re / 4)))) *
          (20 * (1 + z.re)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = xiNearLineUpperConst * (1 + z.re) ^ 3 * Real.exp (-(π * z.re / 4)) := by
        unfold xiNearLineUpperConst; ring

/-- **Upper bound for `Ξ` near the critical line.**  For `|Im z| ≤ 1/2` and `Re z ≥ 2`:
`|Ξ(z)| ≤ K₁ (1 + Re z)³ e^{-π Re z/4}`. -/
theorem norm_riemannPhiTransform_le_near_line {z : ℂ} (hz : |z.im| ≤ 1 / 2) (hre : 2 ≤ z.re) :
    ‖riemannPhiTransform (1 / 2 + I * z)‖ ≤
      xiNearLineUpperConst * (1 + z.re) ^ 3 * Real.exp (-(π * z.re / 4)) := by
  rcases le_total z.im 0 with hneg | hpos
  · exact norm_riemannPhiTransform_le_near_line_of_im_nonpos (by linarith [(abs_le.mp hz).1])
      hneg hre
  · have h := norm_riemannPhiTransform_le_near_line_of_im_nonpos (z := (starRingEnd ℂ) z)
      (by simp; linarith [(abs_le.mp hz).2]) (by simp; linarith) (by simpa using hre)
    rwa [norm_riemannPhiTransform_conj, Complex.conj_re] at h

/-! ## Lower bound near the critical line -/

/-- `c_N = π^{-1/2}/6`. -/
def xiNearLineLowerConst : ℝ := Real.pi ^ (-(1 / 2 : ℝ)) / 6

theorem xiNearLineLowerConst_pos : 0 < xiNearLineLowerConst := by
  unfold xiNearLineLowerConst
  have := Real.rpow_pos_of_pos Real.pi_pos (-(1 / 2 : ℝ))
  positivity

/-- Between `1/4` and `a ≤ 1/2`, `|Γ(x + iy)|` increases once `y ≥ 3`. -/
theorem norm_Gamma_quarter_le {a y : ℝ} (ha : 1 / 4 ≤ a) (hy : 3 ≤ y) :
    ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
  have hy0 : 0 < y := by linarith
  have hne : ∀ x : ℝ, Complex.Gamma ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x
    apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hA0 : 0 < ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr (hne _)
  have hD0 : 0 < ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr (hne _)
  have hcont : IntervalIntegrable (fun x : ℝ => (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re)
      volume (1 / 4) a := by
    apply ContinuousOn.intervalIntegrable
    have hφ : ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (uIcc (1 / 4) a) := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (uIcc (1 / 4) a)
        {z : ℂ | 0 < z.im} := by
      intro x _
      simp only [mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
      exact hy0
    exact Complex.continuous_re.comp_continuousOn (digamma_continuousOn_uhp.comp hφ hmaps)
  have hlog3 : 1 < Real.log y := by
    have h3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    exact h3.trans_le (Real.log_le_log (by norm_num) hy)
  have hC : 1 / y ^ 2 + π / (2 * y) ≤ 1 := by
    have h1 : 1 / y ^ 2 ≤ 1 / 9 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : π / (2 * y) ≤ π / 6 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
    have h3 : π / 6 ≤ 2 / 3 := by linarith [Real.pi_lt_four]
    linarith
  have hpos : 0 ≤ ∫ x in (1 / 4 : ℝ)..a, (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re := by
    apply intervalIntegral.integral_nonneg ha
    intro x hx
    have := re_digamma_ge (x := x) (y := y) (by linarith [hx.1]) hy0
    linarith
  rw [ftc_log_norm_Gamma hy0] at hpos
  have := (Real.log_le_log_iff hA0 hD0).mp (by linarith)
  exact this

/-- **Lower bound for `Ξ` near the critical line, right half.**  For `-1/2 ≤ Im z ≤ 0`,
`Re z ≥ 6`, if every point `x + i Re z`, `x ∈ [1/2 - Im z, 2]`, is at distance `≥ δ'` from every
nontrivial zero, then
`|Ξ(z)| ≥ c_N (Re z)²/(1 + Re z) e^{-π Re z/4} exp(-(3/2) C log(Re z)/δ')`. -/
theorem norm_riemannPhiTransform_ge_near_line {z : ℂ} (hz : -(1 / 2) ≤ z.im) (hneg : z.im ≤ 0)
    (hre : 6 ≤ z.re) {δ' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hfar : ∀ x ∈ Icc (1 / 2 - z.im) 2, ∀ ρ ∈ zetaZeroConfig.carrier,
      δ' ≤ ‖(x : ℂ) + (z.re : ℂ) * I - ρ‖) :
    xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) * Real.exp (-(π * z.re / 4)) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ')) ≤
      ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
  set s : ℂ := 1 / 2 + I * z with hs
  have hsre : s.re = 1 / 2 - z.im := by simp [hs]; ring
  have hsim : s.im = z.re := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hsre0 : 0 < s.re := by rw [hsre]; linarith
  have hσ1 : s.re ≤ 1 := by rw [hsre]; linarith
  rw [riemannPhiTransform_eq_xi, xi_eq_xiUnit_mul_zeta hs0 hs1 hsre0, norm_mul]
  have hC := logDerivZetaConstant_nonneg
  have hlog0 : 0 ≤ Real.log z.re := Real.log_nonneg (by linarith)
  -- the zeta factor
  have hsEq : ((s.re : ℝ) : ℂ) + (z.re : ℂ) * I = s := by
    rw [← hsim]; exact Complex.re_add_im s
  have hζ : (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ')) ≤
      ‖riemannZeta s‖ := by
    have hfar' : ∀ x ∈ Icc s.re 2, ∀ ρ ∈ zetaZeroConfig.carrier,
        δ' ≤ ‖(x : ℂ) + (z.re : ℂ) * I - ρ‖ := by
      intro x hx ρ hρ; rw [hsre] at hx; exact hfar x hx ρ hρ
    have h := log_norm_zeta_ge_horizontal (σ := s.re) (τ := z.re) (by rw [hsre]; linarith)
      (by linarith) (by linarith) hδ' hδ'1 hfar'
    rw [hsEq] at h
    have hpos : 0 < ‖riemannZeta s‖ := by
      rcases eq_or_ne (riemannZeta s) 0 with h0 | h0
      · exfalso
        rcases lt_or_eq_of_le hσ1 with hlt | heq
        · have hmem : s ∈ zetaZeroConfig.carrier := ⟨h0, hsre0, hlt⟩
          have := hfar s.re ⟨by rw [hsre], by linarith⟩ s hmem
          rw [hsEq, sub_self, norm_zero] at this
          linarith
        · exact riemannZeta_ne_zero_of_one_le_re (by rw [heq]) h0
      · exact norm_pos_iff.mpr h0
    have := Real.exp_le_exp.mpr h
    rw [Real.exp_log hpos, Real.exp_sub, Real.exp_log (by norm_num)] at this
    have hk : logDerivZetaConstant * Real.log z.re / δ' * (2 - s.re) ≤
        3 / 2 * logDerivZetaConstant * Real.log z.re / δ' := by
      have h0 : 0 ≤ logDerivZetaConstant * Real.log z.re / δ' := by positivity
      have : 2 - s.re ≤ 3 / 2 := by rw [hsre]; linarith
      calc logDerivZetaConstant * Real.log z.re / δ' * (2 - s.re)
          ≤ logDerivZetaConstant * Real.log z.re / δ' * (3 / 2) :=
            mul_le_mul_of_nonneg_left this h0
        _ = 3 / 2 * logDerivZetaConstant * Real.log z.re / δ' := by ring
    calc (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ'))
        ≤ (1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log z.re / δ' * (2 - s.re))) := by
          gcongr
      _ = (1 / 3) / Real.exp (logDerivZetaConstant * Real.log z.re / δ' * (2 - s.re)) := by
          rw [Real.exp_neg]; ring
      _ ≤ ‖riemannZeta s‖ := this
  -- the archimedean factor
  have hU : 3 * xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) * Real.exp (-(π * z.re / 4)) ≤
      ‖xiUnit s‖ := by
    rw [norm_xiUnit_eq]
    have hss : z.re ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
      have h1 : z.re ≤ ‖s‖ := by
        have := Complex.abs_im_le_norm s; rw [hsim, abs_of_pos (by linarith)] at this; exact this
      have h2 : z.re ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        rw [Complex.sub_im, Complex.one_im, sub_zero, hsim, abs_of_pos (by linarith)] at this
        exact this
      calc z.re ^ 2 = z.re * z.re := by ring
        _ ≤ ‖s‖ * ‖s - 1‖ := mul_le_mul h1 h2 (by linarith) (norm_nonneg _)
    have hpi : Real.pi ^ (-(1 / 2 : ℝ)) ≤ ‖(π : ℂ) ^ (-s / 2)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      have : (-s / 2).re = -(s.re / 2) := by simp; ring
      rw [this]; linarith
    have hs2 : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp
      · simp [hs]
    have hΓ1 := norm_Gamma_quarter_le (a := s.re / 2) (y := z.re / 2) (by rw [hsre]; linarith)
      (by linarith)
    have hΓ2 := norm_Gamma_quarter_line_sharp (s := z.re) (by linarith)
    have hΓ : Real.exp (-(π * z.re / 4)) / (1 + z.re) ≤ ‖Complex.Gamma (s / 2)‖ := by
      rw [hs2]; exact hΓ2.trans hΓ1
    have hpq : 0 < Real.pi ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
    unfold xiNearLineLowerConst
    calc 3 * (Real.pi ^ (-(1 / 2 : ℝ)) / 6) * (z.re ^ 2 / (1 + z.re)) * Real.exp (-(π * z.re / 4))
        = z.re ^ 2 / 2 * (Real.pi ^ (-(1 / 2 : ℝ)) * (Real.exp (-(π * z.re / 4)) / (1 + z.re))) := by
          ring
      _ ≤ ‖s‖ * ‖s - 1‖ / 2 * (‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖) := by
          apply mul_le_mul (by linarith) (mul_le_mul hpi hΓ (by positivity) (norm_nonneg _))
            (by positivity) (by positivity)
  have hz0 : 0 ≤ (1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ')) := by
    positivity
  calc xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) * Real.exp (-(π * z.re / 4)) *
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ'))
      = (3 * xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) * Real.exp (-(π * z.re / 4))) *
          ((1 / 3) * Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / δ'))) := by ring
    _ ≤ ‖xiUnit s‖ * ‖riemannZeta s‖ := mul_le_mul hU hζ hz0 (norm_nonneg _)

/-! ## The resolvent-divided tilted kernel at an on-line zero -/

/-- The floor `m_V` of the divided kernel at the zero. -/
def dividedKernelFloor (θ γ₀ δ : ℝ) : ℝ :=
  Real.exp (θ * (γ₀ - 1 / 2)) * xiNearLineLowerConst * ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) *
    Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
    Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ))

/-- The ceiling `M_V` of the divided kernel on the disc of radius `3δ/4`. -/
def dividedKernelCeil (θ γ₀ δ : ℝ) (m : ℕ) : ℝ :=
  Real.exp (θ * (γ₀ + 1)) * xiNearLineUpperConst * (γ₀ + 2) ^ 3 *
    Real.exp (-(π * (γ₀ - 1) / 4)) * (4 / (3 * δ)) ^ m

theorem dividedKernelFloor_pos {θ γ₀ δ : ℝ} (hγ : 7 ≤ γ₀) : 0 < dividedKernelFloor θ γ₀ δ := by
  unfold dividedKernelFloor
  have := xiNearLineLowerConst_pos
  have : 0 < γ₀ - 1 / 2 := by linarith
  have : 0 < γ₀ + 3 / 2 := by linarith
  positivity

/-- Near an on-line zero, `Ξ` vanishes only at the zero itself. -/
theorem riemannPhiTransform_ne_zero_near_zero {ρ₀ : ℂ} (hline : ρ₀.re = 1 / 2) {δ : ℝ}
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → δ ≤ |ρ.im - ρ₀.im|) {z : ℂ}
    (hz : ‖z - (ρ₀.im : ℂ)‖ < δ) (hne : z ≠ (ρ₀.im : ℂ)) (him : |z.im| < 1 / 2) :
    riemannPhiTransform (1 / 2 + I * z) ≠ 0 := by
  intro h0
  set s : ℂ := 1 / 2 + I * z with hs
  have hsre : s.re = 1 / 2 - z.im := by simp [hs]; ring
  have hsim : s.im = z.re := by simp [hs]
  have hsre0 : 0 < s.re := by rw [hsre]; linarith [(abs_lt.mp him).2]
  have hsre1 : s.re < 1 := by rw [hsre]; linarith [(abs_lt.mp him).1]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre0; simp at hsre0
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre1; simp at hsre1
  rw [riemannPhiTransform_eq_xi, xi_eq_xiUnit_mul_zeta hs0 hs1 hsre0] at h0
  have hζ : riemannZeta s = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (xiUnit_ne_zero hs0 hs1 hsre0)
    · exact h
  have hmem : s ∈ zetaZeroConfig.carrier := ⟨hζ, hsre0, hsre1⟩
  have hsρ : s ≠ ρ₀ := by
    intro h
    apply hne
    apply Complex.ext
    · have := congrArg Complex.im h; rw [hsim] at this; simp [this]
    · have := congrArg Complex.re h; rw [hsre, hline] at this; simp; linarith
  have h1 := hsep s hmem hsρ
  rw [hsim] at h1
  have h2 : |z.re - ρ₀.im| ≤ ‖z - (ρ₀.im : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z - (ρ₀.im : ℂ)); simpa using this
  linarith

/-- The circle bound for the lower estimate: the horizontal path from `1/2 + iw` avoids every zero
by `δ/2`, for `w` on the lower half of the circle of radius `δ/2` about `γ₀`. -/
theorem path_far_of_lower_circle {ρ₀ : ℂ} (hline : ρ₀.re = 1 / 2) {δ : ℝ}
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → δ ≤ |ρ.im - ρ₀.im|) {w : ℂ}
    (hw : ‖w - (ρ₀.im : ℂ)‖ = δ / 2) (hneg : w.im ≤ 0) :
    ∀ x ∈ Icc (1 / 2 - w.im) 2, ∀ ρ ∈ zetaZeroConfig.carrier,
      δ / 2 ≤ ‖(x : ℂ) + (w.re : ℂ) * I - ρ‖ := by
  intro x hx ρ hρ
  by_cases hρρ : ρ = ρ₀
  · subst hρρ
    have hsq : ‖w - (ρ.im : ℂ)‖ ^ 2 ≤ ‖(x : ℂ) + (w.re : ℂ) * I - ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, hline]
      have h1 : -w.im ≤ x - 1 / 2 := by linarith [hx.1]
      have h2 : 0 ≤ -w.im := by linarith
      nlinarith
    rw [hw] at hsq
    have h0 : 0 ≤ δ / 2 := by rw [← hw]; exact norm_nonneg _
    exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).mp hsq
  · have h1 := hsep ρ hρ hρρ
    have h2 : |w.re - ρ₀.im| ≤ δ / 2 := by
      have := Complex.abs_re_le_norm (w - (ρ₀.im : ℂ)); rw [hw] at this; simpa using this
    have h3 : |w.re - ρ.im| ≤ ‖(x : ℂ) + (w.re : ℂ) * I - ρ‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + (w.re : ℂ) * I - ρ); simpa using this
    have h4 : |ρ.im - ρ₀.im| ≤ |w.re - ρ.im| + |w.re - ρ₀.im| := by
      calc |ρ.im - ρ₀.im| = |(w.re - ρ₀.im) - (w.re - ρ.im)| := by ring_nf
        _ ≤ |w.re - ρ₀.im| + |w.re - ρ.im| := abs_sub _ _
        _ = |w.re - ρ.im| + |w.re - ρ₀.im| := by ring
    linarith

/-- **The resolvent-divided tilted kernel at an on-line zero.**  For `ρ₀ = 1/2 + iγ₀` of
multiplicity `m₀`, `γ₀ ≥ 7`, `δ`-separated in ordinate from all other zeros (`0 < δ ≤ 1/2`), the
kernel `F = D_{γ₀}^{m₀} Φ_θ` decays super-exponentially, `(z - γ₀)^{m₀} F̂ = Φ̂_θ`,
`m_V ≤ |F̂(γ₀)| ≤ M_V`, and on `|τ - γ₀| ≤ r < δ/2` (with `B = 2(log(M_V/m_V)+1) r/(δ/2 - r) ≤ 1`)
`|F̂(τ) - F̂(γ₀)| ≤ 2B |F̂(γ₀)|`. -/
theorem divided_tilted_kernel_near_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hline : ρ₀.re = 1 / 2) (hγ : 7 ≤ ρ₀.im) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → δ ≤ |ρ.im - ρ₀.im|) :
    SuperExpDecay (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) ∧
    (∀ z : ℂ, (z - (ρ₀.im : ℂ)) ^ (zetaZeroConfig.mult ρ₀) *
        paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) z =
          paperFT (tiltedPhi θ) z) ∧
    dividedKernelFloor θ ρ₀.im δ ≤
      ‖paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) (ρ₀.im : ℂ)‖ ∧
    ‖paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) (ρ₀.im : ℂ)‖ ≤
      dividedKernelCeil θ ρ₀.im δ (zetaZeroConfig.mult ρ₀) ∧
    ∀ r : ℝ, 0 ≤ r → r < δ / 2 →
      2 * (Real.log (dividedKernelCeil θ ρ₀.im δ (zetaZeroConfig.mult ρ₀) /
          dividedKernelFloor θ ρ₀.im δ) + 1) * r / (δ / 2 - r) ≤ 1 →
      ∀ τ : ℝ, |τ - ρ₀.im| ≤ r →
        ‖paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) (τ : ℂ) -
            paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ))
              (ρ₀.im : ℂ)‖ ≤
          2 * (2 * (Real.log (dividedKernelCeil θ ρ₀.im δ (zetaZeroConfig.mult ρ₀) /
            dividedKernelFloor θ ρ₀.im δ) + 1) * r / (δ / 2 - r)) *
          ‖paperFT (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ))
            (ρ₀.im : ℂ)‖ := by
  obtain ⟨v, hv, hv0, hloc⟩ := exists_tiltedPhi_local_factor hθ0 hθ hρ₀ hline
  set m := zetaZeroConfig.mult ρ₀ with hm
  set γ₀ : ℝ := ρ₀.im with hγ₀
  set F := iterResolvent (γ₀ : ℂ) m (tiltedPhi θ) with hFdef
  have hdecay := superExpDecay_tiltedRiemannKernel hθ0 hθ
  have hγim : |((γ₀ : ℂ)).im| ≤ 1 / 2 := by simp
  obtain ⟨hF, hFloc, hprod⟩ := iterResolvent_spec hdecay hγim hv.continuousAt hloc m le_rfl
  rw [Nat.sub_self] at hFloc
  have hFγ : paperFT F (γ₀ : ℂ) = v (γ₀ : ℂ) := by
    have := hFloc.eq_of_nhds; simpa using this
  -- the entire function `Ψ(z) = e^{zθ} Ξ(z)`
  set Ψ : ℂ → ℂ := fun z => cexp (z * θ) * riemannPhiTransform (1 / 2 + I * z) with hΨ
  have hΨdiff : Differentiable ℂ Ψ := by
    have h1 : Differentiable ℂ (fun z : ℂ => riemannPhiTransform (1 / 2 + I * z)) := by
      have e : (fun z : ℂ => riemannPhiTransform (1 / 2 + I * z)) =
          fun z : ℂ => xi (1 / 2 + I * z) := funext fun z => riemannPhiTransform_eq_xi _
      rw [e]
      exact xi_differentiable.comp (by fun_prop)
    exact (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (z * θ)).mul h1
  have hΦΨ : ∀ z : ℂ, |z.im| ≤ 1 / 2 → paperFT (tiltedPhi θ) z = Ψ z :=
    fun z hz => paperFT_tiltedPhi hθ0 hθ hz
  -- the divided function
  set V : ℂ → ℂ := fun z => if z = (γ₀ : ℂ) then v (γ₀ : ℂ) else Ψ z / (z - (γ₀ : ℂ)) ^ m with hV
  have hFV : ∀ z : ℂ, |z.im| ≤ 1 / 2 → paperFT F z = V z := by
    intro z hz
    by_cases hzγ : z = (γ₀ : ℂ)
    · rw [hzγ, hFγ]; simp [hV]
    · simp only [hV, if_neg hzγ]
      have hpow : (z - (γ₀ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzγ)
      rw [eq_div_iff hpow, mul_comm, hprod z, hΦΨ z hz]
  have him_ev : ∀ᶠ z in 𝓝 (γ₀ : ℂ), |z.im| ≤ 1 / 2 := by
    have hc : Continuous fun z : ℂ => |z.im| := by fun_prop
    have : |((γ₀ : ℂ)).im| < 1 / 2 := by simp
    exact (hc.tendsto _).eventually (Iio_mem_nhds this) |>.mono fun z hz => le_of_lt hz
  have hVloc : V =ᶠ[𝓝 (γ₀ : ℂ)] v := by
    filter_upwards [hloc, him_ev] with z h1 h2
    by_cases hzγ : z = (γ₀ : ℂ)
    · simp [hV, hzγ]
    · simp only [hV, if_neg hzγ]
      have hpow : (z - (γ₀ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzγ)
      rw [div_eq_iff hpow, ← hΦΨ z h2, h1]; ring
  have hball_im : ∀ z : ℂ, ‖z - (γ₀ : ℂ)‖ ≤ 3 * δ / 4 → |z.im| < 1 / 2 := by
    intro z hz
    have := Complex.abs_im_le_norm (z - (γ₀ : ℂ))
    simp at this
    linarith
  have hVdiff : ∀ z : ℂ, ‖z - (γ₀ : ℂ)‖ ≤ 3 * δ / 4 → DifferentiableAt ℂ V z := by
    intro z hz
    by_cases hzγ : z = (γ₀ : ℂ)
    · rw [hzγ]; exact hv.differentiableAt.congr_of_eventuallyEq hVloc
    · have hev : V =ᶠ[𝓝 z] fun w => Ψ w / (w - (γ₀ : ℂ)) ^ m := by
        filter_upwards [eventually_ne_nhds hzγ] with w hw
        simp only [hV, if_neg hw]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact (hΨdiff z).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hzγ))
  have hVne : ∀ z : ℂ, ‖z - (γ₀ : ℂ)‖ ≤ 3 * δ / 4 → V z ≠ 0 := by
    intro z hz
    by_cases hzγ : z = (γ₀ : ℂ)
    · simp only [hV, if_pos hzγ]; exact hv0
    · simp only [hV, if_neg hzγ]
      refine div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) ?_)
        (pow_ne_zero _ (sub_ne_zero.mpr hzγ))
      exact riemannPhiTransform_ne_zero_near_zero hline hsep (by linarith) hzγ
        (hball_im z hz)
  have hVnorm : ∀ z : ℂ, z ≠ (γ₀ : ℂ) →
      ‖V z‖ = Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ /
        ‖z - (γ₀ : ℂ)‖ ^ m := by
    intro z hzγ
    simp only [hV, if_neg hzγ, norm_div, norm_mul, norm_pow, hΨ]
    rw [Complex.norm_exp]
    congr 3
    simp [Complex.mul_re]; ring
  -- the ceiling on the disc of radius `3δ/4`
  set M := dividedKernelCeil θ γ₀ δ m with hMdef
  have hceil_circle : ∀ z ∈ frontier (ball (γ₀ : ℂ) (3 * δ / 4)), ‖V z‖ ≤ M := by
    intro z hz
    rw [frontier_ball _ (by positivity : 3 * δ / 4 ≠ 0)] at hz
    have hzn : ‖z - (γ₀ : ℂ)‖ = 3 * δ / 4 := by simpa [dist_eq_norm] using hz
    have hzγ : z ≠ (γ₀ : ℂ) := by
      intro h; rw [h, sub_self, norm_zero] at hzn; linarith
    rw [hVnorm z hzγ, hzn]
    have hre : |z.re - γ₀| ≤ 3 * δ / 4 := by
      have := Complex.abs_re_le_norm (z - (γ₀ : ℂ)); rw [hzn] at this; simpa using this
    have hre1 := (abs_le.mp hre).1
    have hre2 := (abs_le.mp hre).2
    have hup := norm_riemannPhiTransform_le_near_line (z := z) (hball_im z hzn.le).le
      (by linarith)
    have hK := xiNearLineUpperConst_pos
    have h3 : (1 + z.re) ^ 3 ≤ (γ₀ + 2) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have he1 : Real.exp (θ * z.re) ≤ Real.exp (θ * (γ₀ + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hθ0)
    have he2 : Real.exp (-(π * z.re / 4)) ≤ Real.exp (-(π * (γ₀ - 1) / 4)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hden : (3 * δ / 4) ^ m = ((4 / (3 * δ)) ^ m)⁻¹ := by
      rw [← inv_pow]; congr 1; field_simp
    rw [div_eq_mul_inv, hden, inv_inv, hMdef]
    unfold dividedKernelCeil
    calc Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ * (4 / (3 * δ)) ^ m
        ≤ Real.exp (θ * (γ₀ + 1)) * (xiNearLineUpperConst * (γ₀ + 2) ^ 3 *
            Real.exp (-(π * (γ₀ - 1) / 4))) * (4 / (3 * δ)) ^ m := by
          gcongr
          calc ‖riemannPhiTransform (1 / 2 + I * z)‖
              ≤ xiNearLineUpperConst * (1 + z.re) ^ 3 * Real.exp (-(π * z.re / 4)) := hup
            _ ≤ xiNearLineUpperConst * (γ₀ + 2) ^ 3 * Real.exp (-(π * (γ₀ - 1) / 4)) := by
                gcongr
      _ = _ := by ring
  have hdcc3 : DiffContOnCl ℂ V (ball (γ₀ : ℂ) (3 * δ / 4)) := by
    have hdo : DifferentiableOn ℂ V (closedBall (γ₀ : ℂ) (3 * δ / 4)) := fun z hz =>
      (hVdiff z (by simpa [dist_eq_norm] using hz)).differentiableWithinAt
    exact ⟨hdo.mono ball_subset_closedBall, hdo.continuousOn.mono closure_ball_subset_closedBall⟩
  have hceil : ∀ z ∈ closedBall (γ₀ : ℂ) (3 * δ / 4), ‖V z‖ ≤ M := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdcc3 hceil_circle ?_
    rwa [closure_ball _ (by positivity : 3 * δ / 4 ≠ 0)]
  -- the floor at the zero
  set mV := dividedKernelFloor θ γ₀ δ with hmVdef
  have hmV0 : 0 < mV := dividedKernelFloor_pos hγ
  have hfloor_circle : ∀ z ∈ frontier (ball (γ₀ : ℂ) (δ / 2)), ‖(V z)⁻¹‖ ≤ mV⁻¹ := by
    intro z hz
    rw [frontier_ball _ (by positivity : δ / 2 ≠ 0)] at hz
    have hzn : ‖z - (γ₀ : ℂ)‖ = δ / 2 := by simpa [dist_eq_norm] using hz
    have hzγ : z ≠ (γ₀ : ℂ) := by
      intro h; rw [h, sub_self, norm_zero] at hzn; linarith
    set w : ℂ := if z.im ≤ 0 then z else (starRingEnd ℂ) z with hw
    have hwre : w.re = z.re := by rw [hw]; split_ifs <;> simp
    have hwim : w.im ≤ 0 := by
      rw [hw]; split_ifs with h
      · exact h
      · simp; linarith
    have hwn : ‖w - (γ₀ : ℂ)‖ = δ / 2 := by
      rw [hw]; split_ifs
      · exact hzn
      · rw [← hzn]
        have : (starRingEnd ℂ) z - (γ₀ : ℂ) = (starRingEnd ℂ) (z - (γ₀ : ℂ)) := by simp
        rw [this, Complex.norm_conj]
    have hΞw : ‖riemannPhiTransform (1 / 2 + I * w)‖ = ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
      rw [hw]; split_ifs
      · rfl
      · exact norm_riemannPhiTransform_conj z
    have hwim2 : -(1 / 2) ≤ w.im := by
      have := Complex.abs_im_le_norm (w - (γ₀ : ℂ)); rw [hwn] at this; simp at this
      linarith [(abs_le.mp this).1]
    have hwre2 : |w.re - γ₀| ≤ δ / 2 := by
      have := Complex.abs_re_le_norm (w - (γ₀ : ℂ)); rw [hwn] at this; simpa using this
    have hlow := norm_riemannPhiTransform_ge_near_line hwim2 hwim
      (by linarith [(abs_le.mp hwre2).1]) (by positivity) (by linarith)
      (path_far_of_lower_circle hline hsep hwn hwim)
    rw [hΞw, hwre] at hlow
    rw [hwre] at hwre2
    have hre1 := (abs_le.mp hwre2).1
    have hre2 := (abs_le.mp hwre2).2
    have hC := logDerivZetaConstant_nonneg
    have hc := xiNearLineLowerConst_pos
    -- compare with the floor
    have hfrac : (γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2) ≤ z.re ^ 2 / (1 + z.re) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have hsq : (γ₀ - 1 / 2) ^ 2 ≤ z.re ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      exact mul_le_mul hsq (by linarith) (by linarith) (by positivity)
    have he1 : Real.exp (-(π * (γ₀ + 1 / 2) / 4)) ≤ Real.exp (-(π * z.re / 4)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hlog : Real.log z.re ≤ Real.log (γ₀ + 1) := Real.log_le_log (by linarith) (by linarith)
    have he2 : Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) ≤
        Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log z.re / (δ / 2))) := by
      apply Real.exp_le_exp.mpr
      rw [show 3 / 2 * logDerivZetaConstant * Real.log z.re / (δ / 2) =
        3 * logDerivZetaConstant * Real.log z.re / δ by field_simp]
      have : 3 * logDerivZetaConstant * Real.log z.re / δ ≤
          3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith
    have heθ : Real.exp (θ * (γ₀ - 1 / 2)) ≤ Real.exp (θ * z.re) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hθ0)
    have hXi : xiNearLineLowerConst * ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) *
        Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
        Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) ≤
        ‖riemannPhiTransform (1 / 2 + I * z)‖ := by
      refine le_trans ?_ hlow
      have hB2 : 0 ≤ xiNearLineLowerConst * (z.re ^ 2 / (1 + z.re)) :=
        mul_nonneg hc.le (div_nonneg (sq_nonneg _) (by linarith))
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hfrac hc.le) he1
        (Real.exp_pos _).le hB2) he2 (Real.exp_pos _).le
        (mul_nonneg hB2 (Real.exp_pos _).le)
    have hVlow : mV ≤ ‖V z‖ := by
      rw [hVnorm z hzγ, hzn]
      have hpow : (δ / 2) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      have hpos : 0 < (δ / 2) ^ m := by positivity
      rw [le_div_iff₀ hpos]
      calc mV * (δ / 2) ^ m ≤ mV * 1 := mul_le_mul_of_nonneg_left hpow hmV0.le
        _ = Real.exp (θ * (γ₀ - 1 / 2)) * (xiNearLineLowerConst *
              ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
              Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ))) := by
            rw [hmVdef]; unfold dividedKernelFloor; ring
        _ ≤ Real.exp (θ * z.re) * ‖riemannPhiTransform (1 / 2 + I * z)‖ :=
            mul_le_mul heθ hXi (by positivity) (Real.exp_pos _).le
    rw [norm_inv]
    exact inv_anti₀ hmV0 hVlow
  have hdcc2 : DiffContOnCl ℂ (fun z => (V z)⁻¹) (ball (γ₀ : ℂ) (δ / 2)) := by
    have hdo : DifferentiableOn ℂ (fun z => (V z)⁻¹) (closedBall (γ₀ : ℂ) (δ / 2)) := by
      intro z hz
      have hz' : ‖z - (γ₀ : ℂ)‖ ≤ 3 * δ / 4 := by
        have : ‖z - (γ₀ : ℂ)‖ ≤ δ / 2 := by simpa [dist_eq_norm] using hz
        linarith
      exact ((hVdiff z hz').inv (hVne z hz')).differentiableWithinAt
    exact ⟨hdo.mono ball_subset_closedBall, hdo.continuousOn.mono closure_ball_subset_closedBall⟩
  have hfloor : mV ≤ ‖V (γ₀ : ℂ)‖ := by
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdcc2
      hfloor_circle (subset_closure (mem_ball_self (by positivity : (0 : ℝ) < δ / 2)))
    rw [norm_inv] at hmax
    have hVpos : 0 < ‖V (γ₀ : ℂ)‖ := norm_pos_iff.mpr (hVne _ (by simp; positivity))
    rwa [inv_le_inv₀ hVpos hmV0] at hmax
  have hFγV : paperFT F (γ₀ : ℂ) = V (γ₀ : ℂ) := hFV _ (by simp)
  have hceilγ : ‖V (γ₀ : ℂ)‖ ≤ M := hceil _ (by rw [mem_closedBall, dist_self]; positivity)
  refine ⟨hF, hprod, by rw [hFγV]; exact hfloor, by rw [hFγV]; exact hceilγ,
    fun r hr0 hrR hB τ hτ => ?_⟩
  -- Borel–Carathéodory
  have hdiffB : DifferentiableOn ℂ V (ball (γ₀ : ℂ) (δ / 2)) := fun z hz => by
    have : ‖z - (γ₀ : ℂ)‖ < δ / 2 := by simpa [dist_eq_norm] using hz
    exact (hVdiff z (by linarith)).differentiableWithinAt
  have hneB : ∀ z ∈ ball (γ₀ : ℂ) (δ / 2), V z ≠ 0 := fun z hz => by
    have : ‖z - (γ₀ : ℂ)‖ < δ / 2 := by simpa [dist_eq_norm] using hz
    exact hVne z (by linarith)
  have hMB : ∀ z ∈ ball (γ₀ : ℂ) (δ / 2), ‖V z‖ ≤ M := fun z hz => by
    have : ‖z - (γ₀ : ℂ)‖ < δ / 2 := by simpa [dist_eq_norm] using hz
    exact hceil z (by rw [mem_closedBall, dist_eq_norm]; linarith)
  obtain ⟨g, -, -, hgeq, hgbd⟩ := GaloisForLFunctions.HTGeometry.exists_bound_log_on_ball hr0 hrR
    hdiffB hneB hMB hmV0 hfloor
  have hτn : ‖(τ : ℂ) - (γ₀ : ℂ)‖ ≤ r := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hτ
  have hτball : (τ : ℂ) ∈ ball (γ₀ : ℂ) (δ / 2) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hg := hgbd (τ : ℂ) hτn
  have hFτ : paperFT F (τ : ℂ) = V (τ : ℂ) := hFV _ (by simp)
  rw [hFτ, hFγV, hgeq _ hτball]
  have hsub : V (γ₀ : ℂ) * cexp (g (τ : ℂ)) - V (γ₀ : ℂ) = V (γ₀ : ℂ) * (cexp (g (τ : ℂ)) - 1) := by
    ring
  rw [hsub, norm_mul]
  have hexp := Complex.norm_exp_sub_one_le (x := g (τ : ℂ)) (hg.trans hB)
  calc ‖V (γ₀ : ℂ)‖ * ‖cexp (g (τ : ℂ)) - 1‖ ≤ ‖V (γ₀ : ℂ)‖ * (2 * ‖g (τ : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ ≤ ‖V (γ₀ : ℂ)‖ * (2 * (2 * (Real.log (M / mV) + 1) * r / (δ / 2 - r))) := by
        gcongr
    _ = _ := by ring

end

end RHTower
