import GaloisForLFunctions.RHTower.ZetaSelbergRightEdge
import GaloisForLFunctions.RHTower.ZetaResidueUnitPoleWeightedRectangle
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Selberg's explicit formula for `ζ'/ζ` at a point of the critical strip

Let `x > 1`, `ℓ = log x`, `1 < c ≤ 2`, and `s₀ = σ₀ + it₀` with `σ_L < σ₀ < c`, `0 < T₁ < t₀ < T₂`,
`ζ(s₀) ≠ 0`. Suppose the residue unit `G(s) = (s − 1)ζ(s)` has no zero on the boundary of the
rectangle `[σ_L, c] × [T₁, T₂]`, with `‖G'/G‖ ≤ B_H` on its horizontal edges and `‖G'/G‖ ≤ B_L` on its
left edge. Then

`‖ζ'/ζ(s₀) + Σ_n Λ(n) W_x(n) n^{−s₀} + Σ_ρ m_ρ K_x(ρ − s₀)‖ ≤ E`,

the zero sum over the zeros of `G` in the rectangle, `K_x(w) = (x^{2w} − x^w)/(ℓ w²)`, and
`E = (2(c − σ_L) B_H A/(ℓH²) + (16π/(c−1)²) A/(ℓH) + πA/(aℓT₁) + 2π B_L x^{σ_L−σ₀}/(ℓ(σ₀−σ_L)))/(2π)
  + 1/T₁`, `a = c − σ₀`, `A = x^{2a} + x^a`, `H = min(t₀ − T₁, T₂ − t₀)`
(`norm_logDeriv_zeta_add_selberg_le`).

The proof is the weighted argument principle with the interior pole of `K_x(z − s₀)` at `s₀`,
whose residue is `ζ'/ζ(s₀)` (Selberg's kernel has `φ_x(0) = 1`), the Perron evaluation of the
right edge, and edgewise bounds.
-/

noncomputable section

open Complex MeasureTheory Set Filter ArithmeticFunction

namespace RHTower

open Sieve

/-- The smoothed von Mangoldt polynomial `Σ_n Λ(n) W_x(n) n^{−s}`. -/
def selbergVonMangoldtPoly (x : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s) * (selbergWeight x n : ℂ)

/-- The exponential factor `x^{2u} + x^u ≤ x^{2a} + x^a` for `u ≤ a`. -/
theorem selberg_exp_factor_le {x u a : ℝ} (hx : 1 < x) (hua : u ≤ a) :
    Real.exp (2 * u * Real.log x) + Real.exp (u * Real.log x) ≤
      Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.exp (2 * u * Real.log x) ≤ Real.exp (2 * a * Real.log x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (u * Real.log x) ≤ Real.exp (a * Real.log x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- Kernel bound on a point `z` with `Re(z − s₀) ≤ a` and `|Im(z − s₀)| ≥ h`. -/
theorem norm_selbergKernel_le_of_im {x a h : ℝ} (hx : 1 < x) (hh : 0 < h) {w : ℂ}
    (hwre : w.re ≤ a) (hwim : h ≤ |w.im|) :
    ‖selbergKernel x w‖ ≤
      (Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x)) / (Real.log x * h ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  refine (norm_selbergKernel_le hx w).trans ?_
  have hw2 : h ^ 2 ≤ ‖w‖ ^ 2 := by
    have := Complex.abs_im_le_norm w
    exact pow_le_pow_left₀ hh.le (hwim.trans this) 2
  have hA := selberg_exp_factor_le hx hwre
  calc (Real.exp (2 * w.re * Real.log x) + Real.exp (w.re * Real.log x)) /
        (Real.log x * ‖w‖ ^ 2)
      ≤ (Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x)) /
          (Real.log x * ‖w‖ ^ 2) := div_le_div_of_nonneg_right hA (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hw2 hl.le)

/-- Kernel bound along a vertical line `Re(z − s₀) = u`: `‖K_x(w)‖ ≤ (x^{2u} + x^u)/(ℓ(u² + (Im w)²))`. -/
theorem norm_selbergKernel_le_line {x : ℝ} (hx : 1 < x) (w : ℂ) :
    ‖selbergKernel x w‖ ≤
      (Real.exp (2 * w.re * Real.log x) + Real.exp (w.re * Real.log x)) /
        (Real.log x * (w.re ^ 2 + w.im ^ 2)) := by
  refine (norm_selbergKernel_le hx w).trans (le_of_eq ?_)
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring_nf

/-- The algebra of the contour identity: from the rectangle identity and the full-line right
edge, the explicit-formula remainder is bounded by the edge integrals. -/
theorem selberg_contour_algebra {S Lz D Bt Tp Rw P Lf Δ s₀ : ℂ}
    (hrect : 2 * Real.pi * I * (S + (Lz + (s₀ - 1)⁻¹)) = (Bt - Tp) + I * (Rw + P) - I * Lf)
    (hR : Rw = -(2 * Real.pi) * D - Δ) :
    ‖Lz + D + S‖ ≤ (‖Bt‖ + ‖Tp‖ + ‖Δ‖ + ‖P‖ + ‖Lf‖) / (2 * Real.pi) + ‖(s₀ - 1)⁻¹‖ := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπc : (2 * Real.pi : ℂ) * I ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast hπ.ne'
  have hkey : Lz + D + S = (Bt - Tp - I * Δ + I * P - I * Lf) / (2 * Real.pi * I) - (s₀ - 1)⁻¹ := by
    rw [eq_sub_iff_add_eq, eq_div_iff hπc]
    rw [hR] at hrect
    linear_combination hrect
  rw [hkey]
  have hnI : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  calc ‖(Bt - Tp - I * Δ + I * P - I * Lf) / (2 * Real.pi * I) - (s₀ - 1)⁻¹‖
      ≤ ‖(Bt - Tp - I * Δ + I * P - I * Lf) / (2 * Real.pi * I)‖ + ‖(s₀ - 1)⁻¹‖ :=
        norm_sub_le _ _
    _ ≤ (‖Bt‖ + ‖Tp‖ + ‖Δ‖ + ‖P‖ + ‖Lf‖) / (2 * Real.pi) + ‖(s₀ - 1)⁻¹‖ := by
        gcongr
        rw [norm_div, hnI]
        gcongr
        have h1 := norm_sub_le (Bt - Tp - I * Δ + I * P) (I * Lf)
        have h2 := norm_add_le (Bt - Tp - I * Δ) (I * P)
        have h3 := norm_sub_le (Bt - Tp) (I * Δ)
        have h4 := norm_sub_le Bt Tp
        simp only [norm_mul, Complex.norm_I, one_mul] at h1 h2 h3
        linarith

/-- The edge integrand agrees with `K_x(z − s₀) G'/G(z)` away from `s₀`. -/
theorem selbergKernelPhi_edge_eq {x : ℝ} {s₀ z : ℂ} (hz : z ≠ s₀) (g : ℂ) :
    selbergKernelPhi x (z - s₀) * (z - s₀)⁻¹ * g = selbergKernel x (z - s₀) * g := by
  rw [selbergKernelPhi_mul_inv (sub_ne_zero.mpr hz)]

/-- A horizontal edge at height `T` with `|T − t₀| ≥ H`. -/
theorem norm_selberg_horizontal_edge_le {x σL c T H BH : ℝ} {s₀ : ℂ} (hx : 1 < x)
    (hσc : σL ≤ c) (hH : 0 < H) (hTH : H ≤ |T - s₀.im|)
    (hB : ∀ u ∈ Icc σL c, ‖logDeriv zetaResidueUnit ((u : ℂ) + (T : ℂ) * I)‖ ≤ BH) :
    ‖∫ u in σL..c, selbergKernelPhi x ((u : ℂ) + (T : ℂ) * I - s₀) *
        ((u : ℂ) + (T : ℂ) * I - s₀)⁻¹ * logDeriv zetaResidueUnit ((u : ℂ) + (T : ℂ) * I)‖ ≤
      (Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
        (Real.log x * H ^ 2) * BH * (c - σL) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_).trans
    (le_of_eq (by rw [abs_of_nonneg (by linarith)]))
  rw [uIoc_of_le hσc] at hu
  have hz : (u : ℂ) + (T : ℂ) * I ≠ s₀ := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rw [← this, sub_self, abs_zero] at hTH
    linarith
  rw [selbergKernelPhi_edge_eq hz, norm_mul]
  have hwre : ((u : ℂ) + (T : ℂ) * I - s₀).re ≤ c - s₀.re := by simp; linarith [hu.2]
  have hwim : H ≤ |((u : ℂ) + (T : ℂ) * I - s₀).im| := by simpa using hTH
  have hK := norm_selbergKernel_le_of_im hx hH hwre hwim
  have hBu := hB u ⟨hu.1.le, hu.2⟩
  have hBH : 0 ≤ BH := (norm_nonneg _).trans hBu
  exact mul_le_mul hK hBu (norm_nonneg _) (by positivity)

/-- The left edge at `Re z = σ_L < σ₀`. -/
theorem norm_selberg_left_edge_le {x σL T₁ T₂ BL : ℝ} {s₀ : ℂ} (hx : 1 < x) (hσ : σL < s₀.re)
    (hT : T₁ ≤ T₂)
    (hB : ∀ y ∈ Icc T₁ T₂, ‖logDeriv zetaResidueUnit ((σL : ℂ) + (y : ℂ) * I)‖ ≤ BL) :
    ‖∫ y in T₁..T₂, selbergKernelPhi x ((σL : ℂ) + (y : ℂ) * I - s₀) *
        ((σL : ℂ) + (y : ℂ) * I - s₀)⁻¹ * logDeriv zetaResidueUnit ((σL : ℂ) + (y : ℂ) * I)‖ ≤
      BL * (2 * Real.exp ((σL - s₀.re) * Real.log x) / Real.log x) *
        (Real.pi / (s₀.re - σL)) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hd : 0 < s₀.re - σL := by linarith
  set C : ℝ := BL * (2 * Real.exp ((σL - s₀.re) * Real.log x) / Real.log x) with hC
  refine (intervalIntegral.norm_integral_le_of_norm_le hT (g := fun y =>
    C * ((s₀.re - σL) ^ 2 + (y - s₀.im) ^ 2)⁻¹) (Eventually.of_forall fun y hy => ?_)
    ((integrable_lorentz hd s₀.im).const_mul C).intervalIntegrable).trans ?_
  · have hz : (σL : ℂ) + (y : ℂ) * I ≠ s₀ := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [selbergKernelPhi_edge_eq hz, norm_mul, mul_comm]
    have hBy := hB y ⟨hy.1.le, hy.2⟩
    have hBL : 0 ≤ BL := (norm_nonneg _).trans hBy
    have hK := norm_selbergKernel_le_line hx ((σL : ℂ) + (y : ℂ) * I - s₀)
    have hre : ((σL : ℂ) + (y : ℂ) * I - s₀).re = σL - s₀.re := by simp
    have him : ((σL : ℂ) + (y : ℂ) * I - s₀).im = y - s₀.im := by simp
    rw [hre, him] at hK
    have hu : σL - s₀.re < 0 := by linarith
    have hexp : Real.exp (2 * (σL - s₀.re) * Real.log x) + Real.exp ((σL - s₀.re) * Real.log x) ≤
        2 * Real.exp ((σL - s₀.re) * Real.log x) := by
      have : Real.exp (2 * (σL - s₀.re) * Real.log x) ≤ Real.exp ((σL - s₀.re) * Real.log x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsq : (σL - s₀.re) ^ 2 = (s₀.re - σL) ^ 2 := by ring
    rw [hsq] at hK
    have hpos : 0 < (s₀.re - σL) ^ 2 + (y - s₀.im) ^ 2 := by positivity
    calc ‖logDeriv zetaResidueUnit ((σL : ℂ) + (y : ℂ) * I)‖ *
          ‖selbergKernel x ((σL : ℂ) + (y : ℂ) * I - s₀)‖
        ≤ BL * ((2 * Real.exp ((σL - s₀.re) * Real.log x)) /
            (Real.log x * ((s₀.re - σL) ^ 2 + (y - s₀.im) ^ 2))) := by
          refine mul_le_mul hBy (hK.trans ?_) (norm_nonneg _) hBL
          exact div_le_div_of_nonneg_right hexp (by positivity)
      _ = C * ((s₀.re - σL) ^ 2 + (y - s₀.im) ^ 2)⁻¹ := by rw [hC]; field_simp
  · have hC0 : 0 ≤ C := by
      rw [hC]
      have := hB T₁ ⟨le_rfl, hT⟩
      have hBL : 0 ≤ BL := (norm_nonneg _).trans this
      positivity
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_lorentz_window_le hd s₀.im hT) hC0

/-- The polar part `K_x(z − s₀)(z − 1)⁻¹` along the right edge. -/
theorem norm_selberg_right_pole_le {x c T₁ T₂ : ℝ} {s₀ : ℂ} (hx : 1 < x) (hc : s₀.re < c)
    (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) :
    ‖∫ y in T₁..T₂, selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀) * ((c : ℂ) + (y : ℂ) * I - 1)⁻¹‖ ≤
      (Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
        (Real.log x * T₁) * (Real.pi / (c - s₀.re)) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have ha : 0 < c - s₀.re := by linarith
  set A : ℝ := Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)
    with hA
  set C : ℝ := A / (Real.log x * T₁) with hC
  have hC0 : 0 ≤ C := by rw [hC, hA]; positivity
  refine (intervalIntegral.norm_integral_le_of_norm_le hT (g := fun y =>
    C * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2)⁻¹) (Eventually.of_forall fun y hy => ?_)
    ((integrable_lorentz ha s₀.im).const_mul C).intervalIntegrable).trans ?_
  · have hK := norm_selbergKernel_le_line hx ((c : ℂ) + (y : ℂ) * I - s₀)
    have hre : ((c : ℂ) + (y : ℂ) * I - s₀).re = c - s₀.re := by simp
    have him : ((c : ℂ) + (y : ℂ) * I - s₀).im = y - s₀.im := by simp
    rw [hre, him, ← hA] at hK
    have hy1 : T₁ ≤ ‖(c : ℂ) + (y : ℂ) * I - 1‖ := by
      have := Complex.abs_im_le_norm ((c : ℂ) + (y : ℂ) * I - 1)
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        Complex.one_im, sub_zero] at this
      rw [abs_of_pos (by linarith [hy.1])] at this
      linarith [hy.1]
    have hpos : 0 < (c - s₀.re) ^ 2 + (y - s₀.im) ^ 2 := by positivity
    rw [norm_mul, norm_inv]
    calc ‖selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀)‖ * ‖(c : ℂ) + (y : ℂ) * I - 1‖⁻¹
        ≤ (A / (Real.log x * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2))) * T₁⁻¹ :=
          mul_le_mul hK (inv_anti₀ hT₁ hy1) (by positivity) (by positivity)
      _ = C * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2)⁻¹ := by rw [hC]; field_simp
  · rw [intervalIntegral.integral_const_mul, hC, div_mul_eq_mul_div, div_mul_eq_mul_div]
    have := mul_le_mul_of_nonneg_left (integral_lorentz_window_le ha s₀.im hT)
      (show 0 ≤ A by rw [hA]; positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [this, show 0 < Real.log x * T₁ by positivity]

/-- **Selberg's explicit formula for `ζ'/ζ` at a point of the strip.** -/
theorem norm_logDeriv_zeta_add_selberg_le {x c σL T₁ T₂ H BH BL : ℝ} {s₀ : ℂ}
    (hx : 1 < x) (hc : 1 < c) (hc2 : c ≤ 2) (hσL : σL < s₀.re) (hσc : s₀.re < c)
    (hT₁ : 0 < T₁) (hH : 0 < H) (hH1 : H ≤ s₀.im - T₁) (hH2 : H ≤ T₂ - s₀.im)
    (hs₀ : riemannZeta s₀ ≠ 0)
    (hbot : ∀ u ∈ Icc σL c, zetaResidueUnit ((u : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
      ‖logDeriv zetaResidueUnit ((u : ℂ) + (T₁ : ℂ) * I)‖ ≤ BH)
    (htop : ∀ u ∈ Icc σL c, zetaResidueUnit ((u : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
      ‖logDeriv zetaResidueUnit ((u : ℂ) + (T₂ : ℂ) * I)‖ ≤ BH)
    (hleft : ∀ y ∈ Icc T₁ T₂, zetaResidueUnit ((σL : ℂ) + (y : ℂ) * I) ≠ 0 ∧
      ‖logDeriv zetaResidueUnit ((σL : ℂ) + (y : ℂ) * I)‖ ≤ BL) :
    ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
      ∑ w ∈ zetaResidueUnitClosedRectangleZeros ((σL : ℂ) + (T₁ : ℂ) * I)
          ((c : ℂ) + (T₂ : ℂ) * I),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤
      (2 * ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
          (Real.log x * H ^ 2) * BH * (c - σL)) +
        8 / (c - 1) ^ 2 *
          ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
            Real.log x) * (2 * Real.pi / H) +
        (Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
          (Real.log x * T₁) * (Real.pi / (c - s₀.re)) +
        BL * (2 * Real.exp ((σL - s₀.re) * Real.log x) / Real.log x) *
          (Real.pi / (s₀.re - σL))) / (2 * Real.pi) + 1 / T₁ := by
  have hT₁₀ : T₁ < s₀.im := by linarith
  have hT₂₀ : s₀.im < T₂ := by linarith
  have hT : T₁ ≤ T₂ := by linarith
  have hσLc : σL ≤ c := by linarith
  set z₁ : ℂ := (σL : ℂ) + (T₁ : ℂ) * I with hz₁
  set z₂ : ℂ := (c : ℂ) + (T₂ : ℂ) * I with hz₂
  have hz₁re : z₁.re = σL := by simp [hz₁]
  have hz₁im : z₁.im = T₁ := by simp [hz₁]
  have hz₂re : z₂.re = c := by simp [hz₂]
  have hz₂im : z₂.im = T₂ := by simp [hz₂]
  set φ : ℂ → ℂ := fun z => selbergKernelPhi x (z - s₀) with hφdef
  have hφ : AnalyticOnNhd ℂ φ Set.univ := by
    intro z _
    have h1 : AnalyticAt ℂ (fun w : ℂ => w - s₀) z := analyticAt_id.sub analyticAt_const
    exact AnalyticAt.comp (g := selbergKernelPhi x) (f := fun w : ℂ => w - s₀) (x := z)
      (analyticAt_selbergKernelPhi x (z - s₀)) h1
  have hs₁ : s₀ ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hs₀G : zetaResidueUnit s₀ ≠ 0 := (zetaResidueUnit_ne_zero_iff hs₁).2 hs₀
  have hin : z₁.re < s₀.re ∧ s₀.re < z₂.re ∧ z₁.im < s₀.im ∧ s₀.im < z₂.im := by
    rw [hz₁re, hz₂re, hz₁im, hz₂im]; exact ⟨hσL, hσc, hT₁₀, hT₂₀⟩
  have hre : z₁.re < z₂.re := by rw [hz₁re, hz₂re]; linarith
  have him : z₁.im < z₂.im := by rw [hz₁im, hz₂im]; linarith
  have hbot' : ∀ u ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((u : ℂ) + z₁.im * I) ≠ 0 := by
    intro u hu
    rw [hz₁re, hz₂re, uIcc_of_le hσLc] at hu
    rw [hz₁im]
    exact (hbot u hu).1
  have htop' : ∀ u ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((u : ℂ) + z₂.im * I) ≠ 0 := by
    intro u hu
    rw [hz₁re, hz₂re, uIcc_of_le hσLc] at hu
    rw [hz₂im]
    exact (htop u hu).1
  have hright' : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im, uIcc_of_le hT] at hy
    rw [hz₂re]
    have hne : (c : ℂ) + (y : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [hy.1]
    refine (zetaResidueUnit_ne_zero_iff hne).2 (riemannZeta_ne_zero_of_one_lt_re ?_)
    simp [hc]
  have hleft' : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im, uIcc_of_le hT] at hy
    rw [hz₁re]
    exact (hleft y hy).1
  have hrect := rectIntegral_mul_inv_sub_mul_logDeriv_zetaResidueUnit hφ hre him hin hs₀G
    hbot' htop' hright' hleft'
  -- the zero sum and the residue at `s₀`
  have hzeros : ∀ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂, w ≠ s₀ := by
    intro w hw heq
    have := (mem_zetaResidueUnitClosedRectangleZeros.mp hw).2
    rw [heq] at this
    exact hs₀G this
  have hsum : ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * (φ w * (w - s₀)⁻¹) =
      ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hφdef]
    simp only
    rw [selbergKernelPhi_mul_inv (sub_ne_zero.mpr (hzeros w hw))]
  have hφs₀ : φ s₀ = 1 := by rw [hφdef]; simp only [sub_self]; exact selbergKernelPhi_zero hx
  have hlogG : logDeriv zetaResidueUnit s₀ = logDeriv riemannZeta s₀ + (s₀ - 1)⁻¹ := by
    rw [logDeriv_zeta_eq hs₁ hs₀G]; ring
  rw [hsum, hφs₀, one_mul, hlogG] at hrect
  -- the four edges
  set f : ℂ → ℂ := fun z => φ z * (z - s₀)⁻¹ * logDeriv zetaResidueUnit z with hfdef
  set Bt : ℂ := ∫ u in σL..c, f ((u : ℂ) + (T₁ : ℂ) * I) with hBt
  set Tp : ℂ := ∫ u in σL..c, f ((u : ℂ) + (T₂ : ℂ) * I) with hTp
  set R : ℂ := ∫ y in T₁..T₂, f ((c : ℂ) + (y : ℂ) * I) with hR
  set Lf : ℂ := ∫ y in T₁..T₂, f ((σL : ℂ) + (y : ℂ) * I) with hLf
  have hrectE : rectIntegral f z₁ z₂ = (Bt - Tp) + I * R - I * Lf := by
    unfold rectIntegral
    rw [hz₁re, hz₂re, hz₁im, hz₂im, smul_eq_mul, smul_eq_mul]
  rw [hrectE] at hrect
  -- the right edge splits into the von Mangoldt part and the polar part
  set Rw : ℂ := ∫ y in T₁..T₂, selbergRightEdge x c s₀ y with hRw
  set P : ℂ := ∫ y in T₁..T₂, selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀) *
    ((c : ℂ) + (y : ℂ) * I - 1)⁻¹ with hP
  have hRsplit : R = Rw + P := by
    have hpt : ∀ y ∈ uIcc T₁ T₂, f ((c : ℂ) + (y : ℂ) * I) =
        selbergRightEdge x c s₀ y +
          selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀) * ((c : ℂ) + (y : ℂ) * I - 1)⁻¹ := by
      intro y hy
      rw [uIcc_of_le hT] at hy
      have hne1 : (c : ℂ) + (y : ℂ) * I ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith [hy.1]
      have hne0 : (c : ℂ) + (y : ℂ) * I ≠ s₀ := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hG : zetaResidueUnit ((c : ℂ) + (y : ℂ) * I) ≠ 0 :=
        (zetaResidueUnit_ne_zero_iff hne1).2 (riemannZeta_ne_zero_of_one_lt_re (by simp [hc]))
      rw [hfdef]
      simp only
      rw [hφdef]
      simp only
      rw [selbergKernelPhi_edge_eq hne0, selbergRightEdge,
        show logDeriv zetaResidueUnit ((c : ℂ) + (y : ℂ) * I) =
          logDeriv riemannZeta ((c : ℂ) + (y : ℂ) * I) + ((c : ℂ) + (y : ℂ) * I - 1)⁻¹ by
          rw [logDeriv_zeta_eq hne1 hG]; ring]
      ring
    rw [hR, intervalIntegral.integral_congr hpt]
    have hc1 : ContinuousOn (fun y : ℝ => selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀) *
        ((c : ℂ) + (y : ℂ) * I - 1)⁻¹) (uIcc T₁ T₂) := by
      have hK : Continuous (fun y : ℝ => selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀)) := by
        have hw : ∀ y : ℝ, (c : ℂ) + (y : ℂ) * I - s₀ ≠ 0 := by
          intro y h
          have := congrArg Complex.re h
          simp at this
          linarith
        exact ((differentiable_selbergKernelNum x).continuous.comp (by fun_prop)).div
          (by fun_prop) (fun y => pow_ne_zero 2 (hw y))
      refine hK.continuousOn.mul ((Continuous.continuousOn (by fun_prop)).inv₀ ?_)
      intro y hy
      rw [uIcc_of_le hT] at hy
      intro h
      have := congrArg Complex.im (sub_eq_zero.mp h)
      simp at this
      linarith [hy.1]
    rw [intervalIntegral.integral_add
      ((continuous_selbergRightEdge hc hσc).intervalIntegrable _ _)
      (hc1.intervalIntegrable)]
  set D : ℂ := selbergVonMangoldtPoly x s₀ with hD
  set Δ : ℂ := (∫ y : ℝ, selbergRightEdge x c s₀ y) - Rw with hΔ
  have hRw : Rw = -(2 * Real.pi) * D - Δ := by
    rw [hΔ, integral_selbergRightEdge hx hc hσc, hD, selbergVonMangoldtPoly]
    ring
  rw [hRsplit] at hrect
  have halg := selberg_contour_algebra hrect.symm hRw
  refine halg.trans ?_
  -- edge bounds
  have hBt : ‖Bt‖ ≤ (Real.exp (2 * (c - s₀.re) * Real.log x) +
      Real.exp ((c - s₀.re) * Real.log x)) / (Real.log x * H ^ 2) * BH * (c - σL) := by
    have h := norm_selberg_horizontal_edge_le (T := T₁) (s₀ := s₀) hx hσLc hH
      (by rw [abs_of_neg (by linarith)]; linarith) (fun u hu => (hbot u hu).2)
    simpa only [hBt, hfdef, hφdef] using h
  have hTp : ‖Tp‖ ≤ (Real.exp (2 * (c - s₀.re) * Real.log x) +
      Real.exp ((c - s₀.re) * Real.log x)) / (Real.log x * H ^ 2) * BH * (c - σL) := by
    have h := norm_selberg_horizontal_edge_le (T := T₂) (s₀ := s₀) hx hσLc hH
      (by rw [abs_of_pos (by linarith)]; linarith) (fun u hu => (htop u hu).2)
    simpa only [hTp, hfdef, hφdef] using h
  have hΔb : ‖Δ‖ ≤ 8 / (c - 1) ^ 2 *
      ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
        Real.log x) * (2 * Real.pi / H) :=
    norm_integral_selbergRightEdge_sub_window_le hx hc hc2 hσc hH hH1 hH2
  have hPb : ‖P‖ ≤ (Real.exp (2 * (c - s₀.re) * Real.log x) +
      Real.exp ((c - s₀.re) * Real.log x)) / (Real.log x * T₁) * (Real.pi / (c - s₀.re)) :=
    norm_selberg_right_pole_le (T₂ := T₂) hx hσc hT₁ hT
  have hLb : ‖Lf‖ ≤ BL * (2 * Real.exp ((σL - s₀.re) * Real.log x) / Real.log x) *
      (Real.pi / (s₀.re - σL)) := by
    have h := norm_selberg_left_edge_le (s₀ := s₀) hx hσL hT (fun y hy => (hleft y hy).2)
    simpa only [hLf, hfdef, hφdef] using h
  have hinv : ‖(s₀ - 1)⁻¹‖ ≤ 1 / T₁ := by
    rw [norm_inv, one_div]
    refine inv_anti₀ hT₁ ?_
    have := Complex.abs_im_le_norm (s₀ - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  gcongr
  linarith

end RHTower
