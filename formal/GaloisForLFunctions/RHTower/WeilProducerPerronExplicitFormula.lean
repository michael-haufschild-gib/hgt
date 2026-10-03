import GaloisForLFunctions.RHTower.WeilHerglotzPerronIntegral
import GaloisForLFunctions.RHTower.PerronDigammaSeriesKernel

/-!
# The logarithmically weighted explicit formula for a Weil-positive system

Let `lam` be full-cone Weil-positive, with boundary measure `μ_lam`, Herglotz function `H` and
Weil function `Φ_lam(s) = H(s − ½) + C_lam` (`C_lam = Φ_lam(2) − H(3/2)`).  Put
`Q_L(b) = (e^{bL} − 1 − bL)/b²`.  For `Re z > ½`, `z ≠ 1` and `L ≥ 0`
(`tsum_lamC_mul_max_eq`):

`Σ_n lam(n) n^{−z} (L − log n)⁺ = (−γ/2 − ½ log π − C_lam) L + ½ Σ_k (L/(k+1) − 2Q_L(−z − 2k))`
`    + Q_L(−z) + Q_L(1 − z) − ∫ (Q_L(ir + ½ − z) − irL/(1 + r²)) dμ_lam(r)`.

For `lam = Λ` under RH, `μ_Λ` is the counting measure of the ordinates of the zeros and this is
the classical explicit formula with weight `log(x/n)`; here it holds for every point of the Weil
cone, unconditionally, with the boundary measure in place of the zeros.  Expanding
`Q_L(b) = e^{bL}/b² − 1/b² − L/b`, the terms `−L/b` add up to `L·A_lam(z)` and the terms
`−1/b²` to `A_lam'(z)`, where `A_lam = Σ lam(n) n^{−s}` continued by `U − Φ_lam`.

**Proof.**  The weighted Perron formula (`tsum_term_mul_max_eq_integral`) on `Re s = 1` writes
the left side as `∫ A_lam(z + s) e^{sL}/s² dw`.  On the contour `A_lam = U − Φ_lam` with
`U(v) = ½ψ(v/2) − ½ log π + 1/v + 1/(v − 1)`.  Each part is evaluated without moving the contour:
the Gauss series of `ψ` by `integral_tsum_gaussDigammaSeriesTerm_mul_perron`, the two poles by
`integral_inv_sub_mul_perron_eq`, and `H` by Fubini over `μ_lam`
(`integral_herglotzFunction_mul_perron`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-- The pole weight `Q_L(b) = (e^{bL} − 1 − bL)/b²`. -/
def poleWeight (L : ℝ) (b : ℂ) : ℂ := (cexp (b * L) - 1 - b * L) / b ^ 2

/-- The constant `C_lam = Φ_lam(2) − H(3/2)` of the Weil continuation. -/
def weilConst {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ :=
  weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2)

theorem abscissaOfAbsConv_lamC_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    LSeries.abscissaOfAbsConv (lamC lam) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := lamC lam)
    (x := 1) fun y hy => summable_term_lamC hW (by simpa using hy)
  exact_mod_cast this

theorem integrable_LSeries_lamC_mul_perron {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 1 / 2 < z.re) (L : ℝ) :
    Integrable fun w : ℝ => LSeries (lamC lam) (z + contour 1 w) *
      (cexp (contour 1 w * L) / contour 1 w ^ 2) := by
  have hre : ∀ w : ℝ, (z + contour 1 w).re = z.re + 1 := fun w => by
    rw [Complex.add_re, contour_re]
  have hcont : Continuous fun w : ℝ => LSeries (lamC lam) (z + contour 1 w) := by
    refine continuous_iff_continuousAt.mpr fun w => ?_
    have habs : LSeries.abscissaOfAbsConv (lamC lam) < ((z + contour 1 w).re : ℝ) := by
      rw [hre]
      exact (abscissaOfAbsConv_lamC_le hW).trans_lt (by exact_mod_cast (by linarith))
    have hf : Continuous fun w : ℝ => z + contour 1 w := by simp only [contour]; fun_prop
    exact ContinuousAt.comp (g := LSeries (lamC lam)) (f := fun w : ℝ => z + contour 1 w)
      (LSeries_hasDerivAt habs).continuousAt hf.continuousAt
  refine (integrable_perron_integrand one_pos L).bdd_mul
    (c := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (3 / 2 : ℝ)) hcont.aestronglyMeasurable
    (Eventually.of_forall fun w => norm_LSeries_lamC_le hW (by rw [hre]; linarith))

/-- **The logarithmically weighted explicit formula on the Weil cone.** -/
theorem tsum_lamC_mul_max_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) {L : ℝ} (hL : 0 ≤ L) :
    ∑' n : ℕ, LSeries.term (lamC lam) z n * ((max (L - Real.log n) 0 : ℝ) : ℂ) =
      (-(Real.eulerMascheroniConstant : ℂ) / 2 - (Real.log π : ℂ) / 2 - weilConst hW) * L +
        (∑' k : ℕ, ((L : ℂ) / ((k : ℂ) + 1) - 2 * poleWeight L (-z - 2 * k))) / 2 +
        poleWeight L (-z) + poleWeight L (1 - z) -
        ∫ r, (poleWeight L (I * r - (z - 1 / 2)) - I * r / (1 + (r : ℂ) ^ 2) * L)
          ∂boundaryMeasure hW := by
  have hc : (0 : ℝ) < 1 := one_pos
  have hsumm : LSeriesSummable (lamC lam) (z + ((1 : ℝ) : ℂ)) :=
    summable_term_lamC hW (by simp; linarith)
  rw [tsum_term_mul_max_eq_integral hc hsumm L]
  set P : ℝ → ℂ := fun w => cexp (contour 1 w * L) / contour 1 w ^ 2 with hP
  set Kc : ℂ := -(Real.eulerMascheroniConstant : ℂ) / 2 - (Real.log π : ℂ) / 2 - weilConst hW
    with hKc
  set z₀ : ℂ := z - 1 / 2 with hz₀
  have hz₀re : 0 < z₀.re := by rw [hz₀]; simp; linarith
  set G : ℝ → ℂ := fun w =>
    (∑' n : ℕ, gaussDigammaSeriesTerm ((z + contour 1 w) / 2) n) * P w with hG
  -- the pointwise decomposition
  have hdec : ∀ w : ℝ, LSeries (lamC lam) (z + contour 1 w) * P w =
      G w / 2 + Kc * P w + 1 / (contour 1 w - -z) * P w + 1 / (contour 1 w - (1 - z)) * P w -
        herglotzFunction hW (z₀ + contour 1 w) * P w := by
    intro w
    set v : ℂ := z + contour 1 w with hv
    have hvre : 1 < v.re := by rw [hv, Complex.add_re, contour_re]; linarith
    have hcont := weilContinuation_eq hW hvre
    have hpsi := digamma_eq_neg_euler_add_tsum_gauss (s := v / 2)
      (by have : (v / 2).re = v.re / 2 := by simp
          rw [this]; linarith)
    have hWC : weilContinuation hW v = herglotzFunction hW (z₀ + contour 1 w) + weilConst hW := by
      simp only [weilContinuation, weilConst, hv, hz₀]
      ring_nf
    have hWF : weilFunction lam v = Complex.digamma (v / 2) / 2 - (Real.log π : ℂ) / 2 + 1 / v +
        1 / (v - 1) - LSeries (lamC lam) v := rfl
    have hL : LSeries (lamC lam) v = Complex.digamma (v / 2) / 2 - (Real.log π : ℂ) / 2 + 1 / v +
        1 / (v - 1) - (herglotzFunction hW (z₀ + contour 1 w) + weilConst hW) := by
      rw [← hWC, hcont, hWF]; ring
    have e1 : contour 1 w - -z = v := by rw [hv]; ring
    have e2 : contour 1 w - (1 - z) = v - 1 := by rw [hv]; ring
    rw [hL, e1, e2, hpsi]
    simp only [hG, hKc, hv]
    ring
  -- integrability of the pieces
  have hb2 : (-z).re < 1 := by simp; linarith
  have hb3 : (1 - z).re < 1 := by simp; linarith
  have hI1 : Integrable fun w => LSeries (lamC lam) (z + contour 1 w) * P w :=
    integrable_LSeries_lamC_mul_perron hW hz L
  have hIc : Integrable fun w => Kc * P w := (integrable_perron_integrand hc L).const_mul _
  have hI2 : Integrable fun w => 1 / (contour 1 w - -z) * P w :=
    integrable_inv_sub_mul_perron hc L hb2
  have hI3 : Integrable fun w => 1 / (contour 1 w - (1 - z)) * P w :=
    integrable_inv_sub_mul_perron hc L hb3
  have hI4 : Integrable fun w => herglotzFunction hW (z₀ + contour 1 w) * P w :=
    integrable_herglotzFunction_mul_perron hW hz₀re hc L
  have hIG : Integrable fun w => G w / 2 := by
    refine ((((hI1.sub hIc).sub hI2).sub hI3).add hI4).congr
      (Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hdec w]
    ring
  -- the values
  have hPint : ∫ w, P w = (L : ℂ) := by
    have hK := perron_weighted_kernel hc L
    rw [show (L : ℂ) = ((max L 0 : ℝ) : ℂ) by rw [max_eq_left hL]]
    exact hK
  have vG : ∫ w, G w / 2 =
      (∑' k : ℕ, ((L : ℂ) / ((k : ℂ) + 1) - 2 * poleWeight L (-z - 2 * k))) / 2 := by
    rw [integral_div]
    congr 1
    exact integral_tsum_gaussDigammaSeriesTerm_mul_perron (by linarith) hc hL
  have v2 : ∫ w, 1 / (contour 1 w - -z) * P w = poleWeight L (-z) :=
    integral_inv_sub_mul_perron_eq hc hL hb2 (neg_ne_zero.mpr fun h => by
      rw [h] at hz; simp at hz; linarith)
  have v3 : ∫ w, 1 / (contour 1 w - (1 - z)) * P w = poleWeight L (1 - z) :=
    integral_inv_sub_mul_perron_eq hc hL hb3 (sub_ne_zero.mpr (Ne.symm hz1))
  have v4 : ∫ w, herglotzFunction hW (z₀ + contour 1 w) * P w =
      ∫ r, (poleWeight L (I * r - (z - 1 / 2)) - I * r / (1 + (r : ℂ) ^ 2) * L)
        ∂boundaryMeasure hW :=
    integral_herglotzFunction_mul_perron hW hz₀re hc hL
  have hsplit : ∫ w, LSeries (lamC lam) (z + contour 1 w) * P w =
      (∫ w, G w / 2) + (∫ w, Kc * P w) + (∫ w, 1 / (contour 1 w - -z) * P w) +
        (∫ w, 1 / (contour 1 w - (1 - z)) * P w) -
        ∫ w, herglotzFunction hW (z₀ + contour 1 w) * P w := by
    have h12 : Integrable fun w => G w / 2 + Kc * P w := hIG.add hIc
    have h123 : Integrable fun w => G w / 2 + Kc * P w + 1 / (contour 1 w - -z) * P w :=
      h12.add hI2
    have h1234 : Integrable fun w => G w / 2 + Kc * P w + 1 / (contour 1 w - -z) * P w +
        1 / (contour 1 w - (1 - z)) * P w := h123.add hI3
    rw [integral_congr_ae (Eventually.of_forall hdec), integral_sub h1234 hI4,
      integral_add h123 hI3, integral_add h12 hI2, integral_add hIG hIc]
  rw [hsplit, vG, integral_const_mul, hPint, v2, v3, v4]
  ring

end RHTower.WeilSpectral

end
