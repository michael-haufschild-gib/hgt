/-
# Uniform convergence of logarithmic derivatives, and of their contour integrals

If entire functions `Fₐ` converge to `f` uniformly on a closed disc and `f` does not vanish on an
interior circle, then the logarithmic derivatives converge uniformly on that circle and hence so do
their contour integrals.

Two ingredients: Cauchy's estimate turns a sup bound on a difference into a sup bound on the
derivative of the difference, and the algebraic identity

  `F′/F − f′/f = (F′ − f′)/F + f′(f − F)/(F f)`

turns both into a bound on the difference of logarithmic derivatives.

Main results:
* `norm_deriv_le_of_forall_norm_le` — Cauchy's estimate for the first derivative.
* `tendstoUniformlyOn_deriv_of_tendstoUniformlyOn` — derivatives converge uniformly on a smaller
  disc.
* `norm_logDeriv_sub_le` — the pointwise bound on the difference of logarithmic derivatives.
* `tendsto_circleIntegral_logDeriv` — the contour integrals of the logarithmic derivatives
  converge.
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace GaloisForLFunctions.HTGeometry

open Metric Filter

/-- **Cauchy's estimate for the first derivative.**  A sup bound on a disc of radius `δ` around `z`
bounds `‖h′ z‖` by `ε/δ`. -/
theorem norm_deriv_le_of_forall_norm_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c : ℂ}
    {R ε δ : ℝ} (hδ : 0 < δ) (hbound : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖h w‖ ≤ ε) {z : ℂ}
    (hz : ‖z - c‖ + δ ≤ R) : ‖deriv h z‖ ≤ ε / δ := by
  have hsphere : ∀ w ∈ sphere z δ, ‖h w‖ ≤ ε := by
    intro w hw
    have hwz : ‖w - z‖ = δ := by simpa [Complex.dist_eq] using mem_sphere.mp hw
    refine hbound w ?_
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ = δ + ‖z - c‖ := by rw [hwz]
      _ ≤ R := by linarith
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := z) (R := δ) (C := ε)
    1 hδ hh.diffContOnCl hsphere
  rw [iteratedDeriv_one] at h1
  simpa using h1

/-- **The derivatives converge uniformly on a smaller disc.** -/
theorem tendstoUniformlyOn_deriv_of_tendstoUniformlyOn {α : Type*} {p : Filter α}
    {F : α → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    {c : ℂ} {R ρ : ℝ} (hρR : ρ < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R)) :
    TendstoUniformlyOn (fun a => deriv (F a)) (deriv f) p (closedBall c ρ) := by
  set δ : ℝ := R - ρ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  rw [Metric.tendstoUniformlyOn_iff] at huniform ⊢
  intro ε hε
  have hεδ : 0 < ε * δ / 2 := by positivity
  filter_upwards [huniform (ε * δ / 2) hεδ] with a ha z hz
  have hdiff : Differentiable ℂ (fun w => f w - F a w) := hf.sub (hF a)
  have hbound : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖f w - F a w‖ ≤ ε * δ / 2 := by
    intro w hw
    have hwmem : w ∈ closedBall c R := by
      rw [mem_closedBall, Complex.dist_eq]
      exact hw
    have := ha w hwmem
    rw [Complex.dist_eq] at this
    exact this.le
  have hzc : ‖z - c‖ ≤ ρ := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hzδ : ‖z - c‖ + δ ≤ R := by rw [hδdef]; linarith
  have hderiv := norm_deriv_le_of_forall_norm_le hdiff hδ hbound hzδ
  have hsub : deriv (fun w => f w - F a w) z = deriv f z - deriv (F a) z := by
    exact deriv_fun_sub hf.differentiableAt (hF a).differentiableAt
  rw [hsub] at hderiv
  rw [Complex.dist_eq]
  calc ‖deriv f z - deriv (F a) z‖ ≤ ε * δ / 2 / δ := hderiv
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The pointwise bound on the difference of two logarithmic derivatives, from the identity
`F′/F − f′/f = (F′ − f′)/F + f′(f − F)/(F f)`. -/
theorem norm_logDeriv_sub_le {F f : ℂ → ℂ} {z : ℂ} {m Mf η : ℝ} (hm : 0 < m)
    (hfz : m ≤ ‖f z‖) (hFz : m / 2 ≤ ‖F z‖) (hMf : 0 ≤ Mf) (hdf : ‖deriv f z‖ ≤ Mf)
    (h1 : ‖f z - F z‖ ≤ η) (h2 : ‖deriv (F) z - deriv f z‖ ≤ η) :
    ‖logDeriv F z - logDeriv f z‖ ≤ 2 * η / m + 2 * Mf * η / m ^ 2 := by
  have hFne : F z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hFz
    linarith
  have hfne : f z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfz
    linarith
  have hFpos : 0 < ‖F z‖ := norm_pos_iff.mpr hFne
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfne
  have hid : logDeriv F z - logDeriv f z
      = (deriv F z - deriv f z) / F z + deriv f z * (f z - F z) / (F z * f z) := by
    rw [logDeriv_apply, logDeriv_apply]
    field_simp
    ring
  have hη : 0 ≤ η := le_trans (norm_nonneg _) h1
  have hb1 : ‖(deriv F z - deriv f z) / F z‖ ≤ 2 * η / m := by
    rw [norm_div, div_le_div_iff₀ hFpos hm]
    calc ‖deriv F z - deriv f z‖ * m ≤ η * m := mul_le_mul_of_nonneg_right h2 hm.le
      _ ≤ 2 * η * ‖F z‖ := by nlinarith [hη, hFz]
  have hb2 : ‖deriv f z * (f z - F z) / (F z * f z)‖ ≤ 2 * Mf * η / m ^ 2 := by
    rw [norm_div, norm_mul, norm_mul]
    have hden : 0 < ‖F z‖ * ‖f z‖ := by positivity
    rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < m ^ 2)]
    have hprod : ‖deriv f z‖ * ‖f z - F z‖ ≤ Mf * η :=
      mul_le_mul hdf h1 (norm_nonneg _) hMf
    have hFf : m ^ 2 / 2 ≤ ‖F z‖ * ‖f z‖ := by nlinarith [hFz, hfz, hm]
    calc ‖deriv f z‖ * ‖f z - F z‖ * m ^ 2 ≤ Mf * η * m ^ 2 :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ ≤ 2 * Mf * η * (‖F z‖ * ‖f z‖) := by nlinarith [mul_nonneg hMf hη, hFf]
  calc ‖logDeriv F z - logDeriv f z‖
      = ‖(deriv F z - deriv f z) / F z + deriv f z * (f z - F z) / (F z * f z)‖ := by rw [hid]
    _ ≤ ‖(deriv F z - deriv f z) / F z‖ + ‖deriv f z * (f z - F z) / (F z * f z)‖ :=
        norm_add_le _ _
    _ ≤ 2 * η / m + 2 * Mf * η / m ^ 2 := add_le_add hb1 hb2

end GaloisForLFunctions.HTGeometry
