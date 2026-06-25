/-
# Carrier prerequisites for the n≥2 Mahler norm-descent

To instantiate `carrier_norm_relation` at the genuine Böttcher coordinate, the carrier is
`L = meroField(escapeOpen c)` with `τ` = precomposition by `z ↦ z²+c`. The `meroField`/`IsDomain`
machinery requires the domain `escapeOpen c` to be **connected**. This file supplies that: the exterior
of a disk `{|z| > R}` is the continuous image of the connected product `(R,∞) × (unit circle)` under
`(r, u) ↦ r·u`, hence connected (spheres in `ℂ` are connected since `rank_ℝ ℂ = 2 > 1`).
-/
import GaloisForLFunctions.U0.MahlerEndo
import Mathlib.Analysis.Normed.Module.Connected

open Polynomial Bottcher Set

namespace MahlerPolynomial

/-- **The escape region is connected (PROVED).** `escapeOpen c = {z | max 2 ‖c‖ < ‖z‖}`, the exterior
of a closed disk, is preconnected: it is the image of `(max 2 ‖c‖, ∞) × sphere(0,1)` (a product of
connected sets — `Ioi` and the circle, connected in `ℂ` by `rank_ℝ ℂ = 2 > 1`) under the continuous
`(r, u) ↦ (r:ℂ)·u`. This is the domain-connectedness prerequisite for `meroField(escapeOpen c)`. -/
theorem isPreconnected_escapeOpen (c : ℂ) : IsPreconnected (escapeOpen c) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hs : IsPreconnected ((Ioi (max 2 ‖c‖)) ×ˢ (Metric.sphere (0 : ℂ) 1)) :=
    isPreconnected_Ioi.prod (isConnected_sphere hrank 0 zero_le_one).isPreconnected
  have himg : escapeOpen c
      = (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' ((Ioi (max 2 ‖c‖)) ×ˢ (Metric.sphere (0 : ℂ) 1)) := by
    ext z
    simp only [escapeOpen, mem_setOf_eq, mem_image, mem_prod, mem_Ioi, Metric.mem_sphere,
      dist_zero_right, Prod.exists]
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by rintro rfl; simp only [norm_zero] at hz; linarith [le_max_left 2 ‖c‖]
      refine ⟨‖z‖, z / (‖z‖ : ℂ), ⟨hz, ?_⟩, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hz0),
          div_self (ne_of_gt (norm_pos_iff.mpr hz0))]
      · have hne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (norm_pos_iff.mpr hz0)
        rw [mul_comm]; exact div_mul_cancel₀ z hne
    · rintro ⟨r, u, ⟨hr, hu⟩, rfl⟩
      have hrpos : 0 < r := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hu, mul_one]
      exact hr
  rw [himg]
  exact hs.image _ (Continuous.continuousOn (by fun_prop))

/-- **Precomposition by `z↦z²+c` is injective on analytic functions over `escapeOpen` (PROVED).** If
`f` is analytic on `escapeOpen c` and `f(z²+c) = 0` for all `z ∈ escapeOpen c`, then `f ≡ 0` on
`escapeOpen c`. Proof: `σ(escapeOpen) = {w | R² < ‖w−c‖}` (`R = max 2 ‖c‖`) is open and `⊆ escapeOpen`;
`f = 0` there (every such `w` is `z²+c` for a square root `z` of `w−c` with `‖z‖ > R`), so by the
identity theorem on connected `escapeOpen`, `f ≡ 0`. This is the mathematical core of the injectivity
of the Mahler operator `τ` on `meroField(escapeOpen)`. -/
theorem eqZero_of_comp_quadratic_eqZero {c : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (escapeOpen c))
    (h0 : ∀ z ∈ escapeOpen c, f (z ^ 2 + c) = 0) :
    ∀ z ∈ escapeOpen c, f z = 0 := by
  have hR2 : max 2 ‖c‖ ≤ (max 2 ‖c‖) ^ 2 - ‖c‖ := by
    nlinarith [le_max_left 2 ‖c‖, le_max_right 2 ‖c‖, norm_nonneg c]
  set V : Set ℂ := {w | (max 2 ‖c‖) ^ 2 < ‖w - c‖} with hV
  have hVopen : IsOpen V :=
    isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)
  have hVsub : V ⊆ escapeOpen c := by
    intro w hw
    have hw' : (max 2 ‖c‖) ^ 2 < ‖w - c‖ := hw
    have h1 : ‖w - c‖ ≤ ‖w‖ + ‖c‖ := norm_sub_le w c
    show max 2 ‖c‖ < ‖w‖
    linarith
  have hf0V : ∀ w ∈ V, f w = 0 := by
    intro w hw
    simp only [hV, mem_setOf_eq] at hw
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (by norm_num : 0 < 2)
    have hzn : (max 2 ‖c‖) < ‖z‖ := by
      have : (max 2 ‖c‖) ^ 2 < ‖z‖ ^ 2 := by rw [← norm_pow, hz]; exact hw
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg z) this
    have := h0 z hzn
    rwa [hz, sub_add_cancel] at this
  have hw₀ : (c + ((max 2 ‖c‖) ^ 2 + 1 : ℝ)) ∈ V := by
    simp only [hV, mem_setOf_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]; linarith
  intro z hz
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero (isPreconnected_escapeOpen c)
    (hVsub hw₀)
    (((Filter.eventually_iff.mpr (Filter.mem_of_superset (hVopen.mem_nhds hw₀) hf0V)).filter_mono
      nhdsWithin_le_nhds).frequently) hz

end MahlerPolynomial
