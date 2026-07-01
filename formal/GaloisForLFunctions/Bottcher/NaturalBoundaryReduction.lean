import Mathlib.Analysis.Complex.Polynomial.Basic
import GaloisForLFunctions.Bottcher.EvenEntireClassification

open Complex Set Filter Topology Metric

namespace Bottcher

/-- **Natural-boundary reduction (task02, wiring the back half to the Böttcher side).**  Let `ψ`
(the connected inverse Böttcher coordinate on `{|w|>1}`) be odd and satisfy the Böttcher functional
equation `ψ(w²)=ψ(w)²+c` there.  Suppose the arc-continuation hypothesis holds: `ψ` continues so that
`h(t)=t·ψ(1/t)` extends to an **entire** function `H` of polynomial growth with `H(0)=1` agreeing with
`h` on the punctured unit disk.  Then `c∈{0,−2}`.  Proof: on the punctured disk `H` inherits evenness
and the functional equation `H(t²)=H(t)²+c·t²` from `ψ`; by the identity theorem these hold on all of
`ℂ`; then `c_mem_of_entire_even_functional_eq` applies.  Contrapositive: for `c∉{0,−2}` no such entire
continuation exists — the unit circle is a natural boundary. -/
theorem c_mem_of_psi_entire_continuation {ψ H : ℂ → ℂ} {C : ℝ} {n : ℕ} {c : ℂ}
    (hodd : ∀ w, 1 < ‖w‖ → ψ (-w) = -ψ w)
    (hfe : ∀ w, 1 < ‖w‖ → ψ (w ^ 2) = (ψ w) ^ 2 + c)
    (hH : Differentiable ℂ H)
    (hgrowth : ∀ z, ‖H z‖ ≤ C * (max 1 ‖z‖) ^ n)
    (hH0 : H 0 = 1)
    (hagree : ∀ t, 0 < ‖t‖ → ‖t‖ < 1 → H t = t * ψ (1 / t)) :
    c = 0 ∨ c = -2 := by
  -- identity theorem helper: an entire function vanishing on the unit ball vanishes everywhere
  have entire_zero_of_ball : ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ t ∈ ball (0 : ℂ) 1, F t = 0) → ∀ z, F z = 0 := by
    intro F hF hball z
    have hFan : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
    have h0an : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) univ :=
      (differentiable_const 0).differentiableOn.analyticOnNhd isOpen_univ
    have heq : F =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with t ht
      exact hball t ht
    exact hFan.eqOn_of_preconnected_of_eventuallyEq h0an isPreconnected_univ (mem_univ 0)
      heq (mem_univ z)
  -- evenness of H
  have hHeven : ∀ z, H (-z) = H z := by
    have hE : Differentiable ℂ (fun t => H (-t) - H t) := by fun_prop
    have hEball : ∀ t ∈ ball (0 : ℂ) 1, H (-t) - H t = 0 := by
      intro t ht
      rw [mem_ball, dist_zero_right] at ht
      rcases eq_or_ne t 0 with rfl | ht0
      · simp
      · have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
        have hw : (1 : ℝ) < ‖(1 : ℂ) / t‖ := by
          rw [norm_div, norm_one, lt_div_iff₀ htpos, one_mul]; exact ht
        rw [hagree (-t) (by rwa [norm_neg]) (by rwa [norm_neg]), hagree t htpos ht,
          show (1 : ℂ) / (-t) = -(1 / t) from by ring, hodd (1 / t) hw]
        ring
    intro z
    have := entire_zero_of_ball _ hE hEball z
    linear_combination this
  -- functional equation for H
  have hHfe : ∀ t, H (t ^ 2) = (H t) ^ 2 + c * t ^ 2 := by
    have hG : Differentiable ℂ (fun t => H (t ^ 2) - (H t) ^ 2 - c * t ^ 2) := by fun_prop
    have hGball : ∀ t ∈ ball (0 : ℂ) 1, H (t ^ 2) - (H t) ^ 2 - c * t ^ 2 = 0 := by
      intro t ht
      rw [mem_ball, dist_zero_right] at ht
      rcases eq_or_ne t 0 with rfl | ht0
      · norm_num [hH0]
      · have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
        have ht2pos : 0 < ‖t ^ 2‖ := by rw [norm_pow]; positivity
        have ht2lt : ‖t ^ 2‖ < 1 := by
          rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg t) ht (by norm_num)
        have hw : (1 : ℝ) < ‖(1 : ℂ) / t‖ := by
          rw [norm_div, norm_one, lt_div_iff₀ htpos, one_mul]; exact ht
        rw [hagree (t ^ 2) ht2pos ht2lt, hagree t htpos ht,
          show (1 : ℂ) / t ^ 2 = (1 / t) ^ 2 from by ring, hfe (1 / t) hw]
        ring
    intro t
    have := entire_zero_of_ball _ hG hGball t
    linear_combination this
  exact c_mem_of_entire_even_functional_eq hH hgrowth hHeven hHfe hH0

end Bottcher
