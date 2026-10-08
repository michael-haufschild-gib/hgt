import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Analytic passage for geometrically bounded valuation coefficients

Coefficient limits with a common geometric envelope converge uniformly on
every smaller closed disk. This is the infinite depth passage used by the
actual-source valuation residue function.
-/

open Complex Filter Topology Metric Set
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem geometric_series_norm_summable {a : ℕ → ℂ} {C rho : ℝ}
    (hrho : 0 ≤ rho) (ha : ∀ k, ‖a k‖ ≤ C * rho ^ k)
    {z : ℂ} (hz : rho * ‖z‖ < 1) :
    Summable (fun k => ‖a k * z ^ k‖) := by
  refine ((summable_geometric_of_lt_one (by positivity) hz).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun k => ?_
  calc
    _ = ‖a k‖ * ‖z‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ (C * rho ^ k) * ‖z‖ ^ k := mul_le_mul_of_nonneg_right (ha k) (by positivity)
    _ = C * (rho * ‖z‖) ^ k := by rw [mul_pow]; ring

theorem geometric_series_differentiableOn {a : ℕ → ℂ} {C rho R : ℝ}
    (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hR : 0 ≤ R)
    (ha : ∀ k, ‖a k‖ ≤ C * rho ^ k) (hr : rho * R < 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' k, a k * z ^ k) (ball 0 R) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one (by positivity) hr).mul_left C)
    (fun k => ((differentiable_const (a k)).mul (differentiable_id.pow k)).differentiableOn)
    isOpen_ball
  intro k z hz
  change ‖a k * z ^ k‖ ≤ C * (rho * R) ^ k
  have hzR : ‖z‖ ≤ R := (by simpa only [mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
  calc
    _ = ‖a k‖ * ‖z‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ (C * rho ^ k) * R ^ k := by gcongr; exact ha k
    _ = C * (rho * R) ^ k := by rw [mul_pow]; ring

/-- A common coefficient envelope pays the uniform infinite-sum limit. -/
theorem geometric_series_tendstoUniformlyOn {α : Type*} {L : Filter α} [L.NeBot]
    {a : α → ℕ → ℂ} {u : ℕ → ℂ} {C rho R : ℝ}
    (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hr : rho * R < 1)
    (hu : ∀ k, Tendsto (fun s => a s k) L (𝓝 (u k)))
    (ha : ∀ᶠ s in L, ∀ k, ‖a s k‖ ≤ C * rho ^ k) :
    TendstoUniformlyOn (fun s z => ∑' k, a s k * z ^ k)
      (fun z => ∑' k, u k * z ^ k) L (closedBall 0 R) := by
  have hub (k : ℕ) : ‖u k‖ ≤ C * rho ^ k :=
    le_of_tendsto (hu k).norm (ha.mono fun s hs => hs k)
  have hgeo := summable_geometric_of_lt_one (mul_nonneg hrho hR) hr
  have hdiff : ∀ᶠ s in L, ∀ k, ‖a s k - u k‖ * R ^ k ≤ (2 * C) * (rho * R) ^ k := by
    filter_upwards [ha] with s hs k
    calc
      _ ≤ (‖a s k‖ + ‖u k‖) * R ^ k :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hR _)
      _ ≤ (C * rho ^ k + C * rho ^ k) * R ^ k := by
        gcongr
        · exact hs k
        · exact hub k
      _ = _ := by rw [mul_pow]; ring
  have hlim : Tendsto (fun s => ∑' k, ‖a s k - u k‖ * R ^ k) L (𝓝 0) := by
    have hk (k : ℕ) : Tendsto (fun s => ‖a s k - u k‖ * R ^ k) L (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_mul] using ((hu k).sub_const (u k)).norm.mul_const (R ^ k)
    have hb : ∀ᶠ s in L, ∀ k, ‖‖a s k - u k‖ * R ^ k‖ ≤ (2 * C) * (rho * R) ^ k := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hR _))]
        using hdiff
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
      (hgeo.mul_left (2 * C)) hk hb
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [ha, hdiff, hlim.eventually (gt_mem_nhds he)] with s hs hd heps z hz
  have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hzr : rho * ‖z‖ < 1 := (mul_le_mul_of_nonneg_left hzR hrho).trans_lt hr
  have hsa := geometric_series_norm_summable hrho hs hzr
  have hsu := geometric_series_norm_summable hrho hub hzr
  have hsd : Summable (fun k => ‖(a s k - u k) * z ^ k‖) := by
    apply (hsa.add hsu).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    rw [sub_mul]
    exact norm_sub_le _ _
  have hsr : Summable (fun k => ‖a s k - u k‖ * R ^ k) :=
    (hgeo.mul_left (2 * C)).of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hR k)) (hd ·)
  rw [dist_eq_norm, norm_sub_rev, ← hsa.of_norm.tsum_sub hsu.of_norm]
  simp_rw [← sub_mul]
  apply lt_of_le_of_lt ((norm_tsum_le_tsum_norm hsd).trans ?_) heps
  apply hsd.tsum_le_tsum (fun k => ?_) hsr
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzR _) (norm_nonneg _)

end RHTower.WeilSingularArithmetic
