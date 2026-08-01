import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# Vertical decay of the polygamma tower

On a vertical line in the right half-plane the trigamma is bounded by `1/t² + π/(2t)`.  That bound
holds on a whole disc of fixed radius around the point, so Cauchy's estimate for iterated derivatives
transfers it to every higher polygamma with an extra factor `m!/(σ/2)^m`.

Hence every positive-order polygamma vanishes in the limit along vertical lines, while the digamma
itself grows like `log`.  This is the analytic input for the valuation of the digamma differential
field: in a jet monomial, any derivative factor kills the term.
-/

open Filter Topology Metric Complex

namespace GaloisForLFunctions

/-- Points of a small ball around a vertical point stay in the right half-plane and keep a
positive imaginary part. -/
theorem mem_ball_re_im {σ t : ℝ} {ζ : ℂ}
    (hζ : ζ ∈ Metric.closedBall ((σ : ℂ) + (t : ℂ) * Complex.I) (σ / 2)) :
    σ / 2 ≤ ζ.re ∧ t - σ / 2 ≤ ζ.im := by
  have hd : ‖ζ - ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ / 2 := by
    rw [← dist_eq_norm]
    exact hζ
  have hre := abs_le.mp (le_trans (Complex.abs_re_le_norm _) hd)
  have him := abs_le.mp (le_trans (Complex.abs_im_le_norm _) hd)
  have h1 : (ζ - ((σ : ℂ) + (t : ℂ) * Complex.I)).re = ζ.re - σ := by simp
  have h2 : (ζ - ((σ : ℂ) + (t : ℂ) * Complex.I)).im = ζ.im - t := by simp
  rw [h1] at hre
  rw [h2] at him
  constructor
  · linarith [hre.1]
  · linarith [him.1]

/-- **Cauchy estimate for the polygamma tower on a vertical line.**  The trigamma bound on a fixed
disc around the point, differentiated `m` times, bounds the order-`m+1` polygamma. -/
theorem norm_iteratedDeriv_succ_digamma_vertical_le {σ t : ℝ} (hσ : 0 < σ) (ht : σ < t) (m : ℕ) :
    ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (m.factorial : ℝ) * (1 / (t - σ / 2) ^ 2 + Real.pi / (2 * (t - σ / 2))) / (σ / 2) ^ m := by
  have hr : (0 : ℝ) < σ / 2 := by linarith
  have htpos : 0 < t - σ / 2 := by linarith
  set c : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hc
  have hsubset : Metric.closedBall c (σ / 2) ⊆ {z : ℂ | 0 < z.re} := by
    intro ζ hζ
    have := (mem_ball_re_im hζ).1
    exact lt_of_lt_of_le hr this
  have hdiff : DifferentiableOn ℂ (deriv Complex.digamma) {z : ℂ | 0 < z.re} := by
    intro ζ hζ
    exact ((RHTower.digamma_analyticOnNhd_re_pos.deriv) ζ hζ).differentiableAt.differentiableWithinAt
  have hdcc : DiffContOnCl ℂ (deriv Complex.digamma) (Metric.ball c (σ / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c (ne_of_gt hr)]
    exact hdiff.mono hsubset
  have hbound : ∀ ζ ∈ Metric.sphere c (σ / 2),
      ‖deriv Complex.digamma ζ‖ ≤ 1 / (t - σ / 2) ^ 2 + Real.pi / (2 * (t - σ / 2)) := by
    intro ζ hζ
    obtain ⟨hre, him⟩ := mem_ball_re_im (Metric.sphere_subset_closedBall hζ)
    have hrepos : 0 < ζ.re := lt_of_lt_of_le hr hre
    have himpos : 0 < ζ.im := lt_of_lt_of_le htpos him
    have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
    have hb := RHTower.norm_deriv_digamma_vertical_le hrepos himpos
    rw [← hz] at hb
    refine hb.trans ?_
    have h1 : 1 / ζ.im ^ 2 ≤ 1 / (t - σ / 2) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (le_of_lt htpos) him 2
    have h2 : Real.pi / (2 * ζ.im) ≤ Real.pi / (2 * (t - σ / 2)) := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by linarith) (by linarith)
    linarith
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr hdcc hbound
  rw [iteratedDeriv_succ']
  exact hcauchy

/-- **Vertical decay of every positive-order polygamma.** -/
theorem tendsto_iteratedDeriv_succ_digamma_vertical {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    Tendsto (fun t : ℝ =>
      iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℝ => t - σ / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hA : Tendsto (fun t : ℝ => 1 / (t - σ / 2) ^ 2) atTop (nhds 0) := by
    have hpow : Tendsto (fun t : ℝ => (t - σ / 2) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp hbase
    have hinv := hpow.inv_tendsto_atTop
    have hfun : (fun t : ℝ => (t - σ / 2) ^ 2)⁻¹ = fun t : ℝ => 1 / (t - σ / 2) ^ 2 := by
      funext t
      simp [one_div]
    rwa [hfun] at hinv
  have hB : Tendsto (fun t : ℝ => Real.pi / (2 * (t - σ / 2))) atTop (nhds 0) := by
    have hlin : Tendsto (fun t : ℝ => 2 * (t - σ / 2)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) hbase
    have hinv : Tendsto (fun t : ℝ => (2 * (t - σ / 2))⁻¹) atTop (nhds 0) :=
      hlin.inv_tendsto_atTop
    have := hinv.const_mul Real.pi
    simpa [div_eq_mul_inv] using this
  have hg : Tendsto (fun t : ℝ => (m.factorial : ℝ) *
      (1 / (t - σ / 2) ^ 2 + Real.pi / (2 * (t - σ / 2))) / (σ / 2) ^ m) atTop (nhds 0) := by
    have := ((hA.add hB).const_mul (m.factorial : ℝ)).div_const ((σ / 2) ^ m)
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop σ] with t ht
  exact norm_iteratedDeriv_succ_digamma_vertical_le hσ ht m

end GaloisForLFunctions
