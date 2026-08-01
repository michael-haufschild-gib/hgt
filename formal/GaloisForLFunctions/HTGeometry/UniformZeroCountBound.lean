import Mathlib.Analysis.Complex.JensenFormula

/-!
# A uniform zero-count bound for a family of analytic functions

Jensen's inequality bounds the number of zeros of one analytic function in a ball by the ratio
between its size on a larger sphere and its size at the centre.  For a *family* the same bound
becomes uniform as soon as the family is uniformly bounded above on the sphere and uniformly
bounded below at the centre.

That is the count-stability input needed by a nested-exhaustion residual argument: a locally
uniformly convergent family with nonvanishing limit at the centre satisfies both hypotheses
eventually, so its zero counts in a fixed ball are bounded by one constant.  No argument principle
and no Rouché theorem are required.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeromorphicOn Metric

/-- **Uniform Jensen zero-count bound.**  A family of analytic functions uniformly bounded above on
a sphere and uniformly bounded below at the centre has uniformly bounded zero count in the smaller
ball. -/
theorem sum_divisor_le_of_uniform_bounds {ι : Type*} {c : ℂ} {r R M m : ℝ} {F : ι → ℂ → ℂ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (hm : 0 < m)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (closedBall c |R|))
    (hcentre : ∀ i, m ≤ ‖F i c‖)
    (hsphere : ∀ i, ∀ z ∈ sphere c |R|, ‖F i z‖ ≤ M) (i : ι) :
    ∑ᶠ u, divisor (F i) (closedBall c |r|) u ≤ Real.log (M / m) / Real.log (R / r) := by
  have hcm : m ≤ ‖F i c‖ := hcentre i
  have hcpos : 0 < ‖F i c‖ := lt_of_lt_of_le hm hcm
  have hne : F i c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcpos
    linarith
  have hbase := (hF i).sum_divisor_le r_pos r_lt_R hM hne (hsphere i)
  refine le_trans hbase ?_
  have hlogpos : 0 < Real.log (R / r) := by
    have h1 : 1 < |R / r| := by
      rw [abs_div]
      exact (one_lt_div r_pos).mpr r_lt_R
    rw [← Real.log_abs]
    exact Real.log_pos h1
  have hnum2 : M / ‖F i c‖ ≤ M / m := by
    rw [div_le_div_iff₀ hcpos hm]
    nlinarith [hcm, hm, hM]
  have hnum : Real.log (M / ‖F i c‖) ≤ Real.log (M / m) :=
    Real.log_le_log (by positivity) hnum2
  have hinv : (0:ℝ) ≤ (Real.log (R / r))⁻¹ := le_of_lt (inv_pos.mpr hlogpos)
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum hinv

open Filter Topology

/-- Single-function form of the Jensen zero-count bound. -/
theorem sum_divisor_le_of_bounds {c : ℂ} {r R M m : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (closedBall c |R|))
    (hcentre : m ≤ ‖f c‖) (hsphere : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u ≤ Real.log (M / m) / Real.log (R / r) :=
  sum_divisor_le_of_uniform_bounds (F := fun _ : Unit => f) r_pos r_lt_R hM hm
    (fun _ => hf) (fun _ => hcentre) (fun _ => hsphere) ()

/-- **Nonvanishing at the centre survives pointwise convergence.** -/
theorem eventually_half_norm_le {ι : Type*} {l : Filter ι} {G : ι → ℂ} {g : ℂ}
    (hpt : Tendsto G l (𝓝 g)) (hne : g ≠ 0) :
    ∀ᶠ i in l, ‖g‖ / 2 ≤ ‖G i‖ := by
  have hpos : 0 < ‖g‖ := norm_pos_iff.mpr hne
  have hlt : ‖g‖ / 2 < ‖g‖ := by linarith
  exact (hpt.norm).eventually (eventually_gt_nhds hlt) |>.mono fun i hi => le_of_lt hi

/-- **A uniform limit is uniformly bounded, up to one unit.** -/
theorem eventually_norm_le_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} {S : Set ℂ}
    {F : ι → ℂ → ℂ} {Flim : ℂ → ℂ} {M0 : ℝ}
    (hunif : TendstoUniformlyOn F Flim l S) (hM0 : ∀ z ∈ S, ‖Flim z‖ ≤ M0) :
    ∀ᶠ i in l, ∀ z ∈ S, ‖F i z‖ ≤ M0 + 1 := by
  have h := (Metric.tendstoUniformlyOn_iff.mp hunif) 1 one_pos
  filter_upwards [h] with i hi z hz
  have hdist : dist (F i z) (Flim z) < 1 := by
    rw [dist_comm]
    exact hi z hz
  have hnorm : ‖F i z‖ ≤ ‖Flim z‖ + 1 := by
    have hsub := norm_sub_norm_le (F i z) (Flim z)
    rw [← dist_eq_norm] at hsub
    linarith
  linarith [hM0 z hz]

/-- **Count stability from convergence.**  A family converging uniformly on the sphere and
pointwise at the centre, with nonvanishing limit at the centre, has eventually bounded zero count in
the smaller ball.  This is the count-stability input of a nested-exhaustion residual argument, with
no argument principle and no Rouché theorem. -/
theorem eventually_sum_divisor_le {ι : Type*} {l : Filter ι} {c : ℂ} {r R M0 : ℝ}
    {F : ι → ℂ → ℂ} {Flim : ℂ → ℂ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM0 : 0 ≤ M0)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (closedBall c |R|))
    (hpt : Tendsto (fun i => F i c) l (𝓝 (Flim c))) (hne : Flim c ≠ 0)
    (hunif : TendstoUniformlyOn F Flim l (sphere c |R|))
    (hbound : ∀ z ∈ sphere c |R|, ‖Flim z‖ ≤ M0) :
    ∀ᶠ i in l, ∑ᶠ u, divisor (F i) (closedBall c |r|) u
      ≤ Real.log ((M0 + 1) / (‖Flim c‖ / 2)) / Real.log (R / r) := by
  have hm : 0 < ‖Flim c‖ / 2 := by
    have := norm_pos_iff.mpr hne
    linarith
  filter_upwards [eventually_half_norm_le hpt hne,
    eventually_norm_le_of_tendstoUniformlyOn hunif hbound] with i hcentre hsphere
  exact sum_divisor_le_of_bounds r_pos r_lt_R (by linarith) hm (hF i) hcentre hsphere

end GaloisForLFunctions.HTGeometry
