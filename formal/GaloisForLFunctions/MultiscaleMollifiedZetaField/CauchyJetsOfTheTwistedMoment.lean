import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMomentHasPolynomialDerivatives

/-!
# Differentiating the actual moment under its integral

On a fixed displacement disk, Cauchy bounds dominate every kernel jet by
an integrable multiple of the compact taper. Thus each moment derivative
is the literal integral of the corresponding product derivative.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem analyticAt_disk_jet {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (n : ℕ) {z : ℂ} (hz : z ∈ ball c R) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => exact hf.analyticOnNhd isOpen_ball z hz
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem measurable_disk_jet {F : ℂ → ℝ → ℂ} {c : ℂ} {R : ℝ}
    (hf : ∀ t, DifferentiableOn ℂ (fun z => F z t) (ball c R))
    (hm : ∀ z ∈ ball c R, AEStronglyMeasurable (F z) volume)
    (n : ℕ) {z : ℂ} (hz : z ∈ ball c R) :
    AEStronglyMeasurable (fun t => iteratedDeriv n (fun v => F v t) z) volume := by
  induction n generalizing z with
  | zero => exact hm z hz
  | succ n ih =>
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
    simp only [iteratedDeriv_succ]
    exact aestronglyMeasurable_deriv_param_complex hr
      (fun v hv => ih (hsub hv))
      (fun t => (analyticAt_disk_jet (hf t) n hz).differentiableAt)

private theorem norm_disk_jet {f : ℂ → ℂ} {c : ℂ} {R r B : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hr : 0 < r)
    (hb : ∀ v ∈ ball c R, ‖f v‖ ≤ B) {z : ℂ}
    (hsub : closedBall z r ⊆ ball c R) (n : ℕ) :
    ‖iteratedDeriv n f z‖ ≤ (n.factorial : ℝ) * B / r ^ n :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hf.diffContOnCl_ball hsub) (fun v hv => hb v (hsub (sphere_subset_closedBall hv)))

private theorem hasDerivAt_integral_disk_jet {F : ℂ → ℝ → ℂ} {c : ℂ} {R : ℝ}
    (hf : ∀ t, DifferentiableOn ℂ (fun z => F z t) (ball c R))
    (hm : ∀ z ∈ ball c R, AEStronglyMeasurable (F z) volume)
    {B : ℝ → ℝ} (hB : Integrable B volume)
    (hb : ∀ t z, z ∈ ball c R → ‖F z t‖ ≤ B t)
    (n : ℕ) {z : ℂ} (hz : z ∈ ball c R) :
    HasDerivAt (fun v => ∫ t, iteratedDeriv n (fun u => F u t) v)
      (∫ t, iteratedDeriv (n + 1) (fun u => F u t) z) z := by
  have hzR : dist z c < R := hz
  let r : ℝ := (R - dist z c) / 3
  have hr : 0 < r := by dsimp only [r]; linarith only [hzR]
  have hsub {v : ℂ} (hv : v ∈ ball z r) : closedBall v r ⊆ ball c R := by
    intro u hu
    have hv' : dist v z < r := hv
    have hu' : dist u v ≤ r := hu
    have htri := (dist_triangle u v c).trans (add_le_add (le_refl (dist u v)) (dist_triangle v z c))
    change dist u c < R
    dsimp only [r] at hv' hu'
    linarith only [htri, hv', hu', hzR]
  have hball {v : ℂ} (hv : v ∈ ball z r) : v ∈ ball c R :=
    hsub hv (mem_closedBall_self hr.le)
  have hnorm (j : ℕ) (t : ℝ) {v : ℂ} (hv : v ∈ ball z r) :
      ‖iteratedDeriv j (fun u => F u t) v‖ ≤ (j.factorial : ℝ) / r ^ j * B t := by
    exact (norm_disk_jet (hf t) hr (hb t) (hsub hv) j).trans_eq (by ring)
  have hi : Integrable (fun t => iteratedDeriv n (fun u => F u t) z) volume :=
    (hB.const_mul ((n.factorial : ℝ) / r ^ n)).mono'
      (measurable_disk_jet hf hm n hz)
      (Eventually.of_forall fun t => hnorm n t (mem_ball_self hr))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v t => iteratedDeriv n (fun u => F u t) v)
    (F' := fun v t => iteratedDeriv (n + 1) (fun u => F u t) v)
    (bound := fun t => (((n + 1).factorial : ℝ) / r ^ (n + 1)) * B t)
    (ball_mem_nhds z hr)
    (by filter_upwards [ball_mem_nhds z hr] with v hv
        exact measurable_disk_jet hf hm n (hball hv))
    hi (measurable_disk_jet hf hm (n + 1) hz)
    (Eventually.of_forall fun t v hv => hnorm (n + 1) t hv)
    (hB.const_mul _)
    (by filter_upwards with t
        intro v hv
        simpa only [iteratedDeriv_succ] using
          (analyticAt_disk_jet (hf t) n (hball hv)).differentiableAt.hasDerivAt)).2

private theorem iteratedDeriv_integral_disk {F : ℂ → ℝ → ℂ} {c : ℂ} {R : ℝ}
    (hf : ∀ t, DifferentiableOn ℂ (fun z => F z t) (ball c R))
    (hm : ∀ z ∈ ball c R, AEStronglyMeasurable (F z) volume)
    {B : ℝ → ℝ} (hB : Integrable B volume)
    (hb : ∀ t z, z ∈ ball c R → ‖F z t‖ ≤ B t)
    (n : ℕ) {z : ℂ} (hz : z ∈ ball c R) :
    iteratedDeriv n (fun v => ∫ t, F v t) z =
      ∫ t, iteratedDeriv n (fun v => F v t) z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun v => ∫ t, F v t) =ᶠ[𝓝 z]
        (fun v => ∫ t, iteratedDeriv n (fun u => F u t) v) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with v hv
      exact ih hv
    rw [he.deriv_eq]
    exact (hasDerivAt_integral_disk_jet hf hm hB hb n hz).deriv

private theorem field_point_ne_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) (t : ℝ) :
    (1 / 2 : ℂ) - z + (t : ℂ) * I ≠ 1 := by
  have hr := (Complex.abs_re_le_norm z).trans hz
  intro he
  have hre := congrArg Complex.re he
  norm_num at hre
  linarith only [hre, (abs_le.mp hr).1]

private theorem continuousAt_field_pair (N : ℕ) (w : ℕ → ℝ) {u : ℂ × ℝ}
    (hu : ‖u.1‖ ≤ 1 / 4) :
    ContinuousAt (fun v : ℂ × ℝ => twistedMomentField N w v.1 v.2) u := by
  have hp : ContinuousAt (fun v : ℂ × ℝ => (1 / 2 : ℂ) - v.1 + (v.2 : ℂ) * I) u := by
    fun_prop
  exact ((differentiableAt_riemannZeta (field_point_ne_one hu u.2)).continuousAt.comp
    (f := fun v : ℂ × ℝ => (1 / 2 : ℂ) - v.1 + (v.2 : ℂ) * I) hp).mul
    (((differentiable_edPoly (fun n => (w n : ℂ))
      (fun n hn => (Finset.mem_Icc.mp hn).1)) _).continuousAt.comp
        (f := fun v : ℂ × ℝ => (1 / 2 : ℂ) - v.1 + (v.2 : ℂ) * I) hp)

private theorem field_differentiableOn (N : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    DifferentiableOn ℂ (fun z => twistedMomentField N w z t) (ball 0 (1 / 4)) := by
  intro z hz
  have hn : ‖z‖ ≤ 1 / 4 := le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz)
  have hp : DifferentiableAt ℂ (fun v : ℂ => (1 / 2 : ℂ) - v + (t : ℂ) * I) z := by fun_prop
  exact (((differentiableAt_riemannZeta (field_point_ne_one hn t)).comp z hp).mul
    ((differentiable_edPoly (fun n => (w n : ℂ))
      (fun n hn => (Finset.mem_Icc.mp hn).1) _).comp z hp)).differentiableWithinAt

/-- Every complex displacement derivative of the actual moment is its integral kernel jet. -/
theorem iteratedDeriv_holomorphicTwistedMoment_eq_integral {p q η : ℝ} (hη : 0 < η)
    (N : ℕ) (w : ℕ → ℝ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 4) :
    iteratedDeriv n (holomorphicTwistedMoment p q η N w) z =
      ∫ t, iteratedDeriv n (fun v : ℂ => blockWindowC p q η t *
        (twistedMomentField N w v t * twistedMomentField N w v (-t))) z := by
  let P : ℂ × ℝ → ℂ := fun u =>
    twistedMomentField N w u.1 u.2 * twistedMomentField N w u.1 (-u.2)
  have hc {u : ℂ × ℝ} (hu : ‖u.1‖ ≤ 1 / 4) : ContinuousAt P u := by
    have hneg := (continuousAt_field_pair N w (u := (u.1, -u.2)) hu).comp
      (f := fun v : ℂ × ℝ => (v.1, -v.2)) (by fun_prop)
    exact (continuousAt_field_pair N w hu).mul hneg
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) (1 / 4)).prod
    (isCompact_Icc : IsCompact (Icc (p - η) (q + η)))).exists_bound_of_continuousOn
      (show ContinuousOn P (closedBall 0 (1 / 4) ×ˢ Icc (p - η) (q + η)) from
        fun u hu => (hc (by simpa only [mem_closedBall, dist_zero_right] using hu.1)).continuousWithinAt)
  apply iteratedDeriv_integral_disk (c := 0) (R := 1 / 4)
    (B := fun t => blockWindow p q η t * C)
  · intro t
    exact ((field_differentiableOn N w t).mul (field_differentiableOn N w (-t))).const_mul _
  · intro v hv
    have hn : ‖v‖ ≤ 1 / 4 := le_of_lt (by simpa only [mem_ball, dist_zero_right] using hv)
    have hct : Continuous (fun t => P (v, t)) := continuous_iff_continuousAt.mpr fun t =>
      (hc hn).comp (f := fun x : ℝ => (v, x)) (by fun_prop)
    exact ((contDiff_blockWindowC p q η).continuous.mul hct).aestronglyMeasurable
  · exact ((contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_blockWindow hη)).mul_const C
  · intro t v hv
    by_cases ht : t ∈ Icc (p - η) (q + η)
    · rw [norm_mul, norm_blockWindowC_eq]
      exact mul_le_mul_of_nonneg_left
        (hC (v, t) ⟨ball_subset_closedBall hv, ht⟩) (blockWindow_nonneg p q η t)
    · rw [blockWindowC_eq_zero hη ht]
      have hzero : blockWindow p q η t = 0 := by
        by_contra hn
        exact ht (support_blockWindow_subset hη hn)
      simp only [hzero, zero_mul, norm_zero, le_refl]
  · simpa only [mem_ball, dist_zero_right] using hz

end GaloisForLFunctions.MultiscaleMollifiedZetaField
