import Mathlib
import GaloisForLFunctions.HTGeometry.PoissonJensenFormula

/-!
# The Herglotz transform and its differentiated kernel

The Poisson–Jensen formula computes the Poisson average of `log ‖f‖`.  Nevanlinna's estimate for
the logarithmic derivative needs the *analytic completion* of that Poisson integral — the Herglotz
transform — and its derivative in the interior variable.

This file records the transform, the kernel obtained by differentiating the Herglotz–Riesz kernel
in that variable,

`d/dw ((z − c) + (w − c))/((z − c) − (w − c)) = 2(z − c)/(z − w)²`,

the modulus bound `‖2(z − c)/(z − w)²‖ ≤ 2R/δ²` valid once the circle stays a distance `δ` from
`w`, and the elementary geometry that supplies such a `δ` uniformly on a small ball around an
interior point.  These are the inputs for differentiating the transform under the integral sign.
-/

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory

noncomputable section

/-- The Herglotz transform of a real boundary function: the analytic completion of its Poisson
integral. -/
noncomputable def herglotzTransform (c : ℂ) (R : ℝ) (v : ℂ → ℝ) (w : ℂ) : ℂ :=
  circleAverage (fun z => herglotzRieszKernel c w z * (v z : ℂ)) c R

/-- The kernel obtained by differentiating the Herglotz–Riesz kernel in the interior variable. -/
noncomputable def herglotzDerivKernel (c w z : ℂ) : ℂ := 2 * (z - c) / (z - w) ^ (2 : ℕ)

theorem herglotzRieszKernel_eq (c w z : ℂ) :
    herglotzRieszKernel c w z = (z + w - 2 * c) / (z - w) := by
  rw [herglotzRieszKernel_def]
  congr 1 <;> ring

theorem hasDerivAt_herglotzRieszKernel {c z w : ℂ} (h : z ≠ w) :
    HasDerivAt (fun w' => herglotzRieszKernel c w' z) (herglotzDerivKernel c w z) w := by
  have hzw : z - w ≠ 0 := sub_ne_zero.mpr h
  have hN : HasDerivAt (fun w' : ℂ => z + w' - 2 * c) 1 w := by
    simpa using (((hasDerivAt_id w).const_add z).sub_const (2 * c))
  have hD : HasDerivAt (fun w' : ℂ => z - w') (-1) w := by
    simpa using ((hasDerivAt_id w).const_sub z)
  have hdiv := hN.div hD hzw
  have hval : (1 * (z - w) - (z + w - 2 * c) * (-1)) / (z - w) ^ (2 : ℕ)
      = herglotzDerivKernel c w z := by
    rw [herglotzDerivKernel]
    congr 1
    ring
  rw [hval] at hdiv
  have hfun : (fun w' : ℂ => herglotzRieszKernel c w' z)
      = fun w' : ℂ => (z + w' - 2 * c) / (z - w') := by
    funext w'
    exact herglotzRieszKernel_eq c w' z
  rw [hfun]
  exact hdiv

theorem norm_herglotzDerivKernel_le {c w z : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hz : ‖z - c‖ = R) (hδ : 0 < δ) (hlow : δ ≤ ‖z - w‖) :
    ‖herglotzDerivKernel c w z‖ ≤ 2 * R / δ ^ (2 : ℕ) := by
  rw [herglotzDerivKernel, norm_div, norm_mul, norm_pow, hz]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ hδ.le hlow 2

theorem dist_sphere_ball {c w z : ℂ} {R ε : ℝ} (hz : ‖z - c‖ = R)
    (hε : ε ≤ R - ‖w - c‖) :
    ε ≤ ‖z - w‖ := by
  have := norm_sub_norm_le (z - c) (w - c)
  have hzw : (z - c) - (w - c) = z - w := by ring
  rw [hzw, hz] at this
  linarith

/-- The circle points stay a fixed distance away from every point of a small interior ball. -/
theorem le_norm_circleMap_sub {c w : ℂ} {R ε : ℝ} (hR : 0 < R) (hw : ‖w - c‖ < R)
    (hε : ε = (R - ‖w - c‖) / 2) :
    ∀ w' ∈ ball w ε, ∀ θ : ℝ, ε ≤ ‖circleMap c R θ - w'‖ := by
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hsph : ∀ θ : ℝ, ‖circleMap c R θ - c‖ = R := by
    intro θ
    have h := circleMap_mem_sphere c hR.le θ
    rw [mem_sphere_iff_norm] at h
    exact h
  intro w' hw' θ
  have h2 : ‖w' - w‖ < ε := by rwa [mem_ball_iff_norm] at hw'
  have h3 : ‖w' - c‖ ≤ ‖w' - w‖ + ‖w - c‖ := by
    have hsplit : w' - c = (w' - w) + (w - c) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  refine dist_sphere_ball (hsph θ) ?_
  rw [hε] at h2 ⊢
  linarith

/-- The circle points are never equal to a point of the small interior ball. -/
theorem circleMap_ne_of_mem_ball {c w : ℂ} {R ε : ℝ} (hR : 0 < R) (hw : ‖w - c‖ < R)
    (hε : ε = (R - ‖w - c‖) / 2) :
    ∀ w' ∈ ball w ε, ∀ θ : ℝ, circleMap c R θ ≠ w' := by
  have hεpos : 0 < ε := by rw [hε]; linarith
  intro w' hw' θ h0
  have hle := le_norm_circleMap_sub hR hw hε w' hw' θ
  rw [h0] at hle
  simp at hle
  linarith

end

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory

noncomputable section

theorem norm_circleMap_sub_center {c : ℂ} {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖circleMap c R θ - c‖ = R := by
  have h := circleMap_mem_sphere c hR.le θ
  rw [mem_sphere_iff_norm] at h
  exact h

/-- **Differentiation of the Herglotz transform.**  At every interior point the transform is
complex differentiable, with derivative the circle average against the differentiated kernel. -/
theorem hasDerivAt_herglotzTransform {c : ℂ} {R : ℝ} {v : ℂ → ℝ} (hR : 0 < R)
    (hv : CircleIntegrable v c R) {w : ℂ} (hw : w ∈ ball c R) :
    HasDerivAt (herglotzTransform c R v)
      (circleAverage (fun z => herglotzDerivKernel c w z * (v z : ℂ)) c R) w := by
  classical
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  set ε : ℝ := (R - ‖w - c‖) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hlow := le_norm_circleMap_sub hR hwc hεdef
  have hne := circleMap_ne_of_mem_ball hR hwc hεdef
  set V : ℝ → ℂ := fun θ => ((v (circleMap c R θ) : ℝ) : ℂ) with hVdef
  have hVint : IntervalIntegrable V volume 0 (2 * π) := by
    have hv' : IntervalIntegrable (fun θ : ℝ => v (circleMap c R θ)) volume 0 (2 * π) := hv
    rw [intervalIntegrable_iff] at hv' ⊢
    exact hv'.ofReal
  have hcontK : ∀ w' ∈ ball w ε,
      Continuous (fun θ : ℝ => herglotzRieszKernel c w' (circleMap c R θ)) := by
    intro w' hw'
    simp only [herglotzRieszKernel_eq]
    refine Continuous.div ?_ ?_ (fun θ => sub_ne_zero.mpr (hne w' hw' θ))
    · exact ((continuous_circleMap c R).add continuous_const).sub continuous_const
    · exact (continuous_circleMap c R).sub continuous_const
  have hcontK' : ∀ w' ∈ ball w ε,
      Continuous (fun θ : ℝ => herglotzDerivKernel c w' (circleMap c R θ)) := by
    intro w' hw'
    simp only [herglotzDerivKernel]
    refine Continuous.div ?_ ?_ (fun θ => pow_ne_zero 2 (sub_ne_zero.mpr (hne w' hw' θ)))
    · exact continuous_const.mul ((continuous_circleMap c R).sub continuous_const)
    · exact ((continuous_circleMap c R).sub continuous_const).pow 2
  set F : ℂ → ℝ → ℂ := fun w' θ => herglotzRieszKernel c w' (circleMap c R θ) * V θ with hF
  set F' : ℂ → ℝ → ℂ := fun w' θ => herglotzDerivKernel c w' (circleMap c R θ) * V θ with hF'
  set bound : ℝ → ℝ := fun θ => (2 * R / ε ^ (2 : ℕ)) * ‖V θ‖ with hbound
  have hFint : ∀ w' ∈ ball w ε, IntervalIntegrable (F w') volume 0 (2 * π) := by
    intro w' hw'
    exact hVint.continuousOn_mul ((hcontK w' hw').continuousOn)
  have hF'int : ∀ w' ∈ ball w ε, IntervalIntegrable (F' w') volume 0 (2 * π) := by
    intro w' hw'
    exact hVint.continuousOn_mul ((hcontK' w' hw').continuousOn)
  have hboundint : IntervalIntegrable bound volume 0 (2 * π) := (hVint.norm).const_mul _
  obtain ⟨-, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := w) (bound := bound) (s := ball w ε) (a := 0) (b := 2 * π)
    (μ := volume) (ball_mem_nhds w hεpos)
    (Filter.eventually_of_mem (ball_mem_nhds w hεpos)
      (fun w' hw' => (intervalIntegrable_iff.mp (hFint w' hw')).aestronglyMeasurable))
    (hFint w (mem_ball_self hεpos))
    (intervalIntegrable_iff.mp (hF'int w (mem_ball_self hεpos))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ _ w' hw' => by
      rw [hF', hbound, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_herglotzDerivKernel_le hR (norm_circleMap_sub_center hR θ) hεpos
        (hlow w' hw' θ)))
    hboundint
    (Filter.Eventually.of_forall (fun θ _ w' hw' =>
      (hasDerivAt_herglotzRieszKernel (hne w' hw' θ)).mul_const (V θ)))
  simp only [circleAverage_def]
  exact hderiv.const_smul _

end

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory

noncomputable section

theorem circleIntegrable_herglotz_mul {c : ℂ} {R : ℝ} {v : ℂ → ℝ} (hR : 0 < R)
    (hv : CircleIntegrable v c R) {w : ℂ} (hw : w ∈ ball c R) :
    CircleIntegrable (fun z => herglotzRieszKernel c w z * (v z : ℂ)) c R := by
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  set ε : ℝ := (R - ‖w - c‖) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hne := circleMap_ne_of_mem_ball hR hwc hεdef w (mem_ball_self hεpos)
  have hVint : IntervalIntegrable (fun θ : ℝ => ((v (circleMap c R θ) : ℝ) : ℂ))
      volume 0 (2 * π) := by
    have hv' : IntervalIntegrable (fun θ : ℝ => v (circleMap c R θ)) volume 0 (2 * π) := hv
    rw [intervalIntegrable_iff] at hv' ⊢
    exact hv'.ofReal
  have hcont : Continuous (fun θ : ℝ => herglotzRieszKernel c w (circleMap c R θ)) := by
    simp only [herglotzRieszKernel_eq]
    refine Continuous.div ?_ ?_ (fun θ => sub_ne_zero.mpr (hne θ))
    · exact ((continuous_circleMap c R).add continuous_const).sub continuous_const
    · exact (continuous_circleMap c R).sub continuous_const
  exact hVint.continuousOn_mul hcont.continuousOn

/-- The real part of the Herglotz transform is the Poisson integral of the boundary function. -/
theorem re_herglotzTransform {c : ℂ} {R : ℝ} {v : ℂ → ℝ} (hR : 0 < R)
    (hv : CircleIntegrable v c R) {w : ℂ} (hw : w ∈ ball c R) :
    (herglotzTransform c R v w).re
      = circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • v) c R := by
  have hint := circleIntegrable_herglotz_mul hR hv hw
  rw [herglotzTransform]
  show Complex.reCLM (circleAverage (fun z => herglotzRieszKernel c w z * (v z : ℂ)) c R) = _
  rw [← Complex.reCLM.circleAverage_comp_comm hint]
  apply circleAverage_congr_sphere
  intro z _
  simp [Complex.mul_re]

/-- A holomorphic function on a ball whose real part vanishes has zero derivative. -/
theorem deriv_eq_zero_of_re_eq_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball c R)) (hre : ∀ z ∈ ball c R, (F z).re = 0)
    {w : ℂ} (hw : w ∈ ball c R) :
    deriv F w = 0 := by
  obtain ⟨k, hk⟩ := hF.eq_const_of_re_eq_const hre isOpen_ball
    ⟨⟨c, mem_ball_self hR⟩, (convex_ball c R).isPreconnected⟩
  have hEq : F =ᶠ[nhds w] fun _ => k := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact hk z hz
  rw [hEq.deriv_eq]
  exact deriv_const w k

end

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory

noncomputable section

/-- **Analytic logarithm on a disc.**  A zero-free analytic function on a ball is the exponential
of an analytic function whose derivative is its logarithmic derivative. -/
theorem exists_analytic_log {c : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ G : ℂ → ℂ, (∀ z ∈ ball c R, HasDerivAt G (deriv g z / g z) z) ∧
      (∀ z ∈ ball c R, g z = Complex.exp (G z)) := by
  classical
  have hgdiff : DifferentiableOn ℂ g (ball c R) := hg.differentiableOn
  have hlog : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) := by
    intro z hz
    have hd : DifferentiableAt ℂ (fun z => deriv g z) z :=
      ((hg z hz).deriv).differentiableAt
    exact ((hd.div (hg z hz).differentiableAt (hne z hz)).differentiableWithinAt)
  obtain ⟨G₀, hG₀⟩ := hlog.isExactOn_ball
  set Φ : ℂ → ℂ := fun z => g z * Complex.exp (-G₀ z) with hΦ
  have hΦderiv : ∀ z ∈ ball c R, HasDerivAt Φ 0 z := by
    intro z hz
    have h1 : HasDerivAt g (deriv g z) z := (hg z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun z => Complex.exp (-G₀ z))
        (Complex.exp (-G₀ z) * -(deriv g z / g z)) z := by
      have := ((hG₀ z hz).neg).cexp
      simpa using this
    have h3 := h1.mul h2
    have hgz : g z ≠ 0 := hne z hz
    have hval : deriv g z * Complex.exp (-G₀ z)
        + g z * (Complex.exp (-G₀ z) * -(deriv g z / g z)) = 0 := by
      field_simp
      ring
    rw [hval] at h3
    exact h3
  have hconst : ∀ z ∈ ball c R, Φ z = Φ c := by
    intro z hz
    have hdiffΦ : DifferentiableOn ℂ Φ (ball c R) :=
      fun x hx => (hΦderiv x hx).differentiableAt.differentiableWithinAt
    refine (convex_ball c R).is_const_of_fderivWithin_eq_zero hdiffΦ ?_ hz (mem_ball_self hR)
    intro x hx
    have h1 : fderivWithin ℂ Φ (ball c R) x = fderiv ℂ Φ x :=
      fderivWithin_of_isOpen isOpen_ball hx
    have hfd : HasFDerivAt Φ (0 : ℂ →L[ℂ] ℂ) x := by
      simpa using (hΦderiv x hx).hasFDerivAt
    rw [h1, hfd.fderiv]
  have hk : Φ c ≠ 0 := by
    rw [hΦ]
    exact mul_ne_zero (hne c (mem_ball_self hR)) (Complex.exp_ne_zero _)
  obtain ⟨l, hl⟩ : ∃ l : ℂ, Complex.exp l = Φ c := ⟨Complex.log (Φ c), Complex.exp_log hk⟩
  refine ⟨fun z => G₀ z + l, fun z hz => ?_, fun z hz => ?_⟩
  · simpa using (hG₀ z hz).add_const l
  · have h1' : g z * Complex.exp (-G₀ z) = Φ c := hconst z hz
    have hcancel : g z = (g z * Complex.exp (-G₀ z)) * Complex.exp (G₀ z) := by
      rw [mul_assoc, ← Complex.exp_add]
      simp
    rw [hcancel, h1', ← hl, ← Complex.exp_add]
    congr 1
    ring

end

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory InnerProductSpace

noncomputable section

/-- **The logarithmic derivative as a boundary integral.**  For a zero-free analytic function on a
closed disc, the logarithmic derivative at an interior point is the circle average of the
differentiated Herglotz kernel against `log ‖g‖`. -/
theorem logDeriv_eq_circleAverage_of_ne_zero {c : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hne : ∀ z ∈ closedBall c R, g z ≠ 0)
    {w : ℂ} (hw : w ∈ ball c R) :
    deriv g w / g w
      = circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖g z‖ : ℝ) : ℂ)) c R := by
  classical
  have habs : |R| = R := abs_of_pos hR
  set v : ℂ → ℝ := fun z => Real.log ‖g z‖ with hvdef
  have hvint : CircleIntegrable v c R := by
    have hmero : MeromorphicOn g (sphere c |R|) := by
      rw [habs]
      exact (hg.mono sphere_subset_closedBall).meromorphicOn
    exact hmero.circleIntegrable_log_norm
  set H : ℂ → ℂ := herglotzTransform c R v with hHdef
  have hHderiv : ∀ w' ∈ ball c R, HasDerivAt H
      (circleAverage (fun z => herglotzDerivKernel c w' z * (v z : ℂ)) c R) w' :=
    fun w' hw' => hasDerivAt_herglotzTransform hR hvint hw'
  have hharm : HarmonicOnNhd v (closedBall c |R|) := by
    rw [habs]
    intro x hx
    exact AnalyticAt.harmonicAt_log_norm (hg x hx) (hne x hx)
  have hReH : ∀ w' ∈ ball c R, (H w').re = v w' := by
    intro w' hw'
    rw [hHdef, re_herglotzTransform hR hvint hw']
    have hmem : w' ∈ ball c |R| := by rwa [habs]
    have hval := HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul hharm hmem
    rw [habs] at hval
    exact hval
  obtain ⟨G, hGderiv, hGexp⟩ := exists_analytic_log hR (hg.mono ball_subset_closedBall)
    (fun z hz => hne z (ball_subset_closedBall hz))
  have hReG : ∀ z ∈ ball c R, (G z).re = v z := by
    intro z hz
    show (G z).re = Real.log ‖g z‖
    rw [hGexp z hz, Complex.norm_exp, Real.log_exp]
  have hHdiffOn : DifferentiableOn ℂ H (ball c R) :=
    fun z hz => (hHderiv z hz).differentiableAt.differentiableWithinAt
  have hGdiffOn : DifferentiableOn ℂ G (ball c R) :=
    fun z hz => (hGderiv z hz).differentiableAt.differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ (fun z => H z - G z) (ball c R) :=
    (hHdiffOn.sub hGdiffOn).analyticOnNhd isOpen_ball
  have hFre : ∀ z ∈ ball c R, ((fun z => H z - G z) z).re = 0 := by
    intro z hz
    simp only [Complex.sub_re, hReH z hz, hReG z hz, sub_self]
  have hFd : deriv (fun z => H z - G z) w = 0 :=
    deriv_eq_zero_of_re_eq_zero hR hFan hFre hw
  have hsub : deriv (fun z => H z - G z) w = deriv H w - deriv G w :=
    deriv_sub (hHderiv w hw).differentiableAt (hGderiv w hw).differentiableAt
  rw [hsub, (hHderiv w hw).deriv, (hGderiv w hw).deriv] at hFd
  exact (sub_eq_zero.mp hFd).symm

end

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeasureTheory

noncomputable section

theorem hasDerivAt_innerLogKernel (c u : ℂ) (R : ℝ) (w : ℂ) :
    HasDerivAt (innerLogKernel c u R) (-(starRingEnd ℂ) (u - c) / (R : ℂ)) w := by
  unfold innerLogKernel
  have h1 : HasDerivAt (fun z : ℂ => (R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (u - c) * (z - c))
      (-((starRingEnd ℂ) (u - c))) w := by
    have h2 : HasDerivAt (fun z : ℂ => (starRingEnd ℂ) (u - c) * (z - c))
        ((starRingEnd ℂ) (u - c)) w := by
      simpa using ((hasDerivAt_id w).sub_const c).const_mul ((starRingEnd ℂ) (u - c))
    simpa using h2.const_sub ((R : ℂ) ^ (2 : ℕ))
  simpa [div_eq_mul_inv] using h1.div_const (R : ℂ)

/-- The logarithmic derivative of the Blaschke-corrected kernel at an interior point. -/
theorem logDeriv_innerLogKernel {c u : ℂ} {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hne : innerLogKernel c u R w ≠ 0) :
    deriv (innerLogKernel c u R) w / innerLogKernel c u R w
      = -(starRingEnd ℂ) (u - c) / ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (u - c) * (w - c)) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  rw [(hasDerivAt_innerLogKernel c u R w).deriv, innerLogKernel]
  have hnum : (R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (u - c) * (w - c) ≠ 0 := by
    intro h0
    apply hne
    rw [innerLogKernel, h0, zero_div]
  field_simp

/-- **The divisor term of the differentiated Poisson–Jensen formula.**  For an interior divisor
point the circle average of the differentiated kernel against `log ‖· − u‖` is the logarithmic
derivative of the Blaschke correction. -/
theorem circleAverage_herglotzDerivKernel_log_norm_sub {c u : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : u ∈ ball c R) {w : ℂ} (hw : w ∈ ball c R) :
    circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖z - u‖ : ℝ) : ℂ)) c R
      = -(starRingEnd ℂ) (u - c) / ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (u - c) * (w - c)) := by
  have hunorm : ‖u - c‖ < R := mem_ball_iff_norm.mp hu
  have hnezero : ∀ z ∈ closedBall c R, innerLogKernel c u R z ≠ 0 := by
    intro z hz
    refine innerLogKernel_ne_zero hR ?_
    have hzc : ‖z - c‖ ≤ R := mem_closedBall_iff_norm.mp hz
    nlinarith [norm_nonneg (u - c), norm_nonneg (z - c)]
  have hdiff : Differentiable ℂ (innerLogKernel c u R) :=
    fun z => (hasDerivAt_innerLogKernel c u R z).differentiableAt
  have hanalytic : AnalyticOnNhd ℂ (innerLogKernel c u R) (closedBall c R) := by
    intro z _
    exact hdiff.differentiableOn.analyticAt Filter.univ_mem
  have hcongr : circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖z - u‖ : ℝ) : ℂ)) c R
      = circleAverage (fun z => herglotzDerivKernel c w z *
          ((Real.log ‖innerLogKernel c u R z‖ : ℝ) : ℂ)) c R := by
    refine Real.circleAverage_congr_sphere (fun z hz => ?_)
    rw [abs_of_pos hR] at hz
    rw [norm_innerLogKernel_sphere hR hz]
  rw [hcongr, ← logDeriv_eq_circleAverage_of_ne_zero hR hanalytic hnezero hw]
  exact logDeriv_innerLogKernel hR (hnezero w (ball_subset_closedBall hw))

end

end GaloisForLFunctions.HTGeometry.PoissonJensen
