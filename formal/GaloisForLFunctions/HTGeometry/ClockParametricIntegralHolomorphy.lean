import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import GaloisForLFunctions.HTGeometry.ClockParametricHolomorphy

/-!
# The integral of a holomorphic family is holomorphic

The clock iterates are defined by integrating, over the null coordinates, an expression holomorphic
in the transverse variable. For the induction to continue — the next step differentiates twice in
that variable again — each iterate must itself be holomorphic.

The proof is differentiation under the integral sign with a *complex* parameter. mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` is stated over any `RCLike` field, so it produces
the complex derivative directly, and no appeal to Morera's theorem is needed. Its domination
hypothesis is Cauchy's estimate on a disc, uniform in the integration variable by compactness.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric MeasureTheory intervalIntegral

/-- The first derivative of a holomorphic family is continuous in the parameter. -/
theorem continuous_deriv_parametric {P : Type*} [TopologicalSpace P] {R : ℝ} (hR : 0 < R) {z : ℂ}
    {W : P → ℂ → ℂ} (hWc : Continuous fun q : P × ℂ => W q.1 q.2)
    (hWd : ∀ p : P, ∀ ζ ∈ ball z R, DifferentiableAt ℂ (W p) ζ) :
    Continuous fun p : P => deriv (W p) z := by
  have h := continuous_iteratedDeriv_parametric hR 1 hWc hWd
  have hrw : (fun p : P => iteratedDeriv 1 (W p) z) = fun p : P => deriv (W p) z := by
    funext p
    rw [iteratedDeriv_one]
  rwa [hrw] at h

/-- **The integral of a family holomorphic on a strip is holomorphic on the smaller strip.** -/
theorem hasDerivAt_intervalIntegral_of_holomorphic {a b ρ ρ' : ℝ} (hρ : ρ < ρ')
    {F : ℝ → ℂ → ℂ} (hFc : Continuous fun q : ℝ × ℂ => F q.1 q.2)
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) (imStrip ρ'))
    {z : ℂ} (hz : z ∈ imStrip ρ) :
    HasDerivAt (fun w => ∫ t in a..b, F t w) (∫ t in a..b, deriv (F t) z) z := by
  classical
  have hgap : (0 : ℝ) < ρ' - ρ := by linarith
  set r : ℝ := (ρ' - ρ) / 4 with hrdef
  have hrpos : (0 : ℝ) < r := by rw [hrdef]; linarith
  have hbig : closedBall z ((ρ' - ρ) / 2) ⊆ imStrip ρ' :=
    closedBall_subset_imStrip hρ (le_of_lt (mem_imStrip.mp hz))
  have hslice : ∀ t : ℝ, Continuous (F t) := fun t =>
    hFc.comp (continuous_const.prodMk continuous_id)
  -- a uniform bound on the family over a compact disc
  obtain ⟨M, hM⟩ := ((isCompact_uIcc (a := a) (b := b)).prod
    (isCompact_closedBall z ((ρ' - ρ) / 2))).exists_bound_of_continuousOn hFc.continuousOn
  -- every small disc around a nearby point stays inside the big one
  have hnear : ∀ w ∈ ball z r, closedBall w r ⊆ closedBall z ((ρ' - ρ) / 2) := by
    intro w hw
    refine closedBall_subset_closedBall' ?_
    have : dist w z < r := mem_ball.mp hw
    rw [hrdef] at this ⊢
    linarith
  have hdiffAt : ∀ (t : ℝ), ∀ ζ ∈ closedBall z ((ρ' - ρ) / 2), DifferentiableAt ℂ (F t) ζ := by
    intro t ζ hζ
    exact (hFd t).differentiableAt ((isOpen_imStrip ρ').mem_nhds (hbig hζ))
  -- the derivative is bounded on the small ball, by Cauchy's estimate
  have hbound : ∀ (t : ℝ), t ∈ uIcc a b → ∀ w ∈ ball z r, ‖deriv (F t) w‖ ≤ M / r := by
    intro t ht w hw
    have hsub := hnear w hw
    have hdc : DiffContOnCl ℂ (F t) (ball w r) := by
      refine ⟨fun ζ hζ => ((hdiffAt t ζ (hsub (ball_subset_closedBall hζ))).differentiableWithinAt),
        ?_⟩
      rw [closure_ball w hrpos.ne']
      exact (hslice t).continuousOn
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdc fun ζ hζ => ?_
    exact hM (t, ζ) ⟨ht, hsub (sphere_subset_closedBall hζ)⟩
  have hderivCont : Continuous fun t : ℝ => deriv (F t) z := by
    refine continuous_deriv_parametric (R := (ρ' - ρ) / 2) (by linarith) hFc fun t ζ hζ => ?_
    exact hdiffAt t ζ (ball_subset_closedBall hζ)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball z r) (bound := fun _ => M / r) (F := fun w t => F t w)
    (F' := fun w t => deriv (F t) w) (ball_mem_nhds z hrpos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun w =>
      (Continuous.aestronglyMeasurable
        (hFc.comp (continuous_id.prodMk continuous_const)))
  · exact ((hFc.comp (continuous_id.prodMk continuous_const))).intervalIntegrable a b
  · exact hderivCont.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht w hw => ?_
    exact hbound t (uIoc_subset_uIcc ht) w hw
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ w hw => ?_
    exact (hdiffAt t w (hnear w hw (mem_closedBall_self hrpos.le))).hasDerivAt

theorem differentiableAt_intervalIntegral_of_holomorphic {a b ρ ρ' : ℝ} (hρ : ρ < ρ')
    {F : ℝ → ℂ → ℂ} (hFc : Continuous fun q : ℝ × ℂ => F q.1 q.2)
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) (imStrip ρ'))
    {z : ℂ} (hz : z ∈ imStrip ρ) :
    DifferentiableAt ℂ (fun w => ∫ t in a..b, F t w) z :=
  (hasDerivAt_intervalIntegral_of_holomorphic hρ hFc hFd hz).differentiableAt

/-- **Holomorphy of the parametric integral, as a statement about the smaller strip.** -/
theorem differentiableOn_intervalIntegral_of_holomorphic {a b ρ ρ' : ℝ} (hρ : ρ < ρ')
    {F : ℝ → ℂ → ℂ} (hFc : Continuous fun q : ℝ × ℂ => F q.1 q.2)
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) (imStrip ρ')) :
    DifferentiableOn ℂ (fun w => ∫ t in a..b, F t w) (imStrip ρ) :=
  fun _ hz => (differentiableAt_intervalIntegral_of_holomorphic hρ hFc hFd hz).differentiableWithinAt

/-- **Holomorphy of the parametric integral, without shrinking the strip.** Applying the previous
statement at an intermediate radius chosen for each point separately covers the whole strip. -/
theorem differentiableOn_intervalIntegral_of_holomorphic_self {a b ρ : ℝ}
    {F : ℝ → ℂ → ℂ} (hFc : Continuous fun q : ℝ × ℂ => F q.1 q.2)
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) (imStrip ρ)) :
    DifferentiableOn ℂ (fun w => ∫ t in a..b, F t w) (imStrip ρ) := by
  intro z hz
  have him : |z.im| < ρ := mem_imStrip.mp hz
  have h1 : |z.im| < (|z.im| + ρ) / 2 := by linarith
  have h2 : (|z.im| + ρ) / 2 < ρ := by linarith
  exact (differentiableAt_intervalIntegral_of_holomorphic h2 hFc hFd
    (mem_imStrip.mpr h1)).differentiableWithinAt

/-! ## A continuous retraction onto a closed strip

Statements about parametric integrals in mathlib ask for a globally continuous integrand, whereas
the clock iterates are continuous only on a strip. Composing with a retraction of the plane onto the
closed strip repairs that without changing anything inside: the retraction is the identity there.
-/

/-- The retraction of the plane onto the closed strip of half-width `ρ`. -/
noncomputable def stripRetract (ρ : ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + ((max (-ρ) (min ρ z.im) : ℝ) : ℂ) * Complex.I

theorem continuous_stripRetract (ρ : ℝ) : Continuous (stripRetract ρ) := by
  unfold stripRetract
  fun_prop

theorem stripRetract_im (ρ : ℝ) (z : ℂ) :
    (stripRetract ρ z).im = max (-ρ) (min ρ z.im) := by
  simp [stripRetract]

theorem abs_stripRetract_im_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) :
    |(stripRetract ρ z).im| ≤ ρ := by
  rw [stripRetract_im, abs_le]
  constructor
  · exact le_max_left _ _
  · refine max_le (by linarith) (min_le_left _ _)

theorem stripRetract_eq_self {ρ : ℝ} {z : ℂ} (hz : |z.im| ≤ ρ) : stripRetract ρ z = z := by
  have h1 : min ρ z.im = z.im := min_eq_right (le_of_abs_le hz)
  have h2 : max (-ρ) z.im = z.im := max_eq_right (neg_le_of_abs_le hz)
  rw [stripRetract, h1, h2]
  exact Complex.re_add_im z

end GaloisForLFunctions.HTGeometry
