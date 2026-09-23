import GaloisForLFunctions.RHTower.LocalizedZeroFreeTransfer
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility

/-!
# What the localized criterion still requires, and what it cannot accept

The localized transfer replaces one global real-rooted family by one local family per off-critical
point.  Two facts bound how that weakening may be used.

**The scope shrinks.**  Every zero of `XiC` has `|Im z| < 1/2`, so the localized criterion only ever
needs balls centred in the closed strip `0 < |Im z| ≤ 1/2`.  Outside it a constant family works: the
limit is already nonvanishing there, on a ball of radius `|Im z| - 1/2`.

**Proximity is not structure.**  If an approximating family is merely *close* to `XiC` — closer than
`XiC` itself is to zero on the ball — then its zero-freeness there is immediate, but the hypothesis
of that implication is `|XiC| ≥ m > 0` on the ball, which is the conclusion.

> **Zero-freeness derived from approximation quality is circular.  Only zero-freeness forced by
> structure — real-rootedness, self-adjointness, a positivity constraint — can be used.**

**The heat-flow speed bound fails.**  The natural structural candidate is the de Bruijn–Newman flow,
whose zeros obey `ẏ_j = -2 Σ_k (y_j - y_k)/|z_j - z_k|²`.  A uniform speed bound would keep zeros out
of a fixed ball for a definite time, but the individual drift terms are unbounded: when two zeros
share a real part the term is exactly `1/|y_j - y_k|`, which exceeds any prescribed bound.  There is
no uniform speed, and the backward flow is ill-posed in any case.

This file formalizes the scope restriction, both directions of the proximity guardrail, and the
unboundedness of the drift term.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- The constant sequence converges locally uniformly to its value. -/
theorem tendstoLocallyUniformly_const_self (f : ℂ → ℂ) :
    TendstoLocallyUniformly (fun _ : ℕ => f) f atTop := by
  intro u hu x
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  filter_upwards with n y _
  exact refl_mem_uniformity hu

/-- Points of a ball keep a lower bound on the modulus of the imaginary part. -/
theorem abs_im_ge_of_mem_closedBall {z w : ℂ} {R : ℝ} (hw : w ∈ closedBall z R) :
    |z.im| - R ≤ |w.im| := by
  have hd : dist w z ≤ R := Metric.mem_closedBall.mp hw
  have h := Complex.abs_im_le_norm (w - z)
  rw [← Complex.dist_eq] at h
  have h2 : |w.im - z.im| ≤ R := le_trans (by simpa using h) hd
  have := abs_sub_abs_le_abs_sub z.im w.im
  have hsym : |z.im - w.im| = |w.im - z.im| := abs_sub_comm _ _
  linarith [hsym ▸ this]

/-- **Scope restriction.**  Per-point families are needed only inside the closed strip: outside it
`XiC` is nonvanishing on a ball of radius `|Im z| - 1/2`. -/
theorem riemannHypothesis_of_strip_zeroFree_approximants
    (hloc : ∀ z : ℂ, z.im ≠ 0 → |z.im| ≤ 1 / 2 →
      ∃ (Fn : ℕ → ℂ → ℂ) (R : ℝ), 0 < R ∧
        TendstoLocallyUniformly Fn XiC atTop ∧
        (∀ᶠ n in atTop, Differentiable ℂ (Fn n)) ∧
        (∀ᶠ n in atTop, ∀ w ∈ closedBall z R, Fn n w ≠ 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pointwise_zeroFree_approximants
  intro z hz
  rcases le_or_gt (|z.im|) (1 / 2) with hle | hgt
  · exact hloc z hz hle
  · refine ⟨fun _ => XiC, |z.im| - 1 / 2, by linarith, ?_, ?_, ?_⟩
    · exact tendstoLocallyUniformly_const_self XiC
    · exact Eventually.of_forall
        (fun _ w => (XiC_analytic w (Set.mem_univ w)).differentiableAt)
    · refine Eventually.of_forall (fun _ w hw => ?_)
      exact SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im (by
        have := abs_im_ge_of_mem_closedBall hw
        linarith)

/-- **Proximity gives zero-freeness.**  If the limit has modulus at least `m` on the ball and the
approximant is within `m`, the approximant is zero-free there. -/
theorem zeroFree_of_uniformly_close {F G : ℂ → ℂ} {z : ℂ} {R m : ℝ}
    (hm : ∀ w ∈ closedBall z R, m ≤ ‖G w‖)
    (hclose : ∀ w ∈ closedBall z R, ‖F w - G w‖ < m) :
    ∀ w ∈ closedBall z R, F w ≠ 0 := by
  intro w hw hzero
  have h1 := hm w hw
  have h2 := hclose w hw
  rw [hzero] at h2
  simp only [zero_sub, norm_neg] at h2
  linarith

/-- **And that route is circular.**  The hypothesis `m ≤ ‖XiC w‖` with `m > 0` already asserts that
`XiC` does not vanish on the ball, which is the conclusion sought. -/
theorem proximity_hypothesis_is_conclusion {G : ℂ → ℂ} {z : ℂ} {R m : ℝ} (hm0 : 0 < m)
    (hm : ∀ w ∈ closedBall z R, m ≤ ‖G w‖) (hR : 0 ≤ R) : G z ≠ 0 := by
  have h := hm z (Metric.mem_closedBall_self hR)
  intro hzero
  rw [hzero] at h
  simp at h
  linarith

/-- **The drift term is unbounded.**  When two zeros share a real part, the drift contribution is
`1/|y_j - y_k|`, which exceeds any prescribed bound. -/
theorem drift_term_unbounded (M : ℝ) (hM : 0 < M) :
    ∃ d : ℝ, 0 < d ∧ M < d / d ^ (2 : ℕ) := by
  refine ⟨1 / (M + 1), by positivity, ?_⟩
  have hpos : (0:ℝ) < M + 1 := by linarith
  have hval : (1 / (M + 1)) / (1 / (M + 1)) ^ (2 : ℕ) = M + 1 := by
    field_simp
  rw [hval]
  linarith

/-- The drift term in closed form when the real parts agree: `|y_j - y_k| / |y_j - y_k|² = 1/|y|`. -/
theorem drift_term_eq {d : ℝ} (hd : d ≠ 0) : d / d ^ (2 : ℕ) = 1 / d := by
  field_simp

end RHTower
