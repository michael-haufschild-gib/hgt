import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The Cauchy integral formula on an annulus

A function holomorphic on an annulus is reproduced at a point of the annulus by the difference of
the Cauchy integrals over an outer and an inner circle enclosing it.  The difference quotient
`ζ ↦ (ζ − z)⁻¹ • (f ζ − f z)`, extended by the derivative at `ζ = z`, is holomorphic on the whole
annulus, so its integrals over the two circles agree; what is left is `f z` times the integral of
the Cauchy kernel, which is `2πi` over the outer circle and zero over the inner one.

* `GaloisForLFunctions.HTGeometry.annulusAt` : the open annulus.
* `GaloisForLFunctions.HTGeometry.circleIntegral_sub_inv_eq_zero_of_lt` : the kernel integrates to
  zero over a circle that does not enclose the pole.
* `GaloisForLFunctions.HTGeometry.annulusCauchyFormula` : the formula.
-/

open Complex Metric Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section Annulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The open annulus of radii `a` and `b` about `c`. -/
def annulusAt (c : ℂ) (a b : ℝ) : Set ℂ := {ζ : ℂ | a < ‖ζ - c‖ ∧ ‖ζ - c‖ < b}

theorem mem_annulusAt {c : ℂ} {a b : ℝ} {ζ : ℂ} :
    ζ ∈ annulusAt c a b ↔ a < ‖ζ - c‖ ∧ ‖ζ - c‖ < b := Iff.rfl

theorem isOpen_annulusAt (c : ℂ) (a b : ℝ) : IsOpen (annulusAt c a b) := by
  have heq : annulusAt c a b = (fun ζ : ℂ => ‖ζ - c‖) ⁻¹' Set.Ioo a b := by
    ext ζ
    simp [annulusAt, Set.mem_Ioo]
  rw [heq]
  exact isOpen_Ioo.preimage (continuous_norm.comp (continuous_id.sub continuous_const))

/-- The closed annulus between two radii sits inside the open annulus with wider radii. -/
theorem closedAnnulus_subset {c : ℂ} {a b r R : ℝ} (har : a < r) (hRb : R < b) :
    closedBall c R \ ball c r ⊆ annulusAt c a b := by
  intro ζ hζ
  obtain ⟨h1, h2⟩ := hζ
  rw [mem_closedBall, Complex.dist_eq] at h1
  simp only [mem_ball, Complex.dist_eq, not_lt] at h2
  exact ⟨lt_of_lt_of_le har h2, lt_of_le_of_lt h1 hRb⟩

/-- **The Cauchy kernel integrates to zero over a circle that does not enclose its pole.** -/
theorem circleIntegral_sub_inv_eq_zero_of_lt {c z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z - c‖) : (∮ ζ in C(c, r), (ζ - z)⁻¹) = 0 := by
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty ?_ ?_
  · refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) fun ζ hζ => ?_
    rw [mem_closedBall, Complex.dist_eq] at hζ
    intro hcon
    rw [sub_eq_zero] at hcon
    subst hcon
    exact absurd hζ (not_le.2 hz)
  · intro ζ hζ
    have hζb : ζ ∈ ball c r := hζ.1
    rw [mem_ball, Complex.dist_eq] at hζb
    refine DifferentiableAt.inv (by fun_prop) ?_
    intro hcon
    rw [sub_eq_zero] at hcon
    subst hcon
    exact absurd hζb.le (not_le.2 hz)

/-- **The Cauchy integral formula on an annulus.**  A function holomorphic on the annulus of radii
`a` and `b` is reproduced at every point strictly between two intermediate circles by the difference
of the Cauchy integrals over them. -/
theorem annulusCauchyFormula {f : ℂ → E} {c : ℂ} {a b r R : ℝ}
    (ha : 0 < a) (har : a < r) (hrR : r < R) (hRb : R < b)
    (hf : DifferentiableOn ℂ f (annulusAt c a b))
    {z : ℂ} (hz1 : r < ‖z - c‖) (hz2 : ‖z - c‖ < R) :
    (∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ) - (∮ ζ in C(c, r), (ζ - z)⁻¹ • f ζ)
      = (2 * Real.pi * Complex.I : ℂ) • f z := by
  have hrpos : 0 < r := lt_trans ha har
  have hRpos : 0 < R := lt_trans hrpos hrR
  have hzmem : z ∈ annulusAt c a b :=
    ⟨lt_trans har hz1, lt_trans hz2 hRb⟩
  have hopen : IsOpen (annulusAt c a b) := isOpen_annulusAt c a b
  have hnhds : annulusAt c a b ∈ nhds z := hopen.mem_nhds hzmem
  -- the difference quotient is holomorphic on the whole annulus
  have hdslope : DifferentiableOn ℂ (dslope f z) (annulusAt c a b) :=
    (Complex.differentiableOn_dslope hnhds).2 hf
  have hsubset : closedBall c R \ ball c r ⊆ annulusAt c a b := closedAnnulus_subset har hRb
  have hcont : ContinuousOn (dslope f z) (closedBall c R \ ball c r) :=
    (hdslope.continuousOn).mono hsubset
  have hdiffat : ∀ ζ ∈ (ball c R \ closedBall c r) \ (∅ : Set ℂ), DifferentiableAt ℂ (dslope f z) ζ := by
    intro ζ hζ
    have hmem : ζ ∈ annulusAt c a b := by
      obtain ⟨⟨h1, h2⟩, -⟩ := hζ
      rw [mem_ball, Complex.dist_eq] at h1
      simp only [mem_closedBall, Complex.dist_eq, not_le] at h2
      exact ⟨lt_trans har h2, lt_trans h1 hRb⟩
    exact (hdslope ζ hmem).differentiableAt (hopen.mem_nhds hmem)
  have hsame : (∮ ζ in C(c, R), dslope f z ζ) = ∮ ζ in C(c, r), dslope f z ζ :=
    circleIntegral_eq_of_differentiable_on_annulus_off_countable hrpos hrR.le
      Set.countable_empty hcont hdiffat
  -- the integrand splits off the difference quotient
  have hsplitR : (∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ)
      = (∮ ζ in C(c, R), dslope f z ζ) + (2 * Real.pi * Complex.I : ℂ) • f z := by
    have hne : ∀ ζ ∈ Metric.sphere c R, ζ ≠ z := by
      intro ζ hζ hcon
      subst hcon
      rw [mem_sphere, Complex.dist_eq] at hζ
      exact absurd hζ (ne_of_lt hz2)
    have hcongr : (∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ)
        = ∮ ζ in C(c, R), (dslope f z ζ + (ζ - z)⁻¹ • f z) := by
      refine circleIntegral.integral_congr hRpos.le fun ζ hζ => ?_
      rw [dslope_of_ne _ (hne ζ hζ), slope_def_module, smul_sub]
      abel
    rw [hcongr]
    have hint1 : CircleIntegrable (dslope f z) c R := by
      refine ContinuousOn.circleIntegrable hRpos.le ?_
      refine (hdslope.continuousOn).mono ?_
      intro ζ hζ
      rw [mem_sphere, Complex.dist_eq] at hζ
      exact ⟨by rw [hζ]; linarith, by rw [hζ]; linarith⟩
    have hint2 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ • f z) c R := by
      refine ContinuousOn.circleIntegrable hRpos.le ?_
      refine ContinuousOn.smul ?_ continuousOn_const
      refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) fun ζ hζ => ?_
      exact sub_ne_zero.2 (hne ζ hζ)
    rw [circleIntegral.integral_add hint1 hint2, circleIntegral.integral_smul_const,
      circleIntegral.integral_sub_inv_of_mem_ball
        (by rw [mem_ball, Complex.dist_eq]; exact hz2)]
  have hsplitr : (∮ ζ in C(c, r), (ζ - z)⁻¹ • f ζ) = ∮ ζ in C(c, r), dslope f z ζ := by
    have hne : ∀ ζ ∈ Metric.sphere c r, ζ ≠ z := by
      intro ζ hζ hcon
      subst hcon
      rw [mem_sphere, Complex.dist_eq] at hζ
      exact absurd hζ (ne_of_gt hz1)
    have hcongr : (∮ ζ in C(c, r), (ζ - z)⁻¹ • f ζ)
        = ∮ ζ in C(c, r), (dslope f z ζ + (ζ - z)⁻¹ • f z) := by
      refine circleIntegral.integral_congr hrpos.le fun ζ hζ => ?_
      rw [dslope_of_ne _ (hne ζ hζ), slope_def_module, smul_sub]
      abel
    rw [hcongr]
    have hint1 : CircleIntegrable (dslope f z) c r := by
      refine ContinuousOn.circleIntegrable hrpos.le ?_
      refine (hdslope.continuousOn).mono ?_
      intro ζ hζ
      rw [mem_sphere, Complex.dist_eq] at hζ
      exact ⟨by rw [hζ]; linarith, by rw [hζ]; linarith⟩
    have hint2 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ • f z) c r := by
      refine ContinuousOn.circleIntegrable hrpos.le ?_
      refine ContinuousOn.smul ?_ continuousOn_const
      refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) fun ζ hζ => ?_
      exact sub_ne_zero.2 (hne ζ hζ)
    rw [circleIntegral.integral_add hint1 hint2, circleIntegral.integral_smul_const,
      circleIntegral_sub_inv_eq_zero_of_lt hrpos.le hz1, zero_smul, add_zero]
  rw [hsplitR, hsplitr, hsame]
  abel

end Annulus

end GaloisForLFunctions.HTGeometry
