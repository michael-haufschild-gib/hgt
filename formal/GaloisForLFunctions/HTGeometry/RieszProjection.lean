/-
# The Riesz projection of a spectral contour

For an element `a` of a complete normed `ℂ`-algebra and a circle lying in the resolvent set, the
Riesz projection is

  `P = (2πi)⁻¹ ∮_{|λ−c|=r} (λ − a)⁻¹ dλ`.

Mathlib has the resolvent and its differentiability on the resolvent set
(`spectrum.hasDerivAt_resolvent`) but no Riesz projection.  This file introduces it and proves what
follows immediately from Cauchy's theorem: a contour whose whole disc avoids the spectrum gives the
zero projection.

Main results:
* `resolvent_sub_resolvent` — the **resolvent identity**.
* `rieszProjection` — the definition.
* `circleIntegrable_resolvent` — the resolvent is circle-integrable on a contour in the resolvent
  set.
* `rieszProjection_eq_zero_of_closedBall_subset` — a spectrum-free disc gives the zero projection.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The Riesz projection** attached to a circle in the resolvent set. -/
noncomputable def rieszProjection (a : A) (c : ℂ) (r : ℝ) : A :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ lam in C(c, r), resolvent a lam

/-- The resolvent is continuous, hence circle-integrable, on a contour in the resolvent set. -/
theorem circleIntegrable_resolvent {a : A} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) :
    CircleIntegrable (resolvent a) c r := by
  refine ContinuousOn.circleIntegrable hr fun lam hlam => ?_
  exact ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt

/-- **A spectrum-free disc gives the zero Riesz projection**, by Cauchy's theorem. -/
theorem rieszProjection_eq_zero_of_closedBall_subset (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ closedBall c r, lam ∈ resolventSet ℂ a) :
    rieszProjection a c r = 0 := by
  have hcont : ContinuousOn (resolvent a) (closedBall c r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  have hdiff : ∀ lam ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ (resolvent a) lam := by
    intro lam hlam
    exact (spectrum.hasDerivAt_resolvent_const_left
      (h lam (ball_subset_closedBall hlam.1))).differentiableAt
  rw [rieszProjection,
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
      hcont hdiff,
    smul_zero]

/-! ## The resolvent identity -/

omit [CompleteSpace A] in
theorem isUnit_of_mem_resolventSet {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    IsUnit (algebraMap ℂ A l - a) := hl

omit [CompleteSpace A] in
theorem resolvent_mul_sub {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    resolvent a l * (algebraMap ℂ A l - a) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_of_mem_resolventSet hl)

omit [CompleteSpace A] in
theorem sub_mul_resolvent {a : A} {l : ℂ} (hl : l ∈ resolventSet ℂ a) :
    (algebraMap ℂ A l - a) * resolvent a l = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_of_mem_resolventSet hl)

omit [CompleteSpace A] in
/-- **The resolvent identity** `R(λ) − R(μ) = (μ − λ)·R(λ)R(μ)`. -/
theorem resolvent_sub_resolvent {a : A} {l m : ℂ} (hl : l ∈ resolventSet ℂ a)
    (hm : m ∈ resolventSet ℂ a) :
    resolvent a l - resolvent a m = (m - l) • (resolvent a l * resolvent a m) := by
  have h1 : resolvent a l * (algebraMap ℂ A l - a) = 1 := resolvent_mul_sub hl
  have h2 : (algebraMap ℂ A m - a) * resolvent a m = 1 := sub_mul_resolvent hm
  have hstep : resolvent a l - resolvent a m
      = resolvent a l * ((algebraMap ℂ A m - a) - (algebraMap ℂ A l - a)) * resolvent a m := by
    have e1 : resolvent a l * (algebraMap ℂ A m - a) * resolvent a m = resolvent a l := by
      rw [mul_assoc, h2, mul_one]
    have e2 : resolvent a l * (algebraMap ℂ A l - a) * resolvent a m = resolvent a m := by
      rw [h1, one_mul]
    rw [mul_sub, sub_mul, e1, e2]
  have hdiff : (algebraMap ℂ A m - a) - (algebraMap ℂ A l - a) = (m - l) • (1 : A) := by
    rw [sub_sub_sub_cancel_right, ← map_sub, Algebra.algebraMap_eq_smul_one]
  rw [hstep, hdiff, mul_smul_comm, mul_one, smul_mul_assoc]

end GaloisForLFunctions.HTGeometry
