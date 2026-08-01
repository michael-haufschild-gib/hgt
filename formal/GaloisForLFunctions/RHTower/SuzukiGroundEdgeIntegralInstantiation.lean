import GaloisForLFunctions.RHTower.SuzukiGroundEdgeApertureObstruction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Integral instantiation of the ground-edge average

The ground-edge obstruction is proved algebraically for an abstract moment and mass.  Its analytic
consumer needs those to be genuine integrals: the screw moment of a nonnegative ground weight and
its total mass.

The step from a pointwise profile bound to a moment bound is integration of an inequality against a
nonnegative weight.  With that, the small-aperture exclusion applies to an actual weighted ground
average rather than to an abstract ratio.
-/

namespace RHTower

open MeasureTheory

/-- **Pointwise profile bound integrates to a moment bound.**  A nonnegative weight transfers a
lower bound on the profile to a lower bound on the weighted moment. -/
theorem lowerMoment_of_pointwise_bound {g φ : ℝ → ℝ} {a lower : ℝ} {s : Set ℝ}
    (hs : MeasurableSet s)
    (hprof : ∀ x ∈ s, lower ≤ g (a - x)) (hφ0 : ∀ x ∈ s, 0 ≤ φ x)
    (hφint : IntegrableOn φ s) (hprodint : IntegrableOn (fun x => φ x * g (a - x)) s) :
    lower * (∫ x in s, φ x) ≤ ∫ x in s, φ x * g (a - x) := by
  have hmono : ∫ x in s, lower * φ x ≤ ∫ x in s, φ x * g (a - x) := by
    refine setIntegral_mono_on (hφint.const_mul lower) hprodint hs fun x hx => ?_
    nlinarith [hφ0 x hx, hprof x hx]
  rwa [integral_const_mul] at hmono

/-- **`(3)` with genuine integrals.**  A strict profile threshold and positive ground mass force the
weighted ground average strictly above the target. -/
theorem suzukiGroundEdgeAverage_integral_gt {g φ : ℝ → ℝ} {a target lower : ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (htarget : target < lower)
    (hprof : ∀ x ∈ s, lower ≤ g (a - x)) (hφ0 : ∀ x ∈ s, 0 ≤ φ x)
    (hφint : IntegrableOn φ s) (hprodint : IntegrableOn (fun x => φ x * g (a - x)) s)
    (hmass : 0 < ∫ x in s, φ x) :
    target < suzukiGroundEdgeAverage (∫ x in s, φ x * g (a - x)) (∫ x in s, φ x) :=
  suzukiGroundEdgeAverage_gt_of_lowerMoment htarget hmass
    (lowerMoment_of_pointwise_bound hs hprof hφ0 hφint hprodint)

/-- **Theorem A in integral form.**  For a continuous screw profile vanishing at zero and a strictly
negative target, every sufficiently small aperture makes the weighted ground average of an actual
nonnegative ground weight exceed the target — so the central selector cannot be met there. -/
theorem exists_smallAperture_integral_average_gt {g : ℝ → ℝ} {c : ℝ}
    (hg : ContinuousAt g 0) (hg0 : g 0 = 0) (hc : c < 0) :
    ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ → ∀ φ : ℝ → ℝ,
      (∀ x ∈ Set.Icc (-a) a, 0 ≤ φ x) →
      IntegrableOn φ (Set.Icc (-a) a) →
      IntegrableOn (fun x => φ x * g (a - x)) (Set.Icc (-a) a) →
      0 < (∫ x in Set.Icc (-a) a, φ x) →
      c < suzukiGroundEdgeAverage (∫ x in Set.Icc (-a) a, φ x * g (a - x))
            (∫ x in Set.Icc (-a) a, φ x) := by
  obtain ⟨a₀, ha₀, hbound⟩ :=
    exists_smallAperture_suzukiGroundEdgeProfile_gt hg hg0 (show c / 2 < 0 by linarith)
  refine ⟨a₀, ha₀, fun a ha hle φ hφ0 hφint hprodint hmass => ?_⟩
  exact suzukiGroundEdgeAverage_integral_gt (lower := c / 2) measurableSet_Icc (by linarith)
    (fun x hx => le_of_lt (hbound a ha hle x hx)) hφ0 hφint hprodint hmass

/-! ## The boundary flux law

The Robin compression consumes the flux law `-2 U'(a) = lambda * mass` as a hypothesis.  That law is
`(13)`, and the card derives it by integrating the even eigen-equation across the aperture.  Here it
is derived: the fundamental theorem turns the integral of `-U''` into the endpoint traces of `U'`,
and evenness of the mode — oddness of its derivative — collapses the two traces into one. -/

/-- **`(13)`, the boundary flux law.**  Integrating `-U'' = lambda phi` across `[-a,a]` for an even
mode gives `-2 U'(a) = lambda * mass`. -/
theorem suzukiGroundEdgeFluxLaw {U φ : ℝ → ℝ} {a lam : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt (deriv U) (-(lam * φ x)) x)
    (hintg : IntervalIntegrable (fun x => -(lam * φ x)) MeasureTheory.volume (-a) a)
    (hodd : deriv U (-a) = -deriv U a) :
    -2 * deriv U a = lam * ∫ x in (-a)..a, φ x := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintg
  rw [hodd] at hftc
  have hlhs : ∫ x in (-a)..a, -(lam * φ x) = -(lam * ∫ x in (-a)..a, φ x) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hlhs] at hftc
  linarith

/-- **`(14)`, Robin compression from the eigen-equation.**  With the flux law derived rather than
assumed, the boundary ratio equals the ground-edge average directly from `-U'' = lambda phi`. -/
theorem suzukiGroundEdgeBoundaryRatio_eq_average_of_eigen {U φ : ℝ → ℝ} {a lam : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt (deriv U) (-(lam * φ x)) x)
    (hintg : IntervalIntegrable (fun x => -(lam * φ x)) MeasureTheory.volume (-a) a)
    (hodd : deriv U (-a) = -deriv U a) (hlam : lam ≠ 0)
    (hmass : (∫ x in (-a)..a, φ x) ≠ 0) :
    suzukiGroundEdgeBoundaryRatio lam (U a) (deriv U a)
      = suzukiGroundEdgeAverage (U a) (∫ x in (-a)..a, φ x) :=
  suzukiGroundEdgeBoundaryRatio_eq_average_of_flux hlam hmass
    (suzukiGroundEdgeFluxLaw hderiv hintg hodd)

/-! ## The aperture convolution

The potential `(11)` is a convolution of the screw kernel against the ground weight over the
aperture.  Its derivative passes inside the integral, so the eigen-equation `(10)` for the
second-derivative convolution becomes the differential equation `(12)` for the potential. -/

/-- **Differentiating the aperture convolution under the integral.**  The kernel's `x`-derivative
passes inside, giving the convolution of the derivative. -/
theorem hasDerivAt_apertureConvolution {g dg φ bound : ℝ → ℝ} {a x₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ nhds x₀)
    (hmeas : ∀ᶠ x in nhds x₀, AEStronglyMeasurable (fun y => g (x - y) * φ y)
      (MeasureTheory.volume.restrict (Set.uIoc (-a) a)))
    (hint : IntervalIntegrable (fun y => g (x₀ - y) * φ y) MeasureTheory.volume (-a) a)
    (hmeas' : AEStronglyMeasurable (fun y => dg (x₀ - y) * φ y)
      (MeasureTheory.volume.restrict (Set.uIoc (-a) a)))
    (hbound : ∀ᵐ y ∂MeasureTheory.volume, y ∈ Set.uIoc (-a) a → ∀ x ∈ s,
      ‖dg (x - y) * φ y‖ ≤ bound y)
    (hboundint : IntervalIntegrable bound MeasureTheory.volume (-a) a)
    (hdiff : ∀ᵐ y ∂MeasureTheory.volume, y ∈ Set.uIoc (-a) a → ∀ x ∈ s,
      HasDerivAt (fun x => g (x - y) * φ y) (dg (x - y) * φ y) x) :
    HasDerivAt (fun x => ∫ y in (-a)..a, g (x - y) * φ y)
      (∫ y in (-a)..a, dg (x₀ - y) * φ y) x₀ :=
  (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hmeas'
    hbound hboundint hdiff).2

/-- **`(12)` from `(10)` and `(11)`.**  If the potential's second derivative is the convolution of
the kernel's second derivative, and the weight is an eigenfunction of the second-derivative
convolution `(10)`, then the potential satisfies `-U'' = lambda phi`.

This is exactly the hypothesis `suzukiGroundEdgeFluxLaw` consumes, so the chain
`(10) -> (11) -> (12) -> (13) -> (14)` closes. -/
theorem hasDerivAt_deriv_apertureConvolution_of_eigen {g ddg φ : ℝ → ℝ} {a lam x₀ : ℝ}
    (hUpp : HasDerivAt (deriv fun x => ∫ y in (-a)..a, g (x - y) * φ y)
      (∫ y in (-a)..a, ddg (x₀ - y) * φ y) x₀)
    (heigen : ∫ y in (-a)..a, -(ddg (x₀ - y)) * φ y = lam * φ x₀) :
    HasDerivAt (deriv fun x => ∫ y in (-a)..a, g (x - y) * φ y) (-(lam * φ x₀)) x₀ := by
  have h1 : ∫ y in (-a)..a, -(ddg (x₀ - y)) * φ y
      = -∫ y in (-a)..a, ddg (x₀ - y) * φ y := by
    simp only [neg_mul]
    exact intervalIntegral.integral_neg
  rw [h1] at heigen
  have hval : ∫ y in (-a)..a, ddg (x₀ - y) * φ y = -(lam * φ x₀) := by linarith
  rwa [hval] at hUpp

/-! ## Symmetrization

An even ground weight folds the aperture onto its right half, replacing the one-sided screw profile
by the symmetrized profile `s_a(x) = [g(a-x) + g(a+x)]/2` of `(5)`.  The weighted average `(6)` is
unchanged by the fold, so the feasibility test may be run on `[0,a]` against `s_a`. -/

/-- **The fold.**  Against an even weight, the integral over the full aperture is the integral over
the right half against the symmetrized integrand. -/
theorem integral_fold_even {φ ψ : ℝ → ℝ} {a : ℝ} (hφ : ∀ x, φ (-x) = φ x)
    (h1 : IntervalIntegrable (fun x => φ x * ψ x) MeasureTheory.volume (-a) 0)
    (h2 : IntervalIntegrable (fun x => φ x * ψ x) MeasureTheory.volume 0 a)
    (h3 : IntervalIntegrable (fun x => φ x * ψ (-x)) MeasureTheory.volume 0 a) :
    ∫ x in (-a)..a, φ x * ψ x = ∫ x in (0:ℝ)..a, φ x * (ψ x + ψ (-x)) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hneg : ∫ x in (-a)..(0:ℝ), φ x * ψ x = ∫ x in (0:ℝ)..a, φ x * ψ (-x) := by
    have hcn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := a) fun x => φ x * ψ x
    rw [neg_zero] at hcn
    rw [← hcn]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show φ (-x) * ψ (-x) = φ x * ψ (-x)
    rw [hφ]
  rw [hneg, ← intervalIntegral.integral_add h3 h2]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-- **`(5)` and `(6)`.**  The ground-edge average against an even weight is the average over the
right half of the aperture against the symmetrized profile `s_a`, since the fold leaves both the
moment and the mass unchanged. -/
theorem suzukiGroundEdgeAverage_fold_even {g φ : ℝ → ℝ} {a : ℝ} (hφ : ∀ x, φ (-x) = φ x)
    (hm1 : IntervalIntegrable (fun x => φ x * g (a - x)) MeasureTheory.volume (-a) 0)
    (hm2 : IntervalIntegrable (fun x => φ x * g (a - x)) MeasureTheory.volume 0 a)
    (hw1 : IntervalIntegrable (fun x => φ x * 1) MeasureTheory.volume (-a) 0)
    (hw2 : IntervalIntegrable (fun x => φ x * 1) MeasureTheory.volume 0 a)
    (hm3 : IntervalIntegrable (fun x => φ x * g (a - -x)) MeasureTheory.volume 0 a)
    (hw3 : IntervalIntegrable (fun x => φ x * (1:ℝ)) MeasureTheory.volume 0 a) :
    suzukiGroundEdgeAverage (∫ x in (-a)..a, φ x * g (a - x)) (∫ x in (-a)..a, φ x * 1)
      = suzukiGroundEdgeAverage (∫ x in (0:ℝ)..a, φ x * (g (a - x) + g (a + x)))
          (∫ x in (0:ℝ)..a, φ x * (1 + 1)) := by
  rw [suzukiGroundEdgeAverage, suzukiGroundEdgeAverage,
    integral_fold_even (ψ := fun x => g (a - x)) hφ hm1 hm2 hm3,
    integral_fold_even (ψ := fun _ => (1:ℝ)) hφ hw1 hw2 hw3]
  norm_num

end RHTower
