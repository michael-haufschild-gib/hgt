/-
# Q62 from a zero-centered regular branch circle

This is the repaired non-default "regular-value disk" route: the odd image
winding comes from the base circle around `0`, while the hard geometry is
isolated as a single-valued inverse branch whose lifted circle stays in `Ext`.
-/
import GaloisForLFunctions.Bottcher.LiftedImageWindingQ62
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Set Filter Polynomial
open scoped BigOperators

namespace Bottcher

/-- The zero-centered circle has logarithmic image winding one.  This is the
part of the regular-branch route that is not an existence theorem. -/
theorem zeroCircle_imageWinding_odd {R : ℝ} (hR : 0 < R) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (circleMap (0 : ℂ) R θ)⁻¹ * deriv (circleMap (0 : ℂ) R) θ)
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * ((0 : ℤ) : ℂ) + 1) := by
  have hcircle : (∮ z in C((0 : ℂ), R), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have key := circleIntegral.integral_sub_inv_of_mem_ball
      (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R)
      (by simp [Metric.mem_ball, dist_self, hR])
    simpa only [sub_zero] using key
  have hrhs : 2 * (Real.pi : ℂ) * Complex.I * (2 * ((0 : ℤ) : ℂ) + 1)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    norm_num
  rw [hrhs]
  unfold circleIntegral at hcircle
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcircle

/-- Q62 disconnected/disconnected from the repaired regular-branch input.

For every depth and countable exceptional set, it is enough to find a positive
radius and one single-valued branch `ι` over the zero-centered circle such that
the lifted loop stays in `Ext`, differentiates with velocity `γ'`, and maps
back to `circleMap 0 R`.  The odd winding is then forced by
`zeroCircle_imageWinding_odd`; it is no longer a separate hypothesis. -/
theorem q62_disconnected_of_zeroCircleBranch_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (branchdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (R : ℝ) (ι : ℂ → ℂ) (γ' : ℝ → ℂ),
          0 < R ∧
          (∀ θ : ℝ, ι (circleMap (0 : ℂ) R θ) ∈ Ext) ∧
          Continuous (fun θ : ℝ => ι (circleMap (0 : ℂ) R θ)) ∧
          Continuous γ' ∧
          (∀ θ : ℝ,
            HasDerivAt (fun t : ℝ => ι (circleMap (0 : ℂ) R t)) (γ' θ) θ) ∧
          (∀ θ : ℝ,
            (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R θ))
              = circleMap (0 : ℂ) R θ) ∧
          (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T) ∧
          (∀ θ : ℝ,
            (∏ j ∈ Finset.range (d+1),
              2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ
                = deriv (circleMap (0 : ℂ) R) θ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_liftedImageWindingDeepData_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hbranches⟩ := branchdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ, hvel⟩ :=
    hbranches T hT
  refine ⟨fun θ : ℝ => ι (circleMap (0 : ℂ) R θ), γ',
    circleMap (0 : ℂ) R, deriv (circleMap (0 : ℂ) R), 0,
    hγExt, hγcont, hγ'cont, hγderiv, ?_, ?_, hlift, hvel,
    zeroCircle_imageWinding_odd hR⟩
  · change ι (circleMap (0 : ℂ) R (2 * Real.pi)) = ι (circleMap (0 : ℂ) R 0)
    rw [show circleMap (0 : ℂ) R (2 * Real.pi) = circleMap (0 : ℂ) R 0 by
      simpa using (periodic_circleMap (0 : ℂ) R) 0]
  · intro θ
    rw [hlift θ]
    exact havoidβ θ

/-- Same zero-circle branch reduction, but with the velocity equation discharged
by the chain rule.  The remaining geometric input is now exactly a closed
differentiable lift of the zero-centered circle through one single-valued branch. -/
theorem q62_disconnected_of_zeroCircleLift_escape
    {c₁ c₂ : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hUesc : ∀ z ∈ U, ‖c₁‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₁) : Germ (𝓟 U) ℂ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = (↑(bottcherCoord c₂) : Germ (𝓟 U) ℂ))
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (liftdata : ∀ d : ℕ, ∃ (Ext : Set ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧ Ext.Infinite ∧ U ⊆ Ext ∧
      (∀ z ∈ Ext, (quadratic c₁)^[d+1] z ∈ escapeOpen c₁) ∧
      Ext ⊆ escapeOpen c₂ ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (R : ℝ) (ι : ℂ → ℂ) (γ' : ℝ → ℂ),
          0 < R ∧
          (∀ θ : ℝ, ι (circleMap (0 : ℂ) R θ) ∈ Ext) ∧
          Continuous (fun θ : ℝ => ι (circleMap (0 : ℂ) R θ)) ∧
          Continuous γ' ∧
          (∀ θ : ℝ,
            HasDerivAt (fun t : ℝ => ι (circleMap (0 : ℂ) R t)) (γ' θ) θ) ∧
          (∀ θ : ℝ,
            (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R θ))
              = circleMap (0 : ℂ) R θ) ∧
          (∀ θ : ℝ, circleMap (0 : ℂ) R θ ∉ T))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  apply q62_disconnected_of_zeroCircleBranch_escape hUo hUc hUne hUinf
    hUesc a₁ a₂ ha₁ ha₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, hlifts⟩ := liftdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtc₂, ?_⟩
  intro T hT
  obtain ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ⟩ :=
    hlifts T hT
  refine ⟨R, ι, γ', hR, hγExt, hγcont, hγ'cont, hγderiv, hlift, havoidβ, ?_⟩
  intro θ
  have hcomp₀ : HasDerivAt
      ((fun y : ℂ => (quadratic c₁)^[d+1] y) ∘
        (fun t : ℝ => ι (circleMap (0 : ℂ) R t)))
      ((∏ j ∈ Finset.range (d+1),
        2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ) θ :=
    (hasDerivAt_quadratic_iterate c₁ (ι (circleMap (0 : ℂ) R θ)) (d+1)).comp θ
      (hγderiv θ)
  have hcomp : HasDerivAt
      (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
      ((∏ j ∈ Finset.range (d+1),
        2 * (quadratic c₁)^[j] (ι (circleMap (0 : ℂ) R θ))) * γ' θ) θ := by
    simpa only [Function.comp_apply] using hcomp₀
  have hbase : HasDerivAt
      (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
      (deriv (circleMap (0 : ℂ) R) θ) θ := by
    have hcircderiv : HasDerivAt (circleMap (0 : ℂ) R)
        (deriv (circleMap (0 : ℂ) R) θ) θ :=
      (hasDerivAt_circleMap (0 : ℂ) R θ).differentiableAt.hasDerivAt
    have hev :
        (fun t : ℝ => (quadratic c₁)^[d+1] (ι (circleMap (0 : ℂ) R t)))
          =ᶠ[nhds θ] circleMap (0 : ℂ) R :=
      Filter.Eventually.of_forall hlift
    exact hcircderiv.congr_of_eventuallyEq hev
  exact hcomp.unique hbase

end Bottcher
