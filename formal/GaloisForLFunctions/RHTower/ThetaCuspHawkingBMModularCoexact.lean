import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricEndpoints

/-! The actual coexact derivative commutes with the full modular coordinate pullback. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMGlobalAngularResponse
noncomputable section

/-- The coexact differential in the original complex planar chart. -/
def chartCoexact (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (v : ℂ) : ℂ :=
  fderiv ℝ (f ∘ ofComplex) (z:ℂ) (Complex.I*v)

/-- Evaluation of the actual coordinate covector on a real tangent vector. -/
def covectorAction (V : Covector) (z : Point) (v : ℂ) : ℂ :=
  (v.re:ℂ)*V 0 z+(v.im:ℂ)*V 1 z

/-- The actual modular differential commutes with coexact rotation. -/
theorem chartCoexact_modular_pullback (A : SL(2,ℤ)) (f : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (z : UpperHalfPlane) (v : ℂ) :
    chartCoexact (fun w => f (A • w)) z v =
      chartCoexact f (A • z) ((1/(denom A z)^2)*v) := by
  unfold chartCoexact
  rw [chart_fderiv_modular_pullback A f hf z,ContinuousLinearMap.comp_apply,
    modular_chart_jacobian]
  congr 1
  ring

/-- Scalar invariance gives covector pullback invariance with the full Jacobian. -/
theorem chartCoexact_invariant (A : SL(2,ℤ)) (f : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (hi : ∀ w, f (A • w) = f w) (z : UpperHalfPlane) (v : ℂ) :
    chartCoexact f (A • z) ((1/(denom A z)^2)*v) = chartCoexact f z v := by
  rw [← chartCoexact_modular_pullback A f hf z]
  congr 1
  exact funext hi

/-- Original coordinate coexact components are exactly the actual chart differential. -/
theorem coexact_chartAction (F : Point → ℂ) (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (coexact F) (coordinates z) v =
      chartCoexact (fun w => F (coordinates w)) z v := by
  have he : (fun w : UpperHalfPlane => F (coordinates w)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      F ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  have hx := angularCoordinates_derivative F 0 (z:ℂ)
  have hy := angularCoordinates_derivative F 1 (z:ℂ)
  simp only [direction,Matrix.cons_val_zero,Matrix.cons_val_one] at hx hy
  have hv : Complex.I*v = (-v.im) • (1:ℂ)+v.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  unfold chartCoexact
  rw [he.fderiv_eq,hv,map_add,map_smul,map_smul,hx,hy]
  simp [covectorAction,coexact,Complex.real_smul,coordinates,angularCoordinates]
  ring

/-- Smooth original angular fields give smooth scalar fields in the actual chart. -/
theorem chartSmooth_coordinates (F : Point → ℂ)
    (hF : ∀ z, 0 < z 1 → ContDiffAt ℝ ∞ F z) :
    ChartSmooth (fun z => F (coordinates z)) := by
  intro z
  have he : (fun w : UpperHalfPlane => F (coordinates w)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      F ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  exact ((hF (coordinates z) z.im_pos).comp (z:ℂ)
    angularCoordinates.contDiff.contDiffAt).congr_of_eventuallyEq he

/-- The actual coexact field transforms as a covector under the original modular map. -/
theorem coexact_modular_action (A : SL(2,ℤ)) (F : Point → ℂ)
    (hF : ∀ z, 0 < z 1 → ContDiffAt ℝ ∞ F z)
    (hi : ∀ z : UpperHalfPlane, F (coordinates (A • z)) = F (coordinates z))
    (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (coexact F) (coordinates (A • z)) ((1/(denom A z)^2)*v) =
      covectorAction (coexact F) (coordinates z) v := by
  rw [coexact_chartAction,coexact_chartAction]
  exact chartCoexact_invariant A _ (chartSmooth_coordinates F hF) hi z v

end
end RHTower.D4BMModularCore
