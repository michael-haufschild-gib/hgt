import GaloisForLFunctions.RHTower.DeningerCylinderFunction
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiating a cylinder function

The cylinder condition is stable under differentiation along a character direction.  If a function
of characters is, near a point, an analytic function of finitely many evaluation coordinates, then
its derivative along a direction is computed by the chain rule in those same coordinates, and the
resulting function is again analytic in them — because the derivative of an analytic function is
analytic and evaluating a continuous linear map at a fixed vector is continuous linear.  This is the
differential half of the sentence that the cylinder condition is preserved by restriction, addition,
multiplication and the exterior derivative.

* `deningerCylinderDeriv` : the directional derivative in the coordinates of a representation.
* `deningerHasDerivAt_cylinder` : it is the derivative along the corresponding line.
* `deningerIsCylinderAt_deriv` : the derivative is again cylinder, on the same coordinates.
-/

namespace RHTower

open Filter Topology

section CylinderDerivative

variable {V : Type*}

/-- The evaluation tuple of an affine line of characters is the affine line of evaluation
tuples. -/
theorem deningerEvalTuple_line {r : ℕ} (a : Fin r → V) (P w : V → ℂ) (t : ℂ) :
    (fun i => (P + t • w) (a i)) = (fun i => P (a i)) + t • fun i => w (a i) := rfl

/-- The line through a character in a given direction is continuous. -/
theorem deningerCharacterLine_continuous (P w : V → ℂ) :
    Continuous fun t : ℂ => P + t • w := by
  refine continuous_pi fun v => ?_
  show Continuous fun t : ℂ => P v + t * w v
  fun_prop

/-- **The directional derivative of a cylinder function**, in the coordinates of a local
representation. -/
noncomputable def deningerCylinderDeriv {r : ℕ} (a : Fin r → V) (h : (Fin r → ℂ) → ℂ)
    (w : V → ℂ) (P : V → ℂ) : ℂ :=
  fderiv ℂ h (fun i => P (a i)) fun i => w (a i)

/-- **The derivative along a character direction is the chain rule in the coordinates.** -/
theorem deningerHasDerivAt_cylinder {f : (V → ℂ) → ℂ} {P₀ w : V → ℂ} {r : ℕ} {a : Fin r → V}
    {h : (Fin r → ℂ) → ℂ} (hh : AnalyticAt ℂ h fun i => P₀ (a i))
    (hf : ∀ᶠ P in 𝓝 P₀, f P = h fun i => P (a i)) :
    HasDerivAt (fun t : ℂ => f (P₀ + t • w)) (deningerCylinderDeriv a h w P₀) 0 := by
  set c : Fin r → ℂ := fun i => P₀ (a i) with hc
  set d : Fin r → ℂ := fun i => w (a i) with hd
  have hline : Tendsto (fun t : ℂ => P₀ + t • w) (𝓝 0) (𝓝 P₀) := by
    have := (deningerCharacterLine_continuous P₀ w).tendsto 0
    simpa using this
  have heq : ∀ᶠ t : ℂ in 𝓝 0, f (P₀ + t • w) = h (c + t • d) := by
    filter_upwards [hline.eventually hf] with t ht
    rw [ht]
    rfl
  have hcurve : HasDerivAt (fun t : ℂ => c + t • d) d 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).smul_const d
    rw [one_smul] at h1
    exact h1.const_add c
  have hcomp : HasDerivAt (fun t : ℂ => h (c + t • d)) (fderiv ℂ h c d) 0 := by
    have hd0 : HasFDerivAt h (fderiv ℂ h c) (c + (0 : ℂ) • d) := by
      simpa using hh.differentiableAt.hasFDerivAt
    have hres := hd0.comp_hasDerivAt (0 : ℂ) hcurve
    exact hres
  exact hcomp.congr_of_eventuallyEq heq

/-- **The derivative of a cylinder function is cylinder**, on the same coordinates. -/
theorem deningerIsCylinderAt_deriv {P₀ w : V → ℂ} {r : ℕ} {a : Fin r → V} {h : (Fin r → ℂ) → ℂ}
    (hh : AnalyticAt ℂ h fun i => P₀ (a i)) :
    DeningerIsCylinderAt (deningerCylinderDeriv a h w) P₀ := by
  refine ⟨r, a, fun x => (fderiv ℂ h x) fun i => w (a i), ?_,
    Eventually.of_forall fun P => rfl⟩
  exact ((ContinuousLinearMap.apply ℂ ℂ (fun i => w (a i))).analyticAt _).comp hh.fderiv

end CylinderDerivative

end RHTower
