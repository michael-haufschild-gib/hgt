import GaloisForLFunctions.RHTower.FokasLenellsCausalGraphEvolution
import GaloisForLFunctions.RHTower.FokasLenellsCausalLaplaceIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual derivative and whole-ray identity for damped generator orbits

On the maximal generator domain, the positive-time orbit is differentiable.
The product rule and improper fundamental theorem of calculus identify its
actual Laplace integral with the positive shifted generator equation.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Every positive-time damped maximal-domain orbit has its literal shifted derivative. -/
theorem causalLaplaceOrbit_hasDerivAt (a b : ℝ) (u : causalGeneratorDomain) :
    HasDerivAt (causalLaplaceOrbit a u.val)
      (causalLaplaceOrbit a (causalGenerator u) (Real.exp b)-
        Real.exp a • causalLaplaceOrbit a u.val (Real.exp b)) (Real.exp b) := by
  have hw : HasDerivAt (fun r : ℝ => Real.exp (-Real.exp a*r))
      (Real.exp (-Real.exp a*Real.exp b)*(-Real.exp a)) (Real.exp b) := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id (Real.exp b)).const_mul (-Real.exp a)).exp
  have hv := causalGenerator_positiveOrbit_hasDerivAt b u
  apply (hw.smul hv).congr_deriv
  simp only [causalLaplaceOrbit]
  module

/-- The actual whole-ray Laplace integral obeys the shifted equation on the full maximal domain. -/
theorem causalLaplaceIntegral_generator_identity (a : ℝ) (u : causalGeneratorDomain) :
    causalLaplaceIntegral a (causalGenerator u) =
      Real.exp a • causalLaplaceIntegral a u.val-u.val := by
  have hderiv : ∀ r ∈ Ioi (0:ℝ), HasDerivAt (causalLaplaceOrbit a u.val)
      (causalLaplaceOrbit a (causalGenerator u) r-Real.exp a • causalLaplaceOrbit a u.val r) r := by
    intro r hr
    simpa only [Real.exp_log hr] using causalLaplaceOrbit_hasDerivAt a (Real.log r) u
  have hi := causalLaplaceOrbit_integrable a u.val
  have hg := causalLaplaceOrbit_integrable a (causalGenerator u)
  have hd := hg.sub (hi.smul (Real.exp a))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (causalLaplaceOrbit_continuous a u.val).continuousAt.continuousWithinAt hderiv hd
    (causalLaplaceOrbit_tendsto a u.val)
  have hsm : IntegrableOn (fun r : ℝ => Real.exp a • causalLaplaceOrbit a u.val r) (Ioi (0:ℝ)) volume :=
    hi.smul (Real.exp a)
  have hsplit := integral_sub hg hsm
  change (∫ r in Ioi (0:ℝ), causalLaplaceOrbit a (causalGenerator u) r-Real.exp a • causalLaplaceOrbit a u.val r) =
    (∫ r in Ioi (0:ℝ), causalLaplaceOrbit a (causalGenerator u) r)-
      ∫ r in Ioi (0:ℝ), Real.exp a • causalLaplaceOrbit a u.val r at hsplit
  rw [causalLaplaceOrbit_zero,zero_sub,hsplit,integral_smul] at h
  change causalLaplaceIntegral a (causalGenerator u)-Real.exp a • causalLaplaceIntegral a u.val = -u.val at h
  exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

end
end RHTower.FokasLenells
