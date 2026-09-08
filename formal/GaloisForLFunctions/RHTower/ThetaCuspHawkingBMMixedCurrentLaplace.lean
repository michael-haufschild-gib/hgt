import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedIngoingCurrent
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A genuine half-line integral of the original current, switched at ingoing
time zero. This constructs the transformed source, not a retarded inverse. -/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMIngoingCoordinates
set_option autoImplicit false
noncomputable section

/-- The time-transform kernel of the literal original current at fixed geometry. -/
def currentLaplaceKernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-w*(t:ℂ))*staticCurrent q branch a r z k t

/-- Ingoing-time onset V=t+tortoise(r)>0 fixes the actual lower integration limit. -/
def currentLaplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) : ℂ :=
  ∫ t in Ioi (-tortoise r.val), currentLaplaceKernel q branch a r z k w t

private theorem kernel_factor (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) (t : ℝ) :
    currentLaplaceKernel q branch a r z k w t =
      Complex.exp ((currentRate q branch-w)*(t:ℂ))*
        (Complex.exp (currentRate q branch*(tortoise r.val : ℂ))*ingoingCurrentAmplitude q branch a r z k) := by
  rw [currentLaplaceKernel,staticCurrent_ingoing]
  simp only [Complex.ofReal_add]
  rw [← mul_assoc,← Complex.exp_add,← mul_assoc,← Complex.exp_add]
  congr 2
  ring

private theorem chamber (q : XiZeroCopy) (branch : Bool) {w : ℂ} (hw : 0 < w.re) :
    (currentRate q branch-w).re < 0 := by
  have hv := currentRate_re_lt q branch
  rw [Complex.sub_re]
  linarith

/-- The actual current transform converges absolutely in the right half-plane
for every Xi occurrence and both physical branches. No RH premise is used. -/
theorem currentLaplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (currentLaplaceKernel q branch a r z k w) (Ioi (-tortoise r.val)) := by
  change IntegrableOn (fun t => currentLaplaceKernel q branch a r z k w t) _
  simp_rw [kernel_factor]
  exact (integrableOn_exp_mul_complex_Ioi (chamber q branch hw) _).mul_const _

/-- Exact transformed original current. Its radial frequency factor comes
from the ingoing onset surface, not from changing the source's physical rate. -/
theorem currentLaplace_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    currentLaplace q branch a r z k w =
      Complex.exp (w*(tortoise r.val:ℂ))*ingoingCurrentAmplitude q branch a r z k /
        (w-currentRate q branch) := by
  unfold currentLaplace
  simp_rw [kernel_factor]
  rw [integral_mul_const,integral_exp_mul_complex_Ioi (chamber q branch hw)]
  have he : Complex.exp ((currentRate q branch-w)*((-tortoise r.val:ℝ):ℂ))*
      Complex.exp (currentRate q branch*(tortoise r.val:ℂ)) =
      Complex.exp (w*(tortoise r.val:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show currentRate q branch-w = -(w-currentRate q branch) by ring]
  have he' := he
  rw [show currentRate q branch-w = -(w-currentRate q branch) by ring] at he'
  rw [neg_div_neg_eq]
  rw [div_mul_eq_mul_div,← mul_assoc,he']

/-- The numerator of the source continuation, before dividing by its original
time pole. It retains the fixed original angular and radial amplitude. -/
def regularizedCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (w : ℂ) : ℂ :=
  Complex.exp (w*(tortoise r.val:ℂ))*ingoingCurrentAmplitude q branch a r z k

/-- This continued source numerator is entire in the independent transform frequency. -/
theorem regularizedCurrent_entire (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) :
    Differentiable ℂ (regularizedCurrent q branch a r z k) := by
  unfold regularizedCurrent
  fun_prop

/-- Its value at the physical source rate is exactly the original current at
static time zero. No nonvanishing of that complex source coefficient is assumed. -/
theorem regularizedCurrent_physical (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) :
    regularizedCurrent q branch a r z k (currentRate q branch) =
      staticCurrent q branch a r z k 0 := by
  rw [staticCurrent_ingoing]
  simp only [zero_add,regularizedCurrent]

end
end RHTower.D4BMModularCore
