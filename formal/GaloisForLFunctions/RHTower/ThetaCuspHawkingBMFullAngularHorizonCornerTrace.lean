import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat

/-!
# Literal full-angular horizon corner trace

The future seed's full horizon arm is the coupled null/source-depth corner of
the actual branch-dependent full Riemann kernel.  This identifies that trace
directly; neither the full response nor the native summand is replaced.

Proof-chain role:
`full kernel corner trace -> full seed-cap weak realization -> QNM-cutoff
contact identity -> HB B2`.
-/

open Filter Topology

namespace RHTower.D4BMFullAngularHorizonCornerTrace

open D4BMHorizon D4BMModularCore D4BMFullAngularCircle
open D4BMFullAngularCircleAction D4BMFullAngularGoursat D4BMFutureSeedHorizon D4BMCausalKernel

noncomputable section
set_option autoImplicit false

private theorem source_depth_limit (v : ℝ) :
    Tendsto (fun w : ℝ => (v - w) / 2) atTop atBot := by
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [eventually_ge_atTop (v - 2 * b)] with w hw
  linarith

private theorem closedFullMean_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun z : ℝ => angularMean q branch (Real.arcosh (max 1 z)) X k) :=
  (angularMean_smooth q branch X k).continuous.comp
    (Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun z => le_max_left 1 z))

/-- The direct full Riemann kernel has the literal horizon corner trace used
by `halfKernel`.  The condition is exactly its original direct causal gate. -/
theorem fullAngularRiemannKernel_horizon_corner_tendsto (q : XiZeroCopy) (branch : Bool)
    (tau x v X k : ℝ) (hv : tau + x ≤ v) :
    Tendsto (fun w =>
      fullAngularRiemannKernel q branch (v - (v - w) / 2 - tau) x ((v - w) / 2) X k)
      atTop (𝓝 (halfKernel q branch tau x v X k)) := by
  have hgeom := (D4BMFutureHorizon.invariant_source_horizon tau x v).comp (source_depth_limit v)
  have hclosed := (closedFullMean_continuous q branch X k).tendsto _ |>.comp hgeom
  have htail : (fun w =>
      fullAngularRiemannKernel q branch (v - (v - w) / 2 - tau) x ((v - w) / 2) X k) =ᶠ[atTop]
      fun w => angularMean q branch
        (Real.arcosh (max 1 (invariant (v - tau - (v - w) / 2) x ((v - w) / 2)))) X k := by
    filter_upwards [eventually_ge_atTop (tau - x)] with w hw
    have hu : 0 ≤ w - tau + x := by linarith
    have hV : 0 ≤ v - tau - x := by linarith
    have h := fullAngularRiemannKernel_null_closed q branch ((v - w) / 2)
      (w - tau + x) (v - tau - x) X k hu hV
    have e1 : (w - tau + x + (v - tau - x)) / 2 = v - tau - (v - w) / 2 := by ring
    have e2 : (v - w) / 2 + (w - tau + x - (v - tau - x)) / 2 = x := by ring
    rw [e1, e2] at h
    rw [show v - (v - w) / 2 - tau = v - tau - (v - w) / 2 from by ring]
    exact h
  rw [halfKernel, if_pos hv]
  exact hclosed.congr' htail.symm

end

end RHTower.D4BMFullAngularHorizonCornerTrace
