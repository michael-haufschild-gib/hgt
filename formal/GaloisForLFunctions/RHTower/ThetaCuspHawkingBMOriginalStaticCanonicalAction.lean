import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricOuterTime
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalMetricAction

/-!
Assembly-before-continuation for the complete original static metric action.

Current estimates do not admit the three evolved-source channels' literal
Laplace integrals at a physical QNM.  The continued object is their already
assembled metric action:
the exact static-minus-radial cutoff defect is added back to the canonical
radial cutoff at the same physical horizon.  In the convergence chamber this
literal synchronized cutoff converges to `canonicalAction`; the existing
canonical removal therefore supplies its unique source-defined QNM value.
-/

open Set Filter Topology Metric
namespace RHTower.D4BMOriginalStaticCanonicalAction
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalMetricOuterTime D4BMOriginalCanonicalMetricCutoff
open D4BMOriginalCanonicalMetricGerm D4BMOriginalCanonicalAction
noncomputable section
set_option autoImplicit false

/-- Original static-minus-radial comparison added to the canonical radial
cutoff at the same physical horizon depth.  The synchronization
`e = horizonCoordinate (-T)` makes the radial and static truncations meet at
the same collar boundary. -/
def synchronizedStaticMetricCutoff (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L0 T : ℝ) : ℂ :=
  canonicalMetricCutoff q br amp w (horizonCoordinate (-T))+
    exteriorCutoffDifference q br amp w L0 T

/-- In the genuine time-convergence chamber, the complete synchronized static
metric cutoff selects exactly the canonical radial/corner action.  Thus all
three evolved-source transfers are assembled before continuation, and no
termwise QNM Laplace integral is required. -/
theorem synchronized_static_metric_canonical_limit (q : XiZeroCopy) (br : Bool)
    (amp : ℂ) (w : ℂ) (hw : 3/2 < w.re) (hwi : w.im ≠ 0)
    (hc : D4BMLaplaceRadial.connection w (physicalRadialFrequency q) ≠ 0) :
    ∃ L0 : ℝ, 0 < L0 ∧
      Tendsto (synchronizedStaticMetricCutoff q br amp w L0) atTop
        (𝓝 (canonicalAction q br amp w)) := by
  obtain ⟨L0,hL0,hstatic⟩ := original_exterior_cutoff_difference q br amp w hw hwi
  refine ⟨L0,hL0,?_⟩
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot := by
    apply tendsto_atBot.mpr
    intro x
    filter_upwards [eventually_ge_atTop (-x)] with T hT
    linarith
  have hhorizon : Tendsto (fun T : ℝ => horizonCoordinate (-T))
      atTop (𝓝[>] (0:ℝ)) :=
    D4BMFundamentalNorm.horizonCoordinate_tendsto_positive.comp hneg
  have hradial := (canonical_metric_cutoff_tendsto q br amp w hwi (by linarith) hc).comp hhorizon
  have hsum := hradial.add hstatic
  have hlim : Tendsto (fun T : ℝ => canonicalMetricCutoff q br amp w (horizonCoordinate (-T)) +
      exteriorCutoffDifference q br amp w L0 T) atTop (𝓝 (canonicalAction q br amp w)) := by
    simpa only [canonicalAction, Function.comp_def] using hsum
  exact hlim

/-- The complete static metric action from the convergence chamber has one
explicit analytic continuation across either physical fundamental QNM.  Away
from the QNM this continuation is literally `canonicalAction`, while the
synchronized physical cutoff above identifies that function with the original
static construction wherever direct time integration is valid. -/
theorem complete_static_metric_QNM_continuation (q : XiZeroCopy) (br side : Bool)
    (amp : ℂ) :
    let w0 := physicalFundamentalFrequency q side
    AnalyticAt ℂ (canonicalQNMAction q br side amp) w0 ∧
      (∀ w : ℂ, w ≠ w0 →
        canonicalQNMAction q br side amp w = canonicalAction q br amp w) ∧
      Tendsto (canonicalAction q br amp) (𝓝[≠] w0)
        (𝓝 (canonicalQNMValue q br side amp)) ∧
      ∀ w : ℂ, 3/2 < w.re → w.im ≠ 0 →
        D4BMLaplaceRadial.connection w (physicalRadialFrequency q) ≠ 0 →
        ∃ L0 : ℝ, 0 < L0 ∧
          Tendsto (synchronizedStaticMetricCutoff q br amp w L0) atTop
            (𝓝 (canonicalAction q br amp w)) := by
  dsimp only
  have hqnm := canonical_action_QNM q br side amp
  refine ⟨hqnm.1,?_,hqnm.2.1,?_⟩
  · intro w hw
    simp [canonicalQNMAction,hw]
  · intro w hw hwi hc
    exact synchronized_static_metric_canonical_limit q br amp w hw hwi hc

end
end RHTower.D4BMOriginalStaticCanonicalAction
