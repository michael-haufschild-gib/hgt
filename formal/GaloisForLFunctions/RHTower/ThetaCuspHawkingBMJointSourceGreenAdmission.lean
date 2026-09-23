import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCompactPower
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceRadialAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceGreenBoundary
import Mathlib.Topology.Order.ExtendFrom

/-! The actual full-endpoint principal response is L² in the original infinite tortoise measure. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMJointWave
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def normalizedGreen (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  response w chi s a J K T z/power (w/2) z

private theorem normalizedGreen_continuousOn {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ContinuousOn (normalizedGreen w chi s a J K T) (Ioo 0 1) := by
  intro z hz
  exact (((response_derivatives h s a J K T hz).1.continuousAt).div
    ((power_derivatives (w/2) hz.1).1.continuousAt) (power_ne_zero _ hz.1)).continuousWithinAt

/-- The normalized actual Green response extends continuously across both physical endpoints. -/
theorem normalizedGreen_extension {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ContinuousOn (extendFrom (Ioo 0 1) (normalizedGreen w chi s a J K T)) (Icc 0 1) := by
  apply continuousOn_Icc_extendFrom_Ioo (normalizedGreen_continuousOn h s a J K T)
    (response_ingoing h s a J K T)
  have ht := (response_boundary h s a J K T).div
    ((power_tendsto_one (w/2)).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)) (one_ne_zero : (1:ℂ) ≠ 0)
  simpa only [zero_div,normalizedGreen,Pi.div_apply] using! ht

/-- Actual principal radial response in tortoise coordinates. -/
def tortoiseGreen (w chi s a J K T : ℂ) (t : ℝ) : ℂ :=
  response w chi s a J K T (horizonCoordinate t)

/-- Whole-half-line square integrability of the constructed endpoint Green response. -/
theorem tortoiseGreen_memLp {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    MemLp (tortoiseGreen w chi s a J K T) 2 radialMeasure := by
  let g := extendFrom (Ioo 0 1) (normalizedGreen w chi s a J K T)
  have hg : ContinuousOn g (Icc 0 1) := normalizedGreen_extension h s a J K T
  have hp : ContinuousOn (fun u : ℝ => power w (1+u)) (Icc 0 1) := by
    intro u hu
    have hc := (power_derivatives w (by linarith [hu.1] : 0 < 1+u)).1.continuousAt
    exact (hc.comp_of_eq (continuous_const.add continuous_id).continuousAt rfl).continuousWithinAt
  have hz : Set.MapsTo (fun u : ℝ => 1-u^(2 : ℕ)) (Icc 0 1) (Icc 0 1) := by
    intro u hu
    constructor <;> nlinarith [hu.1,hu.2]
  have hF : ContinuousOn (fun u => power w (1+u)*g (1-u^(2 : ℕ))) (Icc 0 1) :=
    hp.mul (hg.comp (by fun_prop : Continuous (fun u : ℝ => 1-u^(2 : ℕ))).continuousOn hz)
  have hm := laplaceProfile_memLp w (chamber_re_pos h) _ hF
  apply hm.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  have hz := horizonCoordinate_interior t ht
  have he : g (horizonCoordinate t) = normalizedGreen w chi s a J K T (horizonCoordinate t) :=
    extendFrom_extends (normalizedGreen_continuousOn h s a J K T) _ hz
  change Complex.exp (w*(t:ℂ))*(power w (1+radialUnit t)*g (horizonCoordinate t)) = tortoiseGreen w chi s a J K T t
  rw [← mul_assoc,← horizonPower_tortoise w t ht,he]
  dsimp [normalizedGreen,tortoiseGreen]
  field_simp [power_ne_zero (w/2) hz.1]

end
end RHTower.D4BMJointSource
