import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamForcedCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIngoingCoordinates
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspIndicialSelection

/-! The literal mixed current in static and ingoing time, retaining its full
angular source and original fundamental envelope. -/

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMQuadraticMixedSource D4BMIngoingCoordinates D4BMFundamentalScalarMetric
set_option autoImplicit false
noncomputable section

/-- The doubled physical source rate, with the Xi occurrence held fixed. -/
def currentRate (q : XiZeroCopy) (branch : Bool) : ℂ := 2*physicalRate q branch

/-- The actual original mixed current at fixed radius and angular point. -/
def staticCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (t : ℝ) : ℂ :=
  current (physicalRate q branch) r.val
    (envelope (physicalRate q branch) a ![t,r.val,z 0,z 1])
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)

/-- The original current's coefficient at ingoing time zero, including both
the squared-source covector and its retained gradient term. -/
def ingoingCurrentAmplitude (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) : ℂ :=
  current (physicalRate q branch) r.val
    (compactEnvelope (physicalRate q branch) a 0 (r.val : ℂ)⁻¹)
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)

private theorem compactEnvelope_time (s a u : ℂ) (t : ℝ) :
    compactEnvelope s a t u = Complex.exp (s*(t:ℂ))*compactEnvelope s a 0 u := by
  simp only [compactEnvelope,Complex.ofReal_zero,zero_add,mul_add,Complex.exp_add]
  ring

private theorem current_scale (s r B J K c : ℂ) :
    current s r (c*B) J K = c^2*current s r B J K := by
  unfold current
  ring

/-- Exact static/ingoing time factorization of the original source, derived
from the actual coordinate change and the original quadratic envelope. -/
theorem staticCurrent_ingoing (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (z : Point) (k : Fin 2) (t : ℝ) :
    staticCurrent q branch a r z k t =
      Complex.exp (currentRate q branch*((t+tortoise r.val : ℝ):ℂ))*
        ingoingCurrentAmplitude q branch a r z k := by
  have he := envelope_staticPoint (physicalRate q branch) a
    ![t+tortoise r.val,r.val,z 0,z 1] r.property
  have hpt : staticPoint ![t+tortoise r.val,r.val,z 0,z 1] = ![t,r.val,z 0,z 1] := by
    ext j
    fin_cases j <;> simp [staticPoint]
  rw [hpt] at he
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one] at he
  unfold staticCurrent
  rw [he,compactEnvelope_time,current_scale]
  unfold currentRate ingoingCurrentAmplitude
  congr 1
  rw [pow_two,← Complex.exp_add]
  congr 1
  ring

/-- Both actual source rates are strictly damped without a critical-line
assumption, so every frequency in the right half-plane is a time-integral chamber. -/
theorem currentRate_re_lt (q : XiZeroCopy) (branch : Bool) :
    (currentRate q branch).re < -2 := by
  have he : currentRate q branch = D4BMCuspProjection.physicalRate q branch := by
    cases branch <;> rfl
  rw [he]
  exact (D4BMCuspProjection.physicalRate_re_bounds q branch).2

end
end RHTower.D4BMModularCore
