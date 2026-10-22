import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGreenEndpointTrace

/-! The original Green response to the reduced source at an independent angular eigenvalue. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Original gradient coefficient at an arbitrary target angular frequency. -/
def reducedGreenGradient (chi s J : ℂ) : ℂ :=
  (-(1/4+chi^(2 : ℕ))/2-(s+1)*(s+2))*J

/-- The actual endpoint response with its original full-square lift subtracted. -/
def reducedGreen (w chi s a J T : ℂ) (t : ℝ) : ℂ :=
  tortoiseGreen w chi s a J (reducedGreenGradient chi s J) T t-radialLift s w a T t*J

def reducedGreenFirst (w chi s a J T : ℂ) (t : ℝ) : ℂ :=
  tortoiseGreenFirst w chi s a J (reducedGreenGradient chi s J) T t-radialLiftFirst s w a T t*J

def reducedGreenSecond (w chi s a J T : ℂ) (t : ℝ) : ℂ :=
  tortoiseGreenSecond w chi s a J (reducedGreenGradient chi s J) T t-radialLiftSecond s w a T t*J

/-- Both displayed jets are actual derivatives of the independent-frequency reduced response. -/
theorem reducedGreen_hasDerivAt {w chi : ℂ} (h : Chamber w chi) (s a J T : ℂ)
    (t : ℝ) (ht : t < 0) :
    HasDerivAt (reducedGreen w chi s a J T) (reducedGreenFirst w chi s a J T t) t ∧
    HasDerivAt (reducedGreenFirst w chi s a J T) (reducedGreenSecond w chi s a J T t) t := by
  have hg := tortoiseGreen_hasDerivAt h s a J (reducedGreenGradient chi s J) T t ht
  exact ⟨hg.1.sub ((radialLift_hasDerivAt s w a T t).mul_const J),
    hg.2.sub ((radialLiftFirst_hasDerivAt s w a T t).mul_const J)⟩

/-- The angular gradient and lift cancel exactly, leaving the original reduced forcing times J. -/
theorem reducedGreen_equation {w chi : ℂ} (h : Chamber w chi) (s a J T : ℂ)
    (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*reducedGreen w chi s a J T t-reducedGreenSecond w chi s a J T t+
      (horizonCoordinate t:ℂ)*(1/4+chi^(2 : ℕ))*reducedGreen w chi s a J T t =
        reducedCoefficient s w a T t*J := by
  have he := tortoiseGreen_equation h s a J (reducedGreenGradient chi s J) T t ht
  dsimp only [reducedGreen,reducedGreenSecond]
  dsimp [originalForcing,reducedGreenGradient,reducedCoefficient,reducedPolynomial,
    radialLift,radialLiftSecond,horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination he

/-- The general response specializes to each literal principal correction, with its full amplitude retained. -/
theorem reducedGreen_eq_principalDifference (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (i : Fin 3) :
    reducedGreen w (principalFrequency q i) (physicalRate q branch) a (principalAmplitude q i) T =
      principalDifference q branch w a T i := by
  have hg : reducedGreenGradient (principalFrequency q i) (physicalRate q branch) (principalAmplitude q i) =
      principalGradient q branch i := by
    unfold reducedGreenGradient principalGradient
    rw [principalFrequency_parameter]
    ring
  funext t
  simp only [reducedGreen,principalDifference,hg]

end
end RHTower.D4BMJointSource
