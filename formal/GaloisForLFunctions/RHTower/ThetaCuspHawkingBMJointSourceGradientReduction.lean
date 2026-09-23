import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceLiftJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamAngularJets

/-! Exact absorption of the retained gradient source by an explicit field, leaving the complete half-square source. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMHorizon D4BMScalarLinearEquation
noncomputable section

def reducedPolynomial (s w u : ℂ) : ℂ :=
  -2*(1-u^(2 : ℕ))*u*((5*s^(2 : ℕ)+15*s+4)/4+s*(s-1)*(s+2)^(2 : ℕ)*u^(2 : ℕ)/4)+
    s*(s-1)/4*(w^(2 : ℕ)*u^(3 : ℕ)-liftSecondPolynomial s w u)-
    2*(1-u^(2 : ℕ))*(s+1)*(s+2)*(s*(s-1)/4)*u^(3 : ℕ)

def reducedCoefficient (s w a T : ℂ) (t : ℝ) : ℂ :=
  sourceAmplitude s w a T t*reducedPolynomial s w (radialUnit t)

/-- The independent-frequency wave on an actual separated scalar potential, using actual derivatives. -/
def separatedScalarWave (w : ℂ) (b : ℝ → ℂ) (Q : Point → ℂ) (t : ℝ) (z : Point) : ℂ :=
  (w^(2 : ℕ)*b t-deriv (deriv b) t)*Q z-
    (1-(radialUnit t:ℂ)^(2 : ℕ))*b t*scalarLaplacian Q z

/-- The same original wave expression with the complete covector angular operator retained. -/
def separatedStreamWave (w : ℂ) (b : ℝ → ℂ) (J : Covector)
    (t : ℝ) (z : Point) (k : Fin 2) : ℂ :=
  (w^(2 : ℕ)*b t-deriv (deriv b) t)*J k z-
    (1-(radialUnit t:ℂ)^(2 : ℕ))*b t*streamAngularOperator J k z

/-- Exact scalar source reduction: the full gradient energy is retained in the explicit field. -/
theorem scalar_gradient_absorption (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (t : ℝ) (z : Point) (hz : 0 < z 1) :
    originalForcing (physicalRate q branch) w a T (fullSquarePotential q z)
        (fullGradientEnergy q z/2) t =
      separatedScalarWave w (radialLift (physicalRate q branch) w a T)
        (fullSquarePotential q) t z +
      reducedCoefficient (physicalRate q branch) w a T t*fullSquarePotential q z := by
  unfold separatedScalarWave
  rw [(radialLift_derivatives (physicalRate q branch) w a T).2,
    fullSquarePotential_laplacian q branch z hz]
  dsimp [originalForcing,reducedCoefficient,reducedPolynomial,radialLift,radialLiftSecond]
  ring

/-- Exact original covector source reduction, including both actual angular covectors. -/
theorem stream_gradient_absorption (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (t : ℝ) (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    originalForcing (physicalRate q branch) w a T (fullSquareCovector q k z)
        (fullGradientCovector q branch k z) t =
      separatedStreamWave w (radialLift (physicalRate q branch) w a T)
        (fullSquareCovector q) t z k +
      reducedCoefficient (physicalRate q branch) w a T t*fullSquareCovector q k z := by
  unfold separatedStreamWave
  rw [(radialLift_derivatives (physicalRate q branch) w a T).2,
    streamAngularOperator_square q branch z hz k]
  dsimp [originalForcing,reducedCoefficient,reducedPolynomial,radialLift,radialLiftSecond]
  ring

end
end RHTower.D4BMJointSource
