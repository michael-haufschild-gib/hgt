import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeLiftJets

/-! The fixed smooth-onset source and its actual original time-domain gradient reduction. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMHorizon D4BMAngularSeries
noncomputable section

/-- Original wave operator with actual static-time, tortoise, and angular derivatives. -/
def timeFieldWave (U : ℝ → ℝ → Point → ℂ) (τ t : ℝ) (z : Point) : ℂ :=
  deriv (deriv (fun σ => U σ t z)) τ-deriv (deriv (fun x => U τ x z)) t-
    (1-(radialUnit t:ℂ)^(2 : ℕ))*scalarLaplacian (U τ t) z

/-- Actual full-square field with the fixed delayed onset. -/
def timeLiftField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t : ℝ) (z : Point) : ℂ :=
  timeRadialLift (physicalRate q branch) a τ t*fullSquarePotential q z

/-- Complete original scalar current source in time, before cusp subtraction. -/
def timeOriginalForcing (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t : ℝ) (z : Point) : ℂ :=
  originalForcing (physicalRate q branch) 0 a 1 (fullSquarePotential q z)
    (fullGradientEnergy q z/2) t*timeOnset (2*physicalRate q branch) (τ+t)

/-- Exact remaining scalar coefficient, including the differentiated transition profile. -/
def timeReducedCoefficient (s a : ℂ) (τ t : ℝ) : ℂ :=
  reducedCoefficient s 0 a 1 t*timeOnset (2*s) (τ+t)+
    2*radialLiftFirst s 0 a 1 t*timeOnsetFirst (2*s) (τ+t)

/-- Actual time and spatial differentiation retains the first-onset cross term. -/
theorem timeLiftField_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t : ℝ)
    (z : Point) (hz : 0 < z 1) :
    timeFieldWave (timeLiftField q branch a) τ t z =
      timeOnset (2*physicalRate q branch) (τ+t)*
        separatedScalarWave 0 (radialLift (physicalRate q branch) 0 a 1) (fullSquarePotential q) t z-
      2*radialLiftFirst (physicalRate q branch) 0 a 1 t*
        timeOnsetFirst (2*physicalRate q branch) (τ+t)*fullSquarePotential q z := by
  have hL : scalarLaplacian (fun y => timeRadialLift (physicalRate q branch) a τ t*
      fullSquarePotential q y) z =
      timeRadialLift (physicalRate q branch) a τ t*scalarLaplacian (fullSquarePotential q) z := by
    rw [scalarLaplacian_eq _ z hz,scalarLaplacian_eq _ z hz]
    exact hyperbolicLaplacian_const_mul (fullSquarePotential_smooth q z hz 2) _
  unfold timeFieldWave timeLiftField
  simp only [deriv_mul_const_field',deriv_mul_const_field]
  rw [hL,timeRadialLift_timeSecond,timeRadialLift_radialSecond]
  rw [separatedScalarWave,(radialLift_derivatives (physicalRate q branch) 0 a 1).2]
  dsimp only [timeRadialLift,timeRadialLiftSecond]
  ring

/-- The full original time source equals the wave of the explicit lift plus the exact
reduced source. No onset derivative or angular gradient term is discarded. -/
theorem timeOriginalForcing_gradient_absorption (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) (hz : 0 < z 1) :
    timeOriginalForcing q branch a τ t z =
      timeFieldWave (timeLiftField q branch a) τ t z+
        timeReducedCoefficient (physicalRate q branch) a τ t*fullSquarePotential q z := by
  rw [timeLiftField_wave q branch a τ t z hz]
  unfold timeOriginalForcing timeReducedCoefficient
  rw [scalar_gradient_absorption q branch 0 a 1 t z hz]
  ring

/-- The actual reduced source is supported after its original ingoing onset. -/
theorem timeReducedCoefficient_zero_before_onset (s a : ℂ) (τ t : ℝ) (h : τ+t < 0) :
    timeReducedCoefficient s a τ t = 0 := by
  simp [timeReducedCoefficient,timeOnset_zero_of_nonpos (2*s) h.le,timeOnsetFirst_zero_of_neg (2*s) h]

end
end RHTower.D4BMJointSource
