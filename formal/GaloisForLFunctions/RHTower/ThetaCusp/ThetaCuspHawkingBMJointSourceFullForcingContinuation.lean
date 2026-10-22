import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceFieldDifferential

/-! Exact continuation of the complete original cutoff forcing and explicit field. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon D4BMAngularSeries D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The whole angular cutoff commutator retains its actual continued radial coefficient. -/
def continuedCutoffRadialCoefficient (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  (horizonCoordinate t:ℂ)*continuedPrincipalDifference q branch w a i t

/-- The continued complete forcing retains the native remainder and all three cutoff commutators. -/
def continuedCuspResidualForcing (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) p.1*
      squareResidual q (coordinates p.2)+
    ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i p.1*
      cutoffCommutator (principalExponent q i) (coordinates p.2)

/-- Actual independent-frequency field before the joint square-integrable correction. -/
def continuedExplicitField (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*fullSquarePotential q z+
    ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*cutoffPower (principalExponent q i) z

/-- Sum of actual separated wave expressions for the explicit field. -/
def continuedExplicitSeparatedWave (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (t : ℝ) (z : Point) : ℂ :=
  separatedScalarWave w (radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w)) (fullSquarePotential q) t z+
    ∑ i : Fin 3, separatedScalarWave w (continuedPrincipalDifference q branch w a i)
      (cutoffPower (principalExponent q i)) t z

/-- Every actual cutoff derivative appears with its original radial coefficient. -/
theorem continuedCutoffPower_wave (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re)
    (hc : ∀ i : Fin 3, connection w (principalFrequency q i) ≠ 0) (i : Fin 3) (t : ℝ) (ht : t < 0) (z : Point) (hz : 0 < z 1) :
    separatedScalarWave w (continuedPrincipalDifference q branch w a i)
        (cutoffPower (principalExponent q i)) t z =
      reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i*
        cutoff z*(z 1:ℂ)^(principalExponent q i)-
      continuedCutoffRadialCoefficient q branch w a i t*cutoffCommutator (principalExponent q i) z := by
  have he := continuedPrincipalDifference_equation q branch w a hw hwre i (hc i) t ht
  unfold separatedScalarWave
  rw [scalarLaplacian_eq _ z hz]
  change (w^(2 : ℕ)*continuedPrincipalDifference q branch w a i t-
    deriv (deriv (continuedPrincipalDifference q branch w a i)) t)*cutoffPower (principalExponent q i) z-
    (1-(radialUnit t:ℂ)^(2 : ℕ))*continuedPrincipalDifference q branch w a i t*
      hyperbolicLaplacian (cutoffPower (principalExponent q i)) z = _
  dsimp only [cutoffPower,continuedCutoffRadialCoefficient,cutoffCommutator]
  dsimp only [horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination cutoff z*(z 1:ℂ)^(principalExponent q i)*he

/-- Exact source subtraction for the actual original forcing, with no omitted cusp term. -/
theorem originalForcing_continuedExplicitResidual (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re)
    (hc : ∀ i : Fin 3, connection w (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) (z : UpperHalfPlane) :
    originalForcing (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) (fullSquarePotential q (coordinates z))
        (fullGradientEnergy q (coordinates z)/2) t =
      continuedExplicitSeparatedWave q branch w a t (coordinates z)+continuedCuspResidualForcing q branch w a (t,z) := by
  have hsum : (∑ i : Fin 3, separatedScalarWave w (continuedPrincipalDifference q branch w a i)
      (cutoffPower (principalExponent q i)) t (coordinates z)) =
      reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*cutoff (coordinates z)*principalSquare q (coordinates z)-
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*
        cutoffCommutator (principalExponent q i) (coordinates z) := by
    simp_rw [continuedCutoffPower_wave q branch w a hw hwre hc _ t ht (coordinates z) z.im_pos]
    rw [Finset.sum_sub_distrib,principalSquare_expansion q _ z.im_pos,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [scalar_gradient_absorption q branch w a (continuedOnset (physicalRate q branch) w) t _ z.im_pos]
  dsimp only [continuedExplicitSeparatedWave,continuedCuspResidualForcing,squareResidual]
  rw [hsum]
  ring

/-- Every complete forcing coefficient is meromorphic at each spatial point in the continued strip. -/
theorem continuedCuspResidualForcing_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) (z : UpperHalfPlane) :
    MeromorphicAt (fun u => continuedCuspResidualForcing q branch u a (t,z)) w := by
  have hm := (reducedCoefficient_continued_meromorphic (physicalRate q branch) a t w).mul
    (show AnalyticAt ℂ (fun _ : ℂ => squareResidual q (coordinates z)) w from analyticAt_const).meromorphicAt
  have hs := MeromorphicAt.fun_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ =>
    (((show AnalyticAt ℂ (fun _ : ℂ => (horizonCoordinate t:ℂ)) w from analyticAt_const).meromorphicAt.mul
      (continuedPrincipalDifference_meromorphicAt q branch w a hw hwre i t ht)).mul
        (show AnalyticAt ℂ (fun _ : ℂ => cutoffCommutator (principalExponent q i) (coordinates z)) w
          from analyticAt_const).meromorphicAt))
  exact hm.add hs

/-- The complete continued residual is the original full residual in its source convergence chamber. -/
theorem continuedCuspResidualForcing_eq_original (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -1 < w.re) (hs : (2*physicalRate q branch).re < w.re)
    (t : ℝ) (ht : t < 0) (z : UpperHalfPlane) :
    continuedCuspResidualForcing q branch w a (t,z) =
      cuspResidualForcing q branch w a (onsetTransform (2*physicalRate q branch) w) (t,z) := by
  unfold continuedCuspResidualForcing cuspResidualForcing continuedCutoffRadialCoefficient cutoffRadialCoefficient
  simp_rw [continuedPrincipalDifference_eq_original q branch w a hw hwre hs _ t ht]
  rw [continuedOnset,← onsetTransform_eq (2*physicalRate q branch) w hs]

/-- The full continued explicit field agrees with the original field, including its complete square lift. -/
theorem continuedExplicitField_eq_original (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -1 < w.re) (hs : (2*physicalRate q branch).re < w.re)
    (t : ℝ) (ht : t < 0) (z : Point) :
    continuedExplicitField q branch w a t z =
      explicitField q branch w a (onsetTransform (2*physicalRate q branch) w) t z := by
  unfold continuedExplicitField explicitField
  simp_rw [continuedPrincipalDifference_eq_original q branch w a hw hwre hs _ t ht]
  rw [continuedOnset,← onsetTransform_eq (2*physicalRate q branch) w hs]

end
end RHTower.D4BMJointSource
