import GaloisForLFunctions.RHTower.SuzukiXiSecondDefectJetSource
import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Suzuki's second defect as parity growth and a resolvent commutator

The second disk jet of Suzuki's Fourier--Livšic carrier is not merely an endpoint derivative.
Writing the real deficiency response as an even and odd channel gives four source observables:

* `E`, `O`: even and odd defect energies;
* `alpha`, `beta`: their one-sided exponential-tilt moments.

The exact second jet is

`8 * (alpha * O - beta * E) / (E + O)^2`.

Thus negative Xi curvature is equivalent to the odd channel having strictly larger relative
tilt growth than the even channel.  Equivalently, the odd/even energy ratio has a strictly positive
tilt velocity.  Its target value is an unconditional safe-Euler prime--Gamma scalar.

For a self-adjoint resolvent `R` and the position operator `X`, the difference
`alpha - beta` is the matrix element of `[R,X]`.  The inverse commutator identity

`[R,X] = R [X,T] R`,  `R = T⁻¹`,

therefore isolates the genuinely nonlocal arithmetic term.  At an Xi-identifying shift it must
obey an exact balance, not only a sign condition.

No RH assumption or numerical computation occurs.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## Exact parity curvature -/

/-- Second disk curvature in parity-energy coordinates. -/
def suzukiSecondDefectParityCurvature
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) : ℝ :=
  8 * (evenTilt * oddEnergy - oddTilt * evenEnergy) /
    (evenEnergy + oddEnergy) ^ 2

/-- The endpoint source formula becomes the parity curvature once the Fourier values and their
first spectral derivatives are written in even/odd coordinates. -/
theorem suzukiFourier_endpointSecondDefect_eq_parityCurvature
    {F : ℂ → ℂ} {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hsum : evenEnergy + oddEnergy ≠ 0)
    (hFi : F I = ((evenEnergy - oddEnergy : ℝ) : ℂ))
    (hFni : F (-I) = ((evenEnergy + oddEnergy : ℝ) : ℂ))
    (hdFi : deriv F I = I * ((oddTilt - evenTilt : ℝ) : ℂ))
    (hdFni : deriv F (-I) = I * ((evenTilt + oddTilt : ℝ) : ℂ)) :
    4 * I *
        (deriv F I * F (-I) + F I * deriv F (-I)) /
          F (-I) ^ 2 =
      (suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt : ℂ) := by
  have hsumC : ((evenEnergy + oddEnergy : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsum
  rw [hFi, hFni, hdFi, hdFni, suzukiSecondDefectParityCurvature]
  push_cast
  field_simp [hsumC]
  rw [I_sq]
  ring

/-- Negative second curvature is exactly strict dominance of the odd relative tilt moment. -/
theorem suzukiSecondDefectParityCurvature_neg_iff
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt < 0 ↔
      evenTilt / evenEnergy < oddTilt / oddEnergy := by
  rw [suzukiSecondDefectParityCurvature]
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 := sq_pos_of_pos hsum
  rw [div_lt_iff₀ hden]
  norm_num
  rw [div_lt_div_iff₀ heven hodd]
  constructor <;> intro h <;> nlinarith

/-! ## Tilt derivative and odd/even leakage velocity -/

/-- Derivative forced by the quotient rule for the parity defect angle. -/
def suzukiDefectAngleTiltVelocity
    (evenEnergy oddEnergy evenVelocity oddVelocity : ℝ) : ℝ :=
  2 * (evenVelocity * oddEnergy - evenEnergy * oddVelocity) /
    (evenEnergy + oddEnergy) ^ 2

/-- The parity defect angle's derivative under any differentiable source tilt. -/
theorem hasDerivAt_suzukiDefectAngle
    {evenEnergy oddEnergy : ℝ → ℝ}
    {t evenVelocity oddVelocity : ℝ}
    (heven : HasDerivAt evenEnergy evenVelocity t)
    (hodd : HasDerivAt oddEnergy oddVelocity t)
    (hsum : evenEnergy t + oddEnergy t ≠ 0) :
    HasDerivAt
      (fun u => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy u) (oddEnergy u))
      (suzukiDefectAngleTiltVelocity
        (evenEnergy t) (oddEnergy t) evenVelocity oddVelocity) t := by
  have hnum := heven.sub hodd
  have hden := heven.add hodd
  have hquot := hnum.div hden hsum
  change HasDerivAt
    (fun u => (evenEnergy u - oddEnergy u) /
      (evenEnergy u + oddEnergy u))
    (((evenVelocity - oddVelocity) *
        (evenEnergy t + oddEnergy t) -
      (evenEnergy t - oddEnergy t) *
        (evenVelocity + oddVelocity)) /
      (evenEnergy t + oddEnergy t) ^ 2) t at hquot
  have hvelocity :
      ((evenVelocity - oddVelocity) *
          (evenEnergy t + oddEnergy t) -
        (evenEnergy t - oddEnergy t) *
          (evenVelocity + oddVelocity)) /
        (evenEnergy t + oddEnergy t) ^ 2 =
      suzukiDefectAngleTiltVelocity
        (evenEnergy t) (oddEnergy t) evenVelocity oddVelocity := by
    rw [suzukiDefectAngleTiltVelocity]
    field_simp [hsum]
    ring
  change HasDerivAt
    (fun u => (evenEnergy u - oddEnergy u) /
      (evenEnergy u + oddEnergy u))
    (suzukiDefectAngleTiltVelocity
      (evenEnergy t) (oddEnergy t) evenVelocity oddVelocity) t
  rw [← hvelocity]
  exact hquot

/-- With two-sided energy velocities `E' = 2 alpha`, `O' = 2 beta`, the second disk curvature is
twice the source-tilt derivative of the first defect angle. -/
theorem suzukiSecondDefectParityCurvature_eq_two_mul_tiltVelocity
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt =
      2 * suzukiDefectAngleTiltVelocity
        evenEnergy oddEnergy (2 * evenTilt) (2 * oddTilt) := by
  simp only [suzukiSecondDefectParityCurvature, suzukiDefectAngleTiltVelocity]
  ring

/-- Source velocity of the odd/even defect-energy ratio. -/
def suzukiOddEvenTiltRatioVelocity
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) : ℝ :=
  2 * (oddTilt * evenEnergy - evenTilt * oddEnergy) / evenEnergy ^ 2

/-- The odd/even ratio velocity and second disk curvature are equivalent coordinates. -/
theorem suzukiOddEvenTiltRatioVelocity_eq_curvature
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : evenEnergy ≠ 0) (hsum : evenEnergy + oddEnergy ≠ 0) :
    suzukiOddEvenTiltRatioVelocity
        evenEnergy oddEnergy evenTilt oddTilt =
      -suzukiSecondDefectParityCurvature
          evenEnergy oddEnergy evenTilt oddTilt /
        (1 + GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy) ^ 2 := by
  have hone :
      1 + GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy =
        2 * evenEnergy / (evenEnergy + oddEnergy) := by
    rw [GaloisForLFunctions.RHTower.suzukiDefectAngle]
    field_simp [hsum]
    ring
  rw [hone]
  simp only [suzukiOddEvenTiltRatioVelocity, suzukiSecondDefectParityCurvature]
  field_simp [heven, hsum]
  ring

/-- Safe-Euler prime--Gamma target for the odd/even exponential-tilt ratio velocity. -/
def primeArchSuzukiOddEvenTiltRatioCalibration : ℝ :=
  -primeArchSuzukiSecondDefectCalibration /
    (1 + primeArchSuzukiFirstDefectCalibration) ^ 2

theorem primeArchSuzukiOddEvenTiltRatioCalibration_pos :
    0 < primeArchSuzukiOddEvenTiltRatioCalibration := by
  rw [primeArchSuzukiOddEvenTiltRatioCalibration]
  exact div_pos (neg_pos.mpr primeArchSuzukiSecondDefectCalibration_neg)
    (sq_pos_of_pos (by
      have h := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
      linarith))

/-- First- and second-jet convergence forces convergence of the positive odd/even tilt velocity. -/
theorem tendsto_primeArchSuzukiOddEvenTiltRatioCalibration
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {firstJet secondJet : ι → ℝ}
    (hfirst : Tendsto firstJet l
      (nhds primeArchSuzukiFirstDefectCalibration))
    (hsecond : Tendsto secondJet l
      (nhds primeArchSuzukiSecondDefectCalibration)) :
    Tendsto
      (fun j => -secondJet j / (1 + firstJet j) ^ 2) l
      (nhds primeArchSuzukiOddEvenTiltRatioCalibration) := by
  rw [primeArchSuzukiOddEvenTiltRatioCalibration]
  exact hsecond.neg.div
    ((tendsto_const_nhds.add hfirst).pow 2)
    (by
      have h := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
      positivity)

/-- Endpoint Fourier convergence transfers to the real parity curvature without discarding any
source coordinate. -/
theorem tendsto_suzukiSecondDefectParityCurvature_of_endpoint
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → ℂ → ℂ)
    (evenEnergy oddEnergy evenTilt oddTilt : ι → ℝ)
    (hendpoint : Tendsto
      (fun j =>
        4 * I *
          (deriv (F j) I * F j (-I) +
            F j I * deriv (F j) (-I)) /
          F j (-I) ^ 2) l
      (nhds (primeArchSuzukiSecondDefectCalibration : ℂ)))
    (hparity : ∀ᶠ j in l,
      evenEnergy j + oddEnergy j ≠ 0 ∧
      F j I = ((evenEnergy j - oddEnergy j : ℝ) : ℂ) ∧
      F j (-I) = ((evenEnergy j + oddEnergy j : ℝ) : ℂ) ∧
      deriv (F j) I = I * ((oddTilt j - evenTilt j : ℝ) : ℂ) ∧
      deriv (F j) (-I) = I * ((evenTilt j + oddTilt j : ℝ) : ℂ)) :
    Tendsto
      (fun j => suzukiSecondDefectParityCurvature
        (evenEnergy j) (oddEnergy j) (evenTilt j) (oddTilt j)) l
      (nhds primeArchSuzukiSecondDefectCalibration) := by
  have hcast : Tendsto
      (fun j : ι => (suzukiSecondDefectParityCurvature
        (evenEnergy j) (oddEnergy j) (evenTilt j) (oddTilt j) : ℂ)) l
      (nhds (primeArchSuzukiSecondDefectCalibration : ℂ)) := by
    refine hendpoint.congr' ?_
    filter_upwards [hparity] with j hj
    exact suzukiFourier_endpointSecondDefect_eq_parityCurvature
      hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

/-- A source family matching the first and second Xi jets must make its actual odd/even tilt-ratio
velocity converge to the strictly positive prime--Gamma calibration. -/
theorem suzukiOddEvenTiltRatioVelocity_tendsto_primeArch
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (evenEnergy oddEnergy evenTilt oddTilt : ι → ℝ)
    (hfirst : Tendsto
      (fun j => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy j) (oddEnergy j)) l
      (nhds primeArchSuzukiFirstDefectCalibration))
    (hsecond : Tendsto
      (fun j => suzukiSecondDefectParityCurvature
        (evenEnergy j) (oddEnergy j) (evenTilt j) (oddTilt j)) l
      (nhds primeArchSuzukiSecondDefectCalibration))
    (hnonzero : ∀ᶠ j in l,
      evenEnergy j ≠ 0 ∧ evenEnergy j + oddEnergy j ≠ 0) :
    Tendsto
      (fun j => suzukiOddEvenTiltRatioVelocity
        (evenEnergy j) (oddEnergy j) (evenTilt j) (oddTilt j)) l
      (nhds primeArchSuzukiOddEvenTiltRatioCalibration) := by
  have hcoordinate :=
    tendsto_primeArchSuzukiOddEvenTiltRatioCalibration hfirst hsecond
  refine hcoordinate.congr' ?_
  filter_upwards [hnonzero] with j hj
  exact (suzukiOddEvenTiltRatioVelocity_eq_curvature hj.1 hj.2).symm

/-! ## The nonlocal commutator anomaly -/

/-- Second curvature after separating the local tilt term from the nonlocal commutator anomaly. -/
def suzukiSecondDefectCommutatorBalance
    (evenEnergy oddEnergy evenTilt commutatorAnomaly : ℝ) : ℝ :=
  8 * (evenEnergy * commutatorAnomaly -
      evenTilt * (evenEnergy - oddEnergy)) /
    (evenEnergy + oddEnergy) ^ 2

/-- The anomaly is `alpha - beta`; this identity is the exact local/nonlocal split. -/
theorem suzukiSecondDefectParityCurvature_eq_commutatorBalance
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt =
      suzukiSecondDefectCommutatorBalance
        evenEnergy oddEnergy evenTilt (evenTilt - oddTilt) := by
  simp only [suzukiSecondDefectParityCurvature, suzukiSecondDefectCommutatorBalance]
  ring

/-- Exact sign gate: the nonlocal commutator must not overpower the local negative orientation. -/
theorem suzukiSecondDefectCommutatorBalance_neg_iff
    {evenEnergy oddEnergy evenTilt commutatorAnomaly : ℝ}
    (heven : 0 < evenEnergy) (hsum : 0 < evenEnergy + oddEnergy) :
    suzukiSecondDefectCommutatorBalance
        evenEnergy oddEnergy evenTilt commutatorAnomaly < 0 ↔
      commutatorAnomaly <
        evenTilt * (evenEnergy - oddEnergy) / evenEnergy := by
  rw [suzukiSecondDefectCommutatorBalance]
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 := sq_pos_of_pos hsum
  rw [div_lt_iff₀ hden]
  norm_num
  rw [lt_div_iff₀ heven]
  constructor <;> intro h <;> nlinarith

/-- Inverse commutator identity, valid in every noncommutative ring. -/
theorem inverse_commutator_eq
    {A : Type*} [Ring A] {R T X : A}
    (hRT : R * T = 1) (hTR : T * R = 1) :
    R * X - X * R = R * (X * T - T * X) * R := by
  calc
    R * X - X * R =
        R * X * (T * R) - (R * T) * X * R := by rw [hRT, hTR, one_mul, mul_one]
    _ = R * (X * T - T * X) * R := by noncomm_ring

/-- Subtracting a scalar spectral shift does not change the position commutator.  Thus Suzuki's
auxiliary shift enters the torque only through the resolvent vectors, never as a direct source
term. -/
theorem continuousLinearMap_commutator_sub_smul_one_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X A : H →L[ℝ] H) (lambda : ℝ) :
    X * (A - lambda • (1 : H →L[ℝ] H)) -
        (A - lambda • (1 : H →L[ℝ] H)) * X =
      X * A - A * X := by
  have hleft :
      X * (lambda • (1 : H →L[ℝ] H)) = lambda • X := by
    ext v
    simp only [mul_apply_eq_comp, _root_.smul_apply, one_apply_eq_self]
    exact X.map_smul lambda v
  have hright :
      (lambda • (1 : H →L[ℝ] H)) * X = lambda • X := by
    ext v
    simp only [mul_apply_eq_comp, _root_.smul_apply, one_apply_eq_self]
  rw [mul_sub, sub_mul, hleft, hright]
  abel

/-- Resolvent torque identity at matrix-element level.  Once `R=T⁻¹` is self-adjoint, the apparent
commutator of the bounded response is exactly the inverse-dressed commutator of its source
operator. -/
theorem inner_inverseCommutator_eq_inner_dressedCommutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {R T X : H →L[ℝ] H} {c s : H}
    (hR : ContinuousLinearMap.adjoint R = R)
    (hRT : R * T = 1) (hTR : T * R = 1) :
    inner ℝ c ((R * X - X * R) s) =
      inner ℝ (R c) ((X * T - T * X) (R s)) := by
  rw [inverse_commutator_eq hRT hTR]
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_right, hR]

/-- Matrix element of `[R,X]` in a real Hilbert space, expressed by the two parity tilt moments. -/
theorem inner_resolventPositionCommutator_eq_tiltDifference
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {R X : H →L[ℝ] H} {c s : H}
    (hR : ContinuousLinearMap.adjoint R = R)
    (hX : ContinuousLinearMap.adjoint X = X) :
    inner ℝ c ((R * X - X * R) s) =
      inner ℝ (R c) (X s) - inner ℝ (R s) (X c) := by
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    inner_sub_right]
  have hleft : inner ℝ c (R (X s)) = inner ℝ (R c) (X s) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hR]
  have hright : inner ℝ c (X (R s)) = inner ℝ (R s) (X c) := by
    calc
      inner ℝ c (X (R s)) =
          inner ℝ (X c) (R s) := by
            rw [← ContinuousLinearMap.adjoint_inner_right X c (R s), hX]
      _ = inner ℝ (R s) (X c) := real_inner_comm _ _
  rw [hleft, hright]

end

end RHTower
