import GaloisForLFunctions.HTGeometry.SpinFourHiggsMechanism
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Spin(4)-Higgs realization of the finite Seiberg--Witten gauge circle

Writing a quaternion as a pair of complex numbers identifies its left multiplication by a unit
complex quaternion `(Re u, Im u, 0, 0)` with common phase multiplication on a two-component
spinor.  This module builds that unit quaternion and the resulting `Spin(4)` pair explicitly.
It proves that the finite Seiberg--Witten gauge action is the restriction of the corpus's
`SpinFourGaugeGroup` action, and transports its potential invariance along this circle subgroup.

The result is an exact finite algebraic subgroup statement.  It does not construct a continuum
spin connection or identify the radial Higgs potential with a Seiberg--Witten functional.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The standard complex-pair presentation of a real quaternion as a two-component spinor. -/
def quaternionToSeibergWittenSpinor (q : EventQuaternion) : SeibergWittenSpinor :=
  ![((q.re : ℝ) : ℂ) + ((q.imI : ℝ) : ℂ) * Complex.I,
    ((q.imJ : ℝ) : ℂ) + ((q.imK : ℝ) : ℂ) * Complex.I]

/-- A unit complex phase embedded in the real quaternions. -/
def circleQuaternion (u : Circle) : EventQuaternion :=
  ⟨(u : ℂ).re, (u : ℂ).im, 0, 0⟩

/-- The embedded complex phase has unit quaternion norm-square. -/
theorem circleQuaternion_normSq (u : Circle) : Quaternion.normSq (circleQuaternion u) = 1 := by
  have hu := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hu
  rw [Quaternion.normSq_def']
  simpa [circleQuaternion, pow_two] using hu

/-- Left multiplication by the embedded phase is common complex phase multiplication on spinors. -/
theorem circleQuaternion_spinorEquivariant (u : Circle) (q : EventQuaternion) :
    quaternionToSeibergWittenSpinor (circleQuaternion u * q) =
      u • quaternionToSeibergWittenSpinor q := by
  ext i
  fin_cases i
  · change
      ((circleQuaternion u * q).re : ℂ) + ((circleQuaternion u * q).imI : ℂ) * Complex.I =
        (u : ℂ) * ((q.re : ℂ) + (q.imI : ℂ) * Complex.I)
    apply Complex.ext <;>
      simp [circleQuaternion, Complex.mul_re, Complex.mul_im]
  · change
      ((circleQuaternion u * q).imJ : ℂ) + ((circleQuaternion u * q).imK : ℂ) * Complex.I =
        (u : ℂ) * ((q.imJ : ℂ) + (q.imK : ℂ) * Complex.I)
    apply Complex.ext <;>
      simp [circleQuaternion, Complex.mul_re, Complex.mul_im]

/-- The embedded phase as an element of the existing unit-quaternion gauge group. -/
def circleQuaternionGauge (u : Circle) : QuaternionGaugeGroup :=
  ⟨circleQuaternion u, by
    apply mem_sphere_zero_iff_norm.mpr
    have hsq := circleQuaternion_normSq u
    rw [Quaternion.normSq_eq_norm_mul_self] at hsq
    nlinarith [norm_nonneg (circleQuaternion u)]⟩

/-- The quaternionic gauge action restricts to the finite Seiberg--Witten phase action. -/
theorem circleQuaternionGauge_spinorEquivariant (u : Circle) (q : EventQuaternion) :
    quaternionToSeibergWittenSpinor (circleQuaternionGauge u • q) =
      u • quaternionToSeibergWittenSpinor q := by
  change quaternionToSeibergWittenSpinor (circleQuaternion u * q) = _
  exact circleQuaternion_spinorEquivariant u q

/-- The same phase embedded in the first factor of the corpus's `Spin(4)` gauge group. -/
def circleSpinFourGauge (u : Circle) : SpinFourGaugeGroup :=
  (circleQuaternionGauge u, 1)

/-- The `Spin(4)` action of the embedded gauge circle is exactly the finite phase action. -/
theorem circleSpinFourGauge_spinorEquivariant (u : Circle) (q : EventQuaternion) :
    quaternionToSeibergWittenSpinor (circleSpinFourGauge u • q) =
      u • quaternionToSeibergWittenSpinor q := by
  change quaternionToSeibergWittenSpinor
    ((circleQuaternionGauge u : EventQuaternion) * q * star (1 : EventQuaternion)) = _
  simp only [star_one, mul_one]
  exact circleQuaternionGauge_spinorEquivariant u q

/-- The existing radial `Spin(4)` Higgs potential is constant along the embedded gauge circle. -/
theorem spinFourHiggsPotential_circleGaugeInvariant (u : Circle) (q : EventQuaternion) :
    spinFourHiggsPotential (circleSpinFourGauge u • q) = spinFourHiggsPotential q :=
  spinFourHiggsPotential_gaugeInvariant (circleSpinFourGauge u) q

/-- The selected Spin(4)-Higgs vacuum, viewed as a finite Seiberg--Witten spinor. -/
def spinFourHiggsSeibergWittenSpinor : SeibergWittenSpinor :=
  quaternionToSeibergWittenSpinor quaternionHiggsVacuum

/-- The Spin(4)-Higgs vacuum yields an exact finite Seiberg--Witten curvature equation. -/
theorem spinFourHiggsSeibergWitten_solvesEquation :
    seibergWittenEquation (seibergWittenInvariant spinFourHiggsSeibergWittenSpinor)
      spinFourHiggsSeibergWittenSpinor :=
  seibergWittenEquation_inducedCurvature _

/-- The same seed configuration remains a zero-potential point of the preexisting Spin(4)-Higgs model. -/
theorem spinFourHiggsSeibergWitten_zeroPotential :
    spinFourHiggsPotential quaternionHiggsVacuum = 0 :=
  spinFourHiggsMechanism.vacuum_zero

end GaloisForLFunctions.HTGeometry
