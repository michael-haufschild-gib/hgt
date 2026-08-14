import GaloisForLFunctions.RHTower.HedenmalmWardKernelAbelProjector
import GaloisForLFunctions.RHTower.XiHolomorphicAffineCompanionFibreDeterminant

/-!
# Ward--Abel affine-companion multiplicity separator

The complement of the source-only Ward Abel projector is

`n y^2 / (1 + n y^2)`.

It is zero on the critical line and tends to one at every nonzero transverse displacement.  Using
its square root as the transverse coordinate in the phase-safe affine-companion determinant makes
one reflection-complete equal-ordinate fibre of multiplicity `M` converge exactly to determinant
`-4 M^2`.  This is uniform in displacement and counts divisor copies, hence analytic
multiplicity, without inserting `1/y` or selecting a zero-dependent scale.

The theorem is a source/zero connector.  A prime--Gamma upper bound for its height-dephased
four-leg trace remains separate.
-/

open scoped BigOperators
open Complex Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Complement of the source-only Abel approximation to the critical-line projector. -/
def thetaXiWardKernelAbelOffLineWeight (n : ℕ) (q : XiZeroCopy) : ℝ :=
  1 - thetaXiWardKernelAbelWeight n q

/-- Exact saturating transverse normal form. -/
theorem thetaXiWardKernelAbelOffLineWeight_eq (n : ℕ) (q : XiZeroCopy) :
    thetaXiWardKernelAbelOffLineWeight n q =
      (n : ℝ) * (xiSpectralPoint q).im ^ 2 /
        (1 + (n : ℝ) * (xiSpectralPoint q).im ^ 2) := by
  rw [thetaXiWardKernelAbelOffLineWeight,
    thetaXiWardKernelAbelWeight_eq]
  have hden : 0 < 1 + (n : ℝ) * (xiSpectralPoint q).im ^ 2 := by
    positivity
  field_simp [hden.ne']
  ring

theorem thetaXiWardKernelAbelOffLineWeight_nonneg (n : ℕ) (q : XiZeroCopy) :
    0 ≤ thetaXiWardKernelAbelOffLineWeight n q := by
  rw [thetaXiWardKernelAbelOffLineWeight]
  linarith [thetaXiWardKernelAbelWeight_le_one n q]

theorem thetaXiWardKernelAbelOffLineWeight_le_one (n : ℕ) (q : XiZeroCopy) :
    thetaXiWardKernelAbelOffLineWeight n q ≤ 1 := by
  rw [thetaXiWardKernelAbelOffLineWeight]
  linarith [thetaXiWardKernelAbelWeight_nonneg n q]

/-- Source-only Abel complements recover the off-line indicator pointwise. -/
theorem tendsto_thetaXiWardKernelAbelOffLineWeight (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => thetaXiWardKernelAbelOffLineWeight n q) atTop
      (nhds (if (q.1 : ℂ).re = 1 / 2 then 0 else 1)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
    (tendsto_thetaXiWardKernelAbelWeight q)
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · convert h using 1 <;>
      simp [thetaXiWardKernelAbelOffLineWeight, hq]
  · have hq' : (q.1 : ℂ).re ≠ (2 : ℝ)⁻¹ := by simpa using hq
    convert h using 1 <;>
      simp [thetaXiWardKernelAbelOffLineWeight, hq']

/-- Regular transverse coordinate supplied by the Ward Abel complement. -/
def thetaXiWardAbelTransverseCoordinate (n : ℕ) (q : XiZeroCopy) : ℝ :=
  Real.sqrt (thetaXiWardKernelAbelOffLineWeight n q)

theorem thetaXiWardAbelTransverseCoordinate_sq (n : ℕ) (q : XiZeroCopy) :
    thetaXiWardAbelTransverseCoordinate n q ^ 2 =
      thetaXiWardKernelAbelOffLineWeight n q := by
  rw [thetaXiWardAbelTransverseCoordinate,
    Real.sq_sqrt (thetaXiWardKernelAbelOffLineWeight_nonneg n q)]

/-- Abel off-line mass of a finite multiplicity-exact divisor packet. -/
def finiteThetaXiWardAbelOffLineMass
    (s : Finset XiZeroCopy) (n : ℕ) : ℝ :=
  ∑ q ∈ s, thetaXiWardKernelAbelOffLineWeight n q

/-- On an off-line finite packet, regular Abel mass tends to exact divisor-copy cardinality. -/
theorem tendsto_finiteThetaXiWardAbelOffLineMass
    (s : Finset XiZeroCopy) (hoff : ∀ q ∈ s, (q.1 : ℂ).re ≠ 1 / 2) :
    Tendsto (finiteThetaXiWardAbelOffLineMass s) atTop
      (nhds (s.card : ℝ)) := by
  classical
  have hcard : (s.card : ℝ) = ∑ q ∈ s, (1 : ℝ) := by simp
  rw [hcard]
  unfold finiteThetaXiWardAbelOffLineMass
  apply tendsto_finsetSum
  intro q hq
  have hq' : (q.1 : ℂ).re ≠ (2 : ℝ)⁻¹ := by
    simpa using hoff q hq
  simpa [hq'] using
    tendsto_thetaXiWardKernelAbelOffLineWeight q

/-- Phase-safe affine determinant of one finite equal-height packet, using only the regular Ward
Abel transverse coordinate.  `x` is the packet's common centered ordinate. -/
def finiteThetaXiWardAbelAffineFibreDet
    (s : Finset XiZeroCopy) (x : ℝ) (n : ℕ) : ℝ :=
  holomorphicAffineFibreCentralDet s x
    (thetaXiWardAbelTransverseCoordinate n)
    (fun _q => (1 : ℝ)) (fun _q => (1 : ℂ))

/-- Exact finite normalization: determinant is minus four times packet cardinality times regular
Abel off-line mass. -/
theorem finiteThetaXiWardAbelAffineFibreDet_eq
    (s : Finset XiZeroCopy) (x : ℝ) (n : ℕ) :
    finiteThetaXiWardAbelAffineFibreDet s x n =
      -4 * (s.card : ℝ) * finiteThetaXiWardAbelOffLineMass s n := by
  have hA : holomorphicAffineFibreMass s (fun _q => (1 : ℝ))
      (fun _q => (1 : ℂ)) = (s.card : ℝ) := by
    simp [holomorphicAffineFibreMass]
  have hS : holomorphicAffineFibrePhaseSkew s
      (thetaXiWardAbelTransverseCoordinate n) (fun _q => (1 : ℝ))
      (fun _q => (1 : ℂ)) = 0 := by
    simp [holomorphicAffineFibrePhaseSkew]
  have hU : holomorphicAffineFibreTransverseMoment s
      (thetaXiWardAbelTransverseCoordinate n) (fun _q => (1 : ℝ))
      (fun _q => (1 : ℂ)) = finiteThetaXiWardAbelOffLineMass s n := by
    rw [holomorphicAffineFibreTransverseMoment,
      finiteThetaXiWardAbelOffLineMass]
    apply Finset.sum_congr rfl
    intro q hq
    rw [thetaXiWardAbelTransverseCoordinate_sq]
    simp
  rw [finiteThetaXiWardAbelAffineFibreDet,
    holomorphicAffineFibreCentralDet_eq, hA, hS, hU]
  ring

/-- **Submicroscopic multiplicity separator.**  On every finite off-line equal-height packet, the
regular source determinants converge to `-4 M^2`, with `M` the exact divisor-copy multiplicity. -/
theorem tendsto_finiteThetaXiWardAbelAffineFibreDet
    (s : Finset XiZeroCopy) (x : ℝ)
    (hoff : ∀ q ∈ s, (q.1 : ℂ).re ≠ 1 / 2) :
    Tendsto (finiteThetaXiWardAbelAffineFibreDet s x) atTop
      (nhds (-4 * (s.card : ℝ) ^ 2)) := by
  have h := (tendsto_finiteThetaXiWardAbelOffLineMass s hoff).const_mul
    (-4 * (s.card : ℝ))
  have hfun : finiteThetaXiWardAbelAffineFibreDet s x =
      fun n => -4 * (s.card : ℝ) * finiteThetaXiWardAbelOffLineMass s n := by
    funext n
    exact finiteThetaXiWardAbelAffineFibreDet_eq s x n
  rw [hfun]
  simpa [pow_two, mul_assoc] using h

end

end RHTower
