import GaloisForLFunctions.RHTower.CriticalPrimeTailGlobalGreenLaplaceWall
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Positive-definite Euler-log trace of the critical prime-tail source

On every safe line `r > 1/2`, the canonical Euler logarithm

`u ↦ canonicalEulerLogZeta (1/2 + r + iu)`

is exactly the Fourier transform of the positive critical prime-tail Laplace mass.  Consequently
it is positive definite on the additive real line.  Combined with the sharp wall theorem, this
classifies the maximal raw positive-source/passive chamber: positivity is genuine on every safe
line, but its representing mass diverges exactly at `r = 1/2`.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Natural-number presentation of the positive critical Laplace weights. -/
def criticalPrimeTailFourierWeight (r : ℝ) (k : ℕ) : ℝ :=
  criticalPrimeTailLaplaceMass r (natEquivDeningerPrimePowerIndex k)

/-- Negative logarithmic frequencies match the convention `exp(I * frequency * u)`. -/
def criticalPrimeTailFourierFrequency (k : ℕ) : ℝ :=
  -deningerPrimePowerTime (natEquivDeningerPrimePowerIndex k)

/-- Safe vertical Euler-log trace as an atomic Fourier series. -/
def criticalPrimeTailEulerLogVerticalTrace (r u : ℝ) : ℂ :=
  atomicFourierSeries (criticalPrimeTailFourierWeight r)
    criticalPrimeTailFourierFrequency u

theorem criticalPrimeTailLaplaceMass_nonneg (r : ℝ) (n : DeningerPrimePowerIndex) :
    0 ≤ criticalPrimeTailLaplaceMass r n := by
  exact mul_nonneg (criticalPrimeTailAtomWeight_nonneg n) (Real.exp_nonneg _)

theorem criticalPrimeTailFourierWeight_nonneg (r : ℝ) (k : ℕ) :
    0 ≤ criticalPrimeTailFourierWeight r k :=
  criticalPrimeTailLaplaceMass_nonneg r _

theorem summable_abs_criticalPrimeTailFourierWeight
    {r : ℝ} (hr : 1 / 2 < r) :
    Summable (fun k => |criticalPrimeTailFourierWeight r k|) := by
  have hs := (summable_criticalPrimeTailLaplaceMass_iff r).mpr hr
  have hcomp := hs.comp_injective natEquivDeningerPrimePowerIndex.injective
  exact hcomp.congr fun k => by
    change criticalPrimeTailLaplaceMass r (natEquivDeningerPrimePowerIndex k) =
      |criticalPrimeTailLaplaceMass r (natEquivDeningerPrimePowerIndex k)|
    exact (abs_of_nonneg (criticalPrimeTailLaplaceMass_nonneg r _)).symm

/-- The positive-source Fourier series is literally the canonical Euler logarithm. -/
theorem criticalPrimeTailEulerLogVerticalTrace_eq_canonicalEulerLogZeta
    {r : ℝ} (hr : 1 / 2 < r) (u : ℝ) :
    criticalPrimeTailEulerLogVerticalTrace r u =
      canonicalEulerLogZeta ((1 / 2 : ℂ) + (r : ℂ) + (u : ℂ) * I) := by
  let z : ℂ := (r : ℂ) + (u : ℂ) * I
  have hz : 1 / 2 < z.re := by
    dsimp only [z]
    simp
    simpa only [one_div] using hr
  rw [criticalPrimeTailEulerLogVerticalTrace, atomicFourierSeries]
  rw [show (1 / 2 : ℂ) + (r : ℂ) + (u : ℂ) * I =
      (1 / 2 : ℂ) + z by dsimp only [z]; ring,
    ← tsum_criticalPrimeTailAtomWeight_mul_cexp_eq_canonicalEulerLogZeta hz]
  change (∑' k : ℕ,
      (criticalPrimeTailFourierWeight r k : ℂ) *
        realFourierCharacter (criticalPrimeTailFourierFrequency k) u) =
    ∑' n : DeningerPrimePowerIndex,
      (criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))
  calc
    _ = ∑' k : ℕ,
        (criticalPrimeTailAtomWeight (natEquivDeningerPrimePowerIndex k) : ℂ) *
          Complex.exp (-(z *
            (deningerPrimePowerTime (natEquivDeningerPrimePowerIndex k) : ℂ))) := by
      apply tsum_congr
      intro k
      rw [criticalPrimeTailFourierWeight, criticalPrimeTailLaplaceMass,
        criticalPrimeTailFourierFrequency, realFourierCharacter,
        Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      congr 1
      dsimp only [z]
      push_cast
      ring_nf
    _ = _ := Equiv.tsum_eq natEquivDeningerPrimePowerIndex
      (fun n : DeningerPrimePowerIndex =>
        (criticalPrimeTailAtomWeight n : ℂ) *
          Complex.exp (-(z * (deningerPrimePowerTime n : ℂ))))

/-- **C44 safe passivity.**  Every safe vertical canonical Euler-log trace is positive definite. -/
theorem positiveDefiniteOnReal_canonicalEulerLogZeta_vertical
    {r : ℝ} (hr : 1 / 2 < r) :
    PositiveDefiniteOnReal
      (fun u : ℝ =>
        canonicalEulerLogZeta ((1 / 2 : ℂ) + (r : ℂ) + (u : ℂ) * I)) := by
  have hpd : PositiveDefiniteOnReal (criticalPrimeTailEulerLogVerticalTrace r) :=
    positiveDefinite_atomicFourierSeries_of_nonnegative
      (summable_abs_criticalPrimeTailFourierWeight hr)
      (criticalPrimeTailFourierWeight_nonneg r)
  rw [show (fun u : ℝ =>
      canonicalEulerLogZeta ((1 / 2 : ℂ) + (r : ℂ) + (u : ℂ) * I)) =
      criticalPrimeTailEulerLogVerticalTrace r by
    funext u
    exact (criticalPrimeTailEulerLogVerticalTrace_eq_canonicalEulerLogZeta hr u).symm]
  exact hpd

/-- The safe Euler logarithm obeys the sharp characteristic-function norm bound. -/
theorem norm_canonicalEulerLogZeta_vertical_le_totalMass
    {r : ℝ} (hr : 1 / 2 < r) (u : ℝ) :
    ‖canonicalEulerLogZeta ((1 / 2 : ℂ) + (r : ℂ) + (u : ℂ) * I)‖ ≤
      ∑' n : DeningerPrimePowerIndex, criticalPrimeTailLaplaceMass r n := by
  rw [← criticalPrimeTailEulerLogVerticalTrace_eq_canonicalEulerLogZeta hr]
  have hsAbs := summable_abs_criticalPrimeTailFourierWeight hr
  have hs : Summable (fun k : ℕ =>
      (criticalPrimeTailFourierWeight r k : ℂ) *
        realFourierCharacter (criticalPrimeTailFourierFrequency k) u) := by
    rw [← summable_norm_iff]
    simpa [norm_mul, norm_realFourierCharacter, Real.norm_eq_abs] using hsAbs
  rw [criticalPrimeTailEulerLogVerticalTrace, atomicFourierSeries]
  calc
    ‖∑' k : ℕ, (criticalPrimeTailFourierWeight r k : ℂ) *
        realFourierCharacter (criticalPrimeTailFourierFrequency k) u‖ ≤
        ∑' k : ℕ, ‖(criticalPrimeTailFourierWeight r k : ℂ) *
          realFourierCharacter (criticalPrimeTailFourierFrequency k) u‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ = ∑' k : ℕ, criticalPrimeTailFourierWeight r k := by
      apply tsum_congr
      intro k
      rw [norm_mul, norm_realFourierCharacter, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (criticalPrimeTailFourierWeight_nonneg r k)]
    _ = _ := Equiv.tsum_eq natEquivDeningerPrimePowerIndex
      (criticalPrimeTailLaplaceMass r)

end

end RHTower
