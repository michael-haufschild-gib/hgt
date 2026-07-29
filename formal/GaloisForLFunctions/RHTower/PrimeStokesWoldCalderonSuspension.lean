import GaloisForLFunctions.RHTower.PrimeStokesCCMUnitResolventWeld

open Complex Finset
open scoped BigOperators

namespace RHTower

noncomputable section

/-!
# Unit-exponential Wold--Calderón suspension

The unit exponential aperture law partitions into the exact geometric weights of every
rational-dilation Wold tower.  Its first-cell Laplace symbol is the reciprocal Euler factor
divided by the unit Calderón factor, and the cells obey the multiplicative Wold cocycle.

This is the dependency-closed scalar core.  It does not construct the source-effective all-prime
product or prove conservativity on Xi conormal fibres.
-/

/-- Mass of the first interval of length `L` under the unit exponential law. -/
def unitExponentialWoldBoundaryMass (L : ℝ) : ℝ :=
  1 - Real.exp (-L)

/-- Mass of the `k`th interval of length `L` under the unit exponential law. -/
def unitExponentialWoldCellMass (L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-L) ^ k * unitExponentialWoldBoundaryMass L

/-- Unit right-half-plane Calderón resolvent. -/
def unitCalderonResolvent (w : ℂ) : ℂ :=
  1 / (1 + w)

/-- Laplace symbol of the first unit-exponential cell of length `L`. -/
def unitExponentialCalderonFirstCellSymbol (L : ℝ) (w : ℂ) : ℂ :=
  (1 - Complex.exp (-((1 + w) * (L : ℂ)))) / (1 + w)

theorem unitExponentialWoldBoundaryMass_add (L M : ℝ) :
    unitExponentialWoldBoundaryMass (L + M) =
      unitExponentialWoldBoundaryMass L +
        Real.exp (-L) * unitExponentialWoldBoundaryMass M := by
  rw [unitExponentialWoldBoundaryMass, unitExponentialWoldBoundaryMass,
    unitExponentialWoldBoundaryMass]
  rw [show -(L + M) = -L + -M by ring, Real.exp_add]
  ring

theorem unitExponentialWoldBoundaryMass_log
    {q : ℝ} (hq : 0 < q) :
    unitExponentialWoldBoundaryMass (Real.log q) = 1 - q⁻¹ := by
  rw [unitExponentialWoldBoundaryMass, Real.exp_neg, Real.exp_log hq]

theorem unitExponentialWoldBoundaryMass_log_mul
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    unitExponentialWoldBoundaryMass (Real.log (q * r)) =
      unitExponentialWoldBoundaryMass (Real.log q) +
        q⁻¹ * unitExponentialWoldBoundaryMass (Real.log r) := by
  rw [Real.log_mul hq.ne' hr.ne', unitExponentialWoldBoundaryMass_add,
    Real.exp_neg, Real.exp_log hq]

theorem unitExponentialWoldCellMass_log
    {q : ℝ} (hq : 0 < q) (k : ℕ) :
    unitExponentialWoldCellMass (Real.log q) k =
      (1 - q⁻¹) * (q⁻¹) ^ k := by
  rw [unitExponentialWoldCellMass, unitExponentialWoldBoundaryMass_log hq,
    Real.exp_neg, Real.exp_log hq]
  ring

theorem sum_unitExponentialWoldCellMass_range (L : ℝ) (N : ℕ) :
    ∑ k ∈ range N, unitExponentialWoldCellMass L k =
      1 - Real.exp (-L) ^ N := by
  induction N with
  | zero =>
      simp
  | succ N hN =>
      rw [sum_range_succ]
      rw [hN]
      rw [unitExponentialWoldCellMass, unitExponentialWoldBoundaryMass]
      rw [pow_succ]
      ring

theorem exponentialRate_eq_one_of_woldBoundaryMass_eq
    {a L : ℝ} (hL : 0 < L)
    (h : 1 - Real.exp (-(a * L)) = 1 - Real.exp (-L)) :
    a = 1 := by
  have hexp : Real.exp (-(a * L)) = Real.exp (-L) := by linarith
  have harg : -(a * L) = -L := Real.exp_strictMono.injective hexp
  nlinarith

theorem unitExponentialCalderonFirstCellSymbol_eq_defect_mul_resolvent
    (L : ℝ) (w : ℂ) :
    unitExponentialCalderonFirstCellSymbol L w =
      (1 - Complex.exp (-((1 + w) * (L : ℂ)))) *
        unitCalderonResolvent w := by
  rw [unitExponentialCalderonFirstCellSymbol, unitCalderonResolvent]
  simp only [div_eq_mul_inv]
  ring

theorem unitExponentialCalderonFirstCellSymbol_add (L M : ℝ) (w : ℂ) :
    unitExponentialCalderonFirstCellSymbol (L + M) w =
      unitExponentialCalderonFirstCellSymbol L w +
        Complex.exp (-((1 + w) * (L : ℂ))) *
          unitExponentialCalderonFirstCellSymbol M w := by
  rw [unitExponentialCalderonFirstCellSymbol,
    unitExponentialCalderonFirstCellSymbol,
    unitExponentialCalderonFirstCellSymbol]
  have hexp :
      Complex.exp (-((1 + w) * ((L + M : ℝ) : ℂ))) =
        Complex.exp (-((1 + w) * (L : ℂ))) *
          Complex.exp (-((1 + w) * (M : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem unitExponentialCalderonFiniteWoldRenewal
    (L : ℝ) (w : ℂ) (N : ℕ) :
    ∑ k ∈ range N,
        Complex.exp (-((1 + w) * (L : ℂ))) ^ k *
          unitExponentialCalderonFirstCellSymbol L w =
      (1 - Complex.exp (-((1 + w) * (L : ℂ))) ^ N) *
        unitCalderonResolvent w := by
  induction N with
  | zero =>
      simp
  | succ N hN =>
      rw [sum_range_succ]
      rw [hN]
      rw [unitExponentialCalderonFirstCellSymbol_eq_defect_mul_resolvent, pow_succ]
      ring

theorem unitExponentialCalderonFirstCellSymbol_eq_neg_ccm_defect
    {w : ℂ} (hw : 0 < w.re) (L : ℝ) :
    unitExponentialCalderonFirstCellSymbol L w =
      -(1 - Complex.exp (-((1 + w) * (L : ℂ)))) *
        normalizedCCMApertureResolvent 1 w := by
  rw [normalizedCCMApertureResolvent_one_eq_neg_primeStokes hw,
    primeStokesExponentialApertureResolvent,
    unitExponentialCalderonFirstCellSymbol_eq_defect_mul_resolvent,
    unitCalderonResolvent]
  simp [div_eq_mul_inv, add_comm]
  ring

end

end RHTower
