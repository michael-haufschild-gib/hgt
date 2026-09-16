import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCharacteristicTransport

/-!
# Barycentric debt in literal outgoing quantile transport

The actual outgoing quantile cells have already cancelled prime and polar mass exactly.  Their
first nonzero Fourier jet is not an undifferentiated moment error: it is precisely a signed
linear displacement from the arithmetic node minus a nonnegative squared-displacement debt.

This identifies the sharp local datum that a cofinal signed producer must control.  It is neither
a matched Gamma--Slepian coordinate nor an absolute prime/polar estimate.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Signed first displacement of the literal outgoing quantile cell from its arithmetic node. -/
def ccmOutgoingQuantileCellLinearDisplacement (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * (Real.log n - h)

/-- Unavoidable squared-displacement debt of the literal outgoing quantile cell. -/
def ccmOutgoingQuantileCellQuadraticDisplacementDebt (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * (Real.log n - h) ^ 2

/-- Exact barycentric decomposition of the literal cell's quadratic moment error. -/
theorem ccmActualHeadOutgoingQuantileMomentError_eq_barycentricDebt (n : ℕ) :
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * h ^ 2) =
      2 * Real.log n * ccmOutgoingQuantileCellLinearDisplacement n -
        ccmOutgoingQuantileCellQuadraticDisplacementDebt n := by
  rw [ccmActualHeadOutgoingQuantileMomentError_eq_squareDifference]
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let s := Real.log n
  let L : ℝ → ℝ := fun h => Real.exp (h / 2) * (s - h)
  let Q : ℝ → ℝ := fun h => Real.exp (h / 2) * (s - h) ^ 2
  have hL : IntervalIntegrable L volume b0 b1 :=
    (by fun_prop : Continuous L).intervalIntegrable _ _
  have hQ : IntervalIntegrable Q volume b0 b1 :=
    (by fun_prop : Continuous Q).intervalIntegrable _ _
  change (∫ h in b0..b1, Real.exp (h / 2) * (s ^ 2 - h ^ 2)) =
    2 * s * (∫ h in b0..b1, L h) - ∫ h in b0..b1, Q h
  calc
    _ = ∫ h in b0..b1, (2 * s * L h - Q h) := by
      apply intervalIntegral.integral_congr
      intro h _
      dsimp only [L, Q]
      ring
    _ = (∫ h in b0..b1, 2 * s * L h) - ∫ h in b0..b1, Q h := by
      rw [intervalIntegral.integral_sub (hL.const_mul _) hQ]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]

/-- The quadratic transport debt cannot be paid by cancellation inside one cell. -/
theorem ccmOutgoingQuantileCellQuadraticDisplacementDebt_nonneg (n : ℕ) :
    0 ≤ ccmOutgoingQuantileCellQuadraticDisplacementDebt n := by
  unfold ccmOutgoingQuantileCellQuadraticDisplacementDebt
  apply intervalIntegral.integral_nonneg
    (ccmOutgoingPrimeQuantileBoundary_mono_step n)
  intro h _
  positivity

/-- Positive outgoing curvature requires signed barycentric displacement to pay its full
quadratic debt; no absolute mass bound can replace this condition. -/
theorem ccmActualHeadOutgoingQuantileMomentError_le_linearDisplacement (n : ℕ) :
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * h ^ 2) ≤
      2 * Real.log n * ccmOutgoingQuantileCellLinearDisplacement n := by
  rw [ccmActualHeadOutgoingQuantileMomentError_eq_barycentricDebt]
  linarith [ccmOutgoingQuantileCellQuadraticDisplacementDebt_nonneg n]

/-- The first surviving outgoing cosine-phase jet is the exact barycentric balance. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_eq_barycentricDebt
    (n : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 =
      4 * Real.pi ^ 2 *
        (2 * Real.log n * ccmOutgoingQuantileCellLinearDisplacement n -
          ccmOutgoingQuantileCellQuadraticDisplacementDebt n) := by
  rw [ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero,
    ccmActualHeadOutgoingQuantileMomentError_eq_barycentricDebt]

/-- Total signed credit that the first moments of a finite literal quantile block can contribute
toward its curvature. -/
def ccmOutgoingQuantileFiniteBarycentricCredit (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    2 * Real.log n * ccmOutgoingQuantileCellLinearDisplacement n

/-- Total nonnegative squared-displacement debt of a finite literal quantile block. -/
def ccmOutgoingQuantileFiniteQuadraticDisplacementDebt (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ccmOutgoingQuantileCellQuadraticDisplacementDebt n

/-- Global finite curvature is signed barycentric credit minus exact quadratic debt. -/
theorem ccmActualHeadOutgoingQuantileFiniteMomentError_eq_barycentricDebt (N : ℕ) :
    (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) =
      ccmOutgoingQuantileFiniteBarycentricCredit N -
        ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N := by
  unfold ccmOutgoingQuantileFiniteBarycentricCredit
    ccmOutgoingQuantileFiniteQuadraticDisplacementDebt
  rw [← sum_intervalIntegral_quantileCells_eq_zero_to_boundary
    (fun h : ℝ => Real.exp (h / 2) * h ^ 2) (by fun_prop),
    ← Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact ccmActualHeadOutgoingQuantileMomentError_eq_barycentricDebt n

/-- The finite quadratic debt remains nonnegative before taking any cofinal limit. -/
theorem ccmOutgoingQuantileFiniteQuadraticDisplacementDebt_nonneg (N : ℕ) :
    0 ≤ ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N := by
  unfold ccmOutgoingQuantileFiniteQuadraticDisplacementDebt
  exact Finset.sum_nonneg fun n _ =>
    ccmOutgoingQuantileCellQuadraticDisplacementDebt_nonneg n

/-- A nonnegative finite outgoing curvature can occur only after the literal signed barycentric
credit pays the entire accumulated squared-displacement debt. -/
theorem ccmOutgoingQuantileFiniteQuadraticDebt_le_credit_of_momentError_nonneg
    {N : ℕ}
    (h : 0 ≤ (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ x in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (x / 2) * x ^ 2)) :
    ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N ≤
      ccmOutgoingQuantileFiniteBarycentricCredit N := by
  rw [ccmActualHeadOutgoingQuantileFiniteMomentError_eq_barycentricDebt] at h
  linarith

/-- Exact cofinal target in Fourier curvature coordinates: positive finite curvature is
equivalent to an unshorted signed-credit-versus-debt inequality. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero_eq_barycentricDebt
    (N : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N)) 0 =
      4 * Real.pi ^ 2 *
        (ccmOutgoingQuantileFiniteBarycentricCredit N -
          ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N) := by
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero,
    ccmActualHeadOutgoingQuantileFiniteMomentError_eq_barycentricDebt]

end RHTower
