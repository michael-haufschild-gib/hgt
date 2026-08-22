import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroAnchoredMoment
import GaloisForLFunctions.HTGeometry.ShiftedEulerThirdTangent
import GaloisForLFunctions.HTGeometry.InverseSqrtEndpointIntegral

/-!
# Connected Suzuki third tangent as the literal CCM prime-entry source

The ordinary third shifted-Euler tangent contains a disconnected triple convolution.
Taking its Dirichlet connected cumulant before scalarization cancels that composite mass.
After the forced inverse-square-root and inverse-fifth-log dressing, the surviving
prime-power curvature is exactly the CCM Guinand--Weil prime-entry third-jet scale.
-/

open scoped ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

private theorem ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_one_lt
    (k : ℕ) (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryThirdJetScale k =
      16 * (shiftedEulerConnectedThirdTangentArithmetic k).re /
        (Real.sqrt k * Real.log k ^ 5) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog : Real.log (k : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hk))
  have hsqrt : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hkpos)
  rw [ccmGuinandWeilPrimeEntryThirdJetScale,
    shiftedEulerConnectedThirdTangentArithmetic_apply,
    criticalMellinAtomWeight]
  rw [rpow_neg_half_eq_inv_sqrt (Nat.cast_nonneg k)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pow_two]
  norm_num
  field_simp [hlog, hsqrt]
  ring

/-- **Unconditional source-faithful CCM/Suzuki connected-jet bridge.**  At every canonical
non-unit arithmetic label, the literal CCM prime-entry third jet is the connected third Suzuki
tangent with its forced critical-Mellin/logarithmic dressing.  Disconnected composite Euler mass
has already cancelled in the arithmetic-function ring. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent
    (n : ℕ) :
    ccmGuinandWeilPrimeEntryThirdJetScale (n + 2) =
      16 * (shiftedEulerConnectedThirdTangentArithmetic (n + 2)).re /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) *
          Real.log ((n + 2 : ℕ) : ℝ) ^ 5) :=
  ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_one_lt
    (n + 2) (by omega)

/-- Finite connected-Suzuki realization of the literal CCM prime third-grade rate. -/
def ccmFUSuzukiConnectedThirdTangentRateWindow (b H : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      16 * (shiftedEulerConnectedThirdTangentArithmetic k).re /
        (Real.sqrt k * Real.log k ^ 5)
    else 0

/-- The connected pre-scalar Suzuki producer lands coefficient-faithfully on the full finite CCM
prime rate, with no discarded composite or prime-power terms. -/
theorem ccmFUSuzukiConnectedThirdTangentRateWindow_eq_primeThirdGradeRateWindow
    (b H : ℝ) :
    ccmFUSuzukiConnectedThirdTangentRateWindow b H =
      ccmGuinandWeilPrimeThirdGradeRateWindow b H := by
  rw [ccmFUSuzukiConnectedThirdTangentRateWindow,
    ccmGuinandWeilPrimeThirdGradeRateWindow]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · simp only [hbk, if_true]
    symm
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    exact ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_one_lt
      k (by omega)
  · simp only [hbk, if_false]

/-- Completed prime--polar--Gamma producer with connected Suzuki arithmetic formed before its
scalar readout. -/
def ccmFUSuzukiConnectedThirdTangentCompletedRateWindow (b H : ℝ) : ℝ :=
  ccmFUSuzukiConnectedThirdTangentRateWindow b H -
    ccmGuinandWeilPolarThirdGradeRateWindow b H +
      ccmGuinandWeilGammaThirdGradeRateWindow b H

/-- Exact completed-source landing of the connected Suzuki producer. -/
theorem ccmFUSuzukiConnectedThirdTangentCompletedRateWindow_eq
    (b H : ℝ) :
    ccmFUSuzukiConnectedThirdTangentCompletedRateWindow b H =
      ccmGuinandWeilCompletedThirdGradeRateWindow b H := by
  rw [ccmFUSuzukiConnectedThirdTangentCompletedRateWindow,
    ccmGuinandWeilCompletedThirdGradeRateWindow,
    ccmFUSuzukiConnectedThirdTangentRateWindow_eq_primeThirdGradeRateWindow]

/-- Connected Suzuki realization of the moving triangular prime carrier. -/
def ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow (b H : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      (16 * (shiftedEulerConnectedThirdTangentArithmetic k).re /
          (Real.sqrt k * Real.log k ^ 5)) *
        (1 - Real.log k / H)
    else 0

/-- Coupled connected-Suzuki prime producer and literal triangular polar continuum. -/
def ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow (b H : ℝ) : ℝ :=
  ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H -
    ∫ h in b..H,
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2))

/-- The RH-bearing triangular window is one connected Suzuki producer minus its literal polar
continuum.  Connected arithmetic cancellation occurs before scalarization and before the
positive/negative prime--polar regions are compared. -/
theorem ccmGuinandWeilPrimePolarTriangularWindow_eq_connectedSuzukiProducer
    (b H : ℝ) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) =
      ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow b H := by
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow,
    ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow]
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k *
              ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k)
          else 0) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            (16 * (shiftedEulerConnectedThirdTangentArithmetic k).re /
                (Real.sqrt k * Real.log k ^ 5)) *
              (1 - Real.log k / H)
          else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight]
      rw [← mul_assoc,
        criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale]
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_one_lt
        k (by omega)]
    · simp only [hbk, if_false]
  rw [hprime]

end


end RHTower
