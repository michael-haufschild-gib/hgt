import GaloisForLFunctions.RHTower.CCMPrimeEntryChronologicalPair
import GaloisForLFunctions.RHTower.CCMPrimeEntryIntegratedDeficit
import GaloisForLFunctions.RHTower.CCMPrimeEntryJumpBudget

/-!
# Positive storage and chronological signed prime work

The storage is `(r+q)^2+q^2`, where `r` is the square-root-normalized
integrated deficit and `q` the normalized instantaneous Chebyshev error.
Its exact finite-time balance keeps the work sampled before every prime
entry and a quadratic jump budget. Only the latter is bounded here; no
upper estimate for the signed chronological work is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitCausalStorage (T : ℝ) : ℝ :=
  Real.exp (-T) *
    ((ccmLogChebyshevDeficitPrimitive T + Real.exp T - Chebyshev.psi (Real.exp T)) ^ 2 +
      (Real.exp T - Chebyshev.psi (Real.exp T)) ^ 2)

def ccmPrimeDeficitChronologicalWork (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t) +
    2 * ccmLogChebyshevDeficitPrimitive T - ccmPrimeEntryPrejumpWork ⌊Real.exp T⌋₊

theorem ccmPrimeDeficitCausalStorage_nonneg (T : ℝ) :
    0 ≤ ccmPrimeDeficitCausalStorage T := by
  unfold ccmPrimeDeficitCausalStorage
  positivity

@[simp] theorem ccmPrimeDeficitCausalStorage_zero : ccmPrimeDeficitCausalStorage 0 = 2 := by
  simp [ccmPrimeDeficitCausalStorage, ccmLogChebyshevDeficitPrimitive, Chebyshev.psi_one]
  ring

/-- Storage controls the actual critical deficit, with the sharp quadratic
comparison constant two. -/
theorem ccmPrimeDeficitCriticalEnergy_le_causalStorage (T : ℝ) :
    ccmPrimeDeficitCriticalEnergy T ≤ 2 * ccmPrimeDeficitCausalStorage T := by
  unfold ccmPrimeDeficitCriticalEnergy ccmPrimeDeficitCausalStorage
  have h : ccmLogChebyshevDeficitPrimitive T ^ 2 ≤
      2 * ((ccmLogChebyshevDeficitPrimitive T + Real.exp T - Chebyshev.psi (Real.exp T)) ^ 2 +
        (Real.exp T - Chebyshev.psi (Real.exp T)) ^ 2) := by
    nlinarith only [sq_nonneg (ccmLogChebyshevDeficitPrimitive T +
      2 * (Real.exp T - Chebyshev.psi (Real.exp T)))]
  nlinarith only [mul_le_mul_of_nonneg_left h (Real.exp_pos (-T)).le]

private theorem causalStorage_eq_boundary {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCausalStorage T = ccmPrimeEntryPairBoundary T +
      Real.exp T + Real.exp (-T) + 2 * Real.exp (-T) *
        (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) +
      4 * ccmLogChebyshevDeficitPrimitive T - 6 * Chebyshev.psi (Real.exp T) := by
  rw [ccmPrimeDeficitCausalStorage,
    ccmLogChebyshevDeficitPrimitive_eq_entry_prefix hT le_rfl, ccmPrimeEntryPairBoundary]
  have hc : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = Real.exp (-T) *
          ((ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) ^ 2 +
            Chebyshev.psi (Real.exp T) ^ 2) +
        5 * (Real.exp (-T) * Real.exp T) * Real.exp T -
        4 * (Real.exp (-T) * Real.exp T) * (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + 1) -
        6 * (Real.exp (-T) * Real.exp T) * Chebyshev.psi (Real.exp T) +
        Real.exp (-T) * (2 * (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T +
          Chebyshev.psi (Real.exp T)) + 1) := by ring
    _ = _ := by rw [hc]; ring

/-- Exact balance of positive storage, integrated critical energy, signed
chronological work, and all prime-power self-jumps. -/
theorem ccmPrimeDeficitChronologicalWork_balance {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCausalStorage T +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
        2 + 2 * ccmPrimeDeficitChronologicalWork T + ccmPrimeEntryJumpBudget T := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hpsi : Chebyshev.psi (⌊Real.exp T⌋₊ : ℝ) = Chebyshev.psi (Real.exp T) := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [causalStorage_eq_boundary hT,
    ccmPrimeDeficitCriticalEnergy_integral_eq_pair_limit hT,
    ccmPrimeEntryPairLimit_eq_prejumpWork, hpsi,
    ccmPrimeDeficitChronologicalWork, integral_ccmLogChebyshevDeficitPrimitive_eq_background hT,
    ccmPrimeEntryJumpBudget, Sieve.vonMangoldtHarmonicSquareSum_eq_Icc_one _ hN]
  ring

/-- Positivity supplies a lower bound on work. Its direction must not be
reversed when seeking critical-scale control. -/
theorem ccmPrimeDeficitChronologicalWork_lower {T : ℝ} (hT : 0 ≤ T) :
    -(1 + ccmPrimeEntryJumpBudget T / 2) ≤ ccmPrimeDeficitChronologicalWork T := by
  have h := ccmPrimeDeficitChronologicalWork_balance hT
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t :=
    intervalIntegral.integral_nonneg hT (fun t _ => ccmPrimeDeficitCriticalEnergy_nonneg t)
  linarith [ccmPrimeDeficitCausalStorage_nonneg T]

/-- An unconditional upper estimate retains the signed work explicitly;
only the separately proved jump budget has been bounded. -/
theorem ccmPrimeDeficitCausalStorage_add_energy_le_work {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCausalStorage T +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) ≤
        2 * ccmPrimeDeficitChronologicalWork T + T ^ 2 + 78 * T + 52 := by
  rw [ccmPrimeDeficitChronologicalWork_balance hT]
  linarith only [ccmPrimeEntryJumpBudget_le_quadratic hT]

end RHTower
