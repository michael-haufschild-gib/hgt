/-
Symmetric shift of a line-reflection functional equation.

For a completed carrier with Schwarz functional equation about `Re s = 1/2`,
the symmetric translate `F(s + a) F(s - a)` retains the same form with root
number squared.  This records its exact divisor motion: every zero yields the
two shifted zeros and a central-line zero yields a reflected pair at the two
shifted abscissae.
-/
import GaloisForLFunctions.RHTower.WindowRelation

open Complex

namespace RHTower

noncomputable section

/-- Symmetric real shift of a complex carrier. -/
def symmetricShiftProduct (F : ℂ → ℂ) (a : ℝ) (s : ℂ) : ℂ :=
  F (s + (a : ℂ)) * F (s - (a : ℂ))

/-- Schwarz functional equation about the critical line. -/
def hasLineSchwarzFunctionalEquation (F : ℂ → ℂ) (epsilon : ℂ) : Prop :=
  ∀ s : ℂ, F (lineReflect s) = epsilon * (starRingEnd ℂ) (F s)

/-- At zero shift the product is the square of the original carrier. -/
theorem symmetricShiftProduct_zero_shift (F : ℂ → ℂ) (s : ℂ) :
    symmetricShiftProduct F 0 s = F s ^ (2 : ℕ) := by
  simp [symmetricShiftProduct, pow_two]

/-- At zero shift the symmetric product has exactly the original zero set. -/
theorem symmetricShiftProduct_zero_at_zero_iff (F : ℂ → ℂ) (s : ℂ) :
    symmetricShiftProduct F 0 s = 0 ↔ F s = 0 := by
  simp [symmetricShiftProduct]

theorem lineReflect_add_real (s : ℂ) (a : ℝ) :
    lineReflect (s + (a : ℂ)) = lineReflect s - (a : ℂ) := by
  unfold lineReflect
  simp only [map_add, Complex.conj_ofReal]
  ring

theorem lineReflect_sub_real (s : ℂ) (a : ℝ) :
    lineReflect (s - (a : ℂ)) = lineReflect s + (a : ℂ) := by
  unfold lineReflect
  simp only [map_sub, Complex.conj_ofReal]
  ring

/-- A symmetric shift squares the root number of a Schwarz functional equation. -/
theorem hasLineSchwarzFunctionalEquation_symmetricShiftProduct
    {F : ℂ → ℂ} {epsilon : ℂ}
    (hF : hasLineSchwarzFunctionalEquation F epsilon) (a : ℝ) :
    hasLineSchwarzFunctionalEquation (symmetricShiftProduct F a) (epsilon ^ (2 : ℕ)) := by
  intro s
  rw [symmetricShiftProduct, ← lineReflect_sub_real s a, ← lineReflect_add_real s a,
    hF, hF]
  rw [symmetricShiftProduct, map_mul]
  ring

/-- The symmetric shift of the completed Xi function retains its line reflection law. -/
theorem xi_symmetricShiftProduct_lineReflect (a : ℝ) (s : ℂ) :
    symmetricShiftProduct xi a (lineReflect s) =
      (starRingEnd ℂ) (symmetricShiftProduct xi a s) := by
  have hxi : hasLineSchwarzFunctionalEquation xi 1 := by
    intro z
    unfold lineReflect
    rw [xi_one_sub ((starRingEnd ℂ) z), xi_conj]
    simp
  simpa using hasLineSchwarzFunctionalEquation_symmetricShiftProduct hxi a s

/-- Every zero of `F` yields zeros at both symmetric shifted locations. -/
theorem symmetricShiftProduct_zero_translates
    (F : ℂ → ℂ) (a : ℝ) {rho : ℂ} (hrho : F rho = 0) :
    symmetricShiftProduct F a (rho + (a : ℂ)) = 0 ∧
      symmetricShiftProduct F a (rho - (a : ℂ)) = 0 := by
  constructor
  · apply mul_eq_zero_of_right
    simpa only [add_sub_cancel_right] using hrho
  · apply mul_eq_zero_of_left
    simpa only [sub_add_cancel] using hrho

/-- Real parts of the two shifted copies of a critical-line point. -/
theorem symmetricShiftProduct_pair_re
    {rho : ℂ} (a : ℝ) (hrho : rho.re = 1 / 2) :
    (rho + (a : ℂ)).re = 1 / 2 + a ∧
      (rho - (a : ℂ)).re = 1 / 2 - a := by
  constructor
  · simp [hrho]
  · simp [hrho]

/-- Nonzero shifts move both copies of a critical-line point off that line. -/
theorem symmetricShiftProduct_pair_off_critical_line
    {rho : ℂ} (a : ℝ) (hrho : rho.re = 1 / 2) (ha : a ≠ 0) :
    (rho + (a : ℂ)).re ≠ 1 / 2 ∧
      (rho - (a : ℂ)).re ≠ 1 / 2 := by
  have hpair := symmetricShiftProduct_pair_re a hrho
  constructor
  · rw [hpair.1]
    intro h
    apply ha
    linarith
  · rw [hpair.2]
    intro h
    apply ha
    linarith

/-- A critical-line zero of Xi becomes two off-line zeros under every nonzero shift. -/
theorem xi_symmetricShiftProduct_criticalZero_pair_off_critical_line
    {rho : ℂ} (a : ℝ) (hzero : xi rho = 0)
    (hrho : rho.re = 1 / 2) (ha : a ≠ 0) :
    (symmetricShiftProduct xi a (rho + (a : ℂ)) = 0 ∧
      symmetricShiftProduct xi a (rho - (a : ℂ)) = 0) ∧
      ((rho + (a : ℂ)).re ≠ 1 / 2 ∧
        (rho - (a : ℂ)).re ≠ 1 / 2) :=
  ⟨symmetricShiftProduct_zero_translates xi a hzero,
    symmetricShiftProduct_pair_off_critical_line a hrho ha⟩

/-- The two shifts of a critical-line point are line-reflection partners. -/
theorem lineReflect_symmetricShiftProduct_pair
    {rho : ℂ} (a : ℝ) (hrho : rho.re = 1 / 2) :
    lineReflect (rho + (a : ℂ)) = rho - (a : ℂ) := by
  apply Complex.ext
  · rw [lineReflect_re]
    simp [hrho]
    ring
  · simp [lineReflect]

end

end RHTower
