import GaloisForLFunctions.RHTower.ThetaMellinSixIntegralNuclearFormation

/-!
# Signed prime--Hodge integral--nuclear homotopy defect

This module packages the already constructed positive prime--history defect into one two-sided
wall family.  Off the neutral wall it retains every cross-prime entry, is Schatten-one with unit
trace norm, and carries the integral trace `sign t`.  Reflection reverses the operator.  Its
diagonal is the literal theta Mellin-six flux times the unsquared prime density.

No zero, divisor copy, ordinate, or RH premise enters the construction.
-/

open Filter Topology BigOperators

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- The signed two-sided prime--Hodge nuclear wall family. -/
noncomputable def primeHodgeHistoryIntegralNuclearHomotopyDefect (t : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  if ht : t = 0 then 0 else
    (Real.sign t : ℂ) • primeHodgeHistoryDefectOperator (abs_pos.mpr ht)

@[simp] theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_zero :
    primeHodgeHistoryIntegralNuclearHomotopyDefect 0 = 0 := by
  simp [primeHodgeHistoryIntegralNuclearHomotopyDefect]

theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_eq_of_pos
    {t : ℝ} (ht : 0 < t) :
    primeHodgeHistoryIntegralNuclearHomotopyDefect t =
      primeHodgeHistoryDefectOperator ht := by
  simp [primeHodgeHistoryIntegralNuclearHomotopyDefect, ht.ne',
    abs_of_pos ht, Real.sign_of_pos ht]

theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_eq_neg_of_neg
    {t : ℝ} (ht : t < 0) :
    primeHodgeHistoryIntegralNuclearHomotopyDefect t =
      -primeHodgeHistoryDefectOperator (abs_pos.mpr ht.ne) := by
  simp [primeHodgeHistoryIntegralNuclearHomotopyDefect, ht.ne,
    Real.sign_of_neg ht]

@[simp] theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_neg (t : ℝ) :
    primeHodgeHistoryIntegralNuclearHomotopyDefect (-t) =
      -primeHodgeHistoryIntegralNuclearHomotopyDefect t := by
  by_cases ht : t = 0
  · subst t
    simp
  · simp [primeHodgeHistoryIntegralNuclearHomotopyDefect, ht,
      Real.sign_neg, abs_neg]

theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_memSchattenClass_one (t : ℝ) :
    MemSchattenClass 1 (primeHodgeHistoryIntegralNuclearHomotopyDefect t) := by
  by_cases ht : t = 0
  · subst t
    rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_zero]
    simpa using memSchattenClass_one_smul
      (primeHodgeHistoryDefectOperator_memSchattenClass_one zero_lt_one) (0 : ℂ)
  · rw [primeHodgeHistoryIntegralNuclearHomotopyDefect, dif_neg ht]
    exact memSchattenClass_one_smul
      (primeHodgeHistoryDefectOperator_memSchattenClass_one (abs_pos.mpr ht)) _

theorem opTrace_primeHodgeHistoryIntegralNuclearHomotopyDefect (t : ℝ) :
    ContinuousLinearMap.opTrace (primeHodgeHistoryIntegralNuclearHomotopyDefect t) =
      (Real.sign t : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp [primeHodgeHistoryIntegralNuclearHomotopyDefect]
  · rw [primeHodgeHistoryIntegralNuclearHomotopyDefect, dif_neg ht,
      opTrace_smul, opTrace_primeHodgeHistoryDefectOperator (abs_pos.mpr ht), mul_one]

theorem traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect (t : ℝ) :
    traceNorm PrimeHodgeHistoryHilbert
      (primeHodgeHistoryIntegralNuclearHomotopyDefect t) = |Real.sign t| := by
  by_cases ht : t = 0
  · subst t
    simp [primeHodgeHistoryIntegralNuclearHomotopyDefect, traceNorm_zero]
  · rw [primeHodgeHistoryIntegralNuclearHomotopyDefect, dif_neg ht,
      traceNorm_smul,
      traceNorm_primeHodgeHistoryDefectOperator (abs_pos.mpr ht), mul_one,
      Complex.norm_real, Real.norm_eq_abs]

theorem traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect_of_ne
    {t : ℝ} (ht : t ≠ 0) :
    traceNorm PrimeHodgeHistoryHilbert
      (primeHodgeHistoryIntegralNuclearHomotopyDefect t) = 1 := by
  rw [traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect]
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · rw [Real.sign_of_neg htneg]
    norm_num
  · rw [Real.sign_of_pos htpos]
    norm_num

theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_isPositive_of_pos
    {t : ℝ} (ht : 0 < t) :
    (primeHodgeHistoryIntegralNuclearHomotopyDefect t).IsPositive := by
  rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_eq_of_pos ht]
  exact primeHodgeHistoryDefectOperator_isPositive ht

theorem neg_primeHodgeHistoryIntegralNuclearHomotopyDefect_isPositive_of_neg
    {t : ℝ} (ht : t < 0) :
    (-primeHodgeHistoryIntegralNuclearHomotopyDefect t).IsPositive := by
  rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_eq_neg_of_neg ht]
  simp only [neg_neg]
  exact primeHodgeHistoryDefectOperator_isPositive (abs_pos.mpr ht.ne)

@[simp] theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_one :
    primeHodgeHistoryIntegralNuclearHomotopyDefect 1 =
      primeHodgeHistoryIntegralNuclearDefectT := by
  simp [primeHodgeHistoryIntegralNuclearHomotopyDefect,
    primeHodgeHistoryIntegralNuclearDefectT]

/-- Literal signed matrix of the two-sided defect. -/
def primeHodgeHistoryIntegralNuclearHomotopyDefectKernel
    (t : ℝ) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  if t = 0 then 0 else
    (Real.sign t : ℂ) * primeHodgeHistoryDefectKernel |t| ab

theorem primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_sameHistory_ne_zero
    {t : ℝ} (ht : t ≠ 0) (n : ℕ) (p q : Nat.Primes) :
    primeHodgeHistoryIntegralNuclearHomotopyDefectKernel t ((n, p), (n, q)) ≠ 0 := by
  rw [primeHodgeHistoryIntegralNuclearHomotopyDefectKernel, if_neg ht]
  have hsign : (Real.sign t : ℂ) ≠ 0 := by
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · simp [Real.sign_of_neg htneg]
    · simp [Real.sign_of_pos htpos]
  exact mul_ne_zero hsign
    (primeHodgeHistoryDefectKernel_sameHistory_ne_zero (abs_pos.mpr ht) n p q)

/-- On every nonneutral chamber, the signed diagonal of the single defect is exactly theta's
Mellin-six boundary flux times the unsquared, coefficient-faithful prime density. -/
theorem primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_diagonal_eq_thetaFlux
    {t : ℝ} (ht : t ≠ 0) (n : ℕ) (p : Nat.Primes) :
    primeHodgeHistoryIntegralNuclearHomotopyDefectKernel t ((n, p), (n, p)) =
      (Real.sign t : ℂ) *
        (thetaCuspMellinSixFlux n *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight |t| p /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent |t| : ℝ) := by
  rw [primeHodgeHistoryIntegralNuclearHomotopyDefectKernel, if_neg ht,
    primeHodgeHistoryDefectKernel_diagonal (abs_pos.mpr ht),
    primeHodgeHistoryDiagonalWeight_eq_thetaCuspMellinSixFlux]

/-- Closed certificate for one signed pre-divisor, prime-mixed, integral--nuclear homotopy
defect. -/
theorem primeHodgeHistoryIntegralNuclearHomotopyDefect_closed (t : ℝ) :
    MemSchattenClass 1 (primeHodgeHistoryIntegralNuclearHomotopyDefect t) ∧
      ContinuousLinearMap.opTrace (primeHodgeHistoryIntegralNuclearHomotopyDefect t) =
        (Real.sign t : ℂ) ∧
      traceNorm PrimeHodgeHistoryHilbert
        (primeHodgeHistoryIntegralNuclearHomotopyDefect t) = |Real.sign t| ∧
      primeHodgeHistoryIntegralNuclearHomotopyDefect (-t) =
        -primeHodgeHistoryIntegralNuclearHomotopyDefect t ∧
      (0 < t → (primeHodgeHistoryIntegralNuclearHomotopyDefect t).IsPositive) ∧
      (t < 0 → (-primeHodgeHistoryIntegralNuclearHomotopyDefect t).IsPositive) ∧
      (t ≠ 0 → ∀ n p q,
        primeHodgeHistoryIntegralNuclearHomotopyDefectKernel t ((n, p), (n, q)) ≠ 0) := by
  exact ⟨primeHodgeHistoryIntegralNuclearHomotopyDefect_memSchattenClass_one t,
    opTrace_primeHodgeHistoryIntegralNuclearHomotopyDefect t,
    traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect t,
    primeHodgeHistoryIntegralNuclearHomotopyDefect_neg t,
    primeHodgeHistoryIntegralNuclearHomotopyDefect_isPositive_of_pos,
    neg_primeHodgeHistoryIntegralNuclearHomotopyDefect_isPositive_of_neg,
    fun ht n p q =>
      primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_sameHistory_ne_zero ht n p q⟩

end
end RHTower
