import GaloisForLFunctions.ArithmeticDefectRigidity.FixedCofactorsHaveAHarmonicBoundaryTrace
import GaloisForLFunctions.ArithmeticDefectRigidity.ForcingScaleSeparation
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The paid commutator of cofactor renormalization and integer dilation

The finite cofactor operator commutes with every floor dilation. Its linear pole subtraction
has one explicit commutator: the row's boundary trace times the rounding defect of the power.
That defect is bounded by one, uniformly in the cell and dilation. The actual trace therefore
pays a horizon-independent norm budget, even when the dilation moves with the horizon.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Finite cofactor summation commutes with floor dilation on the proved zero-origin domain. -/
theorem finiteCofactorOperator_traceDilation (ε : SubcriticalDamping) (v : poleTraceDomain ε)
    (p : ℕ+) (n : ℕ) :
    finiteCofactorOperator ε (traceDilation ε p v) n = finiteCofactorOperator ε v (n / p) := by
  change (∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) * v ((n / j) / p)) =
    ∑ j ∈ Icc 2 (n / p), (j : ℝ) ^ (-(ε : ℝ)) * v ((n / p) / j)
  have hdiv (j : ℕ) : (n / j) / p = (n / p) / j := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm j (p : ℕ)]
  simp_rw [hdiv]
  apply (sum_subset (Icc_subset_Icc le_rfl (Nat.div_le_self n p)) ?_).symm
  intro j hj hjsmall
  have hjgt : n / p < j := by
    simp only [mem_Icc] at hj hjsmall
    omega
  rw [Nat.div_eq_of_lt hjgt, v.property.1, mul_zero]

/-- The exact failure of pole subtraction to commute with integer dilation. -/
theorem renormalizedCofactorOperator_commutator_eq (ε : SubcriticalDamping)
    (v : poleTraceDomain ε) (p : ℕ+) (n : ℕ) :
    renormalizedCofactorOperator ε (traceDilation ε p v) n -
      renormalizedCofactorOperator ε v (n / p) =
      poleTrace ε v * (((n / p : ℕ) : ℝ) ^ (1 - (ε : ℝ)) -
        (p : ℝ) ^ (-(1 - (ε : ℝ))) * (n : ℝ) ^ (1 - (ε : ℝ))) := by
  change (finiteCofactorOperator ε (traceDilation ε p v) n -
      poleTrace ε (traceDilation ε p v) * (n : ℝ) ^ (1 - (ε : ℝ))) -
    (finiteCofactorOperator ε v (n / p) -
      poleTrace ε v * ((n / p : ℕ) : ℝ) ^ (1 - (ε : ℝ))) = _
  rw [finiteCofactorOperator_traceDilation, poleTrace_traceDilation]
  ring

private theorem power_rounding_error_le (ε : SubcriticalDamping) (p : ℕ+) (n : ℕ) :
    |((n / p : ℕ) : ℝ) ^ (1 - (ε : ℝ)) -
      (p : ℝ) ^ (-(1 - (ε : ℝ))) * (n : ℝ) ^ (1 - (ε : ℝ))| ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property
  have hα : 0 ≤ 1 - (ε : ℝ) := by linarith [ε.property.2]
  have hα1 : 1 - (ε : ℝ) ≤ 1 := by linarith [ε.property.1]
  have hid : (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n (p : ℕ)).symm
  have hrem : ((n % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt n p.property
  have hlo : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [hid, (Nat.cast_nonneg (n % p) : (0 : ℝ) ≤ ((n % p : ℕ) : ℝ))]
  have hhi : (n : ℝ) / (p : ℝ) ≤ ((n / p : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hid, hrem]
  have hpowerlo := Real.rpow_le_rpow (Nat.cast_nonneg (n / p)) hlo hα
  have hpowerhi := (Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg n) hp.le) hhi hα).trans
    (Real.rpow_add_le_add_rpow (Nat.cast_nonneg (n / p)) zero_le_one hα hα1)
  rw [Real.one_rpow] at hpowerhi
  have hscale : (p : ℝ) ^ (-(1 - (ε : ℝ))) * (n : ℝ) ^ (1 - (ε : ℝ)) =
      ((n : ℝ) / (p : ℝ)) ^ (1 - (ε : ℝ)) := by
    rw [Real.div_rpow (Nat.cast_nonneg n) hp.le, Real.rpow_neg hp.le]
    ring
  rw [hscale]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The row's own absolute trace pays the commutator, uniformly over all integer dilations. -/
theorem abs_renormalizedCofactorOperator_commutator_le (ε : SubcriticalDamping)
    (v : poleTraceDomain ε) (p : ℕ+) (n : ℕ) :
    |renormalizedCofactorOperator ε (traceDilation ε p v) n -
      renormalizedCofactorOperator ε v (n / p)| ≤ |poleTrace ε v| := by
  rw [renormalizedCofactorOperator_commutator_eq, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (power_rounding_error_le ε p n) (abs_nonneg (poleTrace ε v))

/-- The commutator has a global pronic norm budget on the full trace domain. -/
theorem pronicNorm_renormalizedCofactorOperator_commutator_le (ε : SubcriticalDamping)
    (v : poleTraceDomain ε) (p : ℕ+) (T : ℕ) :
    pronicNorm T (fun n => renormalizedCofactorOperator ε (traceDilation ε p v) n -
      renormalizedCofactorOperator ε v (n / p)) ≤ |poleTrace ε v| :=
  TransHorizonIncidenceMechanics.pronicNorm_le_of_abs_le (abs_nonneg _)
    (abs_renormalizedCofactorOperator_commutator_le ε v p) T

/-- The actual dilation commutator's energy, with its source trace retained. -/
def actualCofactorCommutatorEnergy (ε : SubcriticalDamping) (p : ℕ+) (T : ℕ) : ℝ :=
  pronicNorm T (fun n =>
    renormalizedCofactorOperator ε (traceDilation ε p (actualTraceVector ε)) n -
      renormalizedCofactorOperator ε (actualTraceVector ε) (n / p)) ^ 2

/-- The actual source pays every dilation commutator with its proved forcing coefficient. -/
theorem actualCofactorCommutatorEnergy_le (ε : SubcriticalDamping) (p : ℕ+) (T : ℕ) :
    actualCofactorCommutatorEnergy ε p T ≤ forcingPowerCoefficient ε ^ 2 := by
  have h := pow_le_pow_left₀ (pronicNorm_nonneg _ _)
    (pronicNorm_renormalizedCofactorOperator_commutator_le ε (actualTraceVector ε) p T) 2
  simpa only [actualCofactorCommutatorEnergy, sq_abs, poleTrace_actualTraceVector] using h

/-- Even a horizon-dependent integer dilation has negligible normalized commutator on escape. -/
theorem admits_or_moving_cofactor_commutator_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ p : ℕ → ℕ+,
      Tendsto (fun T => actualCofactorCommutatorEnergy ε (p T) T /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun p => squeeze_zero
      (fun T => div_nonneg (sq_nonneg _) (dampedMobiusEnergy_nonneg ε T))
      (fun T => div_le_div_of_nonneg_right (actualCofactorCommutatorEnergy_le ε (p T) T)
        (dampedMobiusEnergy_nonneg ε T)) ?_
    exact tendsto_const_nhds.div_atTop hE

end GaloisForLFunctions.ArithmeticDefectRigidity
