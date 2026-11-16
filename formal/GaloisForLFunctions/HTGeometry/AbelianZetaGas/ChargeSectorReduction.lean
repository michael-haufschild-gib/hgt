import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasPositivity
import GaloisForLFunctions.HTGeometry.Quantum.ChargeSectorPinching

/-!
# Exact charge-sector reduction for finite Gibbs observations

The Gibbs Gram kernel already vanishes between unequal monomial charges.
Positive test matrices can therefore be pinched into those sectors with
unchanged trace and unchanged Gibbs objective. This is the charge-block
reduction used for fermionic marginal constraints, transferred to the gas.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix Quantum
open scoped ComplexOrder

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq M]

/-- Every finite Gibbs Gram section is fixed by its monomial-charge pinching. -/
theorem chargePinch_gibbsGram (t : M → ℝ) (word : ι → GasWord M) :
    chargePinch (fun i => GasWord.charge (word i))
      ((GasWord.gramKernel t).submatrix word word) =
        (GasWord.gramKernel t).submatrix word word := by
  apply (chargePinch_eq_self_iff _ _).mpr
  intro i j hij
  change GasWord.gibbsWeight (fun k => (t k : ℂ))
    (GasWord.wstar (word i) * word j) = 0
  rw [GasWord.gibbsWeight_wstar_mul, if_neg hij]

/-- Charge reduction preserves the exact Gibbs objective for every finite test matrix. -/
theorem trace_gibbsGram_chargePinch (t : M → ℝ) (word : ι → GasWord M)
    (X : Matrix ι ι ℂ) :
    ((GasWord.gramKernel t).submatrix word word *
      chargePinch (fun i => GasWord.charge (word i)) X).trace =
        ((GasWord.gramKernel t).submatrix word word * X).trace := by
  rw [← trace_chargePinch_mul, chargePinch_gibbsGram]

/-- Every positive Gibbs test has a positive charge-diagonal replacement of equal trace
and equal objective value. -/
theorem gibbs_positive_test_charge_reduction (t : M → ℝ) (word : ι → GasWord M)
    (X : {A : Matrix ι ι ℂ // A.PosSemidef}) :
    ∃ Y : Matrix ι ι ℂ, Y.PosSemidef ∧ Y.trace = X.1.trace ∧
      (∀ i j, GasWord.charge (word i) ≠ GasWord.charge (word j) → Y i j = 0) ∧
      ((GasWord.gramKernel t).submatrix word word * Y).trace =
        ((GasWord.gramKernel t).submatrix word word * X.1).trace := by
  let charge := fun i => GasWord.charge (word i)
  refine ⟨chargePinch charge X.1, chargePinch_posSemidef charge X.2,
    trace_chargePinch charge X.1, ?_, trace_gibbsGram_chargePinch t word X.1⟩
  exact (chargePinch_eq_self_iff charge _).mp (chargePinch_idempotent charge X.1)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.chargePinch_gibbsGram
#print axioms GaloisForLFunctions.HTGeometry.trace_gibbsGram_chargePinch
#print axioms GaloisForLFunctions.HTGeometry.gibbs_positive_test_charge_reduction
