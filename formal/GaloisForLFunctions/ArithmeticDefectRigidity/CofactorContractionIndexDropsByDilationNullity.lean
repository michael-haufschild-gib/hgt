import GaloisForLFunctions.ArithmeticDefectRigidity.TheClosedCofactorAnnihilatorHasNoCountableIndex
import GaloisForLFunctions.ArithmeticDefectRigidity.ContractedCofactorModulesAreClosedDilationRanges

/-!
# Cofactor contraction index drops by dilation nullity

The finite annihilator-quotient index equals Hilbert dimension. Its change
under a positive cofactor contraction is exactly the dilation nullity.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- In a finite actual module, the principal quotient index drops by precisely the dilation nullity. -/
theorem cofactor_index_add_dilation_nullity {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (p : ℕ+) (hp : 0 < L.kernel p p) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ cofactorAnnihilator L p) +
      Module.finrank ℂ (LinearMap.ker (dilation L p).toLinearMap) =
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) := by
  obtain ⟨M, hK, hI⟩ := exists_actual_contracted_module L p hp
  letI : FiniteDimensional ℂ (Hilbert M) := FiniteDimensional.of_injective
    (contractedKernelIsometry L M p hp hK).toLinearMap
    (contractedKernelIsometry L M p hp hK).injective
  rw [← hI, finrank_quotient_eq_of_finite M, finrank_quotient_eq_of_finite L]
  exact contracted_finrank_add_dilation_nullity L M p hp hK

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cofactor_index_add_dilation_nullity
end
