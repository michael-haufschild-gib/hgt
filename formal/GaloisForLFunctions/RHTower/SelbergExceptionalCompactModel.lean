import GaloisForLFunctions.RHTower.SelbergExceptionalSphericalModel
import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactIrreducibility
import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactUnitarity

/-!
# Exceptional Selberg parameters in the compact principal-series model

Every scalar `0 < λ < 1/4` is realized by the normalized finite compact-picture complementary
series with parameter `s = 2 sqrt(1/4-λ)`.  Its shifted Casimir is `λ`, its positive invariant
form exists, and its Harish-Chandra module is irreducible.  This is the concrete local endpoint of
the Maass-to-representation part of the symmetric-power strategy.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exceptional parameter belongs to the exact compact-picture unitarity locus. -/
theorem SelbergExceptionalEigenvalue.compactLocalParameter_unitarizable
    (eigenvalue : SelbergExceptionalEigenvalue) :
    2 * eigenvalue.complementaryExponent ∈
      UnitarizableCompactSphericalPrincipalParameter := by
  rw [unitarizableCompactSphericalPrincipalParameter_eq_Ioo]
  have hν := eigenvalue.complementaryExponent_mem_Ioo
  rcases hν with ⟨hνpos, hνhalf⟩
  constructor <;> linarith

/-- Shifted compact-picture Casimir has the exceptional eigenvalue as its scalar. -/
theorem SelbergExceptionalEigenvalue.compactSphericalPrincipalLaplacian_eq
    (eigenvalue : SelbergExceptionalEigenvalue) :
    compactSphericalPrincipalLaplacian
        (2 * eigenvalue.complementaryExponent) =
      (eigenvalue.1 : ℂ) • LinearMap.id := by
  rw [compactSphericalPrincipalLaplacian_eq_smul_id]
  congr 1
  norm_cast
  rw [← eigenvalue.eigenvalueOfComplementaryExponent_eq]
  simp [eigenvalueOfComplementaryExponent]
  ring

/-- Exceptional compact-picture Harish-Chandra module is irreducible. -/
theorem SelbergExceptionalEigenvalue.compactSphericalPrincipal_irreducible
    (eigenvalue : SelbergExceptionalEigenvalue) :
    ∀ W : Submodule ℂ
        (normalizedRealCompactKFiniteSubmodule
          (2 * eigenvalue.complementaryExponent)),
      IsCompactSphericalHarishChandraSubmodule
          (2 * eigenvalue.complementaryExponent) W →
        W = ⊥ ∨ W = ⊤ := by
  apply compactSphericalPrincipal_irreducible_of_abs_lt_one
  have hν := eigenvalue.complementaryExponent_mem_Ioo
  rcases hν with ⟨hνpos, hνhalf⟩
  rw [abs_lt]
  constructor <;> linarith

end
end GaloisForLFunctions.RHTower
