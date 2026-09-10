import GaloisForLFunctions.HTGeometry.GomesDerivativePowerChainTransfers
import GaloisForLFunctions.HTGeometry.SuperPoincarePolynomialReflection
import GaloisForLFunctions.HTGeometry.StokesWeylFourierSource

/-!
# Full symmetry algebras of the corpus's actual derivative and momentum operators

The supertranslation momentum is the second derivative, whose full symmetry algebra
is a two-by-two formal power-series matrix algebra. It contains noncommuting
symmetries and nonzero square-zero operators exchanging the two residue chains.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- The actual supertranslation momentum has the complete two-chain formal matrix symmetry algebra. -/
def gomesSupertranslationMomentumCommutantEquiv :
    (Subalgebra.centralizer ℂ {polynomialReflectionD1N2Split.momentum0}) ≃ₐ[ℂ]
      Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) :=
  gomesPolynomialDerivativePowerCommutantEquiv ℂ 2

/-- Every positive power of the corpus's Weyl derivative has its full formal matrix classification. -/
theorem gomesWeylDerivativePowerCommutant_classification (m : ℕ) :
    Nonempty ((Subalgebra.centralizer ℂ
      {GaloisForLFunctions.IrregularStokes.WeylFourier.polynomialDerivativeOperator ^ (m + 1)}) ≃ₐ[ℂ]
        Matrix (Fin (m + 1)) (Fin (m + 1)) (PowerSeries ℂ)) :=
  ⟨gomesPolynomialDerivativePowerCommutantEquiv ℂ (m + 1)⟩

/-- The actual supertranslation momentum admits an explicit pair of noncommuting linear symmetries. -/
theorem gomesSupertranslationMomentum_noncommuting_symmetries :
    ∃ E F : Module.End ℂ ℂ[X],
      E * polynomialReflectionD1N2Split.momentum0 = polynomialReflectionD1N2Split.momentum0 * E ∧
      F * polynomialReflectionD1N2Split.momentum0 = polynomialReflectionD1N2Split.momentum0 * F ∧
      E * F ≠ F * E := by
  let E := gomesDerivativePowerChainTransfer ℂ 2 0 1
  let F := gomesDerivativePowerChainTransfer ℂ 2 1 0
  refine ⟨E.val, F.val, ?_, ?_, ?_⟩
  · exact ((gomesCentralizerSingleton_mem_iff ℂ _ E.val).mp E.property).symm
  · exact ((gomesCentralizerSingleton_mem_iff ℂ _ F.val).mp F.property).symm
  · intro h
    have hEF : E * F = F * E := Subtype.ext h
    have hij := (gomesDerivativePowerChainTransfer_opposite_commute_iff ℂ 2 0 1).mp hEF
    exact Nat.zero_ne_one (congrArg Fin.val hij)

/-- A nonzero square-zero operator is an actual symmetry of the supertranslation momentum. -/
theorem gomesSupertranslationMomentum_nilpotent_symmetry :
    ∃ E : Module.End ℂ ℂ[X], E ≠ 0 ∧ E * E = 0 ∧
      E * polynomialReflectionD1N2Split.momentum0 = polynomialReflectionD1N2Split.momentum0 * E := by
  let E := gomesDerivativePowerChainTransfer ℂ 2 0 1
  refine ⟨E.val, ?_, ?_, ?_⟩
  · intro h
    exact gomesDerivativePowerChainTransfer_ne_zero ℂ 2 0 1 (Subtype.ext h)
  · have hij : (0 : Fin 2) ≠ 1 := fun h => Nat.zero_ne_one (congrArg Fin.val h)
    exact congrArg Subtype.val ((gomesDerivativePowerChainTransfer_square_zero_iff ℂ 2 0 1).mpr hij)
  · exact ((gomesCentralizerSingleton_mem_iff ℂ _ E.val).mp E.property).symm

/-- The transfer from odd to even chain acts on every even divided monomial by zero. -/
theorem gomesSupertranslationOddToEven_even (n : ℕ) :
    (gomesDerivativePowerChainTransfer ℂ 2 0 1).val (gomesDividedMonomialBasis ℂ (n * 2)) = 0 := by
  have h := gomesDerivativePowerChainTransfer_basis ℂ 2 0 1 0 n
  have hij : (0 : Fin 2) ≠ 1 := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  simpa only [Fin.val_zero, Nat.add_zero, if_neg hij] using h

/-- The transfer from odd to even chain sends each odd divided monomial to its preceding even one. -/
theorem gomesSupertranslationOddToEven_odd (n : ℕ) :
    (gomesDerivativePowerChainTransfer ℂ 2 0 1).val (gomesDividedMonomialBasis ℂ (n * 2 + 1)) =
      gomesDividedMonomialBasis ℂ (n * 2) := by
  have h := gomesDerivativePowerChainTransfer_basis ℂ 2 0 1 1 n
  simpa only [Fin.val_one, Fin.val_zero, Nat.add_zero, ite_true] using h

end GaloisForLFunctions.HTGeometry
