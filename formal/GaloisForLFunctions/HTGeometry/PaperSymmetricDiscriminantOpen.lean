import GaloisForLFunctions.HTGeometry.PaperIntegralDiscriminantLocalization
import GaloisForLFunctions.HTGeometry.SymmetricBlockAlgebraicIndependence

/-!
# Native symmetric and Beurling relations on the discriminant complement

Every symmetric root polynomial retains its exact relations in the actual
normal ring after the integral discriminant is inverted. This applies to
the complete countable coefficient families of native multiplier blocks,
including the Bernoulli-scaled Beurling block.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The native symmetric algebra embedded in the actual discriminant-open normal ring. -/
def paperSymmetricDiscriminantOpenEmbedding :
    symmetricSubalgebra (Fin n) K →ₐ[K] PaperDiscriminantNormalOpen K n :=
  (paperDiscriminantOpenCoefficientMap K n).comp
    (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm.toAlgHom

/-- Inverting the generic discriminant kills no native symmetric polynomial. -/
theorem paperSymmetricDiscriminantOpenEmbedding_injective :
    Function.Injective (paperSymmetricDiscriminantOpenEmbedding K n) :=
  (paperDiscriminantOpenCoefficientMap_injective K n).comp
    (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm.injective

/-- Vanishing of an embedded symmetric polynomial is exactly its original vanishing. -/
theorem paperSymmetricDiscriminantOpenEmbedding_eq_zero_iff
    (p : symmetricSubalgebra (Fin n) K) :
    paperSymmetricDiscriminantOpenEmbedding K n p = 0 ↔ (p : MvPolynomial (Fin n) K) = 0 := by
  constructor
  · intro h
    have hp : p = 0 := paperSymmetricDiscriminantOpenEmbedding_injective K n
      (h.trans (map_zero (paperSymmetricDiscriminantOpenEmbedding K n)).symm)
    exact congrArg Subtype.val hp
  · intro h
    rw [show p = 0 from Subtype.ext h, map_zero]

/-- Every scalar polynomial relation of any native symmetric family is preserved exactly. -/
theorem paperSymmetricDiscriminantOpenEmbedding_relations_iff
    {ι : Type*} (a : ι → symmetricSubalgebra (Fin n) K) (p : MvPolynomial ι K) :
    aeval (fun i => paperSymmetricDiscriminantOpenEmbedding K n (a i)) p = 0 ↔
      aeval (fun i => (a i : MvPolynomial (Fin n) K)) p = 0 := by
  have hv : ((aeval a p : symmetricSubalgebra (Fin n) K) : MvPolynomial (Fin n) K) =
      aeval (fun i => (a i : MvPolynomial (Fin n) K)) p :=
    comp_aeval_apply a (symmetricSubalgebra (Fin n) K).val p
  rw [← comp_aeval_apply a (paperSymmetricDiscriminantOpenEmbedding K n) p, ← hv]
  exact paperSymmetricDiscriminantOpenEmbedding_eq_zero_iff K n (aeval a p)

/-- The complete native multiplier coefficient family on the actual discriminant complement. -/
def paperSymmetricBlockDiscriminantOpenCoefficient (r : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    PaperDiscriminantNormalOpen ℚ r :=
  paperSymmetricDiscriminantOpenEmbedding ℚ r
    ⟨PowerSeries.coeff k (symmetricBlock r c), isSymmetric_coeff_symmetricBlock r c k⟩

/-- Removing the collision divisor introduces no scalar relation among multiplier coefficients. -/
theorem paperSymmetricBlockDiscriminantOpenCoefficient_relations_iff
    (r : ℕ) (c : ℕ → ℚ) (p : MvPolynomial ℕ ℚ) :
    aeval (paperSymmetricBlockDiscriminantOpenCoefficient r c) p = 0 ↔
      aeval (fun k => PowerSeries.coeff k (symmetricBlock r c)) p = 0 :=
  paperSymmetricDiscriminantOpenEmbedding_relations_iff ℚ r
    (fun k => ⟨PowerSeries.coeff k (symmetricBlock r c), isSymmetric_coeff_symmetricBlock r c k⟩) p

/-- The native Bernoulli-scaled Beurling coefficients on the actual discriminant complement. -/
def paperBeurlingDiscriminantOpenCoefficient (r k : ℕ) : PaperDiscriminantNormalOpen ℚ r :=
  paperSymmetricBlockDiscriminantOpenCoefficient r (fun j => bernoulli' j / (j.factorial : ℚ)) k

/-- Every scalar relation of the Beurling coefficient family survives on the discriminant complement. -/
theorem paperBeurlingDiscriminantOpenCoefficient_relations_iff (r : ℕ) (p : MvPolynomial ℕ ℚ) :
    aeval (paperBeurlingDiscriminantOpenCoefficient r) p = 0 ↔
      aeval (fun k => PowerSeries.coeff k (beurlingBlock r)) p = 0 :=
  paperSymmetricBlockDiscriminantOpenCoefficient_relations_iff r _ p

end

end GaloisForLFunctions.HTGeometry
