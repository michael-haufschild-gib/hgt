import GaloisForLFunctions.HTGeometry.PaperElementarySymmetricNormalSpace
import GaloisForLFunctions.HTGeometry.SymmetricBlockAlgebraicIndependence

/-!
# Native Beurling and multiplier blocks in the actual normal ring

Every coefficient of the existing symmetric multiplier block enters the
normal ring through its native symmetric coefficient algebra. All scalar
polynomial relations and equality of entire formal blocks are preserved.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The existing multiplier-block coefficient, embedded in the actual normal ring. -/
def paperSymmetricBlockNormalCoefficient (r : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal ℚ r) :=
  paperSymmetricNormalEmbedding ℚ r
    ⟨PowerSeries.coeff k (symmetricBlock r c), isSymmetric_coeff_symmetricBlock r c k⟩

/-- Each actual native block coefficient vanishes exactly when its normal image does. -/
theorem paperSymmetricBlockNormalCoefficient_eq_zero_iff (r : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    paperSymmetricBlockNormalCoefficient r c k = 0 ↔
      PowerSeries.coeff k (symmetricBlock r c) = 0 :=
  paperSymmetricNormalEmbedding_eq_zero_iff ℚ r _

/-- The entire countable native coefficient family retains exactly its scalar polynomial relations. -/
theorem paperSymmetricBlockNormalCoefficient_relations_iff
    (r : ℕ) (c : ℕ → ℚ) (p : MvPolynomial ℕ ℚ) :
    aeval (paperSymmetricBlockNormalCoefficient r c) p = 0 ↔
      aeval (fun k => PowerSeries.coeff k (symmetricBlock r c)) p = 0 := by
  let a : ℕ → symmetricSubalgebra (Fin r) ℚ :=
    fun k => ⟨PowerSeries.coeff k (symmetricBlock r c), isSymmetric_coeff_symmetricBlock r c k⟩
  have hf : aeval (paperSymmetricBlockNormalCoefficient r c) =
      (paperSymmetricNormalEmbedding ℚ r).comp (aeval a) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [aeval_X, AlgHom.comp_apply, aeval_X]
    rfl
  have hv : aeval (fun k => PowerSeries.coeff k (symmetricBlock r c)) =
      (symmetricSubalgebra (Fin r) ℚ).val.comp (aeval a) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [aeval_X, AlgHom.comp_apply, aeval_X]
    rfl
  rw [hf, hv, AlgHom.comp_apply, AlgHom.comp_apply]
  exact paperSymmetricNormalEmbedding_eq_zero_iff ℚ r (aeval a p)

/-- The complete native multiplier block with coefficients in the actual normal ring. -/
def paperSymmetricNormalBlock (r : ℕ) (c : ℕ → ℚ) :
    PowerSeries (PaperIdealAssociatedGraded (paperElementarySymmetricIdeal ℚ r)) :=
  PowerSeries.mk (paperSymmetricBlockNormalCoefficient r c)

/-- Normal-block coefficients are precisely the embedded native coefficients. -/
theorem paperSymmetricNormalBlock_coeff (r : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    PowerSeries.coeff k (paperSymmetricNormalBlock r c) =
      paperSymmetricBlockNormalCoefficient r c k := PowerSeries.coeff_mk k _

/-- Equality of complete native blocks is reflected by their actual normal-ring realizations. -/
theorem paperSymmetricNormalBlock_eq_iff (r : ℕ) (c d : ℕ → ℚ) :
    paperSymmetricNormalBlock r c = paperSymmetricNormalBlock r d ↔
      symmetricBlock r c = symmetricBlock r d := by
  constructor
  · intro h
    apply PowerSeries.ext
    intro k
    have hc := congrArg (PowerSeries.coeff k) h
    rw [paperSymmetricNormalBlock_coeff, paperSymmetricNormalBlock_coeff] at hc
    exact congrArg Subtype.val (paperSymmetricNormalEmbedding_injective ℚ r hc)
  · intro h
    apply PowerSeries.ext
    intro k
    rw [paperSymmetricNormalBlock_coeff, paperSymmetricNormalBlock_coeff]
    apply congrArg (paperSymmetricNormalEmbedding ℚ r)
    apply Subtype.ext
    exact congrArg (PowerSeries.coeff k) h

/-- The actual normal image of a Bernoulli-scaled Beurling coefficient. -/
def paperBeurlingNormalCoefficient (r k : ℕ) :
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal ℚ r) :=
  paperSymmetricBlockNormalCoefficient r (fun j => bernoulli' j / (j.factorial : ℚ)) k

/-- All scalar relations of the existing Beurling coefficient family survive exactly. -/
theorem paperBeurlingNormalCoefficient_relations_iff (r : ℕ) (p : MvPolynomial ℕ ℚ) :
    aeval (paperBeurlingNormalCoefficient r) p = 0 ↔
      aeval (fun k => PowerSeries.coeff k (beurlingBlock r)) p = 0 :=
  paperSymmetricBlockNormalCoefficient_relations_iff r _ p

end

end GaloisForLFunctions.HTGeometry
