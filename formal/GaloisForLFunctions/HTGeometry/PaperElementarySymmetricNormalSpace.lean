import GaloisForLFunctions.HTGeometry.PaperSplitNormalSpace
import GaloisForLFunctions.HTGeometry.PaperIntegralSymmetricRetraction
import GaloisForLFunctions.HTGeometry.PaperNativeReesScalarMap

/-!
# Independent actual normal classes of all elementary symmetric functions

The root-to-coefficient map splits by the integral symmetric retraction
over every commutative ring. Thus its generator ideal retains every
coefficient ideal order, although its generators have degrees one through
`n`. No factorial is inverted, including in positive characteristic.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The actual ideal of the native elementary symmetric coefficients. -/
def paperElementarySymmetricIdeal : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range (fun i : Fin n => esymm (Fin n) K (i + 1)))

/-- All splitting prerequisites are paid by the native symmetric retraction. -/
def paperElementarySymmetricNormalData :
    PaperSplitNormalData K (MvPolynomial (Fin n) K) (Fin n) where
  generator i := esymm (Fin n) K (i + 1)
  retraction := paperIntegralElementarySymmetricRetraction K n

/-- Root substitution preserves every coefficient-variable ideal power exactly. -/
theorem paperElementarySymmetric_mem_power_iff (p : MvPolynomial (Fin n) K) (m : ℕ) :
    aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p ∈ paperElementarySymmetricIdeal K n ^ m ↔
      p ∈ paperHomogeneousGeneratorIdeal (X : Fin n → MvPolynomial (Fin n) K) ^ m := by
  change aeval (paperElementarySymmetricNormalData K n).generator p ∈
    (paperElementarySymmetricNormalData K n).ideal ^ m ↔ _
  rw [(paperElementarySymmetricNormalData K n).ideal_eq_map]
  exact (paperIntegralElementarySymmetricRetraction K n).mem_map_pow_iff _ m p

/-- The scalar-compatible map to the actual normal ring, using the native initial classes. -/
def paperElementarySymmetricNormalMap : MvPolynomial (Fin n) K →ₐ[K]
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n) :=
  paperNativeReesMvPolynomialAlgHom (paperElementarySymmetricNormalData K n).ideal
    (paperElementarySymmetricNormalData K n).idealElements

/-- No nonzero coefficient polynomial vanishes in the actual normal ring. -/
theorem paperElementarySymmetricNormalMap_eq_zero_iff (p : MvPolynomial (Fin n) K) :
    paperElementarySymmetricNormalMap K n p = 0 ↔ p = 0 :=
  (paperElementarySymmetricNormalData K n).polynomialMap_eq_zero_iff p

/-- All elementary symmetric initial classes are polynomially independent. -/
theorem paperElementarySymmetricNormalMap_injective :
    Function.Injective (paperElementarySymmetricNormalMap K n) :=
  (paperElementarySymmetricNormalData K n).polynomialMap_injective

/-- Each coefficient variable is the actual initial class of its elementary symmetric function. -/
theorem paperElementarySymmetricNormalMap_X (i : Fin n) :
    paperElementarySymmetricNormalMap K n (X i) =
      paperNativeReesSpecialization (paperElementarySymmetricIdeal K n)
        (ReesGrading.mono (paperElementarySymmetricIdeal K n) 1 (esymm (Fin n) K (i + 1))
          (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)) :=
  (paperElementarySymmetricNormalData K n).polynomialMap_X i

/-- A homogeneous coefficient expression has exact ideal order unless it is zero. -/
theorem paperElementarySymmetric_homogeneous_mem_succ_iff
    (p : MvPolynomial (Fin n) K) (m : ℕ) (hp : p.IsHomogeneous m) :
    aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p ∈
      paperElementarySymmetricIdeal K n ^ (m + 1) ↔ p = 0 :=
  (paperElementarySymmetricNormalData K n).homogeneous_mem_succ_iff p m hp

/-- The entire existing symmetric coefficient algebra embeds in the actual normal ring. -/
def paperSymmetricNormalEmbedding : symmetricSubalgebra (Fin n) K →ₐ[K]
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n) :=
  (paperElementarySymmetricNormalMap K n).comp
    (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm.toAlgHom

/-- The symmetric algebra embedding loses no native coefficient information. -/
theorem paperSymmetricNormalEmbedding_injective :
    Function.Injective (paperSymmetricNormalEmbedding K n) :=
  (paperElementarySymmetricNormalMap_injective K n).comp
    (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm.injective

/-- Vanishing of an embedded symmetric polynomial is exactly its original vanishing. -/
theorem paperSymmetricNormalEmbedding_eq_zero_iff (p : symmetricSubalgebra (Fin n) K) :
    paperSymmetricNormalEmbedding K n p = 0 ↔ (p : MvPolynomial (Fin n) K) = 0 := by
  constructor
  · intro h
    have hp : p = 0 := paperSymmetricNormalEmbedding_injective K n
      (h.trans (map_zero (paperSymmetricNormalEmbedding K n)).symm)
    exact congrArg Subtype.val hp
  · intro h
    have hp : p = 0 := Subtype.ext h
    rw [hp, map_zero]

end

end GaloisForLFunctions.HTGeometry
