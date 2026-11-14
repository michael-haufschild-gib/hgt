import GaloisForLFunctions.HTGeometry.DifferentialAlgebra.PseudoAffineTranslation
import GaloisForLFunctions.HTGeometry.DifferentialAlgebra.OreAffineFiltration

/-!
# Affine translations of completed pseudodifferential operators

Order preservation on differential operators gives valuation preservation on
Ore fractions. The affine generator change is therefore uniformly continuous
and extends to an automorphism of the completed pseudodifferential ring.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiffOp

open OreLocalization
open scoped OreLocalization nonZeroDivisors

variable {K : Type*} [Field K] [Differential K]

/-- The rational differential order is unchanged by affine generator translation. -/
theorem ordQ_pseudoAffineTranslationHom (a : K) (x : PseudoDiffOp K) :
    ordQ (pseudoAffineTranslationHom a x) = ordQ x := by
  induction x using OreLocalization.ind with
  | _ r s =>
    by_cases hr : r = 0
    · have hx : r /ₒ s = (0 : PseudoDiffOp K) := by
        rw [hr]
        exact OreLocalization.zero_oreDiv s
      rw [hx, map_zero]
    · let τ : DiffOp K ≃+* DiffOp K := affineTranslation a
      have hs : (s : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
      have hτs : τ (s : DiffOp K) ≠ 0 := fun h => hs (τ.injective (h.trans τ.map_zero.symm))
      have hτr : τ r ≠ 0 := fun h => hr (τ.injective (h.trans τ.map_zero.symm))
      have hnumS : (numeratorRingHom (τ (s : DiffOp K)) : PseudoDiffOp K) ≠ 0 :=
        fun h => hτs (numeratorRingHom_injective (h.trans (map_zero _).symm))
      have hnumR : (numeratorRingHom (τ r) : PseudoDiffOp K) ≠ 0 :=
        fun h => hτr (numeratorRingHom_injective (h.trans (map_zero _).symm))
      rw [pseudoAffineTranslationHom, OreLocalization.universalHom_apply]
      change ordQ ((numeratorRingHom (τ (s : DiffOp K)))⁻¹ * numeratorRingHom (τ r)) =
        ordQ (r /ₒ s)
      rw [ordQ_mul _ _ (inv_ne_zero hnumS) hnumR, ordQ_inv _ hnumS,
        ordQ_numeratorRingHom, if_neg hτs, ordQ_numeratorRingHom, if_neg hτr,
        ordQ_oreDiv, if_neg hr]
      change -(degree (affineTranslationHom a (s : DiffOp K)) : ℤ) +
          (degree (affineTranslationHom a r) : ℤ) =
        (degree r : ℤ) - (degree (s : DiffOp K) : ℤ)
      rw [degree_affineTranslationHom, degree_affineTranslationHom]
      exact neg_add_eq_sub _ _

theorem pseudoDiffOpAddValuationValue_pseudoAffineTranslation (a : K) (x : PseudoDiffOp K) :
    pseudoDiffOpAddValuationValue (pseudoAffineTranslation a x) =
      pseudoDiffOpAddValuationValue x := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  by_cases hx : x = 0
  · subst x
    simp
  have hmap : pseudoAffineTranslation a x ≠ 0 :=
    fun h => hx ((pseudoAffineTranslation a).injective (h.trans (map_zero _).symm))
  simp only [pseudoDiffOpAddValuationValue, hx, hmap, if_false]
  exact congrArg _ (congrArg Neg.neg (ordQ_pseudoAffineTranslationHom a x))

/-- The affine substitution preserves the order valuation. -/
theorem pseudoDiffOpValuation_pseudoAffineTranslation (a : K) (x : PseudoDiffOp K) :
    pseudoDiffOpValuation (pseudoAffineTranslation a x) = pseudoDiffOpValuation x :=
  congrArg Multiplicative.toAdd (pseudoDiffOpAddValuationValue_pseudoAffineTranslation a x)

/-- The affine translation is a uniform equivalence for the order-valued topology. -/
def pseudoAffineUniformEquiv (a : K) :
    WithVal (pseudoDiffOpValuation (K := K)) ≃ᵤ WithVal (pseudoDiffOpValuation (K := K)) where
  __ := WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation (pseudoAffineTranslation a)
  uniformContinuous_toFun := uniformContinuous_ringEquiv_of_valuation_eq
    _ _ _ (pseudoDiffOpValuation_pseudoAffineTranslation a)
  uniformContinuous_invFun := by
    apply uniformContinuous_ringEquiv_of_valuation_eq
    intro x
    exact pseudoDiffOpValuation_pseudoAffineTranslation (-a) x

/-- The affine generator change extends to formal pseudodifferential operators. -/
def completedAffineTranslation (a : K) : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation (pseudoAffineTranslation a))
    (pseudoAffineUniformEquiv a).continuous (pseudoAffineUniformEquiv a).symm.continuous

@[simp] theorem completedAffineTranslation_coe (a : K)
    (x : WithVal (pseudoDiffOpValuation (K := K))) :
    completedAffineTranslation a (x : CompletedPseudoDiffOp K) =
      (WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation
        (pseudoAffineTranslation a) x : WithVal (pseudoDiffOpValuation (K := K))) := by
  rw [completedAffineTranslation, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe (uniformContinuous_ringEquiv_of_valuation_eq
      _ _ _ (pseudoDiffOpValuation_pseudoAffineTranslation a))]

end GaloisForLFunctions.HTGeometry.DiffOp

#print axioms GaloisForLFunctions.HTGeometry.DiffOp.completedAffineTranslation
