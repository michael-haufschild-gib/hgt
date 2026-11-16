import GaloisForLFunctions.RepresentationLifting.Differential.OddQuadraticPrimitives
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Odd quadratic primitives in the global meromorphic field

Odd differential self-products have primitives in the actual meromorphic
field and in its rational-function subfield. Translation carries these
primitives to the primitives of the translated functions. Consequently,
periodicity of an odd self-product is exactly vanishing of the derivative
of the corresponding primitive's translation defect.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open Bottcher HTGeometry
open scoped Differential UnivMeroFieldInstances

/-- The quadratic primitive is meromorphic for every meromorphic input and every odd order. -/
theorem meromorphic_oddProduct_has_primitive (n : ℕ) (u : meroField (Set.univ : Set ℂ)) :
    ∃ v : meroField (Set.univ : Set ℂ), v′ = u * differentialJet (2 * n + 1) u :=
  ⟨oddPrimitive n u, deriv_oddPrimitive n u⟩

/-- The same construction never leaves the rational-function field. -/
theorem rational_oddProduct_has_primitive (n : ℕ) (u : RatFunc ℂ) :
    ∃ v : RatFunc ℂ, v′ = u * differentialJet (2 * n + 1) u :=
  ⟨oddPrimitive n u, deriv_oddPrimitive n u⟩

/-- Translation is compatible with the normalized quadratic primitive. -/
theorem translate_oddPrimitive (h : ℂ) (n : ℕ) (u : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv h (oddPrimitive n u) =
      oddPrimitive n (addTranslationMeroEquiv h u) := by
  unfold oddPrimitive
  rw [map_div₀, map_ofNat]
  congr 1
  exact map_doubledOddPrimitive (addTranslationMeroEquiv h).toRingHom
    (addTranslationMeroEquiv_deriv h) n u

/-- The derivative of the primitive's translation defect is the product's translation defect. -/
theorem deriv_meromorphic_oddPrimitive_translation_defect (h : ℂ) (n : ℕ)
    (u : meroField (Set.univ : Set ℂ)) :
    (addTranslationMeroEquiv h (oddPrimitive n u) - oddPrimitive n u)′ =
      addTranslationMeroEquiv h (u * differentialJet (2 * n + 1) u) -
        u * differentialJet (2 * n + 1) u := by
  rw [map_sub, ← addTranslationMeroEquiv_deriv, deriv_oddPrimitive]

/-- An exact periodicity criterion expressed through the primitive, without analytic side inputs. -/
theorem meromorphic_oddProduct_periodic_iff (h : ℂ) (n : ℕ)
    (u : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv h (u * differentialJet (2 * n + 1) u) =
        u * differentialJet (2 * n + 1) u ↔
      (addTranslationMeroEquiv h (oddPrimitive n u) - oddPrimitive n u)′ = 0 := by
  rw [deriv_meromorphic_oddPrimitive_translation_defect, sub_eq_zero]

/-- Rational-to-meromorphic embedding preserves these explicit primitives. -/
theorem rationalToMeromorphic_oddPrimitive (n : ℕ) (u : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (oddPrimitive n u) =
      oddPrimitive n (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) u) := by
  unfold oddPrimitive
  rw [map_div₀, map_ofNat]
  congr 1
  exact map_doubledOddPrimitive _ (fun u => (deriv_algebraMap u).symm) n u

#print axioms meromorphic_oddProduct_has_primitive
#print axioms rational_oddProduct_has_primitive
#print axioms translate_oddPrimitive
#print axioms meromorphic_oddProduct_periodic_iff
#print axioms rationalToMeromorphic_oddPrimitive

end GaloisForLFunctions.RepresentationLifting
