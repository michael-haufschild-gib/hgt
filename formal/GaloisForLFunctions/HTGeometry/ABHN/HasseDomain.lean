/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseReducedness

/-!
# Hasse descent for domains

An injective scalar-extension map reflects the domain property.  Consequently, if all completed
scalar extensions of a commutative global-field algebra are domains, then the global algebra is a
domain.  The converse is not asserted because scalar extension can split a domain.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A commutative algebra is a domain if one field scalar extension is a domain. -/
theorem isDomain_of_tensorProduct_isDomain {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    [IsDomain (L ⊗[K] A)] :
    IsDomain A := by
  exact (Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K L)).isDomain Algebra.TensorProduct.includeRight

/-- A commutative algebra over a number field is a domain if all completed scalar extensions are
domains. -/
theorem numberField_isDomain_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (h : ∀ p : NumberFieldPlace K, IsDomain (completion K p ⊗[K] A)) :
    IsDomain A := by
  letI : IsDomain (completion K (witnessPlace K) ⊗[K] A) := h (witnessPlace K)
  exact isDomain_of_tensorProduct_isDomain (K := K) (L := completion K (witnessPlace K))

/-- A commutative algebra over `F(t)` is a domain if all finite and infinite completed scalar
extensions are domains. -/
theorem rationalFunction_isDomain_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (h : ∀ p : RationalFunctionPlace F,
      IsDomain (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :
    IsDomain A := by
  letI : IsDomain (rationalFunctionCompletion F .infinite ⊗[RatFunc F] A) := h .infinite
  exact isDomain_of_tensorProduct_isDomain (K := RatFunc F)
    (L := rationalFunctionCompletion F .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
