/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite étale algebras

Mathlib supplies the separate typeclass interfaces for an étale algebra and a finite module, but
not their standard joint name.  This module packages the conjunction and proves its descent
through faithfully flat field scalar extension.
-/

namespace Algebra

open scoped TensorProduct

universe u v w

/-- A finite étale algebra is an étale algebra whose underlying module is finite. -/
class FiniteEtale (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] : Prop
    extends Etale R A, Module.Finite R A

/-- An étale finite module carries the finite étale package. -/
instance finiteEtale_of_etale_of_finite (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [Etale R A] [Module.Finite R A] :
    FiniteEtale R A := ⟨⟩

/-- The defining two conditions of finite étaleness. -/
theorem finiteEtale_iff (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] :
    FiniteEtale R A ↔ Etale R A ∧ Module.Finite R A := by
  constructor
  · intro h
    exact ⟨h.toEtale, h.toFinite⟩
  · rintro ⟨hetale, hfinite⟩
    letI : Etale R A := hetale
    letI : Module.Finite R A := hfinite
    exact ⟨⟩

/-- Finite étaleness is reflected by scalar extension along a field extension. -/
theorem finiteEtale_iff_tensorProduct
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] :
    FiniteEtale K A ↔ FiniteEtale L (TensorProduct K L A) := by
  constructor
  · intro h
    letI : FiniteEtale K A := h
    infer_instance
  · intro h
    letI : FiniteEtale L (TensorProduct K L A) := h
    exact (finiteEtale_iff K A).mpr
      ⟨Etale.of_etale_tensorProduct_of_faithfullyFlat L,
        Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L⟩

end Algebra
