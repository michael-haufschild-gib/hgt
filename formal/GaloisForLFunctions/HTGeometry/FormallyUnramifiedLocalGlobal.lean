import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Formal unramifiedness is local on the base

The Kähler module of a base localization is the corresponding localization of the original
Kähler module.  Thus its vanishing at every maximal ideal forces global vanishing.
-/

namespace Algebra

universe u v

/-- Formal unramifiedness after localization at every maximal ideal of the base implies global
formal unramifiedness. -/
theorem formallyUnramified_of_localization_maximal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      FormallyUnramified (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) :
    FormallyUnramified A B := by
  rw [Algebra.formallyUnramified_iff]
  let Mₚ : (P : Ideal A) → [P.IsMaximal] → Type v := fun P _ =>
    Ω[Localization (Algebra.algebraMapSubmonoid B P.primeCompl)⁄Localization.AtPrime P]
  let f : (P : Ideal A) → [P.IsMaximal] → Ω[B⁄A] →ₗ[A] Mₚ P := fun P _ =>
    (KaehlerDifferential.map A (Localization.AtPrime P) B
      (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))).restrictScalars A
  letI (P : Ideal A) [P.IsMaximal] :
      IsLocalizedModule P.primeCompl (f P) := by
    dsimp [f, Mₚ]
    infer_instance
  apply Module.subsingleton_of_localization_maximal Mₚ f
  intro P hP
  letI : P.IsMaximal := hP
  letI : FormallyUnramified (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid B P.primeCompl)) := h P
  exact inferInstance

end Algebra
