import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Five-plane / three-intersection fracture

Compatible pure spinors in ten complexified vector dimensions determine maximal isotropic
five-planes whose intersection has complex dimension three. This file formalizes only the
dimension consequence of those hypotheses:

* the two five-planes span seven dimensions;
* each has two directions relative to the intersection;
* doubling the common three directions gives six;
* combining the two relative two-directions gives four.

The `6 + 4` arithmetic is unconditional once the `5, 5, 3` dimensions are supplied. This file does
not construct pure spinors, prove their intersection theorem, select a real structure, or identify
either count with a physical representation or spacetime.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/--
Two five-planes meeting in a three-plane span seven dimensions, have two relative directions
each, and therefore carry the exact `6 + 4` common-versus-relative doubled count.
-/
theorem five_plane_three_intersection_fracture
    (L₁ L₂ : Submodule 𝕜 V)
    (h₁ : Module.finrank 𝕜 L₁ = 5)
    (h₂ : Module.finrank 𝕜 L₂ = 5)
    (h₁₂ : Module.finrank 𝕜 ↥(L₁ ⊓ L₂) = 3) :
    Module.finrank 𝕜 ↥(L₁ ⊔ L₂) = 7 ∧
      Module.finrank 𝕜 L₁ - Module.finrank 𝕜 ↥(L₁ ⊓ L₂) = 2 ∧
      Module.finrank 𝕜 L₂ - Module.finrank 𝕜 ↥(L₁ ⊓ L₂) = 2 ∧
      Module.finrank 𝕜 ↥(L₁ ⊓ L₂) + Module.finrank 𝕜 ↥(L₁ ⊓ L₂) = 6 ∧
      (Module.finrank 𝕜 L₁ - Module.finrank 𝕜 ↥(L₁ ⊓ L₂)) +
        (Module.finrank 𝕜 L₂ - Module.finrank 𝕜 ↥(L₁ ⊓ L₂)) = 4 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
  omega

end GaloisForLFunctions.HTGeometry
