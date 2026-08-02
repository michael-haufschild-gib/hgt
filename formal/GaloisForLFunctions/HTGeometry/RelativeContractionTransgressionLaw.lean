import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# Relative contraction transgression

An exact or contractible ambient source can acquire nontrivial cohomology
after one restricts its admissible primitives.  The obstruction is not a new
ambient cocycle.  It is the class of the canonical ambient primitive modulo
the admissible primitive sector and the kernel of the boundary map.

This module gives the exact necessity-and-sufficiency law.  For an injective
boundary map, the relative class vanishes precisely when the ambient
contracting primitive itself remains in the restricted sector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A0 A1 A2 : Type*}
variable [Field R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/--
Class of the canonical ambient primitive modulo admissible primitives and
the ambiguity in choosing a primitive.
-/
def relativePrimitiveObstruction
    (S0 : Submodule R A0)
    (d0 : A0 →ₗ[R] A1)
    (h1 : A1 →ₗ[R] A0)
    (x : A1) :
    A0 ⧸ (S0 ⊔ LinearMap.ker d0) :=
  Submodule.Quotient.mk (h1 x)

/--
**Relative primitive classification.**  If `h1 x` is an ambient primitive
of `x`, its relative obstruction vanishes exactly when `x` has a primitive
inside the admitted sector `S0`.
-/
theorem relativePrimitiveObstruction_eq_zero_iff
    (S0 : Submodule R A0)
    (d0 : A0 →ₗ[R] A1)
    (h1 : A1 →ₗ[R] A0)
    (x : A1)
    (hprimitive : d0 (h1 x) = x) :
    relativePrimitiveObstruction S0 d0 h1 x = 0 ↔
      ∃ b : A0, b ∈ S0 ∧ d0 b = x := by
  rw [relativePrimitiveObstruction,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hmem
    rw [Submodule.mem_sup] at hmem
    obtain ⟨b, hb, k, hk, hsum⟩ := hmem
    refine ⟨b, hb, ?_⟩
    have hk0 : d0 k = 0 := hk
    have hsum' := congrArg d0 hsum
    simp only [map_add, hk0, add_zero] at hsum'
    exact hsum'.trans hprimitive
  · rintro ⟨b, hb, hbx⟩
    rw [Submodule.mem_sup]
    refine ⟨b, hb, h1 x - b, ?_, ?_⟩
    · change d0 (h1 x - b) = 0
      rw [map_sub, hprimitive, hbx, sub_self]
    · abel

/--
When the boundary is injective, there is no primitive ambiguity: vanishing
of the relative class is exactly preservation of the canonical primitive.
-/
theorem relativePrimitiveObstruction_eq_zero_iff_of_injective
    (S0 : Submodule R A0)
    (d0 : A0 →ₗ[R] A1)
    (h1 : A1 →ₗ[R] A0)
    (x : A1)
    (hprimitive : d0 (h1 x) = x)
    (hinjective : Function.Injective d0) :
    relativePrimitiveObstruction S0 d0 h1 x = 0 ↔
      h1 x ∈ S0 := by
  rw [relativePrimitiveObstruction_eq_zero_iff
    S0 d0 h1 x hprimitive]
  constructor
  · rintro ⟨b, hb, hbx⟩
    have heq : b = h1 x :=
      hinjective (hbx.trans hprimitive.symm)
    simpa [← heq] using hb
  · intro hmem
    exact ⟨h1 x, hmem, hprimitive⟩

/--
**Contracted-cocycle transgression law.**  For a three-term contraction,
every cocycle is exact in the ambient source.  Its only possible class after
restricting primitives is the relative primitive obstruction above.
-/
theorem contractedCocycle_relativePrimitiveObstruction_eq_zero_iff
    (S0 : Submodule R A0)
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (h1 : A1 →ₗ[R] A0)
    (h2 : A2 →ₗ[R] A1)
    (hcontract : ∀ x, d0 (h1 x) + h2 (d1 x) = x)
    (x : A1)
    (hcocycle : d1 x = 0) :
    relativePrimitiveObstruction S0 d0 h1 x = 0 ↔
      ∃ b : A0, b ∈ S0 ∧ d0 b = x := by
  exact relativePrimitiveObstruction_eq_zero_iff
    S0 d0 h1 x (by
      have hc := hcontract x
      rw [hcocycle, map_zero, add_zero] at hc
      exact hc)

/--
Injective-boundary form of contracted-cocycle transgression: the relative
class vanishes exactly when contraction preserves the primitive sector.
-/
theorem
    contractedCocycle_relativePrimitiveObstruction_eq_zero_iff_of_injective
    (S0 : Submodule R A0)
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (h1 : A1 →ₗ[R] A0)
    (h2 : A2 →ₗ[R] A1)
    (hcontract : ∀ x, d0 (h1 x) + h2 (d1 x) = x)
    (hinjective : Function.Injective d0)
    (x : A1)
    (hcocycle : d1 x = 0) :
    relativePrimitiveObstruction S0 d0 h1 x = 0 ↔
      h1 x ∈ S0 := by
  apply relativePrimitiveObstruction_eq_zero_iff_of_injective
    S0 d0 h1 x
  · have hc := hcontract x
    rw [hcocycle, map_zero, add_zero] at hc
    exact hc
  · exact hinjective

end

end GaloisForLFunctions.HTGeometry
