import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilTestSpace
import Mathlib.Analysis.InnerProductSpace.Completion

noncomputable section

/-!
# The Weil Hilbert space

Under the Riemann hypothesis the Weil hermitian form is a genuine inner product on the test space,
so the test space is a pre-Hilbert space and `H_W` is its completion.  The Riemann hypothesis is
carried as `[Fact RiemannHypothesis]` so that the normed and inner-product structures can be
declared as instances; nothing can produce that instance unconditionally, so the structures are
inert without it.

The carrier is a type synonym `SuzukiWeilTest` rather than the submodule itself: a submodule of
`ℝ → ℂ` already inherits the product uniformity, and the Weil norm must be the only uniform
structure in play for the completion to be the intended one.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The test space carrying the Weil inner product.  It is a type synonym rather than a
`Submodule` coercion so that the Weil norm is its only uniform structure. -/
def SuzukiWeilTest : Type := SuzukiTest

namespace SuzukiWeilTest

instance : AddCommGroup SuzukiWeilTest := inferInstanceAs (AddCommGroup SuzukiTest)

instance : Module ℂ SuzukiWeilTest := inferInstanceAs (Module ℂ SuzukiTest)

/-- The underlying test function. -/
def toTest (ψ : SuzukiWeilTest) : SuzukiTest := ψ

@[simp] theorem toTest_add (ψ φ : SuzukiWeilTest) :
    toTest (ψ + φ) = toTest ψ + toTest φ := rfl

@[simp] theorem toTest_smul (c : ℂ) (ψ : SuzukiWeilTest) :
    toTest (c • ψ) = c • toTest ψ := rfl

theorem toTest_injective : Function.Injective toTest := fun _ _ h => h

end SuzukiWeilTest

section WeilHilbert

variable [hRH : Fact RiemannHypothesis]

instance : Inner ℂ SuzukiWeilTest :=
  ⟨fun ψ φ => suzukiWeilInner (SuzukiWeilTest.toTest ψ) (SuzukiWeilTest.toTest φ)⟩

omit hRH in
theorem suzukiWeil_inner_def (ψ φ : SuzukiWeilTest) :
    (inner ℂ ψ φ : ℂ) = suzukiWeilInner (SuzukiWeilTest.toTest ψ) (SuzukiWeilTest.toTest φ) :=
  rfl

instance : NormedAddCommGroup SuzukiWeilTest :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ SuzukiWeilTest _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y =>
        suzukiWeilInner_conj_symm hRH.out (SuzukiWeilTest.toTest x) (SuzukiWeilTest.toTest y)
      re_inner_nonneg := fun x =>
        re_suzukiWeilInner_self_nonneg hRH.out (SuzukiWeilTest.toTest x)
      definite := fun _ h =>
        SuzukiWeilTest.toTest_injective (suzukiWeilInner_self_eq_zero hRH.out h)
      add_left := fun x y z =>
        suzukiWeilInner_add_left hRH.out (SuzukiWeilTest.toTest x) (SuzukiWeilTest.toTest y)
          (SuzukiWeilTest.toTest z)
      smul_left := fun x y r =>
        suzukiWeilInner_smul_left hRH.out r (SuzukiWeilTest.toTest x)
          (SuzukiWeilTest.toTest y) }

instance : InnerProductSpace ℂ SuzukiWeilTest :=
  InnerProductSpace.ofCore _

/-- **The Weil Hilbert space `H_W`.**  The completion of the smooth compactly supported test
functions in the norm of the Weil hermitian form. -/
abbrev SuzukiHW : Type := UniformSpace.Completion SuzukiWeilTest

end WeilHilbert

end RHTower
