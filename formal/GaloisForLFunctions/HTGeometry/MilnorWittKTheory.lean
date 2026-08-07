import GaloisForLFunctions.HTGeometry.MilnorKTheory
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Tactic.NoncommRing

/-!
# Milnor--Witt `K`-theory of a field

Morel's presentation: the free `ℤ`-algebra on a symbol `[u]` for every unit `u` and one further
symbol `η`, modulo the Steinberg relation `[u][1-u] = 0`, the twisted additivity
`[uv] = [u] + [v] + η[u][v]`, the centrality of `η`, and the hyperbolic relation
`η(η[-1] + 2) = 0`.

The grading is not part of the presentation — `[u]` has degree one and `η` degree minus one — and is
not built here; what is built is the ring itself and the relations that make it, together with the
consequences the Milnor--Witt cards use.

* `MilnorWittK` : the Milnor--Witt `K`-ring.
* `milnorWittSymbol`, `milnorWittEta` : the two families of generators.
* `milnorWittSymbol_mul` : twisted additivity.
* `milnorWittSymbol_mul_oneSub` : the Steinberg relation.
* `milnorWittForget` : killing `η` gives Milnor `K`-theory.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWitt

variable (F : Type*) [Field F]

/-- `-1` as a unit. -/
def negOneUnit : Fˣ := Units.mk0 (-1 : F) (neg_ne_zero.mpr one_ne_zero)

theorem negOneUnit_eq : negOneUnit F = (-1 : Fˣ) := Units.ext rfl

@[simp] theorem negOneUnit_val : ((negOneUnit F : Fˣ) : F) = -1 := rfl

/-- The generators of the Milnor--Witt presentation: a symbol for every unit, and `η`. -/
inductive MWGen (F : Type*) [Field F]
  | sym (u : Fˣ)
  | eta

/-- **Morel's relations** for Milnor--Witt `K`-theory. -/
inductive MilnorWittRel :
    FreeAlgebra ℤ (MWGen F) → FreeAlgebra ℤ (MWGen F) → Prop
  | steinberg (u : Fˣ) (hu : (u : F) ≠ 1) :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MWGen.sym u) *
          FreeAlgebra.ι ℤ (MWGen.sym (oneSubUnit hu))) 0
  | twisted (u v : Fˣ) :
      MilnorWittRel (FreeAlgebra.ι ℤ (MWGen.sym (u * v)))
        (FreeAlgebra.ι ℤ (MWGen.sym u) + FreeAlgebra.ι ℤ (MWGen.sym v)
          + FreeAlgebra.ι ℤ (MWGen.eta (F := F)) *
            FreeAlgebra.ι ℤ (MWGen.sym u) * FreeAlgebra.ι ℤ (MWGen.sym v))
  | central (u : Fˣ) :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MWGen.eta (F := F)) * FreeAlgebra.ι ℤ (MWGen.sym u))
        (FreeAlgebra.ι ℤ (MWGen.sym u) * FreeAlgebra.ι ℤ (MWGen.eta (F := F)))
  | hyperbolic :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MWGen.eta (F := F)) *
          (FreeAlgebra.ι ℤ (MWGen.eta (F := F)) *
            FreeAlgebra.ι ℤ (MWGen.sym (negOneUnit F)) + 2)) 0

/-- **The Milnor--Witt `K`-ring of a field.** -/
abbrev MilnorWittK : Type _ := RingQuot (MilnorWittRel F)

/-- The quotient map onto the Milnor--Witt `K`-ring. -/
def milnorWittMk : FreeAlgebra ℤ (MWGen F) →ₐ[ℤ] MilnorWittK F :=
  RingQuot.mkAlgHom ℤ (MilnorWittRel F)

/-- **The generator `η`.** -/
def milnorWittEta : MilnorWittK F := milnorWittMk F (FreeAlgebra.ι ℤ (MWGen.eta (F := F)))

variable {F}

/-- **The Milnor--Witt symbol** `[u]`. -/
def milnorWittSymbol (u : Fˣ) : MilnorWittK F :=
  milnorWittMk F (FreeAlgebra.ι ℤ (MWGen.sym u))

/-- **Twisted additivity**: `[uv] = [u] + [v] + η[u][v]`. -/
theorem milnorWittSymbol_mul (u v : Fˣ) :
    (milnorWittSymbol (u * v) : MilnorWittK F)
      = milnorWittSymbol u + milnorWittSymbol v + milnorWittEta F * milnorWittSymbol u * milnorWittSymbol v := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.twisted (F := F) u v)
  simpa [milnorWittSymbol, milnorWittEta, milnorWittMk] using h

/-- **The Steinberg relation**: `[u][1 - u] = 0`. -/
theorem milnorWittSymbol_mul_oneSub {u : Fˣ} (hu : (u : F) ≠ 1) :
    (milnorWittSymbol u : MilnorWittK F) * milnorWittSymbol (oneSubUnit hu) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.steinberg (F := F) u hu)
  simpa [milnorWittSymbol, milnorWittMk] using h

/-- **`η` is central on the symbols**. -/
theorem milnorWittEta_comm (u : Fˣ) :
    milnorWittEta F * (milnorWittSymbol u : MilnorWittK F) = milnorWittSymbol u * milnorWittEta F := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.central (F := F) u)
  simpa [milnorWittSymbol, milnorWittEta, milnorWittMk] using h

/-- **The hyperbolic relation**: `η(η[-1] + 2) = 0`. -/
theorem milnorWittEta_hyperbolic :
    milnorWittEta F * (milnorWittEta F * milnorWittSymbol (negOneUnit F) + 2) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.hyperbolic (F := F))
  simpa [milnorWittSymbol, milnorWittEta, milnorWittMk, map_ofNat] using h

/-- The generators, sent to the Milnor symbols with `η` sent to zero. -/
def milnorWittForgetGen : MWGen F → MilnorK F
  | MWGen.sym u => milnorSymbol u
  | MWGen.eta => 0

/-- **Killing `η` gives Milnor `K`-theory.**  Twisted additivity becomes ordinary additivity, the
centrality and hyperbolic relations become `0 = 0`, and the Steinberg relation is the Steinberg
relation. -/
noncomputable def milnorWittForget (F : Type*) [Field F] : MilnorWittK F →ₐ[ℤ] MilnorK F :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (milnorWittForgetGen (F := F)), by
    intro x y hxy
    induction hxy with
    | steinberg u hu =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply, milnorWittForgetGen]
        exact milnorSymbol_mul_oneSub hu
    | twisted u v =>
        simp only [map_add, map_mul, FreeAlgebra.lift_ι_apply, milnorWittForgetGen, zero_mul, add_zero]
        exact milnorSymbol_mul u v
    | central u =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply, milnorWittForgetGen, zero_mul, mul_zero]
    | hyperbolic =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply, milnorWittForgetGen, zero_mul]⟩

@[simp] theorem milnorWittForget_symbol (u : Fˣ) :
    milnorWittForget F (milnorWittSymbol u : MilnorWittK F) = milnorSymbol u := by
  show RingQuot.liftAlgHom ℤ _ (RingQuot.mkAlgHom ℤ (MilnorWittRel F) _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  show FreeAlgebra.lift ℤ (milnorWittForgetGen (F := F)) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem milnorWittForget_eta :
    milnorWittForget F (milnorWittEta F) = (0 : MilnorK F) := by
  show RingQuot.liftAlgHom ℤ _ (RingQuot.mkAlgHom ℤ (MilnorWittRel F) _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  show FreeAlgebra.lift ℤ (milnorWittForgetGen (F := F)) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

end MilnorWitt

end GaloisForLFunctions.HTGeometry
