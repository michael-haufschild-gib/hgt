import GaloisForLFunctions.HTGeometry.MilnorKTheory
import Mathlib.Algebra.FreeAlgebra

/-!
# Milnor--Witt `K`-theory of a field

Milnor--Witt `K`-theory is the ring presented by Morel's generators and relations: a symbol `[u]`
for every unit and one further generator `η`, subject to the Steinberg relation, the twisted
multiplicativity `[uv] = [u] + [v] + η[u][v]`, centrality of `η`, and `η·(η[-1] + 2) = 0`.

Killing `η` collapses twisted multiplicativity to ordinary additivity of the symbol, so the
presentation maps onto Milnor `K`-theory.  That forgetful morphism is one corner of the fundamental
cartesian square of Milnor--Witt `K`-theory; the other corner needs the Witt ring, which is not
available here.

* `MilnorWittK` : the ring, as a quotient of the free algebra on the generators.
* `milnorWittSymbol`, `milnorWittEta` : the generators.
* `milnorWittSymbol_mul_oneSub`, `milnorWittSymbol_mul`, `milnorWittEta_comm`,
  `milnorWittEta_hyperbolic` : the four defining relations.
* `milnorWittForget` : the forgetful morphism onto Milnor `K`-theory.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWitt

variable (F : Type*) [Field F]

/-- The generators of the Milnor--Witt presentation: the extra generator `η` and the unit
symbols. -/
inductive MWGen (F : Type*) [Field F]
  | eta : MWGen F
  | sym : Fˣ → MWGen F

/-- **Morel's relations** for Milnor--Witt `K`-theory. -/
inductive MilnorWittRel :
    FreeAlgebra ℤ (MWGen F) → FreeAlgebra ℤ (MWGen F) → Prop
  | steinberg (a : Fˣ) (ha : (a : F) ≠ 1) :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MWGen.sym a) * FreeAlgebra.ι ℤ (MWGen.sym (oneSubUnit ha))) 0
  | twisted (u v : Fˣ) :
      MilnorWittRel (FreeAlgebra.ι ℤ (MWGen.sym (u * v)))
        (FreeAlgebra.ι ℤ (MWGen.sym u) + FreeAlgebra.ι ℤ (MWGen.sym v) +
          FreeAlgebra.ι ℤ (MWGen.eta) * FreeAlgebra.ι ℤ (MWGen.sym u) *
            FreeAlgebra.ι ℤ (MWGen.sym v))
  | central (u : Fˣ) :
      MilnorWittRel (FreeAlgebra.ι ℤ (MWGen.sym u) * FreeAlgebra.ι ℤ (MWGen.eta))
        (FreeAlgebra.ι ℤ (MWGen.eta) * FreeAlgebra.ι ℤ (MWGen.sym u))
  | hyperbolic :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MWGen.eta) *
          (FreeAlgebra.ι ℤ (MWGen.eta) * FreeAlgebra.ι ℤ (MWGen.sym (-1)) + 2)) 0

/-- **The Milnor--Witt `K`-ring of a field.** -/
abbrev MilnorWittK : Type _ := RingQuot (MilnorWittRel F)

/-- The quotient map onto the Milnor--Witt ring. -/
def milnorWittMk : FreeAlgebra ℤ (MWGen F) →ₐ[ℤ] MilnorWittK F :=
  RingQuot.mkAlgHom ℤ (MilnorWittRel F)

variable {F}

/-- The Milnor--Witt symbol `[u]`. -/
def milnorWittSymbol (u : Fˣ) : MilnorWittK F :=
  milnorWittMk F (FreeAlgebra.ι ℤ (MWGen.sym u))

variable (F) in
/-- The Milnor--Witt generator `η`. -/
def milnorWittEta : MilnorWittK F :=
  milnorWittMk F (FreeAlgebra.ι ℤ MWGen.eta)

/-- **The Steinberg relation.** -/
theorem milnorWittSymbol_mul_oneSub {a : Fˣ} (ha : (a : F) ≠ 1) :
    (milnorWittSymbol a : MilnorWittK F) * milnorWittSymbol (oneSubUnit ha) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.steinberg (F := F) a ha)
  rw [milnorWittSymbol, milnorWittSymbol, milnorWittMk, ← map_mul, h, map_zero]

/-- **Twisted multiplicativity**: `[uv] = [u] + [v] + η[u][v]`. -/
theorem milnorWittSymbol_mul (u v : Fˣ) :
    (milnorWittSymbol (u * v) : MilnorWittK F) =
      milnorWittSymbol u + milnorWittSymbol v +
        milnorWittEta F * milnorWittSymbol u * milnorWittSymbol v := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.twisted (F := F) u v)
  rw [milnorWittSymbol, milnorWittSymbol, milnorWittSymbol, milnorWittEta, milnorWittMk]
  rw [h, map_add, map_add, map_mul, map_mul]

/-- **`η` is central against the symbols.** -/
theorem milnorWittEta_comm (u : Fˣ) :
    (milnorWittSymbol u : MilnorWittK F) * milnorWittEta F =
      milnorWittEta F * milnorWittSymbol u := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.central (F := F) u)
  rw [milnorWittSymbol, milnorWittEta, milnorWittMk, ← map_mul, h, map_mul]

/-- **The hyperbolic relation** `η·(η[-1] + 2) = 0`. -/
theorem milnorWittEta_hyperbolic :
    (milnorWittEta F) * (milnorWittEta F * milnorWittSymbol (-1) + 2) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.hyperbolic (F := F))
  rw [milnorWittEta, milnorWittSymbol, milnorWittMk]
  rw [show ((2 : MilnorWittK F)) =
      RingQuot.mkAlgHom ℤ (MilnorWittRel F) (2 : FreeAlgebra ℤ (MWGen F)) by
    rw [map_ofNat]]
  rw [← map_mul, ← map_add, ← map_mul, h, map_zero]

variable (F) in
/-- The generator values of the forgetful morphism: `η` dies and `[u]` becomes the Milnor
symbol. -/
def milnorWittForgetGen : MWGen F → MilnorK F
  | MWGen.eta => 0
  | MWGen.sym u => milnorSymbol u

theorem milnorWittForget_rel :
    ∀ x y : FreeAlgebra ℤ (MWGen F), MilnorWittRel F x y →
      FreeAlgebra.lift ℤ (milnorWittForgetGen F) x =
        FreeAlgebra.lift ℤ (milnorWittForgetGen F) y := by
  rintro _ _ (⟨a, ha⟩ | ⟨u, v⟩ | ⟨u⟩ | _)
  · rw [map_mul, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, map_zero]
    exact milnorSymbol_mul_oneSub ha
  · rw [FreeAlgebra.lift_ι_apply, map_add, map_add, map_mul, map_mul,
      FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    show milnorSymbol (u * v) = milnorSymbol u + milnorSymbol v + 0 * _ * _
    rw [zero_mul, zero_mul, add_zero, milnorSymbol_mul]
  · rw [map_mul, map_mul, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    show milnorSymbol u * 0 = 0 * milnorSymbol u
    rw [mul_zero, zero_mul]
  · rw [map_mul, map_zero, FreeAlgebra.lift_ι_apply]
    show (0 : MilnorK F) * _ = 0
    rw [zero_mul]

variable (F) in
/-- **The forgetful morphism onto Milnor `K`-theory.**  Killing `η` turns twisted multiplicativity
into ordinary additivity of the symbol, which is exactly the Milnor relation. -/
def milnorWittForget : MilnorWittK F →ₐ[ℤ] MilnorK F :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (milnorWittForgetGen F), milnorWittForget_rel⟩

@[simp]
theorem milnorWittForget_symbol (u : Fˣ) :
    milnorWittForget F (milnorWittSymbol u) = milnorSymbol u := by
  rw [milnorWittForget, milnorWittSymbol, milnorWittMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply _ _

@[simp]
theorem milnorWittForget_eta : milnorWittForget F (milnorWittEta F) = 0 := by
  rw [milnorWittForget, milnorWittEta, milnorWittMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply _ _

/-- **The forgetful morphism is surjective.**  Milnor `K`-theory is generated by the symbols, all
of which are hit. -/
theorem milnorWittForget_surjective : Function.Surjective (milnorWittForget F) := by
  intro z
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective ℤ (MilnorKRel F) z
  induction w using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨algebraMap ℤ (MilnorWittK F) r, ?_⟩
    rw [AlgHom.commutes, AlgHom.commutes]
  | ι x =>
    refine ⟨milnorWittSymbol (Additive.toMul x), ?_⟩
    rw [milnorWittForget_symbol]
    rfl
  | mul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' * b', by rw [map_mul, ha', hb', map_mul]⟩
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩

end MilnorWitt

end GaloisForLFunctions.HTGeometry
