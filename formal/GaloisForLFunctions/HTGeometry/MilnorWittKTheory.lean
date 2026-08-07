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
* `mwSymbol`, `mwEta` : the two families of generators.
* `mwSymbol_mul` : twisted additivity.
* `mwSymbol_mul_oneSub` : the Steinberg relation.
* `mwSymbol_one` : the symbol of `1` vanishes, in a field with more than two elements.
* `mwUnitForm` : the unit form `⟨u⟩ = 1 + η[u]`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWitt

variable (F : Type*) [Field F]

/-- `-1` as a unit. -/
def negOneUnit : Fˣ := Units.mk0 (-1 : F) (neg_ne_zero.mpr one_ne_zero)

@[simp] theorem negOneUnit_val : ((negOneUnit F : Fˣ) : F) = -1 := rfl

/-- The generators of the Milnor--Witt presentation: a symbol for every unit, and `η`. -/
inductive MilnorWittGen (F : Type*) [Field F]
  | unit (u : Fˣ)
  | eta

/-- **Morel's relations** for Milnor--Witt `K`-theory. -/
inductive MilnorWittRel :
    FreeAlgebra ℤ (MilnorWittGen F) → FreeAlgebra ℤ (MilnorWittGen F) → Prop
  | steinberg (u : Fˣ) (hu : (u : F) ≠ 1) :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MilnorWittGen.unit u) *
          FreeAlgebra.ι ℤ (MilnorWittGen.unit (oneSubUnit hu))) 0
  | twisted (u v : Fˣ) :
      MilnorWittRel (FreeAlgebra.ι ℤ (MilnorWittGen.unit (u * v)))
        (FreeAlgebra.ι ℤ (MilnorWittGen.unit u) + FreeAlgebra.ι ℤ (MilnorWittGen.unit v)
          + FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)) *
            FreeAlgebra.ι ℤ (MilnorWittGen.unit u) * FreeAlgebra.ι ℤ (MilnorWittGen.unit v))
  | central (u : Fˣ) :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)) * FreeAlgebra.ι ℤ (MilnorWittGen.unit u))
        (FreeAlgebra.ι ℤ (MilnorWittGen.unit u) * FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)))
  | hyperbolic :
      MilnorWittRel
        (FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)) *
          (FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)) *
            FreeAlgebra.ι ℤ (MilnorWittGen.unit (negOneUnit F)) + 2)) 0

/-- **The Milnor--Witt `K`-ring of a field.** -/
abbrev MilnorWittK : Type _ := RingQuot (MilnorWittRel F)

/-- The quotient map onto the Milnor--Witt `K`-ring. -/
def mwMk : FreeAlgebra ℤ (MilnorWittGen F) →ₐ[ℤ] MilnorWittK F :=
  RingQuot.mkAlgHom ℤ (MilnorWittRel F)

/-- **The generator `η`.** -/
def mwEta : MilnorWittK F := mwMk F (FreeAlgebra.ι ℤ (MilnorWittGen.eta (F := F)))

variable {F}

/-- **The Milnor--Witt symbol** `[u]`. -/
def mwSymbol (u : Fˣ) : MilnorWittK F :=
  mwMk F (FreeAlgebra.ι ℤ (MilnorWittGen.unit u))

/-- **Twisted additivity**: `[uv] = [u] + [v] + η[u][v]`. -/
theorem mwSymbol_mul (u v : Fˣ) :
    (mwSymbol (u * v) : MilnorWittK F)
      = mwSymbol u + mwSymbol v + mwEta F * mwSymbol u * mwSymbol v := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.twisted (F := F) u v)
  simpa [mwSymbol, mwEta, mwMk] using h

/-- **The Steinberg relation**: `[u][1 - u] = 0`. -/
theorem mwSymbol_mul_oneSub {u : Fˣ} (hu : (u : F) ≠ 1) :
    (mwSymbol u : MilnorWittK F) * mwSymbol (oneSubUnit hu) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.steinberg (F := F) u hu)
  simpa [mwSymbol, mwMk] using h

/-- **`η` is central on the symbols**. -/
theorem mwEta_mul_symbol (u : Fˣ) :
    mwEta F * (mwSymbol u : MilnorWittK F) = mwSymbol u * mwEta F := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.central (F := F) u)
  simpa [mwSymbol, mwEta, mwMk] using h

/-- **The hyperbolic relation**: `η(η[-1] + 2) = 0`. -/
theorem mwEta_hyperbolic :
    mwEta F * (mwEta F * mwSymbol (negOneUnit F) + 2) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittRel.hyperbolic (F := F))
  simpa [mwSymbol, mwEta, mwMk, map_ofNat] using h

/-- Twisted additivity with the first entry equal to one: `[1] + η[1][v] = 0`. -/
theorem mwSymbol_one_add (v : Fˣ) :
    (mwSymbol 1 : MilnorWittK F) + mwEta F * mwSymbol 1 * mwSymbol v = 0 := by
  have h := mwSymbol_mul (F := F) 1 v
  rw [one_mul] at h
  have h0 : (mwSymbol 1 + mwSymbol v + mwEta F * mwSymbol 1 * mwSymbol v : MilnorWittK F)
      - mwSymbol v = 0 := sub_eq_zero_of_eq h.symm
  calc (mwSymbol 1 : MilnorWittK F) + mwEta F * mwSymbol 1 * mwSymbol v
      = (mwSymbol 1 + mwSymbol v + mwEta F * mwSymbol 1 * mwSymbol v) - mwSymbol v := by abel
    _ = 0 := h0

/-- **The symbol of `1` vanishes**, in a field with a unit other than `1`.  Multiplying twisted
additivity by `η[1]` turns the left side into `[1]` and the right side into `η²[1][u][1-u]`, which
the Steinberg relation kills. -/
theorem mwSymbol_one (hF : ∃ u : Fˣ, (u : F) ≠ 1) : (mwSymbol 1 : MilnorWittK F) = 0 := by
  obtain ⟨u, hu⟩ := hF
  have hkey : ∀ v : Fˣ, mwEta F * (mwSymbol 1 : MilnorWittK F) * mwSymbol v = -mwSymbol 1 := by
    intro v
    have h := mwSymbol_one_add (F := F) v
    have h' : mwEta F * (mwSymbol 1 : MilnorWittK F) * mwSymbol v + mwSymbol 1 = 0 := by
      rw [← h]; abel
    exact eq_neg_of_add_eq_zero_left h'
  have hmul := mwSymbol_mul (F := F) u (oneSubUnit hu)
  have hexpand : mwEta F * (mwSymbol 1 : MilnorWittK F) * mwSymbol (u * oneSubUnit hu)
      = mwEta F * mwSymbol 1 * mwSymbol u + mwEta F * mwSymbol 1 * mwSymbol (oneSubUnit hu)
        + mwEta F * mwSymbol 1 * (mwEta F * mwSymbol u * mwSymbol (oneSubUnit hu)) := by
    rw [hmul]; noncomm_ring
  rw [hkey (u * oneSubUnit hu), hkey u, hkey (oneSubUnit hu)] at hexpand
  have hz : (-mwSymbol 1 : MilnorWittK F)
      - (-mwSymbol 1 + -mwSymbol 1
        + mwEta F * mwSymbol 1 * (mwEta F * mwSymbol u * mwSymbol (oneSubUnit hu))) = 0 :=
    sub_eq_zero_of_eq hexpand
  have hBT : (mwSymbol 1 : MilnorWittK F)
      - mwEta F * mwSymbol 1 * (mwEta F * mwSymbol u * mwSymbol (oneSubUnit hu)) = 0 := by
    calc (mwSymbol 1 : MilnorWittK F)
        - mwEta F * mwSymbol 1 * (mwEta F * mwSymbol u * mwSymbol (oneSubUnit hu))
        = (-mwSymbol 1 : MilnorWittK F)
          - (-mwSymbol 1 + -mwSymbol 1
            + mwEta F * mwSymbol 1 * (mwEta F * mwSymbol u * mwSymbol (oneSubUnit hu))) := by
          abel
      _ = 0 := hz
  have hval := sub_eq_zero.mp hBT
  have hst : mwEta F * (mwSymbol u : MilnorWittK F) * mwSymbol (oneSubUnit hu) = 0 := by
    rw [mul_assoc, mwSymbol_mul_oneSub hu, mul_zero]
  rw [hval, hst, mul_zero]

/-- **The unit form** `⟨u⟩ = 1 + η[u]`. -/
def mwUnitForm (u : Fˣ) : MilnorWittK F := 1 + mwEta F * mwSymbol u

/-- The unit form of a product, from twisted additivity. -/
theorem mwUnitForm_mul (u v : Fˣ) :
    (mwUnitForm (u * v) : MilnorWittK F)
      = mwUnitForm u + mwUnitForm v - 1 + mwEta F * (mwEta F * mwSymbol u * mwSymbol v) := by
  rw [mwUnitForm, mwUnitForm, mwUnitForm, mwSymbol_mul]
  noncomm_ring

/-- The generators, sent to the Milnor symbols with `η` sent to zero. -/
def mwToMilnorGen : MilnorWittGen F → MilnorK F
  | MilnorWittGen.unit u => milnorSymbol u
  | MilnorWittGen.eta => 0

/-- **Killing `η` gives Milnor `K`-theory.**  Twisted additivity becomes ordinary additivity, the
centrality and hyperbolic relations become `0 = 0`, and the Steinberg relation is the Steinberg
relation. -/
noncomputable def mwToMilnor : MilnorWittK F →ₐ[ℤ] MilnorK F :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (mwToMilnorGen (F := F)), by
    intro x y hxy
    induction hxy with
    | steinberg u hu =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply, mwToMilnorGen]
        exact milnorSymbol_mul_oneSub hu
    | twisted u v =>
        simp only [map_add, map_mul, FreeAlgebra.lift_ι_apply, mwToMilnorGen, zero_mul, add_zero]
        exact milnorSymbol_mul u v
    | central u =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply, mwToMilnorGen, zero_mul, mul_zero]
    | hyperbolic =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply, mwToMilnorGen, zero_mul]⟩

@[simp] theorem mwToMilnor_symbol (u : Fˣ) :
    mwToMilnor (mwSymbol u : MilnorWittK F) = milnorSymbol u := by
  show RingQuot.liftAlgHom ℤ _ (RingQuot.mkAlgHom ℤ (MilnorWittRel F) _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  show FreeAlgebra.lift ℤ (mwToMilnorGen (F := F)) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem mwToMilnor_eta : mwToMilnor (mwEta F) = (0 : MilnorK F) := by
  show RingQuot.liftAlgHom ℤ _ (RingQuot.mkAlgHom ℤ (MilnorWittRel F) _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  show FreeAlgebra.lift ℤ (mwToMilnorGen (F := F)) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

end MilnorWitt

end GaloisForLFunctions.HTGeometry
