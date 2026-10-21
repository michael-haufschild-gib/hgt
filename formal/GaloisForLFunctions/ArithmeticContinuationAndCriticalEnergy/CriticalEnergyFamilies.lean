import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Critical energy families and admission

The programme studies families indexed jointly by a continuous parameter (damping, aperture,
cutoff) and by a discrete observation horizon.  The only notion of success is **admission**: a
bound on the energy at a fixed parameter that is uniform in the horizon.  The quantifier order
`∃ B, ∀ T` is the content; `∀ T, ∃ B` is free and says nothing.

Three graded notions are separated here, because conflating them is the standard error:

* `Admits E ε` — one bound at one parameter, uniform in the horizon;
* `CofinallyAdmits E` — admission at parameters arbitrarily close to `0`, each with its own bound;
* `UniformlyAdmitsOn E s` — one bound for the whole parameter set, strictly stronger than
  admission at each of its points.

Nothing in this module is arithmetic.  It fixes the language that the continuation theorems and
the arithmetic instances must speak.
-/

open Set Filter

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

set_option autoImplicit false

/-- **Admission at a parameter.**  A horizon-uniform bound on the energy.  The bound may depend on
the parameter; it may not depend on the horizon. -/
def Admits (E : ℝ → ℕ → ℝ) (ε : ℝ) : Prop := ∃ B : ℝ, ∀ T : ℕ, E ε T ≤ B

/-- **Cofinal admission.**  Parameters arbitrarily close to `0` are admitted, each with its own
bound.  No bound uniform in the parameter is asked for. -/
def CofinallyAdmits (E : ℝ → ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ Admits E ε

/-- **Uniform admission on a set**: one bound for all parameters of the set. -/
def UniformlyAdmitsOn (E : ℝ → ℕ → ℝ) (s : Set ℝ) : Prop :=
  ∃ B : ℝ, ∀ ε ∈ s, ∀ T : ℕ, E ε T ≤ B

theorem admits_iff_bddAbove {E : ℝ → ℕ → ℝ} {ε : ℝ} :
    Admits E ε ↔ BddAbove (Set.range (E ε)) := by
  constructor
  · exact fun ⟨B, hB⟩ => ⟨B, fun _ ⟨T, hT⟩ => hT ▸ hB T⟩
  · exact fun ⟨B, hB⟩ => ⟨B, fun T => hB ⟨T, rfl⟩⟩

/-- Admission passes to any family dominated by an admitted one. -/
theorem Admits.of_le {E F : ℝ → ℕ → ℝ} {ε : ℝ} (hle : ∀ T, F ε T ≤ E ε T) (h : Admits E ε) :
    Admits F ε :=
  let ⟨B, hB⟩ := h; ⟨B, fun T => (hle T).trans (hB T)⟩

theorem Admits.add {E F : ℝ → ℕ → ℝ} {ε : ℝ} (hE : Admits E ε) (hF : Admits F ε) :
    Admits (fun x T => E x T + F x T) ε :=
  let ⟨B, hB⟩ := hE; let ⟨C, hC⟩ := hF; ⟨B + C, fun T => add_le_add (hB T) (hC T)⟩

theorem Admits.const_mul {E : ℝ → ℕ → ℝ} {ε r : ℝ} (hr : 0 ≤ r) (hE : Admits E ε) :
    Admits (fun x T => r * E x T) ε :=
  let ⟨B, hB⟩ := hE; ⟨r * B, fun T => mul_le_mul_of_nonneg_left (hB T) hr⟩

theorem UniformlyAdmitsOn.admits {E : ℝ → ℕ → ℝ} {s : Set ℝ} {ε : ℝ} (hε : ε ∈ s)
    (h : UniformlyAdmitsOn E s) : Admits E ε :=
  let ⟨B, hB⟩ := h; ⟨B, fun T => hB ε hε T⟩

/-- Admission at a single parameter of a set never upgrades to uniform admission on the set unless
the set is a point: the content of `UniformlyAdmitsOn` is the parameter-free bound. -/
theorem uniformlyAdmitsOn_singleton {E : ℝ → ℕ → ℝ} {ε : ℝ} :
    UniformlyAdmitsOn E {ε} ↔ Admits E ε := by
  constructor
  · exact fun h => h.admits (mem_singleton_iff.mpr rfl)
  · exact fun ⟨B, hB⟩ => ⟨B, fun x hx T => by rw [mem_singleton_iff.mp hx]; exact hB T⟩

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
