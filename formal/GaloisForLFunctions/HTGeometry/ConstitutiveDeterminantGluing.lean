import GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality
import GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion

/-!
# Determinant-glued contextual exact law, positive erasure, and cycle memory

Each incidence of a finite connected graph carries a determinant sign `ε = ±1`, the vertex
constraint is `∏_{e ∋ v} ε_{v,e} = (-1)^{b v}` and gluing identifies the two half-edge signs.
Writing `ε = (-1)^x` turns the whole datum into the parity incidence equation `∂_G x = b`, so one
determinant law carries at once

* the **effectivity obstruction**: a global exact law exists iff the total charge is even iff the
  determinant anomaly `∏_v (-1)^{b v}` is one (`exists_glued_law_iff`), the anomaly being a literal
  gluing identity (`glued_anomaly_trivial`);
* the **cycle memory**: when it exists, the set of global exact laws has exactly
  `2 ^ (|E| − |V| + 1)` elements (`card_gluedLaws`);
* **positive erasure**: every local determinant complex is acyclic with positive shadow one and
  every proper observer face is exact for every charge, so those three readings are the same for
  even and odd total charge (`positive_erasure`).
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section Signs

/-- The determinant sign attached to a parity value. -/
def paritySign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

@[simp] theorem paritySign_zero : paritySign 0 = 1 := by simp [paritySign]

@[simp] theorem paritySign_one : paritySign 1 = -1 := by
  simp [paritySign]

theorem paritySign_ne_zero (x : ZMod 2) : paritySign x ≠ 0 := by
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;> simp

/-- The determinant sign is a character of the parity group. -/
theorem paritySign_add (x y : ZMod 2) : paritySign (x + y) = paritySign x * paritySign y := by
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one y with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]

theorem paritySign_injective : Function.Injective paritySign := by
  intro x y hxy
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one y with rfl | rfl <;> simp_all

theorem paritySign_eq_one_iff (x : ZMod 2) : paritySign x = 1 ↔ x = 0 := by
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;> simp

/-- **Positive erasure at the level of one determinant complex.** -/
theorem paritySign_mul_self (x : ZMod 2) : paritySign x * paritySign x = 1 := by
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;> simp

theorem paritySign_complex_ne_zero (x : ZMod 2) : ((paritySign x : ℤ) : ℂ) ≠ 0 := by
  simpa using paritySign_ne_zero x

/-- The positive determinant shadow of every local complex is one. -/
theorem positiveShadow_paritySign (x : ZMod 2) : positiveShadow ((paritySign x : ℤ) : ℂ) = 1 := by
  rcases zmodTwo_eq_zero_or_one x with rfl | rfl <;> simp [positiveShadow, paritySign]

theorem paritySign_prod {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    paritySign (∑ i ∈ s, f i) = ∏ i ∈ s, paritySign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, paritySign_add, ih]

end Signs

section Gluing

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The glued determinant datum: one sign per edge, obtained from a parity assignment. -/
def gluedSigns (x : G.edgeSet → ZMod 2) : G.edgeSet → ℤ := fun e => paritySign (x e)

/-- **The vertex determinant constraint is the parity incidence equation.** -/
theorem vertex_determinant_constraint (x : G.edgeSet → ZMod 2) (b : V → ZMod 2) (v : V) :
    (∏ e : ContextEdges G v, gluedSigns G x e) = paritySign (b v) ↔
      parityBoundary G x v = b v := by
  simp only [gluedSigns]
  rw [← paritySign_prod, ← parityBoundary_apply_incidence]
  constructor
  · exact fun h => paritySign_injective h
  · exact fun h => by rw [h]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The determinant anomaly is the total parity charge.** -/
theorem anomaly_eq_one_iff (b : V → ZMod 2) :
    (∏ v : V, paritySign (b v)) = 1 ↔ ∑ v, b v = 0 := by
  rw [← paritySign_prod, paritySign_eq_one_iff]

/-- **The anomaly of a glued family is trivial**: summing the vertex constraints counts every edge
sign twice. -/
theorem glued_anomaly_trivial (x : G.edgeSet → ZMod 2) :
    (∏ v : V, ∏ e : ContextEdges G v, gluedSigns G x e) = 1 := by
  have h : ∀ v : V, (∏ e : ContextEdges G v, gluedSigns G x e) = paritySign (parityBoundary G x v) := by
    intro v
    simp only [gluedSigns]
    rw [← paritySign_prod, ← parityBoundary_apply_incidence]
  rw [Finset.prod_congr rfl fun v _ => h v, ← paritySign_prod, sum_parityBoundary_eq_zero,
    paritySign_zero]

/-- **A global exact law exists iff the total charge is even iff the anomaly vanishes.** -/
theorem exists_glued_law_iff (hG : G.Connected) (b : V → ZMod 2) :
    (∃ x, parityBoundary G x = b) ↔ (∑ v, b v = 0) ∧ (∏ v : V, paritySign (b v)) = 1 := by
  rw [exists_parityBoundary_eq_iff G hG b, anomaly_eq_one_iff]
  tauto

end Gluing

section CycleMemory

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The solution fibre is a torsor over the cycle space. -/
noncomputable def solutionEquivKernel {b : V → ZMod 2} {x₀ : G.edgeSet → ZMod 2}
    (hx₀ : parityBoundary G x₀ = b) :
    {x : G.edgeSet → ZMod 2 // parityBoundary G x = b} ≃
      LinearMap.ker (parityBoundary G) where
  toFun x := ⟨x.1 + x₀, by
    simp only [LinearMap.mem_ker, map_add, x.2, hx₀]
    funext v
    exact CharTwo.add_self_eq_zero _⟩
  invFun k := ⟨k.1 + x₀, by
    have hk : parityBoundary G k.1 = 0 := k.2
    rw [map_add, hk, hx₀, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    funext e
    exact charTwo_add_cancel _ _
  right_inv k := by
    apply Subtype.ext
    funext e
    exact charTwo_add_cancel _ _

/-- **The cycle-memory count.**  When a global exact law exists, the set of global exact laws has
exactly `2 ^ (|E| − |V| + 1)` elements. -/
theorem card_gluedLaws [Nonempty V] (hG : G.Connected) {b : V → ZMod 2}
    (hb : ∑ v, b v = 0) :
    Fintype.card {x : G.edgeSet → ZMod 2 // parityBoundary G x = b}
      = 2 ^ (Fintype.card G.edgeSet + 1 - Fintype.card V) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_parityBoundary_eq_of_sum_eq_zero G hG hb
  have hcard : Fintype.card {x : G.edgeSet → ZMod 2 // parityBoundary G x = b}
      = Fintype.card (LinearMap.ker (parityBoundary G)) :=
    Fintype.card_congr (solutionEquivKernel G hx₀)
  have hrn := LinearMap.finrank_range_add_finrank_ker (parityBoundary G)
  rw [finrank_range_parityBoundary G hG, Module.finrank_pi] at hrn
  have hVpos : 0 < Fintype.card V := Fintype.card_pos
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (parityBoundary G))
      = Fintype.card G.edgeSet + 1 - Fintype.card V := by omega
  rw [hcard, Module.card_eq_pow_finrank (K := ZMod 2), hker, ZMod.card]

end CycleMemory

section PositiveErasure

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Positive erasure.**  Local homology, the positive determinant shadow, and proper-face
exactness are the same data for every charge, hence for even and odd total charge alike, while the
anomaly separates them. -/
theorem positive_erasure (hG : G.Connected) (b b' : V → ZMod 2) :
    (∀ x : ZMod 2, LinearMap.ker (torsionDifferential ((paritySign x : ℤ) : ℂ)) = ⊥ ∧
        LinearMap.range (torsionDifferential ((paritySign x : ℤ) : ℂ)) = ⊤) ∧
      (∀ x : ZMod 2, positiveShadow ((paritySign x : ℤ) : ℂ) = 1) ∧
      (∀ W : Finset V, W ≠ Finset.univ → ∃ x, ∀ v ∈ W, parityBoundary G x v = b v) ∧
      (∀ W : Finset V, W ≠ Finset.univ → ∃ x, ∀ v ∈ W, parityBoundary G x v = b' v) := by
  refine ⟨fun x => ⟨torsionDifferential_ker _ (paritySign_complex_ne_zero x),
      torsionDifferential_range _ (paritySign_complex_ne_zero x)⟩,
    positiveShadow_paritySign, fun W hW => exists_parityBoundary_eq_on_of_ne_univ G hG W hW b,
    fun W hW => exists_parityBoundary_eq_on_of_ne_univ G hG W hW b'⟩

/-- **The determinant-gluing law.**  One incidence equation carries global effectivity, the
determinant anomaly, the cycle-memory torsor, and positive erasure. -/
theorem determinant_gluing_law [Nonempty V] (hG : G.Connected) (b : V → ZMod 2) :
    ((∃ x, parityBoundary G x = b) ↔ (∑ v, b v = 0) ∧ (∏ v : V, paritySign (b v)) = 1) ∧
      (∀ x : G.edgeSet → ZMod 2, (∏ v : V, ∏ e : ContextEdges G v, gluedSigns G x e) = 1) ∧
      (∑ v, b v = 0 → Fintype.card {x : G.edgeSet → ZMod 2 // parityBoundary G x = b}
        = 2 ^ (Fintype.card G.edgeSet + 1 - Fintype.card V)) ∧
      (∀ W : Finset V, W ≠ Finset.univ → ∃ x, ∀ v ∈ W, parityBoundary G x v = b v) :=
  ⟨exists_glued_law_iff G hG b, glued_anomaly_trivial G,
    fun hb => card_gluedLaws G hG hb,
    fun W hW => exists_parityBoundary_eq_on_of_ne_univ G hG W hW b⟩

end PositiveErasure

end GaloisForLFunctions.HTGeometry
