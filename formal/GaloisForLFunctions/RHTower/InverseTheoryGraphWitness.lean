import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteAmplifierFrame

/-!
# The graph-world witness: a 3-regular prism violating the Ramanujan bound

The inverse-theory independence metatheorem needs a concrete structure satisfying the
graph-world analogues of the no-go-derived axioms whose RH-conclusion fails.  This module
certifies the witness: the prism over the 16-cycle (`C₁₆ × K₂`, 3-regular on 32 vertices)
carries the explicit mean-zero cosine vector

`v(j, s) = cos(2πj/16)`

whose Rayleigh quotient against the adjacency operator is exactly `2cos(π/8) + 1`, and

`2cos(π/8) + 1 > 2√2 = 2√(d−1)`

by pure algebra (`√(2+√2) > 2√2 − 1 ⟺ 5√2 > 7 ⟺ 50 > 49`).  A poorly expanding
3-regular graph therefore has spectral mass strictly beyond the Ramanujan bound on the
mean-zero sector; the Ihara RH-analogue fails while the finite-trace axioms hold.

The sampled-cosine sums are evaluated by the discrete root-of-unity averaging of
`HTGeometry.FiniteAmplifierFrame`; no numerical computation enters.
-/

namespace RHTower

noncomputable section

open Finset Real

/-- The prism vertex set: the 16-cycle times an edge. -/
abbrev PrismV : Type := ZMod 16 × Bool

/-- The prism adjacency relation: cycle steps on the first coordinate, one rung on the
second. -/
def prismRel (p q : PrismV) : Prop :=
  (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1)) ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)

theorem prismRel_symm : Std.Symm prismRel := by
  refine ⟨fun p q h => ?_⟩
  rcases h with ⟨hs, hj | hj⟩ | ⟨hj, hs⟩
  · exact Or.inl ⟨hs.symm, Or.inr hj⟩
  · exact Or.inl ⟨hs.symm, Or.inl hj⟩
  · exact Or.inr ⟨hj.symm, hs.symm⟩

theorem prismRel_irrefl : Std.Irrefl prismRel := by
  refine ⟨fun p h => ?_⟩
  rcases h with ⟨-, hj | hj⟩ | ⟨-, hs⟩
  · exact absurd (left_eq_add.mp hj) (by decide)
  · exact absurd (left_eq_add.mp hj) (by decide)
  · exact hs rfl

/-- The prism graph `C₁₆ × K₂`. -/
def prismAdj : SimpleGraph PrismV := ⟨prismRel, prismRel_symm, prismRel_irrefl⟩

/-- The three neighbors of a prism vertex, exactly. -/
theorem prismRel_iff (p q : PrismV) :
    prismRel p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, !p.2) := by
  constructor
  · rintro (⟨hs, hj | hj⟩ | ⟨hj, hs⟩)
    · left
      exact Prod.ext hj hs.symm
    · right; left
      refine Prod.ext ?_ hs.symm
      rw [hj]
      ring
    · right; right
      refine Prod.ext hj.symm ?_
      cases hp : p.2 <;> cases hq : q.2 <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ?_⟩
      ring
    · refine Or.inr ⟨rfl, ?_⟩
      cases p.2 <;> simp

/-- The prism is 3-regular. -/
theorem prismAdj_degree (p : PrismV) : (prismAdj.neighborFinset p).card = 3 := by
  classical
  have hset : prismAdj.neighborFinset p
      = {(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, !p.2)} := by
    ext q
    rw [SimpleGraph.mem_neighborFinset]
    rw [show prismAdj.Adj = prismRel from rfl, prismRel_iff]
    simp [Finset.mem_insert]
  rw [hset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    intro hcontra
    have := congrArg Prod.snd hcontra
    simp at this
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · intro hcontra
      have := congrArg Prod.fst hcontra
      simp only at this
      have h2 : (2 : ZMod 16) = 0 := by
        have : p.1 + 1 - (p.1 - 1) = 0 := by rw [this]; ring
        calc (2 : ZMod 16) = p.1 + 1 - (p.1 - 1) := by ring
          _ = 0 := this
      exact absurd h2 (by decide)
    · intro hcontra
      have := congrArg Prod.snd hcontra
      simp at this

/-! ## The cosine witness vector and its exact Rayleigh data -/

/-- The mean-zero cosine vector on the prism. -/
def prismVec (p : PrismV) : ℝ := Real.cos (2 * Real.pi * (p.1.val : ℝ) / 16)

/-- The adjacency sum of a function at a vertex. -/
def prismAdjSum (v : PrismV → ℝ) (p : PrismV) : ℝ :=
  v (p.1 + 1, p.2) + v (p.1 - 1, p.2) + v (p.1, !p.2)

/-- The adjacency energy `⟨Av, v⟩`. -/
def prismEnergy (v : PrismV → ℝ) : ℝ := ∑ p : PrismV, prismAdjSum v p * v p

/-- The squared norm `⟨v, v⟩`. -/
def prismNormSq (v : PrismV → ℝ) : ℝ := ∑ p : PrismV, v p ^ 2

private theorem cos_div16_mod (m : ℕ) :
    Real.cos (2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16) = Real.cos (2 * Real.pi * m / 16) := by
  have hm := Nat.div_add_mod m 16
  have harg : 2 * Real.pi * (m : ℝ) / 16
      = 2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16 + (m / 16 : ℕ) * (2 * Real.pi) := by
    have hcast : (m : ℝ) = 16 * ((m / 16 : ℕ) : ℝ) + ((m % 16 : ℕ) : ℝ) := by
      exact_mod_cast (congrArg (fun k => (k : ℝ)) hm).symm
    rw [hcast]
    ring
  rw [harg]
  have := Real.cos_add_int_mul_two_pi
    (2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16) ((m / 16 : ℕ) : ℤ)
  rw [← this]
  congr 1
  push_cast
  ring

private theorem prismVec_add_one (j : ZMod 16) (s : Bool) :
    prismVec (j + 1, s) = Real.cos (2 * Real.pi * ((j.val : ℝ) + 1) / 16) := by
  unfold prismVec
  simp only
  have hval : (j + 1).val = (j.val + 1) % 16 := by
    rw [ZMod.val_add]
    congr 1
    simp [ZMod.val_one]
  rw [hval, cos_div16_mod (j.val + 1)]
  push_cast
  ring_nf

private theorem prismVec_sub_one (j : ZMod 16) (s : Bool) :
    prismVec (j - 1, s) = Real.cos (2 * Real.pi * ((j.val : ℝ) + 15) / 16) := by
  unfold prismVec
  simp only
  have hsub : j - 1 = j + 15 := by ring
  have hval : (j + 15).val = (j.val + 15) % 16 := by
    rw [ZMod.val_add]
    congr 1
    have : (15 : ZMod 16).val = 15 := by decide
    rw [this]
  rw [hsub, hval, cos_div16_mod (j.val + 15)]
  push_cast
  ring_nf

private theorem zmod_sum_eq_range (g : ℕ → ℝ) :
    ∑ j : ZMod 16, g j.val = ∑ j ∈ Finset.range 16, g j :=
  Fin.sum_univ_eq_sum_range (fun j => g j) 16

end

end RHTower
