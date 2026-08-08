/-
# The invisibility barrier: whole classes of RH₂ deciders are constant

Several independent no-gos in this development have one shape: a natural invariant is *blind* to the
distinction that decides a rung.  This file abstracts that shape into a single barrier principle and
instantiates it, so the statements become metatheorems over *every* decider in a class, not one
example each.

* `decider_blind_of_invariant_collision` — **the barrier principle**: if an invariant `I` sends a
  "pass" and a "fail" configuration to the same value, then *every* decider `D` factoring through `I`
  returns the same verdict on both.  No `I`-decider separates them.

Two structurally different instantiations on the deck charge:

* `deckCharge_quotient_barrier` — the modulus-`n` deck charge collapses `k` and `k + n·q`, so no
  deck-charge decider sees the discarded quotient `index / n`.
* `reflection_parity_barrier` — a fixed-point-free reflection pairing of off-line zeros (matching
  multiplicities) has trivial parity, the empty/RH-passing value; so no parity decider distinguishes a
  reflection-symmetric buckling from the empty configuration.
* `exists_parity_blind_buckling` — a concrete two-zero buckling realizing the collision: parity-blind,
  yet carrying `2 > 0` off-line zeros (RH₂-failing).  The barrier is not vacuous.

The moral, made exact: a rung-deciding functional must read the *discarded quotient* (a quadrant-local
count), never the global charge alone.  The barrier is a constraint on the shape of any proof, in the
spirit of complexity-theoretic barriers — a genre analytic number theory rarely states.
-/
import GaloisForLFunctions.RHTower.SignatureParity

open Complex

namespace RHTower

/-! ### The barrier principle -/

/-- **The invisibility barrier.**  A decider `D` factoring through an invariant `I` is blind to any
"pass"/"fail" pair the invariant collapses: it returns the same verdict on both.  No invariant-factoring
decider separates a collision. -/
theorem decider_blind_of_invariant_collision {X M : Type*} (I : X → M) {pass fail : X}
    (hcoll : I pass = I fail) (D : M → Prop) : D (I pass) ↔ D (I fail) := by rw [hcoll]

/-- **The quantitative barrier.**  The same shape for *bounds* rather than verdicts: a majorant
factoring through an invariant is at least the value of the majorised quantity at *both* members of a
collided pair, so it cannot certify a gap between them.  Where the decider form says "no verdict
separates them", this says "no bound separates them", which is what an inequality-based route needs to be
tested against. -/
theorem le_bound_of_invariant_collision {X M : Type*} (I : X → M) (B : M → ℝ) (Φ : X → ℝ)
    (hB : ∀ x, Φ x ≤ B (I x)) {pass fail : X} (hcoll : I pass = I fail) :
    max (Φ pass) (Φ fail) ≤ B (I pass) := by
  refine max_le (hB pass) ?_
  rw [hcoll]
  exact hB fail

/-! ### Instantiation A — the modulus-`n` quotient barrier -/

/-- **The deck-charge quotient barrier.**  For every decider `D` factoring through the modulus-`n`
deck charge, the indices `k` and `k + n·q` receive the same verdict: the discarded quotient
`index / n` is invisible to any charge decider. -/
theorem deckCharge_quotient_barrier (n : ℕ) (k q : ℤ) (D : ℂ → Prop) :
    D (deckRed n k) ↔ D (deckRed n (k + n * q)) :=
  decider_blind_of_invariant_collision (deckRed n) (deckRed_add_mul n k q).symm D

/-! ### Instantiation B — the reflection-parity barrier -/

/-- **The reflection-parity barrier.**  A fixed-point-free reflection pairing of off-line zeros
(`σ` an involution with no fixed point on `s`, matching multiplicities `m`) has even total order, so
its parity `deckRed 2 (Σ m)` is `1` — the empty/RH-passing value.  Hence every parity decider `D`
gives the buckled configuration the same verdict as the empty one, though it carries `Σ m` off-line
zeros.  No parity decider detects a reflection-symmetric buckling. -/
theorem reflection_parity_barrier {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (σ : ι → ι) (m : ι → ℕ)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i) (hm : ∀ i ∈ s, m (σ i) = m i) (D : ℂ → Prop) :
    D (deckRed 2 (↑(∑ i ∈ s, m i))) ↔ D (deckRed 2 0) := by
  rw [reflection_paired_deckRed_two_eq_one s σ m hσs hσσ hfix hm, deckRed_zero]

/-- **The barrier is not vacuous.**  An explicit two-zero reflection buckling: a fixed-point-free
involution on two off-line zeros of multiplicity one, whose total order `2 > 0` makes it RH₂-failing,
yet whose parity is exactly the empty/RH-passing value.  Every parity decider is fooled by it. -/
theorem exists_parity_blind_buckling :
    ∃ (s : Finset (Fin 2)) (σ : Fin 2 → Fin 2) (m : Fin 2 → ℕ),
      (∀ i ∈ s, σ i ∈ s) ∧ (∀ i ∈ s, σ (σ i) = i) ∧ (∀ i ∈ s, σ i ≠ i) ∧
      (∀ i ∈ s, m (σ i) = m i) ∧ 0 < (∑ i ∈ s, m i) ∧
      deckRed 2 (↑(∑ i ∈ s, m i)) = deckRed 2 0 := by
  refine ⟨Finset.univ, fun i : Fin 2 => 1 - i, fun _ => 1, fun i _ => Finset.mem_univ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; fin_cases i <;> decide
  · intro i _; fin_cases i <;> decide
  · intro i _; rfl
  · simp
  · have hs : (∑ _i ∈ (Finset.univ : Finset (Fin 2)), (1 : ℕ)) = 2 := by simp
    rw [hs, deckRed_zero, deckRed_two_eq_one_iff]
    decide

end RHTower
