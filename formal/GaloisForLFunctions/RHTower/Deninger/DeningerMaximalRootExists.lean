import GaloisForLFunctions.RHTower.Deninger.DeningerRootExponentBound

/-!
# A cyclically reduced element has a maximal root

The exponents for which a root exists form a nonempty set of naturals bounded by the length of the
word, so there is a greatest one, and the root it provides is maximal: a proper root of it would
multiply the exponents past the greatest.

* `deningerExists_maximalRoot` : the maximal root.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A cyclically reduced element has a maximal root.** -/
theorem deningerExists_maximalRoot (V₀ : List (Σ i, G i)) (hV₀ne : V₀ ≠ [])
    (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1) :
    ∃ (y : PushoutI φ) (N : ℕ), 0 < N ∧ y ^ N = deningerLetterProd (φ := φ) V₀ ∧
      ∀ (z : PushoutI φ) (k : ℕ), 1 < k → z ^ k ≠ y := by
  classical
  set P : ℕ → Prop := fun n => ∃ y : PushoutI φ, y ^ n = deningerLetterProd (φ := φ) V₀ with hP
  have hP1 : P 1 := ⟨deningerLetterProd (φ := φ) V₀, pow_one _⟩
  have hb : 1 ≤ V₀.length := List.length_pos_iff.2 hV₀ne
  set N : ℕ := Nat.findGreatest P V₀.length with hN
  have hPN : P N := Nat.findGreatest_spec hb hP1
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_findGreatest hb hP1)
  obtain ⟨y, hy⟩ := hPN
  refine ⟨y, N, hNpos, hy, ?_⟩
  intro z k hk hzk
  have hzN : P (k * N) := by
    refine ⟨z, ?_⟩
    rw [pow_mul, hzk, hy]
  have hle : k * N ≤ V₀.length := by
    obtain ⟨j, hj⟩ : ∃ j, k * N = j + 1 := ⟨k * N - 1, by
      have : 0 < k * N := Nat.mul_pos (by omega) hNpos
      omega⟩
    obtain ⟨w, hw⟩ := hzN
    rw [hj] at hw ⊢
    exact deningerRootExponent_le (d := d) V₀ hV₀ne hV₀red hV₀alt hV₀cyc w j hw
  have hlt : N < k * N := by
    calc N = 1 * N := by ring
      _ < k * N := (Nat.mul_lt_mul_right hNpos).2 (by omega)
  exact Nat.findGreatest_is_greatest hlt hle hzN

end RHTower
