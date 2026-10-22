import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutNormal

/-!
# Uniqueness of roots of cyclically reduced elements

The word of a power of a cyclically reduced transversal word is the concatenation of copies of that
word, again a transversal word.  Since transversal words are determined by their products, equal
powers of cyclically reduced transversal elements have equal words.

* `deningerFlatten` : the concatenation of copies of a word.
* `deningerPow_injective_cycRed` : equal powers force equal words.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- The concatenation of `n` copies of a word. -/
def deningerFlatten (L : List (Σ i, G i)) (n : ℕ) : List (Σ i, G i) :=
  (List.replicate n L).flatten

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_succ (L : List (Σ i, G i)) (n : ℕ) :
    deningerFlatten (G := G) L (n + 1) = L ++ deningerFlatten (G := G) L n := by
  simp [deningerFlatten, List.replicate_succ]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_length (L : List (Σ i, G i)) (n : ℕ) :
    (deningerFlatten (G := G) L n).length = n * L.length := by
  induction n with
  | zero => simp [deningerFlatten]
  | succ n ih => rw [deningerFlatten_succ, List.length_append, ih]; ring

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_mem (L : List (Σ i, G i)) (n : ℕ) (p : Σ i, G i)
    (hp : p ∈ deningerFlatten (G := G) L n) : p ∈ L := by
  induction n with
  | zero => simp [deningerFlatten] at hp
  | succ n ih =>
    rw [deningerFlatten_succ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hp
    · exact ih hp

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_head (L : List (Σ i, G i)) (n : ℕ) (hne : L ≠ []) :
    (deningerFlatten (G := G) L (n + 1)).head? = L.head? := by
  rw [deningerFlatten_succ, List.head?_append_of_ne_nil _ hne]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerLetterProd_flatten (L : List (Σ i, G i)) (n : ℕ) :
    deningerLetterProd (φ := φ) (deningerFlatten (G := G) L n) =
      (deningerLetterProd (φ := φ) L) ^ n := by
  induction n with
  | zero => simp [deningerFlatten]
  | succ n ih =>
    rw [deningerFlatten_succ, deningerLetterProd_append, ih, ← pow_succ']

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
theorem deningerFlatten_isChain (L : List (Σ i, G i))
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) (n : ℕ) :
    List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (deningerFlatten (G := G) L n) := by
  induction n with
  | zero => simp [deningerFlatten]
  | succ n ih =>
    rw [deningerFlatten_succ]
    refine List.isChain_append.2 ⟨halt, ih, ?_⟩
    intro x hx y hy
    rcases hn : L with _ | ⟨a, L''⟩
    · rw [hn] at hx; simp at hx
    · cases n with
      | zero =>
        rw [deningerFlatten] at hy
        simp at hy
      | succ m =>
        rw [deningerFlatten_head L m (by rw [hn]; simp)] at hy
        exact hcyc x hx y hy

/-- **Equal powers of cyclically reduced transversal elements have equal words.** -/
theorem deningerPow_injective_cycRed (L M : List (Σ i, G i)) (n : ℕ) (hn : 0 < n)
    (hsetL : ∀ p ∈ L, p.2 ∈ d.set p.1) (hredL : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (haltL : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcycL : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1)
    (hsetM : ∀ p ∈ M, p.2 ∈ d.set p.1) (hredM : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (haltM : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hcycM : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1)
    (h : (deningerLetterProd (φ := φ) L) ^ n = (deningerLetterProd (φ := φ) M) ^ n) :
    L = M := by
  have hflat : deningerFlatten (G := G) L n = deningerFlatten (G := G) M n := by
    refine deningerLetterProd_injective (d := d) _ _
      (fun p hp => hsetL p (deningerFlatten_mem L n p hp))
      (fun p hp => hredL p (deningerFlatten_mem L n p hp))
      (deningerFlatten_isChain L haltL hcycL n)
      (fun p hp => hsetM p (deningerFlatten_mem M n p hp))
      (fun p hp => hredM p (deningerFlatten_mem M n p hp))
      (deningerFlatten_isChain M haltM hcycM n) ?_
    rw [deningerLetterProd_flatten, deningerLetterProd_flatten, h]
  have hlen : L.length = M.length := by
    have hl := congrArg List.length hflat
    rw [deningerFlatten_length, deningerFlatten_length] at hl
    exact Nat.eq_of_mul_eq_mul_left hn hl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [deningerFlatten_succ, deningerFlatten_succ] at hflat
  exact List.append_inj_left hflat hlen

end RHTower
