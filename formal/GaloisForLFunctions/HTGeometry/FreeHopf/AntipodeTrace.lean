import GaloisForLFunctions.HTGeometry.FreeWordSeriesHopfModel
import Mathlib.Data.List.Palindrome
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Palindromes and the homogeneous antipode trace

On words of degree `n`, the actual free Hopf antipode is signed reversal.
Its diagonal therefore consists precisely of palindromes. Removing the
matching endpoint letters counts these recursively and gives the exact
trace `(-1)ⁿ q^⌈n/2⌉` over an alphabet of size `q`. This is a second
half-exponential trace mechanism alongside the balanced involution in
Zehavi, Proposition 4.16, arXiv:2611.18218.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.FreeHopf

open Finset WordSeries

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Palindromic words in the existing homogeneous word basis. -/
def palindromeWords (n : ℕ) : Finset (List A) :=
  (wordsOfLength n).filter List.Palindrome

@[simp] theorem mem_palindromeWords (w : List A) (n : ℕ) :
    w ∈ palindromeWords n ↔ w.length = n ∧ w.Palindrome := by
  simp only [palindromeWords, Finset.mem_filter, mem_wordsOfLength]

theorem palindromeWords_card_zero : (palindromeWords (A := A) 0).card = 1 := by
  have he : palindromeWords (A := A) 0 = {[]} := by
    ext w
    simp only [mem_palindromeWords, Finset.mem_singleton]
    constructor
    · exact fun h => List.length_eq_zero_iff.mp h.1
    · rintro rfl
      exact ⟨rfl, List.Palindrome.nil⟩
  rw [he, Finset.card_singleton]

theorem palindromeWords_card_one : (palindromeWords (A := A) 1).card = Fintype.card A := by
  symm
  change (Finset.univ : Finset A).card = _
  apply Finset.card_bij (fun a _ => [a])
  · intro a _
    exact (mem_palindromeWords _ _).mpr ⟨rfl, List.Palindrome.singleton a⟩
  · intro a _ b _ h
    simpa using h
  · intro w hw
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp ((mem_palindromeWords _ _).mp hw).1
    exact ⟨a, Finset.mem_univ _, rfl⟩

/-- Removing the two matching endpoints leaves an arbitrary shorter palindrome. -/
theorem palindromeWords_card_add_two (n : ℕ) :
    (palindromeWords (A := A) (n + 2)).card =
      Fintype.card A * (palindromeWords (A := A) n).card := by
  rw [← Finset.card_univ, ← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ => p.1 :: (p.2 ++ [p.1]))
  · rintro ⟨a, w⟩ hp
    obtain ⟨hw, hp⟩ := (mem_palindromeWords _ _).mp (Finset.mem_product.mp hp).2
    exact (mem_palindromeWords _ _).mpr ⟨by simp [hw], List.Palindrome.cons_concat a hp⟩
  · rintro ⟨a, w⟩ _ ⟨b, v⟩ _ h
    obtain ⟨hab, htail⟩ := List.cons.inj h
    change a = b at hab
    change w ++ [a] = v ++ [b] at htail
    subst b
    exact Prod.ext rfl (List.append_cancel_right htail)
  · intro w hw
    obtain ⟨hlen, hp⟩ := (mem_palindromeWords _ _).mp hw
    cases hp with
    | nil => simp at hlen
    | singleton a => simp only [List.length_singleton] at hlen; omega
    | @cons_concat a v hp =>
      refine ⟨(a, v), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      refine (mem_palindromeWords _ _).mpr ⟨?_, hp⟩
      change v.length = n
      simpa using hlen

/-- Exactly half the letters, rounded upward, can be chosen freely in a palindrome. -/
theorem palindromeWords_card (n : ℕ) :
    (palindromeWords (A := A) n).card = Fintype.card A ^ ((n + 1) / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using (palindromeWords_card_zero (A := A))
  | one => simpa using (palindromeWords_card_one (A := A))
  | more n hn _ =>
    rw [palindromeWords_card_add_two, hn]
    have he : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
    rw [he, pow_succ']

variable (k : Type*) [Field k]

/-- The coefficient matrix of the actual antipode on homogeneous monomials. -/
def antipodeWordMatrix (n : ℕ) :
    Matrix (wordsOfLength (A := A) n) (wordsOfLength (A := A) n) k :=
  fun u v => (antipode (single v.val (1 : k))).coeff u.val

/-- The exact homogeneous antipode trace is signed palindrome count. -/
theorem antipodeWordMatrix_trace (n : ℕ) :
    Matrix.trace (antipodeWordMatrix (A := A) k n) =
      (-1 : k) ^ n * (Fintype.card A : k) ^ ((n + 1) / 2) := by
  unfold Matrix.trace Matrix.diag antipodeWordMatrix
  rw [← Finset.sum_subtype (wordsOfLength (A := A) n) (fun _ => Iff.rfl)
    (fun w => (antipode (single w (1 : k))).coeff w)]
  simp only [antipode_coeff, single_coeff]
  have he : (∑ w ∈ wordsOfLength (A := A) n,
      (-1 : k) ^ w.length * (if w.reverse = w then 1 else 0)) =
        (-1 : k) ^ n * (palindromeWords (A := A) n).card := by
    calc
      _ = ∑ w ∈ wordsOfLength (A := A) n,
          (-1 : k) ^ n * (if w.Palindrome then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [mem_wordsOfLength.mp hw, List.Palindrome.iff_reverse_eq]
      _ = (-1 : k) ^ n * ∑ w ∈ wordsOfLength (A := A) n,
          (if w.Palindrome then 1 else 0) := by rw [Finset.mul_sum]
      _ = _ := by rw [← Finset.sum_filter]; simp [palindromeWords]
  rw [he, palindromeWords_card, Nat.cast_pow]

end GaloisForLFunctions.HTGeometry.FreeHopf

#print axioms GaloisForLFunctions.HTGeometry.FreeHopf.palindromeWords_card
#print axioms GaloisForLFunctions.HTGeometry.FreeHopf.antipodeWordMatrix_trace
