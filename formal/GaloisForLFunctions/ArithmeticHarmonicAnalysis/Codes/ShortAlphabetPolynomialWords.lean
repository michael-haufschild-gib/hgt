import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteDifference.ShortModularRigidity
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial words in a short alphabet

A polynomial evaluation word over `ZMod k` whose least representatives
lie in `[0,D]` is constant when `2^degree D < k`. The statement applies
also to composite moduli. For two polynomial words, the same constraint
on their difference permits only a constant offset.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Function Polynomial

private theorem difference_intCast (k n : ℕ) (f : ℕ → ℤ) (j : ℕ) :
    (((fwdDiff 1)^[n] f j : ℤ) : ZMod k) =
      (fwdDiff 1)^[n] (fun i => (f i : ZMod k)) j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    change (((fwdDiff 1)^[n] f (j + 1) - (fwdDiff 1)^[n] f j : ℤ) : ZMod k) = _
    rw [Int.cast_sub, ih, ih]
    rfl

private theorem difference_natCast {R : Type*} [Ring R] (f : R → R) (n j : ℕ) :
    (fwdDiff 1)^[n] (fun i : ℕ => f i) j = (fwdDiff 1)^[n] f (j : R) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    change (fwdDiff 1)^[n] (fun i : ℕ => f i) (j + 1) -
        (fwdDiff 1)^[n] (fun i : ℕ => f i) j =
      (fwdDiff 1)^[n] f ((j : R) + 1) - (fwdDiff 1)^[n] f (j : R)
    rw [ih, ih, Nat.cast_add, Nat.cast_one]

/-- A polynomial word in a sufficiently short consecutive alphabet is constant. -/
theorem polynomial_short_alphabet_iff (k : ℕ) [NeZero k] (P : (ZMod k)[X]) (D : ℕ)
    (hsize : 2 ^ P.natDegree * D < k) :
    (∀ x : ZMod k, (P.eval x).val ≤ D) ↔
      (P.eval 0).val ≤ D ∧ ∀ x : ZMod k, P.eval x = P.eval 0 := by
  constructor
  · intro hb
    let f : ℕ → ℤ := fun j => ((P.eval (j : ZMod k)).val : ℤ)
    have hbound : ∀ j, 0 ≤ f j ∧ f j ≤ 0 + (D : ℤ) := by
      intro j
      dsimp only [f]
      rw [zero_add]
      exact ⟨Int.natCast_nonneg _, by exact_mod_cast hb (j : ZMod k)⟩
    have hm : ∀ j, (fwdDiff 1)^[P.natDegree + 1] f j ≡ 0 [ZMOD (k : ℤ)] := by
      intro j
      apply (ZMod.intCast_eq_intCast_iff _ 0 k).mp
      rw [difference_intCast]
      have he : (fun i => (f i : ZMod k)) = fun i : ℕ => P.eval (i : ZMod k) := by
        funext i
        exact (Int.cast_natCast _).trans (ZMod.natCast_zmod_val _)
      rw [he, difference_natCast (fun x : ZMod k => P.eval x),
        P.fwdDiff_iter_degree_add_one_eq_zero]
      simp only [Pi.zero_apply, Int.cast_zero]
    have hc := (short_modular_iterated_difference_iff f 0 D k hbound P.natDegree
      (by exact_mod_cast hsize)).mp hm
    refine ⟨hb 0, fun x => ?_⟩
    have he := hc x.val
    dsimp only [f] at he
    simp only [Nat.cast_zero, ZMod.natCast_zmod_val] at he
    have hv : (P.eval x).val = (P.eval 0).val := by exact_mod_cast he
    have hc' := congrArg (fun n : ℕ => (n : ZMod k)) hv
    simpa only [ZMod.natCast_zmod_val] using hc'
  · rintro ⟨h0, hc⟩ x
    rw [hc x]
    exact h0

/-- A polynomial word either is constant or leaves every alphabet below its threshold. -/
theorem polynomial_word_alphabet_escape (k : ℕ) [NeZero k] (P : (ZMod k)[X]) (D : ℕ)
    (hsize : 2 ^ P.natDegree * D < k) :
    (∀ x, P.eval x = P.eval 0) ∨ ∃ x, D < (P.eval x).val := by
  by_cases hc : ∀ x, P.eval x = P.eval 0
  · exact Or.inl hc
  · right
    by_contra hn
    have hb : ∀ x, (P.eval x).val ≤ D := by
      intro x
      by_contra hx
      exact hn ⟨x, lt_of_not_ge hx⟩
    exact hc ((polynomial_short_alphabet_iff k P D hsize).mp hb).2

/-- Two polynomial words differing only through a short alphabet differ by a constant. -/
theorem polynomial_words_short_difference_iff (k : ℕ) [NeZero k]
    (P Q : (ZMod k)[X]) (D : ℕ) (hsize : 2 ^ (P - Q).natDegree * D < k) :
    (∀ x, (P.eval x - Q.eval x).val ≤ D) ↔
      (P.eval 0 - Q.eval 0).val ≤ D ∧
        ∀ x, P.eval x - Q.eval x = P.eval 0 - Q.eval 0 := by
  simpa only [eval_sub] using polynomial_short_alphabet_iff k (P - Q) D hsize

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.polynomial_short_alphabet_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.polynomial_word_alphabet_escape
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.polynomial_words_short_difference_iff
