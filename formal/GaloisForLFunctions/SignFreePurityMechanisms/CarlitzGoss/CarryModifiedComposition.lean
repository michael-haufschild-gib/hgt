import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.SingletonCarryBoundary
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CarryInterval
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixMatrixRealization

/-!
# Carry modification of actual digit prefixes

Read the integral inverse contents of actual proper prefixes backwards.
Their periodic residue rows provide the floor and step bounds needed by
the carry recursion. Identifying adjacent natural rows with cyclic
differences allows the modified contents to be realized by actual digits.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Adjacent natural rows with matching endpoints represent the cyclic difference. -/
private theorem cyclicDifference_nat_rows {s : ℕ} [NeZero s] (p : ℤ) (f : ℕ → ℤ)
    (hperiod : f s = f 0) (h : ZMod s) :
    cyclicDifference p (fun j : ZMod s => f j.val) h = p * f (h.val + 1) - f h.val := by
  have hcast : ((h.val + 1 : ℕ) : ZMod s) = h + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have hnext : f (h + 1).val = f (h.val + 1) := by
    by_cases hlt : h.val + 1 < s
    · rw [← hcast, ZMod.val_natCast_of_lt hlt]
    · have he : h.val + 1 = s := by have := ZMod.val_lt h; omega
      rw [← hcast, he, ZMod.natCast_self, ZMod.val_zero, hperiod]
  exact congrArg (fun z : ℤ => p * z - f h.val) hnext

namespace DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Actual proper-prefix inverse contents have periodic natural residue rows,
read from the terminal prefix down to the empty prefix. -/
private theorem exists_backward_inverse_rows (C : DigitComposition p s (m + 1) S) (hp : 2 ≤ p) :
    ∃ w : ℕ → ℕ → ℤ,
      w s = w 0 ∧
      (∀ h, w h m = 0) ∧
      (∀ h n, n ≤ m → (m : ℤ) - n ≤ w h n) ∧
      (∀ h n, n < m → w h (n + 1) + 1 ≤ w h n) ∧
      (∀ h n, n ≤ m → (p : ℤ) * w (h + 1) n - w h n =
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (m - n)) (h : ZMod s)) ∧
      (∀ h n, n ≤ m → (w h n : ℚ) = inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
          (C.prefixDigits (m - n)) j : ℚ)) (h : ZMod s)) := by
  obtain ⟨v, hv0, hvstep, hvE⟩ := C.exists_integral_inverse_prefixes hp
  let w : ℕ → ℕ → ℤ := fun h n => v (m - n) (h : ZMod s)
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
  have hInv (j : ℕ) (hj : j ≤ m) :
      inverseContent (p : ℚ)
        (fun h => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h : ℚ)) =
        fun h => (v j h : ℚ) := by
    have hE : cyclicDifference (p : ℚ) (fun h => (v j h : ℚ)) =
        fun h => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h : ℚ) := by
      funext h
      have he := congrFun (hvE j hj) h
      dsimp only [cyclicDifference] at he ⊢
      exact_mod_cast he
    rw [← hE, inverseContent_cyclicDifference _ hpow]
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext n
    simp only [w, ZMod.natCast_self, Nat.cast_zero]
  · intro h
    simp only [w, Nat.sub_self, hv0]
  · intro h n hn
    have hf := inverse_prefix_floor (hv0 (h : ZMod s))
      (fun j hj => hvstep j hj (h : ZMod s)) (m - n) (Nat.sub_le m n)
    rw [Nat.cast_sub hn] at hf
    exact hf
  · intro h n hn
    have hj : m - (n + 1) < m := by omega
    have he : m - (n + 1) + 1 = m - n := by omega
    have hs := hvstep (m - (n + 1)) hj (h : ZMod s)
    rw [he] at hs
    exact hs
  · intro h n _hn
    have he := congrFun (hvE (m - n) (Nat.sub_le m n)) (h : ZMod s)
    simpa only [cyclicDifference, w, Nat.cast_add, Nat.cast_one] using he
  · intro h n _hn
    exact (congrFun (hInv (m - n) (Nat.sub_le m n)) (h : ZMod s)).symm

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
