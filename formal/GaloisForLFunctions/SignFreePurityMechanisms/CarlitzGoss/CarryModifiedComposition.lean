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

/-- The local carry bounds join across the lower boundary and the unchanged rows. -/
private theorem carry_content_bounds {p : ℤ} {α β m h n : ℕ} {w : ℕ → ℕ → ℤ}
    (hp : 1 ≤ p) (hn : n < m)
    (hhigh : ∀ r, α < r → r ≤ β → (m : ℤ) + 1 ≤ w r 0)
    (hfloor : ∀ r j, j ≤ m → (m : ℤ) - j ≤ w r j)
    (hboundary : ∀ j ≤ m, w α j = (m : ℤ) - j)
    (hstep : ∀ r, w r (n + 1) + 1 ≤ w r n)
    (hnonneg : ∀ r, 0 ≤ p * w (r + 1) n - w r n)
    (hnested : ∀ r, p * w (r + 1) (n + 1) - w r (n + 1) ≤
      p * w (r + 1) n - w r n) :
    let d := intervalCarryRow p α β w
    let c := fun r j => p * d (r + 1) j - d r j
    0 ≤ c h n ∧ c h (n + 1) ≤ c h n ∧
      (α ≤ h ∧ h ≤ β → 0 < c h (n + 1) → c h (n + 1) + (p - 1) ≤ c h n) := by
  dsimp only
  by_cases hh : α ≤ h ∧ h ≤ β
  · by_cases he : h = α
    · subst h
      have hb := intervalCarryRow_content_boundary hp hn hhigh hfloor hboundary (hstep (α + 1))
      refine ⟨hb.1, ?_, fun _ _ => hb.2⟩
      have hg := hb.2
      dsimp only at hg ⊢
      omega
    · have hc := intervalCarryRow_content hp (show α < h by omega) hh.2 (hstep (h + 1))
      exact ⟨hc.1, hc.2.1, fun _ => hc.2.2⟩
  · refine ⟨?_, ?_, fun hc => (hh hc).elim⟩
    · rw [intervalCarryRow_content_outside p α β w hh n]
      exact hnonneg h
    · rw [intervalCarryRow_content_outside p α β w hh (n + 1),
        intervalCarryRow_content_outside p α β w hh n]
      exact hnested h

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

/-- Preserving one proper-prefix inverse coordinate preserves a positive
last remainder whenever the new proper content stays below the available content. -/
private theorem positive_remainder_of_preserved_inverse_coordinate {k : ℕ}
    (C : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) (d : ZMod s → ℤ)
    (hbound : ∀ h, cyclicDifference (p : ℤ) d h ≤
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) S h)
    (hcoord : (d 0 : ℚ) = inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
        (C.prefixDigits (k + 1)) j : ℚ)) 0) :
    PositiveContent (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S -
      cyclicDifference (p : ℤ) d) := by
  let colour : Digit p → ZMod s := fun t => t.1
  let u := tokenContent colour S - cyclicDifference (p : ℤ) d
  have hu (h : ZMod s) : 0 ≤ u h := sub_nonneg.mpr (hbound h)
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
  have hE : cyclicDifference (p : ℚ) (fun h => (d h : ℚ)) =
      fun h => (cyclicDifference (p : ℤ) d h : ℚ) := by
    funext h
    simp only [cyclicDifference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hInv : inverseContent (p : ℚ)
      (fun h => (cyclicDifference (p : ℤ) d h : ℚ)) = fun h => (d h : ℚ) := by
    rw [← hE, inverseContent_cyclicDifference _ hpow]
  have hI : inverseContent (p : ℚ) (fun j => (u j : ℚ)) 0 =
      inverseContent (p : ℚ) (fun j => (tokenContent colour S j : ℚ)) 0 - (d 0 : ℚ) := by
    simp only [u, Pi.sub_apply, Int.cast_sub]
    change inverseContent (p : ℚ)
      ((fun j => (tokenContent colour S j : ℚ)) -
        (fun j => (cyclicDifference (p : ℤ) d j : ℚ))) 0 = _
    rw [inverseContent_sub, hInv]
  have hlast := (positive_tokenContent_iff colour (C.parts (Fin.last (k + 1)))).mpr
    (C.nonempty (Fin.last (k + 1)))
  have hlastpos : 0 < inverseContent (p : ℚ)
      (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) 0 := by
    apply inverseContent_pos hpQ
    · intro h
      exact_mod_cast hlast.1 h
    · obtain ⟨h, hh⟩ := hlast.2
      exact ⟨h, by exact_mod_cast hh⟩
  have hCP := C.prefix_inverse_eq_total_sub_last 0
  have hpos : 0 < inverseContent (p : ℚ) (fun j => (u j : ℚ)) 0 := by
    linarith only [hI, hcoord, hCP, hlastpos]
  refine ⟨hu, ?_⟩
  by_contra hn
  push_neg at hn
  have he (h : ZMod s) : u h = 0 := le_antisymm (hn h) (hu h)
  simp only [inverseContent, cyclicWeighted, he, Int.cast_zero, mul_zero,
    sum_const, nsmul_eq_mul, mul_zero, zero_div] at hpos
  exact lt_irrefl 0 hpos

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
