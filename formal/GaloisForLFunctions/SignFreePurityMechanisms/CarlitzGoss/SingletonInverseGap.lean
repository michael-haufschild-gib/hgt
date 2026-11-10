import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeficientCoordinates

/-!
# An integral inverse-content gap at the singleton residue

A last part of cyclic weight `p^β`, supported strictly below `β`, has cyclic
weight `p^s` at `β`. A singleton in residue `β` has weight one there, so its
proper prefix exceeds the competing prefix by exactly one inverse unit.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {p s : ℕ} [NeZero s]

/-- If a last part has weight `p^β` and lies strictly before residue `β`,
its cyclic weight at `β` is exactly `p^s`. -/
theorem cyclicWeighted_at_residue_gap (hp : 2 ≤ p) (T : Finset (Digit p)) (β : ZMod s)
    (hweight : cyclicWeighted (p : ℤ) (tokenContent (fun t : Digit p => (t.1 : ZMod s)) T) 0 =
      (p : ℤ) ^ β.val)
    (hbelow : ∀ z ∈ T, (z.1 : ZMod s).val < β.val) :
    cyclicWeighted (p : ℤ) (tokenContent (fun t : Digit p => (t.1 : ZMod s)) T) β =
      (p : ℤ) ^ s := by
  have hpoint (z : Digit p) (hz : z ∈ T) :
      (p : ℤ) ^ β.val * (p : ℤ) ^ ((z.1 : ZMod s) - β).val =
        (p : ℤ) ^ s * (p : ℤ) ^ (z.1 : ZMod s).val := by
    have hlt := hbelow z hz
    have hne : β - (z.1 : ZMod s) ≠ 0 := by
      intro he
      have hv := congrArg ZMod.val (sub_eq_zero.mp he)
      omega
    have he : ((z.1 : ZMod s) - β).val = s - (β.val - (z.1 : ZMod s).val) := by
      rw [show (z.1 : ZMod s) - β = -(β - (z.1 : ZMod s)) by ring,
        ZMod.neg_val, if_neg hne, ZMod.val_sub hlt.le]
    have hβ := ZMod.val_lt β
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have he : (p : ℤ) ^ β.val *
      cyclicWeighted (p : ℤ) (tokenContent (fun t : Digit p => (t.1 : ZMod s)) T) β =
      (p : ℤ) ^ s *
        cyclicWeighted (p : ℤ) (tokenContent (fun t : Digit p => (t.1 : ZMod s)) T) 0 := by
    simp only [cyclicWeighted_tokenContent_at, sub_zero, mul_sum]
    exact sum_congr rfl hpoint
  rw [hweight, mul_comm ((p : ℤ) ^ s)] at he
  exact mul_left_cancel₀ (pow_ne_zero _ (by omega : (p : ℤ) ≠ 0)) he

namespace DigitComposition
variable {k : ℕ} {S : Finset (Digit p)}

/-- At the singleton residue, its proper prefix is one full integral
inverse-content unit above the competing proper prefix. -/
theorem prefix_inverse_gap_at_singleton
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x})
    (hweight : cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) 0 =
      (p : ℤ) ^ (x.1 : ZMod s).val)
    (hbelow : ∀ z ∈ D.parts (Fin.last (k + 1)), (z.1 : ZMod s).val < (x.1 : ZMod s).val) :
    inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) j : ℚ))
        (x.1 : ZMod s) =
      inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (D.prefixDigits (k + 1)) j : ℚ))
          (x.1 : ZMod s) + 1 := by
  let β : ZMod s := x.1
  have hD := cyclicWeighted_at_residue_gap hp (D.parts (Fin.last (k + 1))) β hweight hbelow
  change cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) β = (p : ℤ) ^ s at hD
  have hC : cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) β = 1 := by
    simp only [content, hlast, cyclicWeighted_tokenContent_at, sum_singleton, β,
      sub_self, ZMod.val_zero, pow_zero]
  have hcast (u : ZMod s → ℤ) : cyclicWeighted (p : ℚ) (fun j => (u j : ℚ)) β =
      ((cyclicWeighted (p : ℤ) u β : ℤ) : ℚ) := by
    simp only [cyclicWeighted, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hden : (p : ℚ) ^ s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s)))
  have hi : inverseContent (p : ℚ) (fun j => (D.content (Fin.last (k + 1)) j : ℚ)) β -
      inverseContent (p : ℚ) (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) β = 1 := by
    simp only [inverseContent, hcast, hC, hD, Int.cast_one, Int.cast_pow, Int.cast_natCast]
    rw [← sub_div, div_self hden]
  have hCP := C.prefix_inverse_eq_total_sub_last β
  have hDP := D.prefix_inverse_eq_total_sub_last β
  change _ = _ + 1
  linarith only [hCP, hDP, hi]

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.prefix_inverse_gap_at_singleton
