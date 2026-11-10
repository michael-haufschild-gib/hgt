import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IncreasingPrefixCosts
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CarryModifiedComposition
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GeometricCarryGain
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixWeightIdentity

/-!
# Weight gain of the singleton carry modification

The terminal losses put larger available digits in the last part and separate
retained terminal exponents from its maximum. Increasing-prefix cost bounds
and the exact prefix-weight identity then quantify the carry modification.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

private theorem drop_lt_of_positive_total {a b t : ℤ} (hb : 0 < b) (ht : 0 < t)
    (hdrop : a ≤ max 0 (t - b)) : a < t :=
  hdrop.trans_lt (max_lt ht (by omega))

private theorem gap_of_positive_retained_count {a b t : ℤ} (ha : 0 < a)
    (hdrop : a ≤ max 0 (t - b)) : a + b ≤ t := by
  by_cases hle : t - b ≤ 0
  · rw [max_eq_left hle] at hdrop
    omega
  · rw [max_eq_right (by omega : 0 ≤ t - b)] at hdrop
    omega

namespace DigitComposition
variable {p s k : ℕ} {S : Finset (Digit p)}

/-- Outside the singleton's residue, the proper prefix contains all available digits. -/
private theorem singleton_prefix_content_eq_total
    (C : DigitComposition p s (k + 2) S) {x : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (h : ZMod s)
    (hne : (x.1 : ZMod s) ≠ h) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h =
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) S h := by
  let colour : Digit p → ZMod s := fun t => t.1
  have hf : ({x} : Finset (Digit p)).filter (fun t => colour t = h) = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨hz, hcol⟩ := mem_filter.mp hz
    have he := mem_singleton.mp hz
    subst z
    exact hne hcol
  have hz : tokenContent colour {x} h = 0 := by
    simp only [tokenContent, hf, card_empty, Nat.cast_zero]
  have hu := congrFun (tokenContent_union colour C.prefix_disjoint_last) h
  rw [C.prefix_union_last, hlast] at hu
  simpa only [Pi.add_apply, hz, add_zero] using hu.symm

/-- A positive retained residue turns the terminal drop into a full cardinality gap. -/
private theorem terminal_drop_card_gap (C Z : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x})
    (h : ZMod s) (hne : (x.1 : ZMod s) ≠ h)
    (hdrop : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
      max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
        ((p : ℤ) - 1)))
    (hretained : (Z.residuePrefixDigits (k + 1) h).Nonempty) :
    (Z.residuePrefixDigits (k + 1) h).card + (p - 1) ≤
      (S.filter fun t => (t.1 : ZMod s) = h).card := by
  rw [C.singleton_prefix_content_eq_total hlast h hne] at hdrop
  have hpos : (0 : ℤ) < (Z.residuePrefixDigits (k + 1) h).card := by
    exact_mod_cast card_pos.mpr hretained
  change ((Z.residuePrefixDigits (k + 1) h).card : ℤ) ≤
    max 0 (((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) - ((p : ℤ) - 1)) at hdrop
  have hg := gap_of_positive_retained_count hpos hdrop
  have hc : (((Z.residuePrefixDigits (k + 1) h).card + (p - 1) : ℕ) : ℤ) ≤
      ((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    exact hg
  exact_mod_cast hc

/-- Every occupied affected residue leaves a digit in the new last part. -/
private theorem terminal_drop_leaves_last (C Z : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x})
    (h : ZMod s) (hne : (x.1 : ZMod s) ≠ h)
    (hdrop : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
      max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
        ((p : ℤ) - 1)))
    (havailable : (S.filter fun t => (t.1 : ZMod s) = h).Nonempty) :
    ((Z.parts (Fin.last (k + 1))).filter fun t => (t.1 : ZMod s) = h).Nonempty := by
  rw [C.singleton_prefix_content_eq_total hlast h hne] at hdrop
  have hpos : (0 : ℤ) < (S.filter fun t => (t.1 : ZMod s) = h).card := by
    exact_mod_cast card_pos.mpr havailable
  change ((Z.residuePrefixDigits (k + 1) h).card : ℤ) ≤
    max 0 (((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) - ((p : ℤ) - 1)) at hdrop
  have hlt := drop_lt_of_positive_total (by omega : (0 : ℤ) < p - 1) hpos hdrop
  apply Z.last_residue_nonempty_of_prefix_card_lt h
  exact_mod_cast hlt

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
