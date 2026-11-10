import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.BoundaryFeasibility
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PowerSelection
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.BlockExchanges
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits

/-!
# A residue-weight obstruction to optimality

Equality of weighted digit contents in any cyclic row implies congruence of
their values modulo p^s−1. If a later part consists of smaller powers than an
earlier digit, and its rotated residue weights are bounded by that digit's
weight, its weighted total must stay strictly below that weight. Otherwise
exact power selection supplies a congruent block whose exchange improves
the composition's weight.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- Equal weighted residue contents in any cyclic row imply equal integer values modulo p^s−1. -/
theorem dvd_tokenValue_sub_of_weighted_eq {α : Type*} (p : ℕ) (hp : 2 ≤ p)
    (exponent : α → ℕ) (S T : Finset α) (h : ZMod s)
    (he : cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) S) h =
      cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) T) h) :
    ((p : ℤ) ^ s - 1) ∣ tokenValue p exponent S - tokenValue p exponent T := by
  let u := tokenContent (fun x => (exponent x : ZMod s)) S -
    tokenContent (fun x => (exponent x : ZMod s)) T
  have hsub (j : ZMod s) : cyclicWeighted (p : ℤ) u j =
      cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) S) j -
        cyclicWeighted (p : ℤ) (tokenContent (fun x => (exponent x : ZMod s)) T) j := by
    simp only [u, cyclicWeighted, Pi.sub_apply, mul_sub, sum_sub_distrib]
  have hnum : cyclicWeighted (p : ℤ) u h = 0 := by rw [hsub, he, sub_self]
  have hcast : ((cyclicWeighted (p : ℤ) u h : ℤ) : ℚ) =
      cyclicWeighted (p : ℚ) (fun j => (u j : ℚ)) h := by
    simp only [cyclicWeighted, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hr : inverseContent (p : ℚ) (fun j => (u j : ℚ)) h = (0 : ℤ) := by
    rw [inverseContent, ← hcast, hnum]
    simp only [Int.cast_zero, zero_div]
  have hzero := weighted_dvd_of_inverseContent_integral_at p hp u h ⟨0, hr⟩
  rw [hsub] at hzero
  have hS := dvd_tokenValue_sub_weightedContent (s := s) p hp exponent S
  have hT := dvd_tokenValue_sub_weightedContent (s := s) p hp exponent T
  have hadd := dvd_add (dvd_sub hS hT) hzero
  have hcancel (a b c d : ℤ) : (a - b - (c - d)) + (b - d) = a - c := by ring
  simpa only [hcancel] using hadd

namespace DigitComposition
variable {p m : ℕ} {S : Finset (Digit p)}

/-- A later part made of smaller powers cannot contain enough smaller cyclic weights
to replace an earlier larger digit by a congruent block. -/
theorem IsOptimal.weighted_content_lt_of_smaller_powers {C : DigitComposition p s m S}
    (hC : C.IsOptimal) (hp : 2 ≤ p) {i j : Fin m} (hij : i < j)
    {x : Digit p} (hx : x ∈ C.parts i) (h : ZMod s)
    (hbelow : ∀ y ∈ C.parts j, y.1 < x.1)
    (hrot : ∀ y ∈ C.parts j, ((y.1 : ZMod s) - h).val ≤ ((x.1 : ZMod s) - h).val) :
    cyclicWeighted (p : ℤ) (C.content j) h < (p : ℤ) ^ ((x.1 : ZMod s) - h).val := by
  by_contra hn
  have hge := le_of_not_gt hn
  obtain ⟨W, hW, heW⟩ := exists_subset_cyclicWeighted_eq_pow p
    (fun y : Digit p => (y.1 : ZMod s)) (C.parts j) h ((x.1 : ZMod s) - h).val hrot hge
  have hWne : W.Nonempty := by
    by_contra hnW
    have hWe : W = ∅ := not_nonempty_iff_eq_empty.mp hnW
    have hpos : (0 : ℤ) < (p : ℤ) ^ ((x.1 : ZMod s) - h).val :=
      pow_pos (by exact_mod_cast (show 0 < p by omega)) _
    simp only [hWe, tokenContent, filter_empty, card_empty, Nat.cast_zero,
      cyclicWeighted, mul_zero, sum_const_zero] at heW
    linarith only [heW, hpos]
  have heX : cyclicWeighted (p : ℤ)
      (tokenContent (fun y : Digit p => (y.1 : ZMod s)) {x}) h =
        (p : ℤ) ^ ((x.1 : ZMod s) - h).val := by
    rw [cyclicWeighted_tokenContent_at]
    exact sum_singleton _ _
  have hres : ((p : ℤ) ^ s - 1) ∣ digitValue p {x} - digitValue p W :=
    dvd_tokenValue_sub_of_weighted_eq p hp Prod.fst {x} W h (heX.trans heW.symm)
  have hopt := hC.block_value_le hij (singleton_subset_iff.mpr hx) hW (singleton_nonempty x) hWne hres
  have hsmall := digitValue_lt_pow (by omega : 1 ≤ p) W (fun y hy => hbelow y (hW hy))
  simp only [digitValue, tokenValue, sum_singleton] at hopt
  change (p : ℤ) ^ x.1 ≤ digitValue p W at hopt
  linarith only [hopt, hsmall]

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.weighted_content_lt_of_smaller_powers
