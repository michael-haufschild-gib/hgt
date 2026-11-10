import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeficientCoordinates

/-!
# The normalized last-part weight

When every proper part has zeroth inverse coordinate one and the last part is
a singleton, deleting that singleton and any other available digit makes the
zeroth coordinate deficient. The boundary identity therefore fixes the zeroth
cyclic weight of any competing last part containing the other digit.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- A normalized singleton last part and any competing last part containing another digit
have the same zeroth cyclic weight. -/
theorem weighted_last_eq_of_singleton_normalized
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x y : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x})
    (hnorm : ∀ i : Fin (k + 1),
      inverseContent (p : ℚ) (fun j => (C.content i.castSucc j : ℚ)) 0 = 1)
    (hy : y ∈ D.parts (Fin.last (k + 1))) (hyx : y ≠ x) :
    cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) 0 = (p : ℤ) ^ (x.1 : ZMod s).val := by
  let colour : Digit p → ZMod s := fun t => t.1
  have hP : inverseContent (p : ℚ)
      (fun j => (tokenContent colour (C.prefixDigits (k + 1)) j : ℚ)) 0 =
        ((k + 1 : ℕ) : ℚ) := by
    rw [C.initial.inverseContent_sum_parts]
    change (∑ i : Fin (k + 1), inverseContent (p : ℚ)
      (fun j => (C.content i.castSucc j : ℚ)) 0) = ((k + 1 : ℕ) : ℚ)
    simp only [hnorm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hyP : y ∈ C.prefixDigits (k + 1) := by
    rw [← C.sdiff_last_eq_prefix, hlast]
    exact mem_sdiff.mpr ⟨D.subset _ hy, fun he => hyx (mem_singleton.mp he)⟩
  have hR : S \ {x, y} = C.prefixDigits (k + 1) \ {y} := by
    rw [← C.sdiff_last_eq_prefix, hlast]
    ext z
    simp only [mem_sdiff, mem_insert, mem_singleton]
    tauto
  have hunit : 0 < inverseContent (p : ℚ) (fun j => (tokenContent colour {y} j : ℚ)) 0 := by
    have ht := (positive_tokenContent_iff colour {y}).mpr (singleton_nonempty y)
    apply inverseContent_pos (by exact_mod_cast (show 1 < p by omega))
    · intro j
      exact_mod_cast ht.1 j
    · obtain ⟨j, hj⟩ := ht.2
      exact ⟨j, by exact_mod_cast hj⟩
  have hdef : inverseContent (p : ℚ)
      (fun j => (tokenContent colour (S \ {x, y}) j : ℚ)) 0 < ((k + 1 : ℕ) : ℚ) := by
    rw [hR, tokenContent_sdiff colour (singleton_subset_iff.mpr hyP)]
    simp only [Pi.sub_apply, Int.cast_sub]
    have hRinv : inverseContent (p : ℚ)
        (fun j => (tokenContent colour (C.prefixDigits (k + 1)) j : ℚ) -
          (tokenContent colour {y} j : ℚ)) 0 =
        inverseContent (p : ℚ) (fun j => (tokenContent colour (C.prefixDigits (k + 1)) j : ℚ)) 0 -
          inverseContent (p : ℚ) (fun j => (tokenContent colour {y} j : ℚ)) 0 :=
      inverseContent_sub _ _ _ _
    rw [hRinv, hP]
    linarith only [hunit]
  have hx : x ∈ C.parts (Fin.last (k + 1)) := by rw [hlast]; exact mem_singleton_self x
  have he := (C.weighted_last_eq_and_lt_of_deficient_deletion D hp hx hy hyx.symm 0 hdef).1
  rw [← he]
  change cyclicWeighted (p : ℤ) (tokenContent colour (C.parts (Fin.last (k + 1)))) 0 = _
  rw [hlast, cyclicWeighted_tokenContent_at, sum_singleton, sub_zero]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.weighted_last_eq_of_singleton_normalized
