import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeficientCoordinates
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ResidueBlockObstruction

/-!
# Cyclic order at a deficient coordinate

If the deleted last-part digit preceded a larger available digit in cyclic
order, the two-digit weight bound would place every last-part residue at or before
that larger digit. Equal last-part weights would then supply a congruent
exchange block, contradicting optimality.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- A deficient deletion coordinate puts the larger available digit strictly before
the deleted last-part digit in cyclic residue order. -/
theorem IsOptimal.rotated_exponent_lt_of_deficient_deletion
    {C D : DigitComposition p s (k + 2) S} (hC : C.IsOptimal) (hp : 2 ≤ p) {x y : Digit p}
    (hx : x ∈ C.parts (Fin.last (k + 1))) (hy : y ∈ D.parts (Fin.last (k + 1)))
    (hbelow : ∀ z ∈ C.parts (Fin.last (k + 1)), z.1 < y.1) (h : ZMod s)
    (hlt : inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h <
        ((k + 1 : ℕ) : ℚ)) :
    ((y.1 : ZMod s) - h).val < ((x.1 : ZMod s) - h).val := by
  have hxy : x ≠ y := by
    intro he
    have hh := hbelow x hx
    rw [he] at hh
    exact lt_irrefl _ hh
  obtain ⟨heq, hsumlt⟩ := C.weighted_last_eq_and_lt_of_deficient_deletion D hp hx hy hxy h hlt
  let w : Digit p → ℤ := fun z => (p : ℤ) ^ ((z.1 : ZMod s) - h).val
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hw (z : Digit p) : 0 ≤ w z := pow_nonneg (by omega) _
  have hsum : cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h =
      ∑ z ∈ C.parts (Fin.last (k + 1)), w z := cyclicWeighted_tokenContent_at p _ _ h
  change cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h < w x + w y at hsumlt
  by_contra hn
  have hle : ((x.1 : ZMod s) - h).val ≤ ((y.1 : ZMod s) - h).val := le_of_not_gt hn
  have hrot : ∀ z ∈ C.parts (Fin.last (k + 1)),
      ((z.1 : ZMod s) - h).val ≤ ((y.1 : ZMod s) - h).val := by
    intro z hz
    by_cases hzx : z = x
    · simpa only [hzx] using hle
    · have htwo : w x + w z ≤ cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h := by
        rw [hsum]
        have hsub : {x, z} ⊆ C.parts (Fin.last (k + 1)) := by
          intro t ht
          rcases mem_insert.mp ht with he | he
          · exact he.symm ▸ hx
          · exact (mem_singleton.mp he).symm ▸ hz
        have hh := sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hw t)
        rw [sum_insert (by simpa only [mem_singleton] using Ne.symm hzx), sum_singleton] at hh
        exact hh
      have hwlt : w z < w y := by linarith only [htwo, hsumlt]
      by_contra hng
      have he : ((y.1 : ZMod s) - h).val ≤ ((z.1 : ZMod s) - h).val := by omega
      have hh : w y ≤ w z := pow_le_pow_right₀ hpZ he
      exact (not_lt_of_ge hh) hwlt
  obtain ⟨i, hyi⟩ := C.cover y (D.subset _ hy)
  have hi : i < Fin.last (k + 1) := by
    by_contra hn
    have he : i = Fin.last (k + 1) := Fin.ext (by
      have hh := i.isLt
      change ¬ i.val < k + 1 at hn
      simp only [Fin.val_last]
      omega)
    rw [he] at hyi
    exact lt_irrefl _ (hbelow y hyi)
  have hl := hC.weighted_content_lt_of_smaller_powers hp hi hyi h hbelow hrot
  have hg : w y ≤ cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) h := by
    simp only [content, cyclicWeighted_tokenContent_at]
    exact single_le_sum (fun z _ => hw z) hy
  change cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h < w y at hl
  rw [← heq] at hg
  exact (not_lt_of_ge hg) hl

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.rotated_exponent_lt_of_deficient_deletion
