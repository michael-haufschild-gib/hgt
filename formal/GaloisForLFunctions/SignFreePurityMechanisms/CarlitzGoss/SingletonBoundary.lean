import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeficientCoordinates

/-!
# Residue support determined by a singleton boundary

A proper prefix on the integral feasibility boundary fixes the cyclic weight
of a competing last part. Before the singleton residue, this weight excludes
all residue representatives below that boundary coordinate.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- At every boundary coordinate of a singleton-last composition, another
last part containing a different digit has the singleton's cyclic weight. -/
theorem weighted_last_eq_of_singleton_boundary
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x y : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (h : ZMod s)
    (hP : inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
        (C.prefixDigits (k + 1)) j : ℚ)) h = ((k + 1 : ℕ) : ℚ))
    (hy : y ∈ D.parts (Fin.last (k + 1))) (hyx : y ≠ x) :
    cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) h =
      (p : ℤ) ^ ((x.1 : ZMod s) - h).val := by
  let colour : Digit p → ZMod s := fun t => t.1
  have hyP : y ∈ C.prefixDigits (k + 1) := by
    rw [← C.sdiff_last_eq_prefix, hlast]
    exact mem_sdiff.mpr ⟨D.subset _ hy, fun he => hyx (mem_singleton.mp he)⟩
  have hR : S \ {x, y} = C.prefixDigits (k + 1) \ {y} := by
    rw [← C.sdiff_last_eq_prefix, hlast]
    ext z
    simp only [mem_sdiff, mem_insert, mem_singleton]
    tauto
  have hunit : 0 < inverseContent (p : ℚ) (fun j => (tokenContent colour {y} j : ℚ)) h := by
    have ht := (positive_tokenContent_iff colour {y}).mpr (singleton_nonempty y)
    apply inverseContent_pos (by exact_mod_cast (show 1 < p by omega))
    · intro j
      exact_mod_cast ht.1 j
    · obtain ⟨j, hj⟩ := ht.2
      exact ⟨j, by exact_mod_cast hj⟩
  have hdef : inverseContent (p : ℚ)
      (fun j => (tokenContent colour (S \ {x, y}) j : ℚ)) h < ((k + 1 : ℕ) : ℚ) := by
    rw [hR, tokenContent_sdiff colour (singleton_subset_iff.mpr hyP)]
    simp only [Pi.sub_apply, Int.cast_sub]
    change inverseContent (p : ℚ)
      ((fun j => (tokenContent colour (C.prefixDigits (k + 1)) j : ℚ)) -
        (fun j => (tokenContent colour {y} j : ℚ))) h < _
    rw [inverseContent_sub, hP]
    linarith only [hunit]
  have hx : x ∈ C.parts (Fin.last (k + 1)) := by rw [hlast]; exact mem_singleton_self x
  have he := (C.weighted_last_eq_and_lt_of_deficient_deletion D hp hx hy hyx.symm h hdef).1
  rw [← he]
  change cyclicWeighted (p : ℤ) (tokenContent colour (C.parts (Fin.last (k + 1)))) h = _
  rw [hlast, cyclicWeighted_tokenContent_at, sum_singleton]

/-- A boundary before the singleton residue excludes every smaller residue
from a competing last part. -/
theorem last_residue_ge_of_singleton_boundary
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x y : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (h : ZMod s)
    (hP : inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
        (C.prefixDigits (k + 1)) j : ℚ)) h = ((k + 1 : ℕ) : ℚ))
    (hy : y ∈ D.parts (Fin.last (k + 1))) (hyx : y ≠ x)
    (hhx : h.val ≤ (x.1 : ZMod s).val) :
    ∀ z ∈ D.parts (Fin.last (k + 1)), h.val ≤ (z.1 : ZMod s).val := by
  have he := C.weighted_last_eq_of_singleton_boundary D hp hlast h hP hy hyx
  intro z hz
  have hle : (p : ℤ) ^ ((z.1 : ZMod s) - h).val ≤
      (p : ℤ) ^ ((x.1 : ZMod s) - h).val := by
    rw [← he]
    simp only [content, cyclicWeighted_tokenContent_at]
    exact single_le_sum (fun t _ => pow_nonneg (by omega : (0 : ℤ) ≤ p) _) hz
  have hpZ : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
  have hexp := (pow_le_pow_iff_right₀ hpZ).mp hle
  by_contra hn
  have hzlt : (z.1 : ZMod s).val < h.val := by omega
  have hne : h - (z.1 : ZMod s) ≠ 0 := by
    intro heq
    have hv := congrArg ZMod.val (sub_eq_zero.mp heq)
    omega
  have hez : ((z.1 : ZMod s) - h).val = s - (h.val - (z.1 : ZMod s).val) := by
    rw [show (z.1 : ZMod s) - h = -(h - (z.1 : ZMod s)) by ring,
      ZMod.neg_val, if_neg hne, ZMod.val_sub hzlt.le]
  rw [hez, ZMod.val_sub hhx] at hexp
  have hxlt := ZMod.val_lt (x.1 : ZMod s)
  have hhlt := ZMod.val_lt h
  omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.last_residue_ge_of_singleton_boundary
