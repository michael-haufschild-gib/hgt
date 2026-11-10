import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitShifts
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CommonCoordinate

/-!
# Exponent shifts of optimal and greedy compositions

Shifting all digit exponents gives a bijection between admissible compositions
of the original and shifted collections. All part values and weights scale by
the same positive power of p, preserving optimality and reverse lexicographic
order. A suitable shift places the shared inverse-content coordinate at zero.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Multiplying all part values by p^d gives a composition of the shifted digit collection. -/
def shift (C : DigitComposition p s m S) (d : ℕ) :
    DigitComposition p s m (shiftDigits d S) where
  parts := fun i => shiftDigits d (C.parts i)
  subset := fun i => image_subset_image (C.subset i)
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hea⟩ := mem_image.mp hx
    obtain ⟨b, hb, heb⟩ := mem_image.mp hy
    have he : a = b := shiftDigit_injective d (hea.trans heb.symm)
    exact disjoint_left.mp (C.disjoint hij) ha (he.symm ▸ hb)
  cover := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨i, hi⟩ := C.cover y hy
    exact ⟨i, mem_image.mpr ⟨y, hi, rfl⟩⟩
  nonempty := fun i => (C.nonempty i).image (shiftDigit d)
  divisible := fun i hi => (dvd_digitValue_shiftDigits_iff d (C.parts i)).mpr (C.divisible i hi)

theorem shift_value (C : DigitComposition p s m S) (d : ℕ) (i : Fin m) :
    (C.shift d).value i = C.value i * (p : ℤ) ^ d := digitValue_shiftDigits d (C.parts i)

theorem shift_weight (C : DigitComposition p s m S) (d : ℕ) :
    (C.shift d).weight = C.weight * (p : ℤ) ^ d := by
  simp only [weight, shift_value, mul_assoc, sum_mul]

theorem shift_content (C : DigitComposition p s m S) (d : ℕ) (i : Fin m) (h : ZMod s) :
    (C.shift d).content i h = C.content i (h - d) :=
  tokenContent_shiftDigits d (C.parts i) h

theorem shift_inverseContent (C : DigitComposition p s m S) (d : ℕ) (i : Fin m) (h : ZMod s) :
    inverseContent (p : ℚ) (fun j => ((C.shift d).content i j : ℚ)) h =
      inverseContent (p : ℚ) (fun j => (C.content i j : ℚ)) (h - d) := by
  simp only [shift_content]
  exact inverseContent_translate (p : ℚ) (fun j => (C.content i j : ℚ)) d h

/-- A subset of a shifted collection is exactly the image of its preimage in the original set. -/
theorem shiftDigits_filter_preimage (d : ℕ) {T : Finset (Digit p)} (hT : T ⊆ shiftDigits d S) :
    shiftDigits d (S.filter fun x => shiftDigit d x ∈ T) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hy).2
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_image.mp (hT hx)
    exact mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, he.symm ▸ hx⟩, he⟩

/-- Lowering all exponents in a shifted composition reverses the shift. -/
def unshift (d : ℕ) (C : DigitComposition p s m (shiftDigits d S)) :
    DigitComposition p s m S where
  parts := fun i => S.filter fun x => shiftDigit d x ∈ C.parts i
  subset := fun i => filter_subset _ _
  disjoint := by
    intro i j hij
    exact disjoint_left.mpr fun x hx hy =>
      disjoint_left.mp (C.disjoint hij) (mem_filter.mp hx).2 (mem_filter.mp hy).2
  cover := by
    intro x hx
    obtain ⟨i, hi⟩ := C.cover (shiftDigit d x) (mem_image.mpr ⟨x, hx, rfl⟩)
    exact ⟨i, mem_filter.mpr ⟨hx, hi⟩⟩
  nonempty := by
    intro i
    obtain ⟨x, hx⟩ := C.nonempty i
    obtain ⟨y, hy, he⟩ := mem_image.mp (C.subset i hx)
    exact ⟨y, mem_filter.mpr ⟨hy, he.symm ▸ hx⟩⟩
  divisible := by
    intro i hi
    apply (dvd_digitValue_shiftDigits_iff d _).mp
    rw [shiftDigits_filter_preimage d (C.subset i)]
    exact C.divisible i hi

theorem shift_unshift (d : ℕ) (C : DigitComposition p s m (shiftDigits d S)) :
    (C.unshift d).shift d = C := by
  apply ext_parts
  funext i
  exact shiftDigits_filter_preimage d (C.subset i)

theorem unshift_shift (C : DigitComposition p s m S) (d : ℕ) :
    (C.shift d).unshift d = C := by
  apply ext_parts
  funext i
  ext x
  change x ∈ S.filter (fun t => shiftDigit d t ∈ shiftDigits d (C.parts i)) ↔ x ∈ C.parts i
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_image.mp (mem_filter.mp hx).2
    exact shiftDigit_injective d he ▸ hy
  · intro hx
    exact mem_filter.mpr ⟨C.subset i hx, mem_image.mpr ⟨x, hx, rfl⟩⟩

/-- Exponent shifts preserve weight optimality. -/
theorem isOptimal_shift_iff (C : DigitComposition p s m S) (d : ℕ) (hp : 0 < p) :
    (C.shift d).IsOptimal ↔ C.IsOptimal := by
  have hpd : (0 : ℤ) < (p : ℤ) ^ d := pow_pos (by exact_mod_cast hp) _
  constructor
  · intro hC D
    have hh := hC (D.shift d)
    rw [shift_weight, shift_weight] at hh
    nlinarith only [hh, hpd]
  · intro hC D
    have hh := mul_le_mul_of_nonneg_right (hC (D.unshift d)) hpd.le
    rw [← shift_weight, shift_unshift, ← shift_weight] at hh
    exact hh

/-- Multiplication by a positive power preserves the reversed lexicographic order. -/
theorem shift_reverseValues_lt_iff (C D : DigitComposition p s m S) (d : ℕ) (hp : 0 < p) :
    (C.shift d).reverseValues < (D.shift d).reverseValues ↔ C.reverseValues < D.reverseValues := by
  have hpd : (0 : ℤ) < (p : ℤ) ^ d := pow_pos (by exact_mod_cast hp) _
  change Pi.Lex (· < ·) (· < ·)
      (fun i : Fin m => (C.shift d).value i.rev) (fun i : Fin m => (D.shift d).value i.rev) ↔
    Pi.Lex (· < ·) (· < ·) (fun i : Fin m => C.value i.rev) (fun i : Fin m => D.value i.rev)
  simp only [shift_value]
  constructor
  · rintro ⟨j, he, hj⟩
    refine ⟨j, fun i hi => ?_, ?_⟩
    · have hh := he i hi
      nlinarith only [hh, hpd]
    · nlinarith only [hj, hpd]
  · rintro ⟨j, he, hj⟩
    exact ⟨j, fun i hi => congrArg (fun z : ℤ => z * (p : ℤ) ^ d) (he i hi),
      mul_lt_mul_of_pos_right hj hpd⟩

/-- Exponent shifts preserve greediness. -/
theorem isGreedy_shift_iff (C : DigitComposition p s m S) (d : ℕ) (hp : 0 < p) :
    (C.shift d).IsGreedy ↔ C.IsGreedy := by
  constructor
  · intro hC D
    by_contra hn
    have hh := (shift_reverseValues_lt_iff C D d hp).mpr (lt_of_not_ge hn)
    exact (not_lt_of_ge (hC (D.shift d))) hh
  · intro hC D
    by_contra hn
    have hh : (C.shift d).reverseValues < ((D.unshift d).shift d).reverseValues := by
      rw [shift_unshift]
      exact lt_of_not_ge hn
    exact (not_lt_of_ge (hC (D.unshift d))) ((shift_reverseValues_lt_iff C _ d hp).mp hh)

/-- An exponent shift places the common boundary coordinate at zero. -/
theorem exists_shift_common_inverse_zero {k : ℕ} {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) :
    ∃ d : ℕ, ∀ i : Fin (k + 1),
      inverseContent (p : ℚ) (fun j => ((C.shift d).content i.castSucc j : ℚ)) 0 = 1 := by
  obtain ⟨r, hr⟩ := exists_common_inverse_one hp hC
  have hd : ((s - r.val : ℕ) : ZMod s) = -r := by
    rw [Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt r)), ZMod.natCast_self,
      ZMod.natCast_zmod_val, zero_sub]
  refine ⟨s - r.val, fun i => ?_⟩
  rw [shift_inverseContent, hd, sub_neg_eq_add, zero_add]
  exact hr i

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.isOptimal_shift_iff
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.isGreedy_shift_iff
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_shift_common_inverse_zero
