import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IntegralPrefixContents
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.SingletonBoundary
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.SingletonInverseGap

/-!
# Selecting the carry interval from actual compositions

The singleton residue lies one inverse-content unit above the competing
prefix. The last preceding coordinate at the minimum determines a nonempty
carry interval. Its lower boundary also contains the competing last support.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Normalized singleton and competing last parts determine a carry interval
with a minimal lower boundary and strictly larger interior inverse coordinates. -/
theorem exists_singleton_carry_boundary
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x y : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x})
    (hnorm : ∀ i : Fin (k + 1),
      inverseContent (p : ℚ) (fun j => (C.content i.castSucc j : ℚ)) 0 = 1)
    (hy : y ∈ D.parts (Fin.last (k + 1))) (hyx : y ≠ x)
    (hweight : cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) 0 =
      (p : ℤ) ^ (x.1 : ZMod s).val)
    (hbelow : ∀ z ∈ D.parts (Fin.last (k + 1)), (z.1 : ZMod s).val < (x.1 : ZMod s).val) :
    ∃ α : ZMod s, α.val < (x.1 : ZMod s).val ∧
      inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
          (C.prefixDigits (k + 1)) j : ℚ)) α = ((k + 1 : ℕ) : ℚ) ∧
      (∀ h : ZMod s, α.val < h.val → h.val ≤ (x.1 : ZMod s).val →
        ((k + 1 : ℕ) : ℚ) + 1 ≤ inverseContent (p : ℚ)
          (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s))
            (C.prefixDigits (k + 1)) j : ℚ)) h) ∧
      (∀ z ∈ D.parts (Fin.last (k + 1)), α.val ≤ (z.1 : ZMod s).val) := by
  let colour : Digit p → ZMod s := fun t => t.1
  let u := tokenContent colour (C.prefixDigits (k + 1))
  have hdiv : ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0 := by
    have hh := dvd_sub C.initial_total_divisible
      (dvd_tokenValue_sub_weightedContent (s := s) p hp Prod.fst (C.prefixDigits (k + 1)))
    simpa only [digitValue, u, colour, sub_sub_cancel] using hh
  obtain ⟨a, ha⟩ := inverseContent_integral p hp u hdiv
  have hzero : inverseContent (p : ℚ) (fun j => (u j : ℚ)) 0 = ((k + 1 : ℕ) : ℚ) := by
    rw [C.initial.inverseContent_sum_parts]
    change (∑ i : Fin (k + 1), inverseContent (p : ℚ)
      (fun j => (C.content i.castSucc j : ℚ)) 0) = ((k + 1 : ℕ) : ℚ)
    simp only [hnorm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hlower (h : ZMod s) : ((k + 1 : ℕ) : ℚ) ≤
      inverseContent (p : ℚ) (fun j => (u j : ℚ)) h :=
    C.initial.inverseContent_ge_length_of_total_divisible hp C.initial_total_divisible h
  have htop : ((k + 1 : ℕ) : ℚ) + 1 ≤
      inverseContent (p : ℚ) (fun j => (u j : ℚ)) (x.1 : ZMod s) := by
    have he := C.prefix_inverse_gap_at_singleton D hp hlast hweight hbelow
    have hg := D.initial.inverseContent_ge_length_of_total_divisible hp D.initial_total_divisible
      (x.1 : ZMod s)
    change _ ≤ inverseContent (p : ℚ) (fun j => (u j : ℚ)) (x.1 : ZMod s)
    linarith only [he, hg]
  let v : ℕ → ℤ := fun h => a (h : ZMod s)
  have hv0 : v 0 = ((k + 1 : ℕ) : ℤ) := by
    rw [ha] at hzero
    dsimp only at hzero
    simpa only [v, Nat.cast_zero] using (show a 0 = ((k + 1 : ℕ) : ℤ) by exact_mod_cast hzero)
  have hvlo (h : ℕ) (_hh : h ≤ (x.1 : ZMod s).val) : ((k + 1 : ℕ) : ℤ) ≤ v h := by
    have hl := hlower (h : ZMod s)
    rw [ha] at hl
    dsimp only at hl
    exact_mod_cast hl
  have hvtop : ((k + 1 : ℕ) : ℤ) + 1 ≤ v (x.1 : ZMod s).val := by
    rw [ha] at htop
    dsimp only at htop
    have hi : ((k + 1 : ℕ) : ℤ) + 1 ≤ a (x.1 : ZMod s) := by exact_mod_cast htop
    simpa only [v, ZMod.natCast_zmod_val] using hi
  obtain ⟨α, hαβ, hαeq, hstrict⟩ := exists_last_inverse_boundary v hv0 hvlo hvtop
  have hαs : α < s := hαβ.trans (ZMod.val_lt (x.1 : ZMod s))
  have hval : (α : ZMod s).val = α := ZMod.val_natCast_of_lt hαs
  have hP : inverseContent (p : ℚ) (fun j => (u j : ℚ)) (α : ZMod s) =
      ((k + 1 : ℕ) : ℚ) := by
    rw [ha]
    change (v α : ℚ) = _
    exact_mod_cast hαeq
  refine ⟨(α : ZMod s), by rw [hval]; exact hαβ, hP, ?_, ?_⟩
  · intro h hαh hhβ
    rw [hval] at hαh
    have hh := hstrict h.val hαh hhβ
    simp only [v, ZMod.natCast_zmod_val] at hh
    rw [ha]
    dsimp only
    exact_mod_cast hh
  · exact C.last_residue_ge_of_singleton_boundary D hp hlast (α : ZMod s) hP hy hyx
      (by rw [hval]; exact hαβ.le)

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_singleton_carry_boundary
