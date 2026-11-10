import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ResiduePrefixCost
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.LastResidueMaximum

/-!
# Geometric costs of increasing residue prefixes

Increasing allocation turns residue-count gaps into exponent gaps. Applied
to successive proper prefixes, these give the double-geometric cost bound.
Applied to the final complement, they separate retained digits from the
largest last-part digit by one full residue degree.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

theorem digitValue_nonneg (p : ℕ) (A : Finset (Digit p)) : 0 ≤ digitValue p A :=
  sum_nonneg fun x _ => pow_nonneg (Nat.cast_nonneg p) x.1

private theorem sum_reflect_proper_prefixes (f : ℕ → ℤ) (k : ℕ) :
    (∑ n ∈ Icc 1 k, f (k + 1 - n)) = ∑ n ∈ Icc 1 k, f n := by
  apply sum_bij (fun n _ => k + 1 - n)
  · intro n hn
    have hb := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn j hj he
    have hn' := mem_Icc.mp hn
    have hj' := mem_Icc.mp hj
    omega
  · intro j hj
    have hb := mem_Icc.mp hj
    refine ⟨k + 1 - j, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · exact fun _ _ => rfl

namespace DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- Digits of one residue allocated to an initial segment of parts. -/
def residuePrefixDigits (C : DigitComposition p s m S) (j : ℕ) (h : ZMod s) : Finset (Digit p) :=
  (C.prefixDigits j).filter fun x => (x.1 : ZMod s) = h

theorem residuePrefixDigits_subset (C : DigitComposition p s m S) (j : ℕ) (h : ZMod s) :
    C.residuePrefixDigits j h ⊆ S.filter (fun x => (x.1 : ZMod s) = h) := by
  intro x hx
  exact mem_filter.mpr ⟨C.prefix_subset j (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

theorem residuePrefixDigits_mono (C : DigitComposition p s m S) {i j : ℕ} (hij : i ≤ j)
    (h : ZMod s) : C.residuePrefixDigits i h ⊆ C.residuePrefixDigits j h := by
  intro x hx
  obtain ⟨hx, hcol⟩ := mem_filter.mp hx
  obtain ⟨t, ht, hxt⟩ := (C.mem_prefix i x).mp hx
  exact mem_filter.mpr ⟨(C.mem_prefix j x).mpr ⟨t, by omega, hxt⟩, hcol⟩

theorem residuePrefixDigits_mod (C : DigitComposition p s m S) (j : ℕ) (h : ZMod s)
    {x : Digit p} (hx : x ∈ C.residuePrefixDigits j h) : x.1 % s = h.val := by
  have he := congrArg ZMod.val (mem_filter.mp hx).2
  simpa only [ZMod.val_natCast] using he

/-- A strict terminal-prefix deficit leaves an actual last-part digit in that residue. -/
theorem last_residue_nonempty_of_prefix_card_lt {k : ℕ}
    (C : DigitComposition p s (k + 2) S) (h : ZMod s)
    (hcard : (C.residuePrefixDigits (k + 1) h).card <
      (S.filter fun x => (x.1 : ZMod s) = h).card) :
    ((C.parts (Fin.last (k + 1))).filter fun x => (x.1 : ZMod s) = h).Nonempty := by
  let A := C.residuePrefixDigits (k + 1) h
  let B := S.filter fun z => (z.1 : ZMod s) = h
  have hAB : A ⊆ B := C.residuePrefixDigits_subset (k + 1) h
  have hrem : (B \ A).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset hAB]
    change A.card < B.card at hcard
    omega
  obtain ⟨y, hy⟩ := hrem
  obtain ⟨hyS, hycol⟩ := mem_filter.mp (mem_sdiff.mp hy).1
  have hyUnion : y ∈ C.prefixDigits (k + 1) ∪ C.parts (Fin.last (k + 1)) := by
    rw [C.prefix_union_last]
    exact hyS
  have hyLast : y ∈ C.parts (Fin.last (k + 1)) := (mem_union.mp hyUnion).resolve_left
    (fun hyp => (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨hyp, hycol⟩))
  exact ⟨y, mem_filter.mpr ⟨hyLast, hycol⟩⟩

/-- Two increasing allocations with equal residue-prefix counts have equal
residue-prefix values. -/
theorem TauMonotone.residue_prefix_value_eq {C D : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hD : D.TauMonotone) (j : ℕ) (h : ZMod s)
    (hc : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h =
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (D.prefixDigits j) h) :
    digitValue p (C.residuePrefixDigits j h) = digitValue p (D.residuePrefixDigits j h) := by
  have hcard : (C.residuePrefixDigits j h).card = (D.residuePrefixDigits j h).card := by
    change ((C.residuePrefixDigits j h).card : ℤ) = ((D.residuePrefixDigits j h).card : ℤ) at hc
    exact_mod_cast hc
  have hp1 : (1 : ℤ) ≤ p := by omega
  change (∑ x ∈ C.residuePrefixDigits j h, (p : ℤ) ^ x.1) =
    ∑ x ∈ D.residuePrefixDigits j h, (p : ℤ) ^ x.1
  apply le_antisymm
  · apply smallest_subset_sum_le (S := S.filter fun t => (t.1 : ZMod s) = h)
      (fun t : Digit p => (p : ℤ) ^ t.1) (D.residuePrefixDigits_subset j h) hcard
    intro a ha b hb
    exact pow_le_pow_right₀ hp1 (hC.prefix_smallest j h ha hb)
  · apply smallest_subset_sum_le (S := S.filter fun t => (t.1 : ZMod s) = h)
      (fun t : Digit p => (p : ℤ) ^ t.1) (C.residuePrefixDigits_subset j h) hcard.symm
    intro a ha b hb
    exact pow_le_pow_right₀ hp1 (hD.prefix_smallest j h ha hb)

variable [NeZero s]

/-- Every prefix value is the sum of its residue-prefix values. -/
theorem value_prefix_eq_sum_residue (C : DigitComposition p s m S) (j : ℕ) :
    digitValue p (C.prefixDigits j) = ∑ h : ZMod s, digitValue p (C.residuePrefixDigits j h) := by
  change (∑ x ∈ C.prefixDigits j, (p : ℤ) ^ x.1) =
    ∑ h : ZMod s, ∑ x ∈ (C.prefixDigits j).filter (fun t => (t.1 : ZMod s) = h), (p : ℤ) ^ x.1
  rw [sum_fiberwise]

/-- Positive residue-prefix count gaps give the geometric bound for the sum
of all earlier proper-prefix values in that residue. -/
theorem TauMonotone.residue_prefix_cost_le {k : ℕ} {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.TauMonotone) (h : ZMod s) (E : ℕ)
    (hE : E % s = h.val) (hmax : ∀ x ∈ C.residuePrefixDigits (k + 1) h, x.1 ≤ E)
    (hgap : ∀ j < k + 1,
      0 < tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h →
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h + ((p : ℤ) - 1) ≤
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (j + 1)) h) :
    ((p : ℤ) ^ s - 1) ^ 2 * (∑ j ∈ Icc 1 k, digitValue p (C.residuePrefixDigits j h)) ≤
      ((p : ℤ) - 1) * (p : ℤ) ^ s * (p : ℤ) ^ E := by
  let A := fun j => C.residuePrefixDigits j h
  have hgapCard (j : ℕ) (hj : j < k + 1) (hne : (A j).Nonempty) :
      (A j).card + (p - 1) ≤ (A (j + 1)).card := by
    have hpos : 0 < tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h := by
      change (0 : ℤ) < (A j).card
      exact_mod_cast card_pos.mpr hne
    have hg := hgap j hj hpos
    change ((A j).card : ℤ) + ((p : ℤ) - 1) ≤ ((A (j + 1)).card : ℤ) at hg
    have hc : (((A j).card + (p - 1) : ℕ) : ℤ) ≤ ((A (j + 1)).card : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      exact hg
    exact_mod_cast hc
  have hcard (n : ℕ) (hn : n ∈ Icc 1 k) (hne : (A (k + 1 - n)).Nonempty) :
      (A (k + 1 - n)).card + n * (p - 1) ≤ (A (k + 1)).card := by
    have hb := mem_Icc.mp hn
    have he : k + 1 - n + n = k + 1 := by omega
    have hc := card_gap_of_positive_prefixes_upto A (p - 1) (k + 1) hgapCard hne n (by omega)
    rw [he] at hc
    exact hc
  have hcost := residue_prefix_weight_le_of_card_gap hp (NeZero.pos s) k E
    (fun n => A (k + 1 - n)) (A (k + 1))
    (fun x hx => C.residuePrefixDigits_mod (k + 1) h hx) hE hmax
    (fun n _ => C.residuePrefixDigits_mono (Nat.sub_le _ _) h)
    (fun n _ x hx y hy => hC.prefix_smallest (k + 1 - n) h hx
      (mem_sdiff.mpr ⟨C.residuePrefixDigits_subset (k + 1) h (mem_sdiff.mp hy).1,
        (mem_sdiff.mp hy).2⟩)) hcard
  rw [sum_reflect_proper_prefixes (fun j => digitValue p (A j)) k] at hcost
  exact hcost

omit [NeZero s] in
/-- Losing `p−1` digits in a residue puts every retained terminal digit a
full residue degree below the largest digit of the last part. -/
theorem TauMonotone.retained_exponent_gap {k E : ℕ} {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.TauMonotone) (h : ZMod s)
    (hmax : ∀ z ∈ C.parts (Fin.last (k + 1)), z.1 ≤ E)
    (hcard : (C.residuePrefixDigits (k + 1) h).card + (p - 1) ≤
      (S.filter fun x => (x.1 : ZMod s) = h).card)
    {x : Digit p} (hx : x ∈ C.residuePrefixDigits (k + 1) h) : x.1 + s ≤ E := by
  let A := C.residuePrefixDigits (k + 1) h
  let B := S.filter fun z => (z.1 : ZMod s) = h
  have hAB : A ⊆ B := C.residuePrefixDigits_subset (k + 1) h
  have hlt : A.card < B.card := by
    change A.card + (p - 1) ≤ B.card at hcard
    omega
  obtain ⟨z, hz, hzcol, hzmax⟩ := hC.exists_last_max
    (C.last_residue_nonempty_of_prefix_card_lt h hlt)
  have hres (t : Digit p) (ht : t ∈ B) : t.1 % s = h.val := by
    have he := congrArg ZMod.val (mem_filter.mp ht).2
    simpa only [ZMod.val_natCast] using he
  have hzres : z.1 % s = h.val := by
    have he := congrArg ZMod.val hzcol
    simpa only [ZMod.val_natCast] using he
  have hgap := exponent_gap_of_prefix_card_gap (n := 1) hAB hres hzres
    (fun t ht => hzmax t (mem_filter.mp ht).1 (mem_filter.mp ht).2)
    (fun t ht u hu => hC.prefix_smallest (k + 1) h ht hu)
    (by simpa only [one_mul] using hcard) hx
  simpa only [one_mul] using hgap.trans (hmax z hz)

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.TauMonotone.residue_prefix_cost_le
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.TauMonotone.retained_exponent_gap
