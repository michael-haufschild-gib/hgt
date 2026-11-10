import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CommonCoordinate
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PowerSelection

/-!
# Boundary identities from a deficient deletion

Deleting one last-part digit and another digit can lower an inverse coordinate
below the number of proper parts. Each divisible prefix has an integral inverse
coordinate, bounded below by that number and above by the deficient coordinate
plus one. Thus both prefixes attain the same boundary, forcing equal last-part
cyclic weights and a strict upper bound by the two deleted digit weights.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Disjoint token collections have additive residue counts. -/
theorem tokenContent_union {s : ℕ} {α : Type*} [DecidableEq α]
    (colour : α → ZMod s) {S T : Finset α} (hd : Disjoint S T) :
    tokenContent colour (S ∪ T) = tokenContent colour S + tokenContent colour T := by
  funext h
  simp only [tokenContent, filter_union, Pi.add_apply]
  rw [card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _)), Nat.cast_add]

/-- A single digit contributes at most one to each inverse-content coordinate. -/
theorem inverseContent_singleton_le_one {s p : ℕ} [NeZero s] {α : Type*} [DecidableEq α]
    (hp : 2 ≤ p) (colour : α → ZMod s) (x : α) (h : ZMod s) :
    inverseContent (p : ℚ) (fun j => (tokenContent colour {x} j : ℚ)) h ≤ 1 := by
  apply inverseContent_le_one (by exact_mod_cast (show 1 < p by omega))
  intro j
  have hc : (({x} : Finset α).filter fun t => colour t = j).card ≤ 1 := by
    have hh := card_le_card (filter_subset (fun t => colour t = j) {x})
    simpa only [card_singleton] using hh
  have hi : tokenContent colour {x} j ≤ (p : ℤ) - 1 := by
    dsimp only [tokenContent]
    omega
  exact_mod_cast hi

namespace DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- A deficient two-digit deletion pins the divisible prefix to its integral boundary. -/
theorem prefix_inverse_eq_of_deficient_deletion (C : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) {x y : Digit p} (hx : x ∈ C.parts (Fin.last (k + 1)))
    (h : ZMod s)
    (hlt : inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h <
        ((k + 1 : ℕ) : ℚ)) :
    inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) j : ℚ)) h =
        ((k + 1 : ℕ) : ℚ) := by
  let colour : Digit p → ZMod s := fun t => t.1
  let P := C.prefixDigits (k + 1)
  let R := S \ {x, y}
  have hsub : P ⊆ R ∪ {y} := by
    intro z hz
    by_cases hzy : z = y
    · exact mem_union_right _ (mem_singleton.mpr hzy)
    · apply mem_union_left
      refine mem_sdiff.mpr ⟨C.prefix_subset _ hz, ?_⟩
      intro hzxy
      rcases mem_insert.mp hzxy with hzx | hzy'
      · subst z
        exact disjoint_left.mp C.prefix_disjoint_last hz hx
      · exact hzy (mem_singleton.mp hzy')
  have hd : Disjoint R {y} := by
    apply disjoint_left.mpr
    intro z hz hzy
    exact (mem_sdiff.mp hz).2 (mem_insert.mpr (Or.inr hzy))
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hmono := inverseContent_mono hpQ
    (fun j => (show (tokenContent colour P j : ℚ) ≤ tokenContent colour (R ∪ {y}) j by
      exact_mod_cast tokenContent_subset colour hsub j)) h
  rw [tokenContent_union colour hd, inverseContent_add_int] at hmono
  have hunit := inverseContent_singleton_le_one hp colour y h
  have hge := C.initial.inverseContent_ge_length_of_total_divisible hp C.initial_total_divisible h
  have hw : ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) (tokenContent colour P) 0 := by
    have hh := dvd_sub C.initial_total_divisible
      (dvd_tokenValue_sub_weightedContent (s := s) p hp Prod.fst P)
    simpa only [digitValue, colour, P, sub_sub_cancel] using hh
  obtain ⟨a, ha⟩ := inverseContent_integral p hp (tokenContent colour P) hw
  have halt : (a h : ℚ) < ((k + 1 : ℕ) : ℚ) + 1 := by
    have he := congrFun ha h
    change inverseContent (p : ℚ) (fun j => (tokenContent colour R j : ℚ)) h <
      ((k + 1 : ℕ) : ℚ) at hlt
    linarith only [hmono, hunit, hlt, he]
  have hai : a h < ((k + 1 : ℕ) : ℤ) + 1 := by exact_mod_cast halt
  have hle : (a h : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by
    exact_mod_cast (show a h ≤ ((k + 1 : ℕ) : ℤ) by omega)
  have he := congrFun ha h
  change inverseContent (p : ℚ) (fun j => (tokenContent colour P j : ℚ)) h =
    ((k + 1 : ℕ) : ℚ)
  change ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ)
    (fun j => (tokenContent colour P j : ℚ)) h at hge
  linarith only [hge, hle, he]

omit [NeZero s] in
/-- The inverse content of the proper prefix is total inverse content minus the last part's. -/
theorem prefix_inverse_eq_total_sub_last (C : DigitComposition p s (k + 2) S) (h : ZMod s) :
    inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) j : ℚ)) h =
    inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h -
    inverseContent (p : ℚ) (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) h := by
  rw [← C.sdiff_last_eq_prefix, tokenContent_sdiff _ (C.subset _)]
  simp only [Pi.sub_apply, Int.cast_sub]
  exact inverseContent_sub _ _ _ _

/-- At a deficient deletion coordinate, the two last parts have equal cyclic weight,
strictly below the combined weights of the deleted digits. -/
theorem weighted_last_eq_and_lt_of_deficient_deletion
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) {x y : Digit p}
    (hx : x ∈ C.parts (Fin.last (k + 1))) (hy : y ∈ D.parts (Fin.last (k + 1)))
    (hxy : x ≠ y) (h : ZMod s)
    (hlt : inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h <
        ((k + 1 : ℕ) : ℚ)) :
    cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h =
      cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) h ∧
    cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h <
      (p : ℤ) ^ ((x.1 : ZMod s) - h).val + (p : ℤ) ^ ((y.1 : ZMod s) - h).val := by
  let colour : Digit p → ZMod s := fun t => t.1
  have hC := C.prefix_inverse_eq_of_deficient_deletion hp hx h hlt
  have hpair : ({y, x} : Finset (Digit p)) = {x, y} := by
    ext z
    simp only [mem_insert, mem_singleton, or_comm]
  have hD := D.prefix_inverse_eq_of_deficient_deletion hp hy h (by rw [hpair]; exact hlt)
  rw [C.prefix_inverse_eq_total_sub_last] at hC
  rw [D.prefix_inverse_eq_total_sub_last] at hD
  have hI : inverseContent (p : ℚ) (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) h =
      inverseContent (p : ℚ) (fun j => (D.content (Fin.last (k + 1)) j : ℚ)) h := by
    linarith only [hC, hD]
  have hsub : {x, y} ⊆ S := by
    intro z hz
    rcases mem_insert.mp hz with he | he
    · exact he.symm ▸ C.subset _ hx
    · exact (mem_singleton.mp he).symm ▸ D.subset _ hy
  rw [tokenContent_sdiff colour hsub] at hlt
  simp only [Pi.sub_apply, Int.cast_sub] at hlt
  have hRinv : inverseContent (p : ℚ)
      (fun j => (tokenContent colour S j : ℚ) - (tokenContent colour {x, y} j : ℚ)) h =
      inverseContent (p : ℚ) (fun j => (tokenContent colour S j : ℚ)) h -
        inverseContent (p : ℚ) (fun j => (tokenContent colour {x, y} j : ℚ)) h :=
    inverseContent_sub _ _ _ _
  rw [hRinv] at hlt
  have hIl : inverseContent (p : ℚ) (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) h <
      inverseContent (p : ℚ) (fun j => (tokenContent colour {x, y} j : ℚ)) h := by
    change inverseContent (p : ℚ) (fun j => (tokenContent colour S j : ℚ)) h -
      inverseContent (p : ℚ) (fun j => (C.content (Fin.last (k + 1)) j : ℚ)) h =
      ((k + 1 : ℕ) : ℚ) at hC
    linarith only [hC, hlt]
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hden : (0 : ℚ) < (p : ℚ) ^ s - 1 := sub_pos.mpr (one_lt_pow₀ hpQ (NeZero.ne s))
  have hWcast (u : ZMod s → ℤ) : ((cyclicWeighted (p : ℤ) u h : ℤ) : ℚ) =
      cyclicWeighted (p : ℚ) (fun j => (u j : ℚ)) h := by
    simp only [cyclicWeighted, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have he : cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h =
      cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) h := by
    unfold inverseContent at hI
    have hh := le_antisymm ((div_le_div_iff_of_pos_right hden).mp hI.le)
      ((div_le_div_iff_of_pos_right hden).mp hI.ge)
    rw [← hWcast, ← hWcast] at hh
    exact_mod_cast hh
  have hl : cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h <
      cyclicWeighted (p : ℤ) (tokenContent colour {x, y}) h := by
    unfold inverseContent at hIl
    have hh := (div_lt_div_iff_of_pos_right hden).mp hIl
    rw [← hWcast, ← hWcast] at hh
    exact_mod_cast hh
  refine ⟨he, ?_⟩
  rw [cyclicWeighted_tokenContent_at, sum_insert (by simpa only [mem_singleton] using hxy),
    sum_singleton] at hl
  exact hl

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.prefix_inverse_eq_of_deficient_deletion
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.weighted_last_eq_and_lt_of_deficient_deletion
