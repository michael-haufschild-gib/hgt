import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentBounds
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.LastBlockOperations

/-!
# Placing a digit layer in the last part

For divisible total value, inverse-content feasibility has an integral margin.
Removing a layer bounded by p−1 either preserves the strict threshold or leaves
a divisible boundary composition. In both cases the removed layer can be placed
in the last part. Applying this to the highest digit block gives a last part
whose value exceeds half the total.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S T : Finset (Digit p)}

/-- Divisible total value rounds the feasibility threshold up to the number of parts. -/
theorem inverseContent_ge_length_of_total_divisible (C : DigitComposition p s (k + 1) S)
    (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    ∀ h, ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h := by
  have hd := dvd_sub hN (dvd_tokenValue_sub_weightedContent (s := s) p hp Prod.fst S)
  have hw : ((p : ℤ) ^ s - 1) ∣
      cyclicWeighted (p : ℤ) (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S) 0 := by
    simpa only [digitValue, sub_sub_cancel] using hd
  apply inverseContent_ge_succ_of_divisible p k hp _ hw
  exact (nonempty_iff_inverseContent hp k S).mp ⟨C⟩

/-- Any nonempty sublayer can be placed in the last part of a divisible digit composition. -/
theorem exists_last_contains_layer (C : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S)
    (hT : T ⊆ S) (hTne : T.Nonempty)
    (hTv : ∀ h : ZMod s, tokenContent (fun t : Digit p => (t.1 : ZMod s)) T h ≤ (p : ℤ) - 1) :
    ∃ D : DigitComposition p s (k + 2) S, T ⊆ D.parts (Fin.last (k + 1)) := by
  let colour : Digit p → ZMod s := fun t => t.1
  let u : ZMod s → ℚ := fun h => tokenContent colour S h
  let v : ZMod s → ℚ := fun h => tokenContent colour T h
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hu : ∀ h, ((k + 2 : ℕ) : ℚ) ≤ inverseContent (p : ℚ) u h :=
    C.inverseContent_ge_length_of_total_divisible hp hN
  have hv : ∀ h, v h ≤ (p : ℚ) - 1 := by
    intro h
    change (tokenContent colour T h : ℚ) ≤ (p : ℚ) - 1
    exact_mod_cast hTv h
  have hrinv (h : ZMod s) : inverseContent (p : ℚ)
      (fun j => (tokenContent colour (S \ T) j : ℚ)) h =
        inverseContent (p : ℚ) u h - inverseContent (p : ℚ) v h := by
    rw [tokenContent_sdiff colour hT]
    simp only [Pi.sub_apply, Int.cast_sub]
    exact inverseContent_sub (p : ℚ) u v h
  by_cases hfull : v = fun _ => (p : ℚ) - 1
  · have hcrit : ∀ h, (k : ℚ) < inverseContent (p : ℚ)
        (fun j => (tokenContent colour (S \ T) j : ℚ)) h := by
      intro h
      rw [hrinv, hfull, inverseContent_full_layer hpQ]
      have hh := hu h
      push_cast at hh
      linarith only [hh]
    obtain ⟨R⟩ := (nonempty_iff_inverseContent hp k (S \ T)).mpr hcrit
    have hvZ : tokenContent colour T = cyclicDifference (p : ℤ) (fun _ => 1) := by
      funext h
      have hh := congrFun hfull h
      change (tokenContent colour T h : ℚ) = (p : ℚ) - 1 at hh
      change tokenContent colour T h = (p : ℤ) * 1 - 1
      rw [mul_one]
      exact_mod_cast hh
    have hvd : ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) (tokenContent colour T) 0 := by
      rw [hvZ, cyclicWeighted_cyclicDifference]
      exact dvd_mul_right _ _
    have hTd : ((p : ℤ) ^ s - 1) ∣ digitValue p T := by
      have hh := dvd_add (dvd_tokenValue_sub_weightedContent (s := s) p hp Prod.fst T) hvd
      simpa only [digitValue, colour, sub_add_cancel] using hh
    have hRd : ((p : ℤ) ^ s - 1) ∣ digitValue p (S \ T) := by
      have he : digitValue p (S \ T) = digitValue p S - digitValue p T :=
        eq_sub_of_add_eq (tokenValue_sdiff p Prod.fst hT)
      rw [he]
      exact dvd_sub hN hTd
    let D := R.appendLast sdiff_disjoint hTne (R.all_divisible_of_total hRd) (sdiff_union_of_subset hT)
    refine ⟨D, ?_⟩
    change T ⊆ (Fin.snoc R.parts T : Fin (k + 2) → Finset (Digit p)) (Fin.last (k + 1))
    simpa only [Fin.snoc_last] using (Subset.refl T)
  · have hcrit : ∀ h, ((k + 1 : ℕ) : ℚ) < inverseContent (p : ℚ)
        (fun j => (tokenContent colour (S \ T) j : ℚ)) h := by
      intro h
      rw [hrinv]
      have hh := hu h
      have hvh := inverseContent_lt_one hpQ hv hfull h
      push_cast at hh ⊢
      linarith only [hh, hvh]
    obtain ⟨R⟩ := (nonempty_iff_inverseContent hp (k + 1) (S \ T)).mpr hcrit
    refine ⟨R.extendLast sdiff_disjoint (sdiff_union_of_subset hT), ?_⟩
    rw [R.extendLast_parts, Fin.snoc_last]
    exact subset_union_right

/-- A divisible digit collection has an admissible composition with more than half its value last. -/
theorem exists_last_gt_half (C : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    ∃ D : DigitComposition p s (k + 2) S,
      digitValue p S < 2 * D.value (Fin.last (k + 1)) := by
  have hp1 : 1 ≤ p := by omega
  have hS : S.Nonempty := (C.nonempty 0).mono (C.subset 0)
  obtain ⟨e, _, hne, htop⟩ := exists_dominant_digitBlock hp1 S hS
  have hsub : digitBlock S e ⊆ S := filter_subset _ _
  have hv (h : ZMod s) : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (digitBlock S e) h ≤ (p : ℤ) - 1 := by
    simpa only [Nat.cast_sub hp1, Nat.cast_one] using content_digitBlock_le S e h
  obtain ⟨D, hD⟩ := C.exists_last_contains_layer hp hN hsub hne hv
  have hval := tokenValue_subset p Prod.fst hD
  change digitValue p (digitBlock S e) ≤ D.value (Fin.last (k + 1)) at hval
  exact ⟨D, by linarith only [htop, hval]⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_last_gt_half
