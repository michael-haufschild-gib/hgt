import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.SingleResidueOptimality
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ShiftCompositions
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TwoDigitFeasibility

/-!
# Minimal nongreedy optima

Well-ordering first minimizes the number of parts, then the number of digits.
Exponent shifts normalize the common inverse-content coordinate. Deletion
then forces disjoint last-part residues and a deficient inverse coordinate
whenever a last-part digit and a larger available digit are removed.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s : ℕ} [NeZero s]

/-- A disagreement between a weight maximum and a greedy composition needs at least three parts
and at least two residue classes. -/
theorem counterexample_size_bounds {m : ℕ} {S : Finset (Digit p)}
    {O G : DigitComposition p s m S} (hp : 2 ≤ p)
    (hO : O.IsOptimal) (hG : G.IsGreedy) (hne : O.value ≠ G.value) : 3 ≤ m ∧ 2 ≤ s := by
  have hm : 3 ≤ m := by
    cases m with
    | zero => exact (hne (funext fun i => Fin.elim0 i)).elim
    | succ m =>
      cases m with
      | zero =>
        apply (hne ?_).elim
        have ho : O.value 0 = digitValue p S := (Fin.sum_univ_one O.value).symm.trans O.sum_values
        have hg : G.value 0 = digitValue p S := (Fin.sum_univ_one G.value).symm.trans G.sum_values
        funext i
        have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
        rw [hi]
        exact ho.trans hg.symm
      | succ m =>
        cases m with
        | zero => exact (hne (((isOptimal_two_iff_isGreedy O).mp hO).values_eq hG)).elim
        | succ m => omega
  refine ⟨hm, ?_⟩
  by_contra hs
  have hs0 := NeZero.pos s
  have he : s = 1 := by omega
  subst s
  exact hne (values_eq_of_single_residue hp (Or.inl hO) (Or.inr hG))

omit [NeZero s] in
/-- Any counterexample admits a least number of parts, and then a least number of digits. -/
theorem exists_minimal_counterexample
    (hbad : ∃ (m : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s m S),
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value) :
    ∃ (m : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s m S),
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value ∧
      ∀ n (T : Finset (Digit p)) (A B : DigitComposition p s n T),
        A.IsOptimal → B.IsGreedy → A.value ≠ B.value →
        m ≤ n ∧ (n = m → S.card ≤ T.card) := by
  classical
  let P (m : ℕ) := ∃ (S : Finset (Digit p)) (O G : DigitComposition p s m S),
    O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value
  have hP : ∃ m, P m := hbad
  let m := Nat.find hP
  obtain ⟨S, O, G, hO, hG, hne⟩ := Nat.find_spec hP
  let Q (n : ℕ) := ∃ (T : Finset (Digit p)), T.card = n ∧
    ∃ A B : DigitComposition p s m T, A.IsOptimal ∧ B.IsGreedy ∧ A.value ≠ B.value
  have hQ : ∃ n, Q n := ⟨S.card, S, rfl, O, G, hO, hG, hne⟩
  obtain ⟨T, hT, A, B, hA, hB, hAB⟩ := Nat.find_spec hQ
  refine ⟨m, T, A, B, hA, hB, hAB, ?_⟩
  intro n U A' B' hA' hB' hAB'
  have hmn : m ≤ n := Nat.find_min' hP ⟨U, A', B', hA', hB', hAB'⟩
  refine ⟨hmn, ?_⟩
  intro hn
  subst n
  have hh : Nat.find hQ ≤ U.card := Nat.find_min' hQ ⟨U, rfl, A', B', hA', hB', hAB'⟩
  rw [hT]
  exact hh

/-- A minimal counterexample can be shifted so all proper parts have inverse coordinate zero equal to one. -/
theorem exists_normalized_minimal_counterexample (hp : 2 ≤ p)
    (hbad : ∃ (m : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s m S),
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value) :
    ∃ (k : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s (k + 2) S),
      1 ≤ k ∧ 2 ≤ s ∧ O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value ∧
      (∀ i : Fin (k + 1), inverseContent (p : ℚ) (fun j => (O.content i.castSucc j : ℚ)) 0 = 1) ∧
      ∀ n (T : Finset (Digit p)) (A B : DigitComposition p s n T),
        A.IsOptimal → B.IsGreedy → A.value ≠ B.value →
        k + 2 ≤ n ∧ (n = k + 2 → S.card ≤ T.card) := by
  obtain ⟨m, S, O, G, hO, hG, hne, hmin⟩ := exists_minimal_counterexample hbad
  obtain ⟨hm, hs⟩ := counterexample_size_bounds hp hO hG hne
  obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  subst m
  obtain ⟨d, hd⟩ := exists_shift_common_inverse_zero hp (Or.inl hO)
  let O' := O.shift d
  have hp0 : 0 < p := by omega
  have hO' : O'.IsOptimal := (O.isOptimal_shift_iff d hp0).mpr hO
  have hOn : ¬ O'.IsGreedy := by
    intro hg
    exact hne (((O.isGreedy_shift_iff d hp0).mp hg).values_eq hG)
  obtain ⟨G', hG'⟩ := exists_greedy ⟨O'⟩
  have hne' : O'.value ≠ G'.value := fun hv => hOn ((isGreedy_congr_values hv).mpr hG')
  refine ⟨k, shiftDigits d S, O', G', by omega, hs, hO', hG', hne', hd, ?_⟩
  intro n T A B hA hB hAB
  have hh := hmin n T A B hA hB hAB
  refine ⟨hh.1, fun hn => ?_⟩
  rw [card_shiftDigits]
  exact hh.2 hn

/-- Minimality forbids a shared residue class in the two last parts. -/
theorem last_residue_disjoint_of_minimal {k : ℕ} {S : Finset (Digit p)}
    {O G : DigitComposition p s (k + 2) S} (hp : 2 ≤ p)
    (hO : O.IsOptimal) (hG : G.IsGreedy) (hne : O.value ≠ G.value)
    (hmin : ∀ n (T : Finset (Digit p)) (A B : DigitComposition p s n T),
      A.IsOptimal → B.IsGreedy → A.value ≠ B.value →
      k + 2 ≤ n ∧ (n = k + 2 → S.card ≤ T.card)) :
    ∀ h : ZMod s, ¬ (((O.parts (Fin.last (k + 1))).filter fun x => (x.1 : ZMod s) = h).Nonempty ∧
      ((G.parts (Fin.last (k + 1))).filter fun x => (x.1 : ZMod s) = h).Nonempty) := by
  intro h hh
  obtain ⟨n, T, A, B, hsize, hA, hB, hAB⟩ :=
    exists_smaller_of_common_last_residue hp hO hG hne h hh.1 hh.2
  have hm := hmin n T A B hA hB hAB
  rcases hsize with hlt | ⟨he, hcard⟩
  · omega
  · have hc := hm.2 he
    omega

/-- In a minimal counterexample, deleting a last-part digit and a larger available digit
crosses below the non-strict feasibility threshold in some coordinate. -/
theorem exists_deficient_coordinate_of_minimal {k : ℕ} {S : Finset (Digit p)}
    {O : DigitComposition p s (k + 2) S} (hp : 2 ≤ p) (hO : O.IsOptimal)
    (hmin : ∀ n (T : Finset (Digit p)) (A B : DigitComposition p s n T),
      A.IsOptimal → B.IsGreedy → A.value ≠ B.value →
      k + 2 ≤ n ∧ (n = k + 2 → S.card ≤ T.card))
    {x y : Digit p} (hx : x ∈ O.parts (Fin.last (k + 1))) (hy : y ∈ S)
    (hbelow : ∀ z ∈ O.parts (Fin.last (k + 1)), z.1 < y.1) :
    ∃ h : ZMod s, inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h <
        ((k + 1 : ℕ) : ℚ) := by
  by_contra hn
  push Not at hn
  obtain ⟨A, B, hcard, hA, hB, hAB⟩ := exists_smaller_of_two_digit_threshold hp hO hx hy hbelow hn
  have hh := (hmin (k + 2) (S \ {x}) A B hA hB hAB).2 rfl
  omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_normalized_minimal_counterexample
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.last_residue_disjoint_of_minimal
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_deficient_coordinate_of_minimal
