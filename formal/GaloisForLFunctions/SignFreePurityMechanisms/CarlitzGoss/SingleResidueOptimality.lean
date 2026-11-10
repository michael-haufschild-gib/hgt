import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CommonCoordinate

/-!
# Unique greedy optimality when q=p

With one residue class, the common inverse coordinate forces exactly p−1 digit
occurrences in each proper part. Thus every optimal or greedy composition has
the same content matrix. Increasing allocation gives equality of numerical
part values, proving that greediness and weight optimality coincide and that
the maximizing numerical composition is unique.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p m k : ℕ} {S : Finset (Digit p)}

/-- With one residue class, every proper part of an optimum has exactly p−1 digits. -/
theorem content_castSucc_eq_sub_one {C : DigitComposition p 1 (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) (i : Fin (k + 1)) (j : ZMod 1) :
    C.content i.castSucc j = (p : ℤ) - 1 := by
  obtain ⟨h, hh⟩ := exists_common_inverse_one hp hC
  have hi : inverseContent (p : ℚ) (fun t => (C.content i.castSucc t : ℚ)) = fun _ => 1 := by
    funext t
    rw [Subsingleton.elim t h]
    exact hh i
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have he := congrFun (cyclicDifference_inverseContent (s := 1) (p : ℚ)
    (by simpa only [pow_one] using ne_of_gt hpQ)
    (fun t => (C.content i.castSucc t : ℚ))) j
  rw [hi] at he
  simp only [cyclicDifference, mul_one] at he
  exact_mod_cast he.symm

/-- For one residue class, all optimal and greedy compositions have the same content matrix. -/
theorem content_eq_of_single_residue {C D : DigitComposition p 1 (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) (hD : D.IsOptimal ∨ D.IsGreedy) :
    C.content = D.content := by
  have hi (i : Fin (k + 1)) (h : ZMod 1) : C.content i.castSucc h = D.content i.castSucc h := by
    rw [content_castSucc_eq_sub_one hp hC, content_castSucc_eq_sub_one hp hD]
  funext i h
  refine Fin.lastCases ?_ (fun j => hi j h) i
  have hCsum := C.content_sum_parts h
  have hDsum := D.content_sum_parts h
  rw [Fin.sum_univ_castSucc] at hCsum hDsum
  have hs : (∑ j : Fin (k + 1), C.content j.castSucc h) =
      ∑ j : Fin (k + 1), D.content j.castSucc h := sum_congr rfl fun j _ => hi j h
  linarith only [hCsum, hDsum, hs]

/-- In one residue class, optimal and greedy numerical compositions coincide. -/
theorem values_eq_of_single_residue {C D : DigitComposition p 1 m S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) (hD : D.IsOptimal ∨ D.IsGreedy) :
    C.value = D.value := by
  cases m with
  | zero => exact funext fun i => Fin.elim0 i
  | succ m =>
    cases m with
    | zero =>
      have hc := C.sum_values
      have hd := D.sum_values
      have hc0 : C.value 0 = digitValue p S := (Fin.sum_univ_one C.value).symm.trans hc
      have hd0 : D.value 0 = digitValue p S := (Fin.sum_univ_one D.value).symm.trans hd
      funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      rw [hi]
      exact hc0.trans hd0.symm
    | succ k =>
      have hc : C.TauMonotone := hC.elim (fun h => h.tauMonotone hp) (fun h => h.tauMonotone hp)
      have hd : D.TauMonotone := hD.elim (fun h => h.tauMonotone hp) (fun h => h.tauMonotone hp)
      exact hc.values_eq hp hd (content_eq_of_single_residue hp hC hD)

/-- Greedy compositions are precisely the weight maxima when q=p. -/
theorem isOptimal_iff_isGreedy_single_residue (C : DigitComposition p 1 m S) (hp : 2 ≤ p) :
    C.IsOptimal ↔ C.IsGreedy := by
  constructor
  · intro hC
    obtain ⟨G, hG⟩ := exists_greedy ⟨C⟩
    have hv := values_eq_of_single_residue hp (Or.inl hC) (Or.inr hG)
    have hr : C.reverseValues = G.reverseValues := by unfold reverseValues; rw [hv]
    intro D
    rw [hr]
    exact hG D
  · intro hC
    obtain ⟨O, hO⟩ := exists_optimal ⟨C⟩
    have hv := values_eq_of_single_residue hp (Or.inr hC) (Or.inl hO)
    have hw : C.weight = O.weight := by unfold weight; rw [hv]
    intro D
    rw [hw]
    exact hO D

/-- The maximizing numerical composition is unique for q=p. -/
theorem IsOptimal.values_eq_single_residue {C D : DigitComposition p 1 m S}
    (hp : 2 ≤ p) (hC : C.IsOptimal) (hD : D.IsOptimal) : C.value = D.value :=
  values_eq_of_single_residue hp (Or.inl hC) (Or.inl hD)

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.isOptimal_iff_isGreedy_single_residue
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.values_eq_single_residue
