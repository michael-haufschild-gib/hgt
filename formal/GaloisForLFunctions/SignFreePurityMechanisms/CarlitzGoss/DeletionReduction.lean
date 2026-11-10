import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.LastResidueMaximum
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixBoundary

/-!
# Deletion reductions for nongreedy optima

A common last-part digit can be deleted from both compositions. If it exhausts
either last part, feasibility forces both last parts to be that singleton,
so deleting the whole part reduces their length. Increasing allocation aligns
equal-power labels whenever the last parts share a residue class.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S T : Finset (Digit p)}

/-- Transport a composition along equality of its digit collections. -/
def castDigits (C : DigitComposition p s m S) (h : S = T) : DigitComposition p s m T := h ▸ C

theorem castDigits_value (C : DigitComposition p s m S) (h : S = T) :
    (C.castDigits h).value = C.value := by cases h; rfl

theorem isOptimal_castDigits_iff (C : DigitComposition p s m S) (h : S = T) :
    (C.castDigits h).IsOptimal ↔ C.IsOptimal := by cases h; rfl

theorem isGreedy_castDigits_iff (C : DigitComposition p s m S) (h : S = T) :
    (C.castDigits h).IsGreedy ↔ C.IsGreedy := by cases h; rfl

variable [NeZero s]

/-- A common last-part token in a nongreedy optimum produces a smaller counterexample. -/
theorem exists_smaller_of_common_last_token {k : ℕ}
    {C D : DigitComposition p s (k + 2) S} (hp : 2 ≤ p)
    (hC : C.IsOptimal) (hD : D.IsGreedy) (hne : C.value ≠ D.value)
    {x : Digit p} (hxC : x ∈ C.parts (Fin.last (k + 1)))
    (hxD : x ∈ D.parts (Fin.last (k + 1))) :
    ∃ (n : ℕ) (T : Finset (Digit p)) (O G : DigitComposition p s n T),
      (n < k + 2 ∨ (n = k + 2 ∧ T.card < S.card)) ∧
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value := by
  have hTC : {x} ⊆ C.parts (Fin.last (k + 1)) := singleton_subset_iff.mpr hxC
  have hTD : {x} ⊆ D.parts (Fin.last (k + 1)) := singleton_subset_iff.mpr hxD
  by_cases hremC : (C.parts (Fin.last (k + 1)) \ {x}).Nonempty
  · have hremD : (D.parts (Fin.last (k + 1)) \ {x}).Nonempty :=
      (nonempty_sdiff_iff_last_nonempty hp (Or.inr hD) hTD).mp ⟨C.removeLast hTC hremC⟩
    have hcard : (S \ {x}).card < S.card := by
      have he : S \ {x} = S.erase x := by
        ext y
        simp only [mem_sdiff, mem_singleton, mem_erase, and_comm]
      rw [he]
      exact card_erase_lt_of_mem (C.subset _ hxC)
    refine ⟨k + 2, S \ {x}, C.removeLast hTC hremC, D.removeLast hTD hremD,
      Or.inr ⟨rfl, hcard⟩, hC.removeLast hTC hremC, hD.removeLast hTD hremD, ?_⟩
    exact fun hv => hne ((removeLast_values_eq_iff C D hTC hTD hremC hremD).mp hv)
  · have hremD : ¬ (D.parts (Fin.last (k + 1)) \ {x}).Nonempty := by
      intro hd
      exact hremC ((nonempty_sdiff_iff_last_nonempty hp (Or.inl hC) hTC).mp
        ⟨D.removeLast hTD hd⟩)
    have hCL : C.parts (Fin.last (k + 1)) = {x} := by
      apply Subset.antisymm ?_ hTC
      intro y hy
      by_contra hn
      exact hremC ⟨y, mem_sdiff.mpr ⟨hy, hn⟩⟩
    have hDL : D.parts (Fin.last (k + 1)) = {x} := by
      apply Subset.antisymm ?_ hTD
      intro y hy
      by_contra hn
      exact hremD ⟨y, mem_sdiff.mpr ⟨hy, hn⟩⟩
    have hPC : C.prefixDigits (k + 1) = S \ {x} := by rw [← C.sdiff_last_eq_prefix, hCL]
    have hPD : D.prefixDigits (k + 1) = S \ {x} := by rw [← D.sdiff_last_eq_prefix, hDL]
    let C0 := C.initial.castDigits hPC
    let D0 := D.initial.castDigits hPD
    refine ⟨k + 1, S \ {x}, C0, D0, Or.inl (by omega),
      (isOptimal_castDigits_iff C.initial hPC).mpr hC.initial,
      (isGreedy_castDigits_iff D.initial hPD).mpr hD.initial, ?_⟩
    intro hv
    have hv0 : C.initial.value = D.initial.value := by
      simpa only [C0, D0, castDigits_value] using hv
    have hlast : C.value (Fin.last (k + 1)) = D.value (Fin.last (k + 1)) := by
      change digitValue p (C.parts (Fin.last (k + 1))) = digitValue p (D.parts (Fin.last (k + 1)))
      rw [hCL, hDL]
    apply hne
    rw [C.values_eq_snoc_initial, D.values_eq_snoc_initial, hv0, hlast]

/-- A shared last-part residue in a nongreedy optimum produces fewer parts or fewer digits. -/
theorem exists_smaller_of_common_last_residue {k : ℕ}
    {C D : DigitComposition p s (k + 2) S} (hp : 2 ≤ p)
    (hC : C.IsOptimal) (hD : D.IsGreedy) (hne : C.value ≠ D.value) (h : ZMod s)
    (hresC : ((C.parts (Fin.last (k + 1))).filter fun x => (x.1 : ZMod s) = h).Nonempty)
    (hresD : ((D.parts (Fin.last (k + 1))).filter fun x => (x.1 : ZMod s) = h).Nonempty) :
    ∃ (n : ℕ) (T : Finset (Digit p)) (O G : DigitComposition p s n T),
      (n < k + 2 ∨ (n = k + 2 ∧ T.card < S.card)) ∧
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value := by
  obtain ⟨x, hx, hxh, hmaxC⟩ := (hC.tauMonotone hp).exists_last_max hresC
  obtain ⟨y, hy, hyh, hmaxD⟩ := (hD.tauMonotone hp).exists_last_max hresD
  have he : x.1 = y.1 := le_antisymm (hmaxD x (C.subset _ hx) hxh) (hmaxC y (D.subset _ hy) hyh)
  obtain ⟨E, hEv, hxE⟩ := D.exists_same_values_last_mem hp (C.subset _ hx) hy he
  have hE : E.IsGreedy := (isGreedy_congr_values hEv).mpr hD
  have hneE : C.value ≠ E.value := fun hv => hne (hv.trans hEv)
  exact exists_smaller_of_common_last_token hp hC hE hneE hx hxE

omit [NeZero s] in
/-- Disjoint last-part residue supports force the greedy last part to contain a larger power. -/
theorem IsGreedy.last_exponent_gt_of_disjoint_residues
    {C D : DigitComposition p s (m + 1) S} (hD : D.IsGreedy) (hp : 2 ≤ p)
    {y : Digit p} (hy : y ∈ D.parts (Fin.last m))
    (hmax : ∀ z ∈ D.parts (Fin.last m), z.1 ≤ y.1)
    (hsep : ∀ x ∈ C.parts (Fin.last m), ∀ z ∈ D.parts (Fin.last m),
      (x.1 : ZMod s) ≠ (z.1 : ZMod s)) :
    ∀ x ∈ C.parts (Fin.last m), x.1 < y.1 := by
  intro x hx
  by_contra hn
  have hxy : x.1 ≠ y.1 := fun he => hsep x hx y hy (congrArg (fun n : ℕ => (n : ZMod s)) he)
  have hyx : y.1 < x.1 := by omega
  have hsmall := digitValue_lt_pow (by omega : 1 ≤ p) (D.parts (Fin.last m))
    (fun z hz => (hmax z hz).trans_lt hyx)
  have hlarge := tokenValue_subset p Prod.fst (singleton_subset_iff.mpr hx)
  simp only [tokenValue, sum_singleton] at hlarge
  have hvalue := hD.last_max C
  change C.value (Fin.last m) ≤ D.value (Fin.last m) at hvalue
  change D.value (Fin.last m) < (p : ℤ) ^ x.1 at hsmall
  change (p : ℤ) ^ x.1 ≤ C.value (Fin.last m) at hlarge
  linarith only [hsmall, hlarge, hvalue]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_smaller_of_common_last_residue
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.last_exponent_gt_of_disjoint_residues
