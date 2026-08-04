import GaloisForLFunctions.HTGeometry.JetFieldOrderCharacterization

/-!
# Differentiation raises the jet order by exactly one

The order of an element of the free differential rational field is the least jet level at which it is
a rational function of the jets.  Differentiating raises that level by exactly one, because the
partial derivative in the fresh jet of the derivative is the partial derivative in the previous jet
of the element.

This is the mechanism behind every order bound for differential generators: a differential rational
function of an element of order `N` has order at least `N`, so no generator can be simpler than the
elements it generates.
-/

namespace GaloisForLFunctions.HTGeometry

namespace JetField

open scoped Differential

noncomputable section

variable {C : Type u} {ι : Type v} [Field C]

variable [Fintype ι] [CharZero C]

/-- Above its order, every partial derivative vanishes. -/
theorem pd_eq_zero_of_ordJet_lt (u : JetField C ι) {j : ι} {m : ℕ} (hm : ordJet u < m) :
    pd (j, m) u = 0 :=
  (mem_jetLevel_iff.1 ((ordJet_le_iff u (ordJet u)).1 le_rfl)) j m hm

/-- At its order, some partial derivative does not vanish. -/
theorem exists_pd_ne_zero_of_ordJet_ne_zero {u : JetField C ι} (hu : ordJet u ≠ 0) :
    ∃ j : ι, pd (j, ordJet u) u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hlevel : u ∈ IntermediateField.adjoin C
      ((fun p => (jet p : JetField C ι)) '' {p : ι × ℕ | p.2 ≤ ordJet u - 1}) := by
    refine mem_jetLevel_iff.2 ?_
    intro j m hm
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hm) with hlt | heq
    · exact pd_eq_zero_of_ordJet_lt u (by omega)
    · have : m = ordJet u := by omega
      rw [this]
      exact hcon j
  have hle := (ordJet_le_iff u (ordJet u - 1)).2 hlevel
  omega

/-- **Differentiation raises the jet order by at most one.** -/
theorem ordJet_deriv_le (u : JetField C ι) : ordJet (u′) ≤ ordJet u + 1 := by
  refine (ordJet_le_iff _ _).2 (mem_jetLevel_iff.2 ?_)
  intro j m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pd_deriv_succ]
  rw [pd_eq_zero_of_ordJet_lt u (by omega), pd_eq_zero_of_ordJet_lt u (by omega), map_zero,
    add_zero]

/-- **Differentiation raises the jet order by exactly one.**  The fresh partial derivative of the
derivative is the previous partial derivative of the element, which does not vanish at the order. -/
theorem ordJet_deriv_eq {u : JetField C ι} (hu : ordJet u ≠ 0) :
    ordJet (u′) = ordJet u + 1 := by
  refine le_antisymm (ordJet_deriv_le u) ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := exists_pd_ne_zero_of_ordJet_ne_zero hu
  apply hj
  have hzero : pd (j, ordJet u + 1) (u′) = 0 :=
    pd_eq_zero_of_ordJet_lt (u′) (by omega)
  rw [pd_deriv_succ, pd_eq_zero_of_ordJet_lt u (by omega), map_zero, zero_add] at hzero
  exact hzero

/-- **No differential rational function of an element is simpler than the element.**  Every jet of an
element of positive order has strictly larger order. -/
theorem ordJet_lt_ordJet_deriv {u : JetField C ι} (hu : ordJet u ≠ 0) :
    ordJet u < ordJet (u′) := by
  rw [ordJet_deriv_eq hu]
  omega

/-- **Iterated differentiation raises the jet order by exactly the number of derivatives.** -/
theorem ordJet_iterate {u : JetField C ι} (hu : ordJet u ≠ 0) (k : ℕ) :
    ordJet (differentialJet k u) = ordJet u + k := by
  induction k with
  | zero => simp
  | succ k hk =>
      have hne : ordJet (differentialJet k u) ≠ 0 := by
        rw [hk]
        omega
      rw [differentialJet_succ, ordJet_deriv_eq hne, hk]
      omega

/-- An element of positive order has jets of strictly increasing order, so no two of them coincide
and none of them is the element itself unless the count is zero. -/
theorem ordJet_iterate_strictMono {u : JetField C ι} (hu : ordJet u ≠ 0) {k l : ℕ} (hkl : k < l) :
    ordJet (differentialJet k u) < ordJet (differentialJet l u) := by
  rw [ordJet_iterate hu, ordJet_iterate hu]
  omega

end

end JetField

end GaloisForLFunctions.HTGeometry
