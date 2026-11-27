import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.Layer

/-! # Finite mutual classes and well-founded strict forcing -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Set

theorem accumulated_self {t : ℝ} (ht : 0<t) : t ∈ accumulated t :=
  ⟨ht,1,zero_lt_one,fun _ _ h => h⟩

/-- Multiplying the witnessing scales puts two implications at the same scale. -/
theorem accumulated_trans {t u v : ℝ} (a : u ∈ accumulated t) (b : v ∈ accumulated u) :
    v ∈ accumulated t := by
  obtain ⟨_,m,hm,f⟩ := a
  obtain ⟨hv,n,hn,g⟩ := b
  have i : Forces (t*↑(m*n)) (u*↑(m*n)) := by
    simpa only [Nat.cast_mul,mul_assoc] using forces_dilate f n
  have j : Forces (u*↑(m*n)) (v*↑(m*n)) := by
    rw [Nat.mul_comm]
    simpa only [Nat.cast_mul,mul_assoc] using forces_dilate g m
  exact ⟨hv,m*n,mul_pos hm hn,fun N a hit => j N a (i N a hit)⟩

theorem resonant_of_accumulated {t u : ℝ} (ht : 0<t) (res : Resonant t) (hit : u ∈ accumulated t) :
    Resonant u := by
  obtain ⟨pu,m,hm,force⟩ := hit
  have pos : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have st := mul_pos ht pos
  have ut := mul_pos pu pos
  apply (resonant_nat_iff pu hm).mp
  apply (contains_resonant ut).mp
  exact ⟨_,least_spectrum st ((resonant_nat_iff ht hm).mpr res),ut,force⟩

/-- Normalized readings which force each other. -/
def mutualOrders (t : ℝ) := {u ∈ accumulated t | t ∈ accumulated u}

theorem finite_mutual {t : ℝ} (ht : 0<t) (res : Resonant t) : (mutualOrders t).Finite := by
  apply (finite_sameLength ht res).subset
  rintro u ⟨f,g⟩
  exact ⟨f,le_antisymm (shortest_monotone ht res f)
    (shortest_monotone f.1 (resonant_of_accumulated ht res f) g)⟩

abbrev ResonantOrder := {t : ℝ // 0<t ∧ Resonant t}

def strictConsequence (u t : ResonantOrder) :=
  u.val ∈ accumulated t.val ∧ t.val ∉ accumulated u.val

private def grade (t : ResonantOrder) := (shortest t.val,(sameLength t.val).ncard)

private theorem grade_drops {u t : ResonantOrder} (h : strictConsequence u t) :
    Prod.Lex (·<·) (·<·) (grade u) (grade t) := by
  have le := shortest_monotone t.property.1 t.property.2 h.1
  rcases lt_or_eq_of_le le with lt | eq
  · exact Prod.Lex.left _ _ lt
  · have sub : sameLength u.val ⊂ sameLength t.val := by
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨fun v hit => ⟨accumulated_trans h.1 hit.1,hit.2.trans eq⟩,?_⟩
      intro same
      have own : t.val ∈ sameLength t.val := ⟨accumulated_self t.property.1,rfl⟩
      rw [← same] at own
      exact h.2 own.1
    unfold grade
    rw [eq]
    exact Prod.Lex.right _ (Set.ncard_lt_ncard sub (finite_sameLength t.property.1 t.property.2))

theorem strict_wellFounded : WellFounded strictConsequence :=
  Subrelation.wf (fun {_ _} h => grade_drops h)
    (InvImage.wf grade (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)

/-- Every infinite sequence of successive forced readings eventually stays
in one finite mutual class. -/
theorem eventually_mutual (f : ℕ → ResonantOrder)
    (step : ∀ n, (f (n+1)).val ∈ accumulated (f n).val) :
    ∃ N, (mutualOrders (f N).val).Finite ∧ ∀ k, (f (N+k)).val ∈ mutualOrders (f N).val := by
  classical
  obtain ⟨x,⟨N,rfl⟩,minimal⟩ := strict_wellFounded.has_min (Set.range f) ⟨f 0,0,rfl⟩
  have reach (k : ℕ) : (f (N+k)).val ∈ accumulated (f N).val := by
    induction k with
    | zero => exact accumulated_self (f N).property.1
    | succ k ih => exact accumulated_trans ih (step (N+k))
  refine ⟨N,finite_mutual (f N).property.1 (f N).property.2,fun k => ⟨reach k,?_⟩⟩
  by_contra missing
  exact minimal _ ⟨N+k,rfl⟩ ⟨reach k,missing⟩

#print axioms accumulated_trans
#print axioms resonant_of_accumulated
#print axioms finite_mutual
#print axioms strict_wellFounded
#print axioms eventually_mutual

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
