import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.BondSets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrunedSweep
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # A physical circuit omitting disjoint weak bonds -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

private theorem covers (u : PathShell n) (h : ℝ) (v : Fin (n+2)) :
    ∃ e∈(removable u h)ᶜ, v=e.castSucc ∨ v=e.succ := by
  have hkeep (e : Fin (n+1)) (he : e.val%2=0 ∨ e.val=n) : e∈(removable u h)ᶜ := by
    apply mem_compl.mpr
    intro hi
    obtain ⟨ho,hl⟩ := (mem_filter.mp hi).2
    omega
  by_cases hv : v.val=n+1
  · exact ⟨Fin.last n,hkeep _ (Or.inr rfl),Or.inr (Fin.ext hv)⟩
  by_cases hp : v.val%2=0
  · let e : Fin (n+1) := ⟨v.val,by have := v.isLt; omega⟩
    exact ⟨e,hkeep e (Or.inl hp),Or.inl (Fin.ext rfl)⟩
  · let e : Fin (n+1) := ⟨v.val-1,by have := v.isLt; omega⟩
    exact ⟨e,hkeep e (Or.inl (by change (v.val-1)%2=0; omega)),Or.inr (Fin.ext (by change v.val=v.val-1+1; omega))⟩

/-- Every removable weak edge saves one gate for a cost of at most
9|t|h in operator error, in addition to the single sweep error. -/
theorem affordable_after_pruning (u : PathShell n) (h t : ℝ) :
    let R := removable u h
    HasProjectiveCircuitApproximation (n+2) (9 * |t| * h*R.card+t^2*(84*‖u‖^2))
      ((n+1)-R.card) (unitaryEvolution (pathHamiltonian u) t) := by
  intro R
  obtain ⟨z,hz,C,hC,he⟩ := pruned_sweep u Rᶜ (covers u h) |t| (abs_nonneg _)
  have hmass : (∑ e∈R, ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))|) ≤ R.card*(9*h) := by
    calc
      _ ≤ ∑ _e∈R, ∑ _ab : Fin 3×Fin 3, h := by
        apply sum_le_sum
        intro e hR
        exact sum_le_sum fun ab _ => (mem_filter.mp (mem_filter.mp hR).1).2 ab
      _ = _ := by simp [nsmul_eq_mul]
  have hcount : Rᶜ.card=(n+1)-R.card := by simp only [card_compl,Fintype.card_fin]
  have hfit : HasProjectiveCircuitApproximation (n+2) (9 * |t| * h*R.card+t^2*(84*‖u‖^2))
      ((n+1)-R.card) (unitaryEvolution (pathHamiltonian u) |t|) := by
    refine ⟨z,hz,C,hC.trans_eq hcount,?_⟩
    rw [compl_compl,sq_abs] at he
    apply he.trans
    apply add_le_add _ le_rfl
    exact (mul_le_mul_of_nonneg_left hmass (abs_nonneg t)).trans_eq (by ring)
  rcases le_total 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using hfit
  · let H := (⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
    simpa only [abs_of_nonpos ht,neg_neg] using hfit.neg_time H

#print axioms affordable_after_pruning
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
