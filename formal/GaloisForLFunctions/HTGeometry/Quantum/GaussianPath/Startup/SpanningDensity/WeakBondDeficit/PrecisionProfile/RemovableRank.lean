import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.WeakEdgeSweep
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Sweep error from a prescribed number of removable weak bonds -/
open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
open private covers from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.WeakEdgeSweep
variable {n : ℕ}

/-- Any d removable weak bonds suffice for the upper bound, even if many
more bonds pass the same threshold. This keeps the upper speed proportional
to d when the threshold is a measured order statistic. -/
theorem rank_distance_upper (u : PathShell n) (d : ℕ) {h : ℝ}
    (hd : d≤(removable u h).card) (t : ℝ) :
    Metric.infDist (unitaryEvolution (pathHamiltonian u) t) (phaseCircuitMatrixImageAtMost (n+2) (n+1-d))≤
      |t| * (9*(d:ℝ)*h)+t^2*(84*‖u‖^2) := by
  classical
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq hd
  have hcover (v : Fin (n+2)) : ∃ e∈Sᶜ, v=e.castSucc ∨ v=e.succ := by
    obtain ⟨e,he,hv⟩ := covers u h v
    exact ⟨e,mem_compl.mpr (fun hh => (mem_compl.mp he) (hS hh)),hv⟩
  obtain ⟨z,hz,C,hC,herr⟩ := pruned_sweep u Sᶜ hcover |t| (abs_nonneg _)
  have hmass : (∑ e∈S, ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))|)≤9*(d:ℝ)*h := calc
    _ ≤ ∑ _e∈S, ∑ _ab : Fin 3×Fin 3, h := sum_le_sum fun e he =>
      sum_le_sum fun ab _ => (mem_filter.mp (mem_filter.mp (hS he)).1).2 ab
    _ = _ := by simp [hcard,nsmul_eq_mul]; ring
  have hcount : Sᶜ.card=(n+1)-d := by rw [card_compl,Fintype.card_fin,hcard]
  rw [compl_compl,sq_abs] at herr
  apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
  have hf : HasProjectiveCircuitApproximation (n+2) (|t| * (9*(d:ℝ)*h)+t^2*(84*‖u‖^2)) (n+1-d)
      (unitaryEvolution (pathHamiltonian u) |t|) :=
    ⟨z,hz,C,hC.trans_eq hcount,herr.trans (add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) le_rfl)⟩
  rcases le_total 0 t with ht|ht
  · rwa [abs_of_nonneg ht] at hf ⊢
  · let H := (⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
    simpa only [abs_of_nonpos ht,neg_neg] using hf.neg_time H

#print axioms rank_distance_upper
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
