import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Sums of nonnegative coordinate observables over a finite path -/
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- Complete the missing last bond row to bound any nonnegative coordinate sum. -/
theorem prefix_sum_le (ω : PathPauliDisorder) (n : ℕ) (f : ℝ→ℝ) (hf : ∀ x, 0≤f x) :
    (∑ l, f (pathPauliDisorderShell ω n l)) ≤ ∑ d : PathPauliDirections, ∑ i∈Finset.range (n+2), f (ω (i,d)) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  apply add_le_add
  · rw [Finset.sum_comm]
    exact le_of_eq (Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun i => f (ω (i,.inl a))) (n+2))
  · change (∑ e : Fin (n+1), ∑ a : Fin 3, ∑ b : Fin 3, f (ω (e.val,.inr (a,b)))) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun e => ∑ a : Fin 3, ∑ b : Fin 3, f (ω (e,.inr (a,b))))]
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show n+1≤n+2 by omega))
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _))
    rw [Finset.sum_comm]
    exact le_of_eq (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

end
end GaloisForLFunctions.HTGeometry.LocalPatches
