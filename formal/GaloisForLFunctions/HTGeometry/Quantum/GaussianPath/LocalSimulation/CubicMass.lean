import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # An extensive cubic coefficient bound on one fixed Gaussian chain -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

private theorem prefix_sum_le (ω : PathPauliDisorder) (n : ℕ) (f : ℝ→ℝ) (hf : ∀ x, 0≤f x) :
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

/-- A deterministic multiple of the number of sites bounds the sum of
cubed absolute couplings eventually on almost every infinite draw. -/
theorem gaussian_cubic_mass : ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
    (∑ l, |pathPauliDisorderShell ω n l|^3) ≤ B*(n+2:ℕ) := by
  let γ := gaussianReal 0 1
  let f (x : ℝ) := |x|^3
  let M := ∫ x, f x ∂γ
  have hf (x) : 0≤f x := pow_nonneg (abs_nonneg _) _
  have hM : 0≤M := integral_nonneg hf
  have hi : Integrable f γ := by
    have h : MemLp id (3:ℕ) γ := memLp_id_gaussianReal' _ (by simp)
    simpa only [id_eq,Real.norm_eq_abs] using h.integrable_norm_pow'
  have hs (d : PathPauliDirections) := coordinate_strong_law γ d f (by fun_prop) hi
  refine ⟨12*(M+1),by positivity,?_⟩
  filter_upwards [ae_all_iff.mpr hs] with ω hω
  have he (d : PathPauliDirections) := (hω d).eventually_lt_const (show M<M+1 by linarith)
  filter_upwards [(tendsto_add_atTop_nat 2).eventually (Filter.eventually_all.mpr he)] with n hn
  have hp : 0<((n+2:ℕ):ℝ) := by positivity
  apply (prefix_sum_le ω n f hf).trans
  calc
    _ ≤ ∑ _d : PathPauliDirections, (M+1)*(n+2:ℕ) := Finset.sum_le_sum fun d _ => ((div_lt_iff₀ hp).mp (hn d)).le
    _ = _ := by simp [PathPauliDirections,Fintype.card_sum,Fintype.card_prod]; ring

#print axioms gaussian_cubic_mass
end
end GaloisForLFunctions.HTGeometry.LocalPatches
