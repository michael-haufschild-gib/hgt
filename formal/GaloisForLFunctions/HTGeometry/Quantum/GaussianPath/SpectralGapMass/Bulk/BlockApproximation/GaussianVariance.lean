import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.ShellSums
import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments

/-! # Limiting spectral variance per site of the frozen Gaussian chain -/
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

private theorem complete_rows_le (ω : PathPauliDisorder) (n : ℕ) :
    (∑ d : PathPauliDirections, ∑ i∈range (n+1), (ω (i,d))^2) ≤
      ∑ l : PathLabel n, (pathPauliDisorderShell ω n l)^2 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  apply add_le_add
  · change _ ≤ ∑ i : Fin (n+2), ∑ a : Fin 3, (ω (i.val,.inl a))^2
    rw [sum_comm,Fin.sum_univ_eq_sum_range (fun i => ∑ a : Fin 3, (ω (i,.inl a))^2)]
    exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _)
  · change _ ≤ ∑ i : Fin (n+1), ∑ a : Fin 3, ∑ b : Fin 3, (ω (i.val,.inr (a,b)))^2
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ a : Fin 3, ∑ b : Fin 3, (ω (i,.inr (a,b)))^2)]
    exact le_of_eq (by simp only [sum_comm (s:=range (n+1))])

/-- There are three onsite and nine bond directions. The open boundary
removes one bond row and leaves the limiting variance per site equal to twelve. -/
theorem gaussian_variance_per_site :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n : ℕ =>
      (∑ l : PathLabel n, (pathPauliDisorderShell ω n l)^2)/((n+2:ℕ):ℝ)) atTop (𝓝 12) := by
  let γ := gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => x^2) γ :=
    (memLp_id_gaussianReal' (μ:=0) (v:=1) 2 (by simp)).integrable_sq
  have h (d : PathPauliDirections) := LocalPatches.coordinate_strong_law γ d (fun x => x^2) (by fun_prop) hi
  filter_upwards [ae_all_iff.mpr h] with ω hw
  let F (m : ℕ) := ∑ d : PathPauliDirections, ∑ i∈range m, (ω (i,d))^2
  have hs : Tendsto (fun m : ℕ => F m/(m:ℝ)) atTop (𝓝 12) := by
    have hh := tendsto_finset_sum univ (fun d _ => hw d)
    simpa only [F,sum_div,γ,gaussianZero_integral_sq,NNReal.coe_one,sum_const,card_univ,
      PathPauliDirections,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,nsmul_eq_mul,mul_one] using hh
  have htop (j : ℕ) := hs.comp (tendsto_add_atTop_nat j)
  have hinv : Tendsto (fun n : ℕ => (1:ℝ)/((n+2:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
  have hlo : Tendsto (fun n : ℕ => F (n+1)/((n+2:ℕ):ℝ)) atTop (𝓝 12) := by
    have hmul := (htop 1).mul (tendsto_const_nhds.sub hinv)
    convert hmul using 1
    · funext n
      change F (n+1)/((n+2:ℕ):ℝ)=F (n+1)/((n+1:ℕ):ℝ)*(1-1/((n+2:ℕ):ℝ))
      push_cast
      field_simp
      ring
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo (htop 2)
  · exact fun n => div_le_div_of_nonneg_right (complete_rows_le ω n) (by positivity)
  · exact fun n => div_le_div_of_nonneg_right
      (LocalPatches.prefix_sum_le ω n (fun x => x^2) (fun x => sq_nonneg x)) (by positivity)

#print axioms gaussian_variance_per_site
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
