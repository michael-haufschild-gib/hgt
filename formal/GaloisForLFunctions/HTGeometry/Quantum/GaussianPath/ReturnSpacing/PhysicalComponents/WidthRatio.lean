import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.ShellSums
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CoordinateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock

/-! # Longitudinal field mass controls the energy diameter -/
open Filter MeasureTheory ProbabilityTheory Matrix Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Each of the twelve coefficient directions has the same limiting
absolute mass per site. Consequently twice the full mass is eventually
at most twenty-five times the mass of the longitudinal fields. -/
theorem gaussian_width_field_ratio : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
    let u := pathPauliDisorderShell ω n
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
    circuitHamiltonianSpectralWidth H ≤ 25 * ∑ i : Fin (n+2), |u (.inl (i,2))| := by
  let γ := gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => |x|) γ := by
    have h : MemLp id 1 γ := memLp_id_gaussianReal' _ (by simp)
    simpa only [id_eq,Real.norm_eq_abs] using (memLp_one_iff_integrable.mp h).norm
  have hs (d : PathPauliDirections) := LocalPatches.coordinate_strong_law γ d abs measurable_abs hi
  obtain ⟨a,_,ha,_,hm⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [ae_all_iff.mpr hs,hm] with ω hω hm
  let S (m : ℕ) (d : PathPauliDirections) := ∑ i ∈ Finset.range m, |ω (i,d)|
  have ht (d : PathPauliDirections) : Tendsto (fun m : ℕ => S m d/m-S m (.inl 2)/m) atTop (𝓝 0) := by
    simpa only [sub_self] using (hω d).sub (hω (.inl 2))
  have he (d : PathPauliDirections) := (ht d).eventually_lt_const (div_pos ha (by norm_num : (0:ℝ)<24))
  filter_upwards [hm,(tendsto_add_atTop_nat 2).eventually (Filter.eventually_all.mpr he)] with n hlow hn
  intro u H
  let N := n+2
  have hp : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hz : (∑ i : Fin (n+2), |u (.inl (i,2))|) = S N (.inl 2) :=
    Fin.sum_univ_eq_sum_range (fun i => |ω (i,.inl 2)|) _
  have hfield : a*N ≤ S N (.inl 2) := (show a*N ≤ ∑ i : Fin (n+2), |u (.inl (i,2))| from hlow.1).trans_eq hz
  have hdir (d : PathPauliDirections) : S N d ≤ (25/24)*S N (.inl 2) := by
    have hd := hn d
    change S N d/(N:ℝ)-S N (.inl 2)/(N:ℝ)<a/24 at hd
    rw [←sub_div,div_lt_iff₀ hp] at hd
    linarith only [hd,hfield]
  have hmass := (LocalPatches.prefix_sum_le ω n abs abs_nonneg).trans (Finset.sum_le_sum (s:=Finset.univ) (fun d _ => hdir d))
  have hcard : Fintype.card PathPauliDirections = 12 := by
    simp [PathPauliDirections,Fintype.card_sum,Fintype.card_prod]
  rw [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hmass
  have hnorm : ‖pathHamiltonian u‖ ≤ ∑ l, |u l| := by
    rw [pathHamiltonian_eq_sum]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun l _ => by rw [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
  obtain ⟨_,_,hcenter⟩ := exists_optimal_scalarCenteredHamiltonian H
  have hw : circuitHamiltonianSpectralWidth H/2 ≤ ‖pathHamiltonian u‖ := by
    simpa only [scalarCenteredHamiltonian,Complex.ofReal_zero,zero_smul,sub_zero] using hcenter 0
  rw [hz]
  linarith only [hw,hnorm,hmass]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
