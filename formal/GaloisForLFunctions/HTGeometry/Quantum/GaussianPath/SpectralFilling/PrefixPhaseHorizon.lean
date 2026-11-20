import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.GaussianPhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliFirstThreshold
import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Absolute filling horizons on all sufficiently large prefixes of one Gaussian path -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev D (k : ℕ) := 2^(k+3)
private abbrev Coord (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))
/-- Identify numbered energies with one anchor and the remaining relative phases. -/
def prefixPhaseEnergyEquiv (k : ℕ) : Fin (D k) ≃ Fin ((D k-1)+1) :=
  finCongr (by
    have h : 0 < D k := by dsimp [D]; positivity
    omega)

private def riskParameter (k : ℕ) : ℝ :=
  (1/2:ℝ)^k/(1+((phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)).card:ℝ)*(2*((D k).factorial:ℝ)))

/-- Deterministic physical time horizon for a path of k+3 sites. -/
def pauliPrefixPhaseHorizon (k : ℕ) : ℝ :=
  gaussianPhaseClock (prefixPhaseEnergyEquiv k) (1/80) (((k+3:ℕ):ℝ)^2) (riskParameter k)

private def xPrefix (k : ℕ) (ω : PathPauliDisorder) (i : Coord k) : ℝ :=
  pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)

private def cubeClockWorks {d : ℕ} (E : Fin (d+1) → ℝ) (G : ℝ) : Prop :=
  ∀ u : ℝ, ∀ c : Fin d → ℝ, ∃ t ∈ Icc u (u+G), ∀ j, turnDist (t*RHTower.zeroProjectiveFrequency E j-c j) < 1/80

private def clockException (k : ℕ) : Set (Coord k → ℝ) :=
  {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
       (∀ i, |E i| ≤ ((k+3:ℕ):ℝ)^2) ∧ ¬ ∀ σ : Equiv.Perm (Fin (D k)),
         cubeClockWorks ((E ∘ σ) ∘ (prefixPhaseEnergyEquiv k).symm) (pauliPrefixPhaseHorizon k)}

private theorem clockException_measure (k : ℕ) :
    (Measure.pi fun _ : Coord k => gaussianReal 0 1) (clockException k) ≤ (1/2:ℝ≥0∞)^k := by
  let S := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  let B := (S.card:ℝ)*(2*((D k).factorial:ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 < (1:ℝ)/2 := by norm_num
  have h1 : 0 < 1+B := by positivity
  have hr : 0 < riskParameter k := div_pos (pow_pos hp k) h1
  have hr' : riskParameter k ≤ 1 := (div_le_one h1).mpr ((pow_le_one₀ hp.le (by norm_num)).trans (by linarith only [hB]))
  have h := gaussian_pauli_phase_clock_failure_le k (D k-1) (prefixPhaseEnergyEquiv k) (ρ := 1/80)
    (R := ((k+3:ℕ):ℝ)^2) (r := riskParameter k) (by norm_num) (by linarith only [Real.pi_gt_three])
    (sq_nonneg _) hr hr'
  apply h.trans
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hprice : B*riskParameter k ≤ (1/2:ℝ)^k := by
    change B*((1/2:ℝ)^k/(1+B)) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ h1).mpr
    linarith only [pow_nonneg hp.le k]
  have he : (S.card:ℝ)*(2*((D k).factorial:ℝ)*riskParameter k) ≤ (1/2:ℝ)^k := by
    simpa only [B,mul_assoc] using hprice
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (by rw [ENNReal.ofReal_pow hp.le,one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]; norm_num)

private theorem prefix_clock_exceptions_eventually_absent :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, xPrefix k ω ∉ clockException k := by
  let A (k : ℕ) := xPrefix k ⁻¹' clockException k
  have hm (k : ℕ) : pathPauliDisorderLaw (A k) ≤ (1/2:ℝ≥0∞)^k := by
    have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
    refine (Measure.le_map_apply hmp.measurable.aemeasurable (clockException k)).trans ?_
    rw [hmp.map_eq]
    exact clockException_measure k
  apply ae_eventually_notMem
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hm)
  simp only [one_div,ENNReal.tsum_geometric_two]
  norm_num

private theorem path_eigenvalue_abs_le_mass {n : ℕ} (u : PathShell n) (i) :
    |(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i| ≤ ∑ l : PathLabel n, |u l| := by
  apply (abs_eigenvalue_le_l2_opNorm (isSelfAdjoint_pathHamiltonian u).isHermitian i).trans
  rw [pathHamiltonian_eq_sum]
  refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => ?_)
  rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]

private theorem path_energy_permutation (k : ℕ) (ω : PathPauliDisorder)
    (hinj : Function.Injective (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues) :
    let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) (xPrefix k ω)).eigenvalues
    let ep := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
    ∃ σ : Equiv.Perm (Fin (D k)), E ∘ σ = ep ∘ (qubitConfigFin (k+3)).symm := by
  classical
  intro E ep
  let u := pathPauliDisorderShell ω (k+1)
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let e := qubitConfigFin (k+3)
  have hg := range_eigenvalues_reindex e hH
  have he := isHermitian_eigenvalues_congr (isHermitian_reindex e hH)
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) (xPrefix k ω)) (reindex_pathHamiltonian u)
  rw [he] at hg
  have hmem (i : Fin (D k)) : ep (e.symm i) ∈ Set.range E := by
    rw [show Set.range E = Set.range ep from hg]; exact Set.mem_range_self _
  choose f hf using hmem
  have hfinj : Function.Injective f := fun i j hij => e.symm.injective (hinj ((hf i).symm.trans ((congrArg E hij).trans (hf j))))
  exact ⟨Equiv.ofBijective f hfinj.bijective_of_finite,funext hf⟩

/-- Almost surely every sufficiently long prefix fills every relative-phase
box of radius 1/80 in every interval of the deterministic horizon above. -/
theorem gaussian_path_eventually_calibrated_phase_filling :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let e := (qubitConfigFin (k+3)).trans (prefixPhaseEnergyEquiv k)
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ u : ℝ, ∀ c : Fin (D k-1) → ℝ, ∃ t ∈ Icc u (u+pauliPrefixPhaseHorizon k),
        ∀ j, turnDist (t*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-c j) < 1/80 := by
  obtain ⟨_,b,_,_,hmass⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hmass,prefix_clock_exceptions_eventually_absent,gaussian_path_all_prefixes_maximally_projective] with ω hw hb hspec
  obtain ⟨m,hm⟩ := exists_nat_gt (12+b)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hb,eventually_ge_atTop m] with k hk hgood hl
  let N := k+3
  let u := pathPauliDisorderShell ω (k+1)
  let ep := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
  let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) (xPrefix k ω)).eigenvalues
  obtain ⟨σ,hσ⟩ := path_energy_permutation k ω (hspec k).injective
  have hmN : (12+b) ≤ (N:ℝ) := hm.le.trans (by exact_mod_cast (by dsimp [N]; omega : m ≤ N))
  have hwidth : ∀ i, |ep i| ≤ (N:ℝ)^2 := fun i =>
    (path_eigenvalue_abs_le_mass u i).trans ((path_pauli_coefficient_mass_le u b hk.2).trans
      (by simpa only [pow_two] using mul_le_mul_of_nonneg_right hmN (Nat.cast_nonneg N)))
  have hE (j) : |E j| ≤ (N:ℝ)^2 := by
    obtain ⟨i,rfl⟩ := σ.surjective j
    exact (congrArg (fun f : Fin (D k) → ℝ => |f i|) hσ).le.trans (hwidth _)
  have hall : ∀ τ : Equiv.Perm (Fin (D k)), cubeClockWorks ((E ∘ τ) ∘ (prefixPhaseEnergyEquiv k).symm) (pauliPrefixPhaseHorizon k) := by
    by_contra hn
    exact hgood ⟨hE,hn⟩
  have hh := hall σ
  change E ∘ σ = ep ∘ (qubitConfigFin N).symm at hσ
  rw [hσ] at hh
  exact hh

#print axioms gaussian_path_eventually_calibrated_phase_filling
end
end GaloisForLFunctions.HTGeometry
