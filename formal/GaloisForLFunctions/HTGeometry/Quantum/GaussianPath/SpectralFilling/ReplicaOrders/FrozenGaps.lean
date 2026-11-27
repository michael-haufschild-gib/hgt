import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.SimultaneousDetuning
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.PacketRisk

/-! # Explicit simultaneous replica gaps on every sufficiently long frozen prefix -/
open Set Filter Real MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open private xPrefix path_energy_permutation path_eigenvalue_abs_le_mass from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
noncomputable section

private def orderBound (k q : ℕ) : ℕ := degreeBound (2^(k+3)) q

private theorem orderBound_pos (k q : ℕ) : 0 < orderBound k q := by
  have hD : 0 < (2:ℕ)^(k+3) := by positivity
  exact lt_min (by positivity) (pow_pos (Nat.choose_pos (by omega)) _)
private def risk (k q : ℕ) : ℝ := (1/2:ℝ)^(k+q+1)/(2*(orderBound k q:ℝ))

/-- Deterministic detuning scale on the K=k+3 prefix. At each fixed
replica order q its inverse is at most exp[O_q(K·2^(2qK))]. -/
def replicaGap (k q : ℕ) : ℝ :=
  (risk k q / max 1 (2*(q:ℝ)*((k+3:ℕ):ℝ)^2))^(orderBound k q)

theorem replicaGap_pos (k q : ℕ) : 0 < replicaGap k q := by
  have hd : 0 < orderBound k q := orderBound_pos k q
  unfold replicaGap risk
  exact pow_pos (div_pos (by positivity) (zero_lt_one.trans_le (le_max_left ..))) _

private def exception (k q : ℕ) : Set (Coordinate k→ℝ) :=
  {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
       (∀ i, |E i| ≤ ((k+3:ℕ):ℝ)^2) ∧ ∃ p : Pair (Level k) q, |gap E p| < replicaGap k q}

private theorem exception_measure (k q : ℕ) :
    (Measure.pi fun _ : Coordinate k => gaussianReal 0 1) (exception k q) ≤ (1/2:ℝ≥0∞)^(k+q+1) := by
  let d := orderBound k q
  have hd : 0 < d := orderBound_pos k q
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have h₂ : 0 < 2*(d:ℝ) := by positivity
  have hr : 0 < risk k q := div_pos (pow_pos (by norm_num) _) h₂
  have hr' : risk k q ≤ 1 := (div_le_one h₂).mpr
    ((pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).trans (by linarith only [hd']))
  apply (gaussian_replica_detuning k q hr hr' (((k+3:ℕ):ℝ)^2)).trans
  change ENNReal.ofReal (2*(d:ℝ)*((1/2:ℝ)^(k+q+1)/(2*(d:ℝ)))) ≤ _
  rw [show 2*(d:ℝ)*((1/2:ℝ)^(k+q+1)/(2*(d:ℝ)))=(1/2:ℝ)^(k+q+1) by field_simp]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num

private theorem eventually_all_orders :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∀ q : ℕ, xPrefix k ω ∉ exception k q := by
  apply SpectralJets.AllHeights.eventually_no_packet pathPauliDisorderLaw (fun k q => xPrefix k ⁻¹' exception k q)
  intro k q
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  apply (Measure.le_map_apply hmp.measurable.aemeasurable (exception k q)).trans
  rw [hmp.map_eq]
  exact exception_measure k q

/-- One draw works simultaneously for every replica order on every
sufficiently long prefix, with an explicit gap in physical energy units. -/
theorem gaussian_frozen_replica_gaps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ q : ℕ, ∀ p : Pair (Level k) q, replicaGap k q ≤ |gap (E ∘ (qubitConfigFin (k+3)).symm) p| := by
  obtain ⟨_,b,_,_,hmass⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hmass,eventually_all_orders,gaussian_path_all_prefixes_maximally_projective] with ω hw hb hspec
  obtain ⟨m,hm⟩ := exists_nat_gt (12+b)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hb,eventually_ge_atTop m] with k hk hgood hl
  intro E q p
  let K := k+3
  let u := pathPauliDisorderShell ω (k+1)
  let e := qubitConfigFin K
  let G := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian K) (xPrefix k ω)).eigenvalues
  obtain ⟨σ,hσ⟩ := path_energy_permutation k ω (hspec k).injective
  change G ∘ σ=E ∘ e.symm at hσ
  have hh : 12+b ≤ (K:ℝ) := hm.le.trans (by exact_mod_cast (by dsimp only [K]; omega : m ≤ K))
  have hwidth (i) : |E i| ≤ (K:ℝ)^2 := (path_eigenvalue_abs_le_mass u i).trans
    ((path_pauli_coefficient_mass_le u b hk.2).trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg K)))
  have hg (j) : |G j| ≤ (K:ℝ)^2 := by
    obtain ⟨i,rfl⟩ := σ.surjective j
    exact (congrArg (fun f => |f i|) hσ).le.trans (hwidth _)
  rw [←hσ]
  rw [gap_relabel]
  exact le_of_not_gt (fun h => hgood q ⟨hg,⟨relabel σ p,h⟩⟩)

#print axioms gaussian_frozen_replica_gaps
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
