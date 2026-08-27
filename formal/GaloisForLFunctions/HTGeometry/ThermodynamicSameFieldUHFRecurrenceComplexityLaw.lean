import GaloisForLFunctions.HTGeometry.ThermodynamicSelectedPathLifecycleLaw
import GaloisForLFunctions.HTGeometry.ThermodynamicPathUHFPrefixConvergence

/-!
# One thermodynamic field across recurrence and complexity

This capstone discharges all selection, locality, spectral, summability, and infinite-volume
premises for one static nearest-neighbour Pauli field on the countable qubit path.

Every finite prefix is a literal restriction of that field and has maximally projective spectrum.
Its projective quantum returns are syndetic at every resolution.  Pair-grouped prefixes obey the
laboratory two-qubit gate ramp, and sufficiently large prefixes have recurrent near-Hilbert hard
excursions with literal consecutive re-entry.  The same coefficients generate a bounded
self-adjoint element of the standard qubit UHF algebra, a point-norm continuous one-parameter
automorphism group, and the finite-prefix dynamics converge to it uniformly on compact times.
-/

open Filter Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StaticLocalLaboratoryComplexityGrowthLaw
open PrimeQuasiLocalCharge

/-- A finite maximally projective Hamiltonian returns, up to global phase, inside every interval of
one fixed length at every positive operator-norm resolution. -/
theorem maximallyProjective_unitaryEvolution_projectiveReturn_syndetic
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
      ∃ t ∈ Icc a (a + B), ∃ c : ℂ, ‖c‖ = 1 ∧
        ‖unitaryEvolution H t - c •
          (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ < ε := by
  let V := hermitianEigenbasisUnitary hH
  let U : Set (Fin d → UnitAddCircle) :=
    (projectiveSpectralMatrix e V) ⁻¹'
      Metric.ball (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ε
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have horbitZero : projectiveSpectralMatrix e V
      (0 : Fin d → UnitAddCircle) = 1 := by
    have hdiag : Matrix.diagonal (fun q : Fin n → Bool =>
        fourier 1 (RHTower.zeroAnchoredPhase d
          (0 : Fin d → UnitAddCircle) (e q))) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
        simp only [Matrix.one_apply, if_pos]
        generalize hr : e i = r
        refine Fin.cases ?_ (fun k => ?_) r <;>
          simp [RHTower.zeroAnchoredPhase]
      · simp [hij]
    rw [projectiveSpectralMatrix, hdiag, Matrix.mul_one]
    exact V.2.2
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp [U, Metric.mem_ball, horbitZero, hε]
  obtain ⟨B, hB, hrec⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom
      (fun i => hH.eigenvalues (e.symm i)))
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom
      (fun i => hH.eigenvalues (e.symm i)) hmax)
    hUopen hUne
  refine ⟨B, hB, fun a => ?_⟩
  obtain ⟨t, ht, htU⟩ := hrec a
  change RHTower.projectivePhysicalPhaseFlow
    (fun i => hH.eigenvalues (e.symm i)) t ∈ U at htU
  let anchor : ℂ :=
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor : ‖anchor‖ = 1 := by
    dsimp [anchor]
    rw [Complex.norm_exp]
    simp
  refine ⟨t, ht, anchor, hanchor, ?_⟩
  have hphysical : unitaryEvolution H t =
      anchor • projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow
          (fun i => hH.eigenvalues (e.symm i)) t) := by
    exact unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e hH t
  rw [hphysical]
  have hfactor :
      anchor • projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) - anchor • 1 =
        anchor • (projectiveSpectralMatrix e V
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) - 1) := by
    module
  rw [hfactor, norm_smul, hanchor, one_mul]
  simpa [U, Metric.mem_ball, dist_eq_norm] using htU

/-- Every literal finite prefix of a simultaneously projective path field has syndetic
projective quantum recurrence at every positive resolution. -/
theorem infinitePathPrefix_projectiveReturn_syndetic
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈
      chainProjectiveGood k)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
      ∃ t ∈ Icc a (a + B), ∃ c : ℂ, ‖c‖ = 1 ∧
        ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
          c • (1 : Matrix (Fin (k + 3) → Bool)
            (Fin (k + 3) → Bool) ℂ)‖ < ε := by
  let n := k + 3
  let d := 2 ^ n - 1
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hdim : 2 ^ n = d + 1 := by
    dsimp [d]
    omega
  let e : (Fin n → Bool) ≃ Fin (d + 1) :=
    (qubitConfigFin n).trans (finCongr hdim)
  let hH : (pathHamiltonian (infinitePathPrefixShell k p)).IsHermitian := by
    exact isSelfAdjoint_pathHamiltonian _
  have hcanon : MaximallyProjectiveEnergy hH.eigenvalues :=
    infinitePathPrefixHamiltonian_eigenvalues_maximallyProjective hp k
  have hmax : MaximallyProjectiveEnergy
      (fun i => hH.eigenvalues (e.symm i)) :=
    hcanon.comp_equiv_relabel e.symm
  simpa [n] using
    (maximallyProjective_unitaryEvolution_projectiveReturn_syndetic
      e hH hmax hε)

/-- Complete property bundle for one static nearest-neighbour field across all finite prefixes and
its standard infinite-volume UHF dynamics. -/
structure ThermodynamicSameFieldLifecycle
    (p : InfinitePathLabel → ℝ) : Prop where
  coefficient_close :
    ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i
  coefficient_summable : Summable (fun i => |p i|)
  prefix_maximallyProjective :
    ∀ k, MaximallyProjectiveEnergy
      (pathEigenValues k (infinitePathPrefixShell k p))
  prefix_projective_recurrence :
    ∀ (k : ℕ) (ε : ℝ), 0 < ε →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
        ∃ t ∈ Icc a (a + B), ∃ c : ℂ, ‖c‖ = 1 ∧
          ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
            c • (1 : Matrix (Fin (k + 3) → Bool)
              (Fin (k + 3) → Bool) ℂ)‖ < ε
  laboratory_ramp :
    ∀ (N K : ℕ) (c : List (LocalGate (PairQubit (N + 2)))) (t ε : ℝ),
      8 ≤ K → 8 * K ≤ N + 2 →
      0 < ε → ε ≤ 1 / 100 →
      128 * Real.pi * ε * K ≤ t →
      t < 128 * Real.pi * ε * (K + 1) →
      ‖circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ ≤ ε →
      K ≤ twoGateCount c
  eventually_excursion_reentry :
    ∀ᶠ k : ℕ in atTop,
      ContinuousCircuitExcursionLaw (k + 3)
        (nearHilbertContinuousCircuitBudget (k + 3))
        (pathHamiltonian (infinitePathPrefixShell k p))
  infinite_hamiltonian_selfAdjoint :
    IsSelfAdjoint (infinitePathUHFHamiltonian p)
  infinite_evolution_unitary :
    ∀ t, infinitePathUHFEvolution p t ∈ unitary (PrimeUHFAlgebra qubitLocalDim)
  infinite_evolution_continuous : Continuous (infinitePathUHFEvolution p)
  infinite_evolution_zero : infinitePathUHFEvolution p 0 = 1
  infinite_evolution_add :
    ∀ s t, infinitePathUHFEvolution p (s + t) =
      infinitePathUHFEvolution p s * infinitePathUHFEvolution p t
  infinite_dynamics_pointNormContinuous :
    ∀ A, Continuous (fun t => infinitePathUHFDynamics coefficient_summable t A)
  infinite_dynamics_zero :
    infinitePathUHFDynamics coefficient_summable 0 =
      StarAlgEquiv.refl ℂ (PrimeUHFAlgebra qubitLocalDim)
  infinite_dynamics_add :
    ∀ s t A,
      infinitePathUHFDynamics coefficient_summable (s + t) A =
        infinitePathUHFDynamics coefficient_summable s
          (infinitePathUHFDynamics coefficient_summable t A)
  prefix_is_literalPartialSum :
    ∀ k, embeddedInfinitePathPrefixHamiltonian p k =
      ∑ l : PathLabel (k + 1),
        infinitePathUHFTerm p (pathLabelToInfinite k l)
  prefix_hamiltonian_converges :
    Tendsto (embeddedInfinitePathPrefixHamiltonian p)
      atTop (nhds (infinitePathUHFHamiltonian p))
  prefix_evolution_uniformOnCompact :
    ∀ T ε : ℝ, 0 ≤ T → 0 < ε →
      ∃ K, ∀ k, K ≤ k → ∀ t : ℝ, |t| ≤ T →
        ‖embeddedInfinitePathPrefixEvolution p k t -
          infinitePathUHFEvolution p t‖ < ε
  prefix_heisenberg_uniformOnCompact :
    ∀ A T ε, 0 ≤ T → 0 < ε →
      ∃ K, ∀ k, K ≤ k → ∀ t : ℝ, |t| ≤ T →
        ‖embeddedInfinitePathPrefixHeisenberg p k t A -
          infinitePathUHFHeisenberg p t A‖ < ε

/-- **Unconditional same-field thermodynamic recurrence--complexity law.** One countable static
nearest-neighbour Pauli field simultaneously realizes every finite-volume and infinite-volume
clause in `ThermodynamicSameFieldLifecycle`; no premise is left for a caller to supply. -/
theorem exists_thermodynamicSameFieldLifecycle :
    ∃ p : InfinitePathLabel → ℝ, ThermodynamicSameFieldLifecycle p := by
  obtain ⟨p, hpclose, hpgood, hsum⟩ :=
    exists_nestedCentered_allPrefixes_projective_summable
  have hprojective : ∀ k, MaximallyProjectiveEnergy
      (pathEigenValues k (infinitePathPrefixShell k p)) :=
    fun k => infinitePathPrefixShell_maximallyProjective hpgood k
  have hramp :
      ∀ (N K : ℕ) (c : List (LocalGate (PairQubit (N + 2)))) (t ε : ℝ),
        8 ≤ K → 8 * K ≤ N + 2 →
        0 < ε → ε ≤ 1 / 100 →
        128 * Real.pi * ε * K ≤ t →
        t < 128 * Real.pi * ε * (K + 1) →
        ‖circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ ≤ ε →
        K ≤ twoGateCount c := by
    intro N K c t ε hK hKL hε hεsmall htlo hthi hclose
    exact thermodynamicPairHamiltonian_twoGateCount_ge
      c hK hKL hpclose hε hεsmall htlo hthi hclose
  have hexcursion := eventually_infinitePathPrefix_continuousCircuitExcursions hpgood
  exact ⟨p, {
    coefficient_close := hpclose
    coefficient_summable := hsum
    prefix_maximallyProjective := hprojective
    prefix_projective_recurrence := fun k ε hε =>
      infinitePathPrefix_projectiveReturn_syndetic hpgood k hε
    laboratory_ramp := hramp
    eventually_excursion_reentry := hexcursion
    infinite_hamiltonian_selfAdjoint :=
      isSelfAdjoint_infinitePathUHFHamiltonian hsum
    infinite_evolution_unitary := infinitePathUHFEvolution_mem_unitary hsum
    infinite_evolution_continuous := continuous_infinitePathUHFEvolution p
    infinite_evolution_zero := infinitePathUHFEvolution_zero p
    infinite_evolution_add := infinitePathUHFEvolution_add p
    infinite_dynamics_pointNormContinuous :=
      continuous_infinitePathUHFDynamics_apply hsum
    infinite_dynamics_zero := infinitePathUHFDynamics_zero hsum
    infinite_dynamics_add := infinitePathUHFDynamics_add_apply hsum
    prefix_is_literalPartialSum :=
      embeddedInfinitePathPrefixHamiltonian_eq_sum p
    prefix_hamiltonian_converges :=
      tendsto_embeddedInfinitePathPrefixHamiltonian hsum
    prefix_evolution_uniformOnCompact :=
      embeddedInfinitePathPrefixEvolution_uniformOnCompact hsum
    prefix_heisenberg_uniformOnCompact :=
      embeddedInfinitePathPrefixHeisenberg_uniformOnCompact hsum }⟩

end

end GaloisForLFunctions.HTGeometry
