import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalExtremality
import GaloisForLFunctions.HTGeometry.DiagonalSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.ProjectiveExactReturnRankOne
import GaloisForLFunctions.HTGeometry.QuditPathChainRecurrenceExponent
import GaloisForLFunctions.HTGeometry.OrbitFidelityRecurrenceExponent
import GaloisForLFunctions.HTGeometry.CollisionEnsembleLaw
import GaloisForLFunctions.HTGeometry.EternityHorizonCapstone
import GaloisForLFunctions.HTGeometry.EternityOperatorReturnCorollary

/-!
# Finite-horizon instability of the physical quantum recurrence exponent

Every finite-time operator-norm tube around every finite Hermitian Hamiltonian of dimension at
least three contains two commuting simple-spectrum Hamiltonians with one common eigenbasis.  For
every fixed normalized state cyclic in that shared basis, one neighbour has survival-fidelity
first-return exponent zero while the other has the maximal generic exponent `(D - 2) / 2`.

Thus neither the complete propagator on a bounded time interval nor the state preparation fixes the
asymptotic physical first-return exponent.  The proof combines dense exact periodic spectra, global
nullity of the very-well-approximable sorted-gap-ratio locus, common-eigenbasis spectral transport,
and the sharp cyclic-orbit fidelity exponent law.

Main result:
* `exists_sameEigenbasis_periodic_and_maximalPhysicalReturn_uniform_horizon` — the same-state,
  full-propagator finite-horizon non-identifiability theorem.
-/

open Filter Topology MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

def diagonalSpectralGenerator (a : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun i => if i = a then 1 else 0)

theorem isHermitian_diagonalSpectralGenerator (a : Fin D) :
    (diagonalSpectralGenerator a).IsHermitian := by
  rw [diagonalSpectralGenerator, Matrix.isHermitian_diagonal_iff]
  intro i
  split <;> simp_all

theorem spectralEnsembleMatrix_diagonalSpectralGenerator (θ : Fin D → ℝ) :
    spectralEnsembleMatrix diagonalSpectralGenerator θ =
      Matrix.diagonal (fun i => (θ i : ℂ)) := by
  ext i j
  simp [spectralEnsembleMatrix, diagonalSpectralGenerator, Matrix.sum_apply,
    Matrix.diagonal_apply]

theorem diagonalSpectralGenerator_spectrumEscapesRealRelations :
    SpectrumEscapesRealRelations
      (Set.range (spectralEnsembleMatrix (diagonalSpectralGenerator (D := D)))) := by
  apply SpectrumEscapesAffineRelations.toRealRelations
  intro c hbalanced hc target
  obtain ⟨M, hM, E, hEinj, hroot, hesc⟩ :=
    diagonalSet_spectrumEscapesAffineRelations c hbalanced hc target
  obtain ⟨E', rfl⟩ := hM
  refine ⟨spectralEnsembleMatrix diagonalSpectralGenerator E', ⟨E', rfl⟩, E, hEinj, ?_, hesc⟩
  simpa [spectralEnsembleMatrix_diagonalSpectralGenerator] using hroot

theorem injectiveRealSpectrumSet_isOpen (D : ℕ) :
    IsOpen {E : Fin D → ℝ | Function.Injective E} := by
  classical
  have hset : {E : Fin D → ℝ | Function.Injective E}
      = ⋂ i : Fin D, ⋂ j : Fin D, ⋂ _ : i ≠ j, {E : Fin D → ℝ | E i ≠ E j} := by
    ext E
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro hinj i j hij heq
      exact hij (hinj heq)
    · intro hpairs i j heq
      by_contra hij
      exact hpairs i j hij heq
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine isOpen_iInter_of_finite fun _ => ?_
  have hcont : Continuous fun E : Fin D → ℝ => E i - E j :=
    (continuous_apply i).sub (continuous_apply j)
  have hopen := hcont.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne
  convert hopen using 1
  ext E
  simp only [mem_preimage, mem_setOf_eq, sub_ne_zero]

theorem mem_simpleEnsembleLocus_diagonalSpectralGenerator_of_injective
    {E : Fin D → ℝ} (hE : Function.Injective E) :
    E ∈ simpleEnsembleLocus
      (fun a : Fin D => isHermitian_diagonalSpectralGenerator a) := by
  let hP : ∀ a : Fin D, (diagonalSpectralGenerator a).IsHermitian :=
    fun a => isHermitian_diagonalSpectralGenerator a
  let hH := isHermitian_spectralEnsembleMatrix hP E
  apply hermitianEigenvalues_injective_of_rootPacket hH E hE
  intro i
  rw [spectralEnsembleMatrix_diagonalSpectralGenerator]
  exact matrixCharpolyRelation_diagonal_root (fun j => ((E j : ℝ) : ℂ)) i

theorem sortedTuple_eigenvalues_diagonal_real (E : Fin D → ℝ) :
    sortedTuple
        ((Matrix.isHermitian_diagonal_iff.mpr fun i => Complex.conj_ofReal (E i)).eigenvalues)
      = sortedTuple E := by
  apply eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) (monotone_sortedTuple _)
  intro p
  rw [sum_pow_sortedTuple, sum_pow_sortedTuple,
    sum_pow_eigenvalues_eq_trace_pow_re]
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  change (∑ i, ((E i : ℂ) ^ p)).re = ∑ i, E i ^ p
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem sortedEnsembleSpectrum_diagonalSpectralGenerator
    (E : Fin D → ℝ) :
    sortedEnsembleSpectrum
        (fun a : Fin D => isHermitian_diagonalSpectralGenerator a) E
      = sortedTuple E := by
  apply eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) (monotone_sortedTuple _)
  intro p
  rw [sum_pow_sortedTuple, sum_pow_sortedTuple,
    sum_pow_eigenvalues_eq_trace_pow_re]
  rw [spectralEnsembleMatrix_diagonalSpectralGenerator]
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  change (∑ i, ((E i : ℂ) ^ p)).re = ∑ i, E i ^ p
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem exists_close_simpleSpectrum_not_vwa_sortedGapRatio {e : ℕ}
    (E : Fin (e + 3) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E' : Fin (e + 3) → ℝ,
      Function.Injective E' ∧
      (∀ i, dist (E' i) (E i) < ε) ∧
      ¬ KleinbockMargulis.VWA
        (anchoredGapRatioMap (sortedTuple E') 0 1 (fun k : Fin (e + 1) => k.succ.succ)) := by
  let hP : ∀ a : Fin (e + 3), (diagonalSpectralGenerator a).IsHermitian :=
    fun a => isHermitian_diagonalSpectralGenerator a
  obtain ⟨E₀, hE₀inj, hE₀close, -⟩ :=
    exists_close_simpleSpectrum_hasPositiveProjectiveReturn (d := e + 2) (by omega) E
      (half_pos hε)
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (injectiveRealSpectrumSet_isOpen (e + 3)) E₀ hE₀inj
  let r' := min r (ε / 2)
  have hr' : 0 < r' := lt_min hr (half_pos hε)
  have hballinj : Metric.ball E₀ r' ⊆ {F : Fin (e + 3) → ℝ | Function.Injective F} := by
    intro F hF
    exact hball (lt_of_lt_of_le (Metric.mem_ball.mp hF) (min_le_left _ _))
  have hballsimple : Metric.ball E₀ r' ⊆ simpleEnsembleLocus hP := by
    intro F hF
    exact mem_simpleEnsembleLocus_diagonalSpectralGenerator_of_injective (hballinj hF)
  let bad : Set (Fin (e + 3) → ℝ) :=
    {F ∈ simpleEnsembleLocus hP |
      KleinbockMargulis.VWA
        (anchoredGapRatioMap (sortedEnsembleSpectrum hP F) 0 1
          (fun k : Fin (e + 1) => k.succ.succ))}
  have hbad : volume bad = 0 := by
    exact volume_vwa_sortedGapRatio_eq_zero (n := e + 1) (by omega) hP
      diagonalSpectralGenerator_spectrumEscapesRealRelations
      (fun a b hab => Fin.succ_injective _ (Fin.succ_injective _ hab))
      (fun _ => Fin.succ_ne_zero _)
      (fun k => by
        have h1 : (1 : Fin (e + 3)) = Fin.succ (0 : Fin (e + 2)) := rfl
        rw [h1]
        intro hk
        exact Fin.succ_ne_zero k (Fin.succ_injective _ hk))
      (by exact zero_ne_one)
  have hnsub : ¬ Metric.ball E₀ r' ⊆ bad := by
    intro hsub
    have hle := measure_mono (μ := volume) hsub
    rw [hbad] at hle
    have hz : volume (Metric.ball E₀ r') = 0 := le_antisymm hle (by simp)
    exact (Metric.measure_ball_pos volume E₀ hr').ne' hz
  obtain ⟨E', hE'ball, hE'good⟩ := Set.not_subset.mp hnsub
  have hE'inj : Function.Injective E' := hballinj hE'ball
  have hE'simple : E' ∈ simpleEnsembleLocus hP := hballsimple hE'ball
  have hnv : ¬ KleinbockMargulis.VWA
      (anchoredGapRatioMap (sortedEnsembleSpectrum hP E') 0 1
        (fun k : Fin (e + 1) => k.succ.succ)) := by
    intro hvwa
    exact hE'good ⟨hE'simple, hvwa⟩
  refine ⟨E', hE'inj, ?_, ?_⟩
  · have hcoord := (dist_pi_lt_iff hr').mp (Metric.mem_ball.mp hE'ball)
    intro i
    calc
      dist (E' i) (E i) ≤ dist (E' i) (E₀ i) + dist (E₀ i) (E i) := dist_triangle _ _ _
      _ < r' + ε / 2 := add_lt_add (hcoord i) (hE₀close i)
      _ ≤ ε / 2 + ε / 2 := add_le_add (min_le_right _ _) le_rfl
      _ = ε := by ring
  · rw [sortedEnsembleSpectrum_diagonalSpectralGenerator] at hnv
    exact hnv

theorem spectralReturnDeficit_eq_zero_of_projectiveReturn
    {d : ℕ} (E p : Fin (d + 1) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j)
    {t : ℝ}
    (hret : ∀ j : Fin d, ∃ m : ℤ,
      t * (E j.succ - E 0) = 2 * Real.pi * (m : ℝ)) :
    spectralReturnDeficit E p t = 0 := by
  rw [spectralReturnDeficit, spectralReturnAmplitude_eq_finitePhaseOverlap]
  apply (_root_.HTGeometry.finitePhase_fidelityDeficit_eq_zero_iff p _ hp1 hppos
    (fun j => Complex.norm_exp_ofReal_mul_I _)).2
  have hphase : ∀ i : Fin (d + 1),
      Complex.exp (((-(t * E i) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rfl
    · obtain ⟨m, hm⟩ := hret j
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨-m, ?_⟩
      have hmC := congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hm
      push_cast at hmC ⊢
      linear_combination -hmC * Complex.I
  intro i j
  exact (hphase i).trans (hphase j).symm

theorem tendsto_log_fidelityReturnTime_zero_of_hasPositiveProjectiveReturn
    {d : ℕ} (E p : Fin (d + 1) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j)
    (hret : HasPositiveProjectiveReturn E) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨T, hT, hm⟩ := hret
  obtain ⟨N, hN⟩ := exists_nat_gt (t₀ / T)
  have hNpos : 0 < N := by
    have hquot : 0 < t₀ / T := div_pos ht₀ hT
    exact_mod_cast (lt_trans hquot hN)
  let τ : ℝ := (N : ℝ) * T
  have ht₀τ : t₀ ≤ τ := by
    dsimp [τ]
    rw [div_lt_iff₀ hT] at hN
    exact (le_of_lt hN)
  have hτpos : 0 < τ := mul_pos (by exact_mod_cast hNpos) hT
  have hretτ : ∀ j : Fin d, ∃ z : ℤ,
      τ * (E j.succ - E 0) = 2 * Real.pi * (z : ℝ) := by
    intro j
    obtain ⟨z, hz⟩ := hm j
    refine ⟨(N : ℤ) * z, ?_⟩
    dsimp [τ]
    rw [mul_assoc, hz]
    push_cast
    ring
  have hzero : spectralReturnDeficit E p τ = 0 :=
    spectralReturnDeficit_eq_zero_of_projectiveReturn E p hp1 hppos hretτ
  have hreturn : ∀ {δ : ℝ}, 0 < δ →
      (fidelityReturnSet E p t₀ δ).Nonempty ∧ fidelityReturnTime E p t₀ δ ≤ τ := by
    intro δ hδ
    have hmem : τ ∈ fidelityReturnSet E p t₀ δ := ⟨ht₀τ, by rw [hzero]; exact hδ⟩
    exact ⟨⟨τ, hmem⟩, csInf_le (bddBelow_fidelityReturnSet E p t₀ δ) hmem⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_div_log_one_div (Real.log t₀))
    (tendsto_const_div_log_one_div (Real.log τ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ hδ1
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ]
      linarith [hδ1.2]
    have hr := hreturn hδ
    have hlower := le_fidelityReturnTime hr.1
    have htimepos : 0 < fidelityReturnTime E p t₀ δ := lt_of_lt_of_le ht₀ hlower
    exact (div_le_div_iff_of_pos_right hlogpos).2 (Real.log_le_log ht₀ hlower)
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ hδ1
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ]
      linarith [hδ1.2]
    have hr := hreturn hδ
    have hlower := le_fidelityReturnTime hr.1
    have htimepos : 0 < fidelityReturnTime E p t₀ δ := lt_of_lt_of_le ht₀ hlower
    exact (div_le_div_iff_of_pos_right hlogpos).2 (Real.log_le_log htimepos hr.2)

theorem tendsto_log_orbitFidelityReturnTime_zero_of_hasPositiveProjectiveReturn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (ρ : α ≃ Fin (d + 1))
    {H : Matrix α α ℂ} {eigenbasis : α → α → ℂ} {energy : α → ℝ}
    (heb : IsOrthoEigenBasis H eigenbasis energy)
    {Ω : α → ℂ} (hΩ : finiteComplexInner Ω Ω = 1)
    (hcyc : ∀ j, finiteComplexInner (eigenbasis j) Ω ≠ 0)
    (hret : HasPositiveProjectiveReturn (fun i => energy (ρ.symm i)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log (orbitFidelityReturnTime H Ω t₀ δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let p : Fin (d + 1) → ℝ := fun i => spectralWeights eigenbasis Ω (ρ.symm i)
  have hp1 : ∑ i, p i = 1 := by
    rw [show (∑ i, p i) = ∑ j, spectralWeights eigenbasis Ω j from
      Equiv.sum_comp ρ.symm (spectralWeights eigenbasis Ω)]
    exact sum_spectralWeights heb hΩ
  have hppos : ∀ i, 0 < p i := by
    intro i
    change 0 < spectralWeights eigenbasis Ω (ρ.symm i)
    rw [spectralWeights]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hcyc (ρ.symm i)))
  have hmain := tendsto_log_fidelityReturnTime_zero_of_hasPositiveProjectiveReturn
    (fun i => energy (ρ.symm i)) p hp1 hppos hret ht₀
  refine hmain.congr' ?_
  filter_upwards with δ
  rw [orbitFidelityReturnTime_eq ρ heb Ω t₀ δ]

def coordinateEigenBasis {α : Type*} [DecidableEq α] (j : α) : α → ℂ :=
  Pi.single j 1

theorem isOrthoEigenBasis_diagonal_real
    {α : Type*} [Fintype α] [DecidableEq α] (E : α → ℝ) :
    IsOrthoEigenBasis (Matrix.diagonal fun i => (E i : ℂ)) coordinateEigenBasis E := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    simp [finiteComplexInner, coordinateEigenBasis, Pi.single_apply, eq_comm]
  · intro j
    funext i
    by_cases hij : i = j <;>
      simp [Matrix.mulVec_diagonal, coordinateEigenBasis, hij]
  · intro ψ
    funext i
    simp [finiteComplexInner, coordinateEigenBasis, Pi.single_apply, eq_comm]

def spectralTransportEigenBasis
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A.IsHermitian) (j : α) : α → ℂ :=
  (hA.eigenvectorUnitary : Matrix α α ℂ) *ᵥ coordinateEigenBasis j

def spectralTransportMatrix
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A.IsHermitian) (E : α → ℝ) : Matrix α α ℂ :=
  (hA.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ E) *
    star (hA.eigenvectorUnitary : Matrix α α ℂ)

theorem isOrthoEigenBasis_spectralTransport
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A.IsHermitian) (E : α → ℝ) :
    IsOrthoEigenBasis
      ((hA.eigenvectorUnitary : Matrix α α ℂ) *
        Matrix.diagonal (fun i => (E i : ℂ)) *
        star (hA.eigenvectorUnitary : Matrix α α ℂ))
      (spectralTransportEigenBasis hA) E := by
  let V : Matrix α α ℂ := (hA.eigenvectorUnitary : Matrix α α ℂ)
  let U : Matrix α α ℂ := star V
  have hU : Uᴴ * U = 1 := by
    simpa [U, V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := by
    simpa [U, V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hbase := isOrthoEigenBasis_conj (isOrthoEigenBasis_diagonal_real E) hU hU'
  unfold spectralTransportEigenBasis
  simpa [U, V, Matrix.star_eq_conjTranspose] using hbase

theorem isHermitian_spectralTransportMatrix
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (E : Fin (n + 1) → ℝ) :
    (spectralTransportMatrix hA E).IsHermitian := by
  simpa [spectralTransportMatrix, Unitary.conjStarAlgAut_apply] using
    isHermitian_unitary_conj_diagonal hA.eigenvectorUnitary E

theorem spectralTransportMatrix_comm_original
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (E : Fin (n + 1) → ℝ) :
    spectralTransportMatrix hA E * A = A * spectralTransportMatrix hA E := by
  let f := Unitary.conjStarAlgAut ℂ
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hA.eigenvectorUnitary
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let D' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ E)
  have hAeq : A = f D := hA.spectral_theorem
  have hcomm : D' * D = D * D' := by
    change Matrix.diagonal (RCLike.ofReal ∘ E) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        Matrix.diagonal (RCLike.ofReal ∘ E)
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hB : spectralTransportMatrix hA E = f D' := by
    simp [spectralTransportMatrix, f, D', Unitary.conjStarAlgAut_apply]
  rw [hB, hAeq, ← map_mul, hcomm, map_mul]

theorem spectralTransportMatrix_comm
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (E F : Fin (n + 1) → ℝ) :
    spectralTransportMatrix hA E * spectralTransportMatrix hA F =
      spectralTransportMatrix hA F * spectralTransportMatrix hA E := by
  let f := Unitary.conjStarAlgAut ℂ
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hA.eigenvectorUnitary
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ E)
  let D' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ F)
  have hcomm : D * D' = D' * D := by
    change Matrix.diagonal (RCLike.ofReal ∘ E) * Matrix.diagonal (RCLike.ofReal ∘ F) =
      Matrix.diagonal (RCLike.ofReal ∘ F) * Matrix.diagonal (RCLike.ofReal ∘ E)
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hE : spectralTransportMatrix hA E = f D := by
    simp [spectralTransportMatrix, f, D, Unitary.conjStarAlgAut_apply]
  have hF : spectralTransportMatrix hA F = f D' := by
    simp [spectralTransportMatrix, f, D', Unitary.conjStarAlgAut_apply]
  rw [hE, hF, ← map_mul, hcomm, map_mul]

theorem spectralTransportMatrix_sub_norm_lt
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) {E : Fin (n + 1) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ i, dist (E i) (hA.eigenvalues i) < ε) :
    ‖spectralTransportMatrix hA E - A‖ < ε := by
  have hdiag : Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ E) =
      Matrix.diagonal (fun i => (E i : ℂ)) := by
    congr 1
  rw [spectralTransportMatrix, hdiag, l2_opNorm_spectralTransport_sub hA E]
  refine (pi_norm_lt_iff hε).mpr fun i => ?_
  simpa [Real.dist_eq, Real.norm_eq_abs] using hclose i

/-- Every bounded-time operator tube contains two commuting Hamiltonians with one common
eigenbasis but incompatible physical survival-fidelity first-return exponents. -/
theorem exists_sameEigenbasis_periodic_and_maximalPhysicalReturn_uniform_horizon
    (e : ℕ) (A : Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ) (hA : A.IsHermitian)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∃ (Bper Bmax : Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ)
      (Eper Emax : Fin (e + 3) → ℝ)
      (basis : Fin (e + 3) → Fin (e + 3) → ℂ),
      Bper.IsHermitian ∧ Bmax.IsHermitian ∧
      Bper * A = A * Bper ∧ Bmax * A = A * Bmax ∧ Bper * Bmax = Bmax * Bper ∧
      Function.Injective Eper ∧ Function.Injective Emax ∧
      IsOrthoEigenBasis Bper basis Eper ∧ IsOrthoEigenBasis Bmax basis Emax ∧
      HasPositiveProjectiveReturn Eper ∧
      (¬ KleinbockMargulis.VWA
        (anchoredGapRatioMap (sortedTuple Emax) 0 1
          (fun k : Fin (e + 1) => k.succ.succ))) ∧
      (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution Bper t - unitaryEvolution A t‖ < η) ∧
      (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution Bmax t - unitaryEvolution A t‖ < η) ∧
      ∀ Ω : Fin (e + 3) → ℂ,
        finiteComplexInner Ω Ω = 1 →
        (∀ j, finiteComplexInner (basis j) Ω ≠ 0) →
        ∀ {t₀ : ℝ}, 0 < t₀ →
          Tendsto
              (fun δ : ℝ => Real.log (orbitFidelityReturnTime Bper Ω t₀ δ) /
                Real.log (1 / δ))
              (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
            Tendsto
              (fun δ : ℝ => Real.log (orbitFidelityReturnTime Bmax Ω t₀ δ) /
                Real.log (1 / δ))
              (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
  have hradius : 0 < η / T := div_pos hη hT
  obtain ⟨Eper, hEperinj, hEperclose, hEperret⟩ :=
    exists_close_simpleSpectrum_hasPositiveProjectiveReturn (d := e + 2) (by omega)
      hA.eigenvalues hradius
  obtain ⟨Emax, hEmaxinj, hEmaxclose, hEmaxnv⟩ :=
    exists_close_simpleSpectrum_not_vwa_sortedGapRatio hA.eigenvalues hradius
  let Bper := spectralTransportMatrix hA Eper
  let Bmax := spectralTransportMatrix hA Emax
  let basis := spectralTransportEigenBasis hA
  have hBper : Bper.IsHermitian := isHermitian_spectralTransportMatrix hA Eper
  have hBmax : Bmax.IsHermitian := isHermitian_spectralTransportMatrix hA Emax
  have hcommper : Bper * A = A * Bper := spectralTransportMatrix_comm_original hA Eper
  have hcommmax : Bmax * A = A * Bmax := spectralTransportMatrix_comm_original hA Emax
  have hcommboth : Bper * Bmax = Bmax * Bper := spectralTransportMatrix_comm hA Eper Emax
  have hebper : IsOrthoEigenBasis Bper basis Eper := by
    simpa [Bper, basis, spectralTransportMatrix, Function.comp_def] using
      isOrthoEigenBasis_spectralTransport hA Eper
  have hebmax : IsOrthoEigenBasis Bmax basis Emax := by
    simpa [Bmax, basis, spectralTransportMatrix, Function.comp_def] using
      isOrthoEigenBasis_spectralTransport hA Emax
  have hnormper : ‖Bper - A‖ < η / T :=
    spectralTransportMatrix_sub_norm_lt hA hradius hEperclose
  have hnormmax : ‖Bmax - A‖ < η / T :=
    spectralTransportMatrix_sub_norm_lt hA hradius hEmaxclose
  have hcloseper : ∀ t : ℝ, |t| ≤ T →
      ‖unitaryEvolution Bper t - unitaryEvolution A t‖ < η := by
    intro t ht
    exact norm_unitaryEvolution_sub_lt_of_le_horizon hA hBper hT hnormper ht
  have hclosemax : ∀ t : ℝ, |t| ≤ T →
      ‖unitaryEvolution Bmax t - unitaryEvolution A t‖ < η := by
    intro t ht
    exact norm_unitaryEvolution_sub_lt_of_le_horizon hA hBmax hT hnormmax ht
  refine ⟨Bper, Bmax, Eper, Emax, basis, hBper, hBmax, hcommper, hcommmax, hcommboth,
    hEperinj, hEmaxinj, hebper, hebmax, hEperret, hEmaxnv, hcloseper, hclosemax, ?_⟩
  intro Ω hΩ hcyc t₀ ht₀
  constructor
  · simpa using tendsto_log_orbitFidelityReturnTime_zero_of_hasPositiveProjectiveReturn
      (Equiv.refl (Fin (e + 3))) hebper hΩ hcyc hEperret ht₀
  · let ρ : Fin (e + 3) ≃ Fin (e + 3) := (Tuple.sort Emax).symm
    have hsortedInj : Function.Injective (sortedTuple Emax) := injective_sortedTuple hEmaxinj
    have hgap : Emax (ρ.symm 0) < Emax (ρ.symm 1) := by
      change sortedTuple Emax 0 < sortedTuple Emax 1
      refine lt_of_le_of_ne (monotone_sortedTuple Emax (by simp)) ?_
      intro heq
      exact zero_ne_one (hsortedInj heq)
    have hnv : ¬ KleinbockMargulis.VWA
        (anchoredGapRatioMap (fun i => Emax (ρ.symm i)) 0 1
          (fun k : Fin (e + 1) => k.succ.succ)) := by
      exact hEmaxnv
    exact tendsto_log_orbitFidelityReturnTime ρ hebmax hΩ hcyc hgap hnv ht₀

end

end GaloisForLFunctions.HTGeometry
