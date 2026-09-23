import GaloisForLFunctions.HTGeometry.QuditPathNoncommutingLocalWitness
import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw
import GaloisForLFunctions.HTGeometry.ReturnTimeThresholdComparisonLaw
import GaloisForLFunctions.RHTower.FiniteLocalizedSpectralSupportRecurrenceLaw
import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphExtremalityLaw
import GaloisForLFunctions.RHTower.FiniteQuantumObserverPostExitRateDistortionLaw
import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherence

open Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem exists_canonicalReindexedCoordinate_of_mem_submodule
    {D : ℕ} {Physical : Type} [Fintype Physical]
    (L : Submodule ℝ (Matrix Physical Physical ℂ))
    (eSt : Physical ≃ Fin D)
    (P : Fin (Module.finrank ℝ L) → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ a, P a = Matrix.reindex eSt eSt (realMatrixSubmoduleGenerator L a))
    (H : Matrix Physical Physical ℂ) (hH : H ∈ L) :
    ∃ p, spectralEnsembleMatrix P p = Matrix.reindex eSt eSt H := by
  classical
  obtain ⟨p, hp⟩ := exists_realAffineMatrix_eq_of_mem_submodule L H hH
  refine ⟨p, ?_⟩
  rw [← realAffineMatrix_zero_eq_spectralEnsembleMatrix]
  calc
    realAffineMatrix 0 P p =
        Matrix.reindex eSt eSt
          (realAffineMatrix 0 (realMatrixSubmoduleGenerator L) p) := by
      ext i j
      simp [realAffineMatrix, hP, Matrix.reindex]
    _ = Matrix.reindex eSt eSt H := congrArg (Matrix.reindex eSt eSt) hp

/-- One shifted arbitrary-qudit path Hamiltonian, chosen before every finite observer, obeys the
exact coherence-graph first-return exponent simultaneously for all observers. -/
theorem exists_quditPath_universalObserverFirstReturnLaw (N Q : ℕ) :
    ∃ D : ℕ, (Q + 2) ^ (N + 2) = D ∧ 4 ≤ D ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin (N + 2)),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph (N + 2)) ∧
      T.HasNoncommutingOnsiteEdgePair ∧
      ∃ (eSt : Physical ≃ Fin D)
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin D) (Fin D) ℂ)
        (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        ∃ theta : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ,
          theta ∈ simpleEnsembleLocus hP ∧
          HasUniversalFiniteObserverFirstReturnLaw
            (sortedEnsembleSpectrum hP theta) := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      hpair, eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily_with_noncommutingPair
      (N + 2) (Q + 2) (by omega) (by omega)
  letI := instP
  letI := instPd
  haveI := hNeZero
  obtain ⟨U, hUopen, hUconn, hUne, hUsimple⟩ :=
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily
  have hae := ae_hasUniversalFiniteObserverFirstReturnLaw
    hPHermitian hfamily.toRealRelations hUopen hUconn hUne hUsimple
  let bad := {theta ∈ U |
    ¬ HasUniversalFiniteObserverFirstReturnLaw
      (sortedEnsembleSpectrum hPHermitian theta)}
  have hbad : volume bad = 0 := by
    rw [MeasureTheory.ae_iff] at hae
    simpa only [bad, Classical.not_imp] using hae
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUne
  have hdiff : volume (U \ bad) = volume U := measure_sdiff_null hbad
  have hdiffNe : volume (U \ bad) ≠ 0 := by
    rw [hdiff]
    exact hUpos.ne'
  obtain ⟨theta, hthetaU, hthetaNotBad⟩ := nonempty_of_measure_ne_zero hdiffNe
  have hthetaUniversal : HasUniversalFiniteObserverFirstReturnLaw
      (sortedEnsembleSpectrum hPHermitian theta) := by
    by_contra hfail
    exact hthetaNotBad ⟨hthetaU, hfail⟩
  exact ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
    hpair, eSt, hNeZero, P, hPHermitian, hprov, theta, hUsimple hthetaU,
    hthetaUniversal⟩

/-- Exact selected-Hamiltonian presentation: first generator is a literal onsite term, second is a
literal elementary edge term, both have coefficient one, and their commutator is nonzero. -/
def HasUnitNoncommutingOnsiteEdgePresentation
    {D : ℕ} {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical]
    (T : RootedTensorTree Physical Observer) (eSt : Physical ≃ Fin D)
    {m : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (theta : Fin m → ℝ) : Prop :=
  ∃ site A B pA pB,
    T.IsOneSite site A ∧
    T.IsElementaryEdgeTerm B ∧
    A.IsHermitian ∧ B.IsHermitian ∧
    A ∈ T.hermitianLocalHamiltonianSubmodule ∧
    B ∈ T.hermitianLocalHamiltonianSubmodule ∧
    A * B ≠ B * A ∧
    spectralEnsembleMatrix P pA = Matrix.reindex eSt eSt A ∧
    spectralEnsembleMatrix P pB = Matrix.reindex eSt eSt B ∧
    spectralEnsembleMatrix
        (Fin.cons (Matrix.reindex eSt eSt A)
          (Fin.cons (Matrix.reindex eSt eSt B) P))
        (Fin.cons 1 (Fin.cons 1 fun i => theta i - pA i - pB i)) =
      spectralEnsembleMatrix P theta

/-- Static-local arbitrary-qudit path capstone.  One simple Hamiltonian, with a literal
noncommuting onsite/edge pair retained at unit coefficients, obeys every finite observer's exact
coherence-graph first-return exponent. -/
theorem exists_quditPath_staticLocalUniversalObserverFirstReturnLaw (N Q : ℕ) :
    ∃ D : ℕ, (Q + 2) ^ (N + 2) = D ∧ 4 ≤ D ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin (N + 2)),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph (N + 2)) ∧
      ∃ (eSt : Physical ≃ Fin D)
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin D) (Fin D) ℂ)
        (hP : ∀ a, (P a).IsHermitian)
        (theta : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        theta ∈ simpleEnsembleLocus hP ∧
        HasUniversalFiniteObserverFirstReturnLaw
          (sortedEnsembleSpectrum hP theta) ∧
        HasUnitNoncommutingOnsiteEdgePresentation T eSt P theta := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      hpair, eSt, hNeZero, P, hP, hprov, theta, hthetaSimple, hthetaUniversal⟩ :=
    exists_quditPath_universalObserverFirstReturnLaw N Q
  letI := instP
  letI := instPd
  obtain ⟨site, A, B, hAone, hBedge, hAHermitian, hBHermitian,
      hAmem, hBmem, hcomm⟩ := hpair
  obtain ⟨pA, hpA⟩ := exists_canonicalReindexedCoordinate_of_mem_submodule
    T.hermitianLocalHamiltonianSubmodule eSt P hprov A hAmem
  obtain ⟨pB, hpB⟩ := exists_canonicalReindexedCoordinate_of_mem_submodule
    T.hermitianLocalHamiltonianSubmodule eSt P hprov B hBmem
  refine ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hP, theta, hprov, hthetaSimple, hthetaUniversal, ?_⟩
  refine ⟨site, A, B, pA, pB, hAone, hBedge, hAHermitian, hBHermitian,
    hAmem, hBmem, hcomm, hpA, hpB, ?_⟩
  exact spectralEnsembleMatrix_cons_two_compensated
    (Matrix.reindex eSt eSt A) (Matrix.reindex eSt eSt B)
    P theta pA pB hpA hpB

/-- Density-matrix specialization: one matrix observer inherits the exact capacity exponent. -/
theorem HasUniversalFiniteObserverFirstReturnLaw.singleMatrix
    {d : ℕ} {energy : Fin d → ℝ}
    (h : HasUniversalFiniteObserverFirstReturnLaw energy)
    (B : Matrix (Fin d) (Fin d) ℂ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (finiteQuantumObserverReturnTime (fun _ : Fin 1 => 1)
            (fun _ => B) energy t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((Fintype.card
        (graphNonRoot (finiteObserverCoherenceGraph
          (fun _ : Fin 1 => 1) (fun _ => B))) - 1 : ℕ) : ℝ) / 2)) := by
  exact h 1 (fun _ => 1) (fun _ => B) (fun _ => by norm_num) ht₀

/-- Rank-one density matrix of a pure state in the energy basis. -/
def pureStateObserverMatrix {d : ℕ} (psi : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => psi i * star (psi j)

/-- Exact nonzero spectral support of a pure state. -/
def pureStateSpectralSupport {d : ℕ} (psi : Fin d → ℂ) : Finset (Fin d) :=
  Finset.univ.filter fun i => psi i ≠ 0

theorem finiteObserverUnionWeight_pureStateObserverMatrix
    {d : ℕ} (psi : Fin d → ℂ) (i j : Fin d) :
    finiteObserverUnionWeight (fun _ : Fin 1 => 1)
        (fun _ => pureStateObserverMatrix psi) i j =
      ‖psi i‖ ^ (2 : ℕ) * ‖psi j‖ ^ (2 : ℕ) := by
  rw [finiteObserverUnionWeight]
  simp [pureStateObserverMatrix, mul_pow]

/-- A pure-state observer sees the complete graph on its exact support and no other edge. -/
theorem pureStateObserver_coherenceGraph_eq_localizedSupport
    {d : ℕ} (psi : Fin d → ℂ) :
    finiteObserverCoherenceGraph (fun _ : Fin 1 => 1)
        (fun _ => pureStateObserverMatrix psi) =
      finiteLocalizedSpectralSupportGraph (pureStateSpectralSupport psi) := by
  ext i j
  rw [finiteObserverCoherenceGraph_adj]
  change (i ≠ j ∧
      (0 < finiteObserverUnionWeight (fun _ : Fin 1 => 1)
          (fun _ => pureStateObserverMatrix psi) i j ∨
       0 < finiteObserverUnionWeight (fun _ : Fin 1 => 1)
          (fun _ => pureStateObserverMatrix psi) j i)) ↔
    i ≠ j ∧ i ∈ pureStateSpectralSupport psi ∧
      j ∈ pureStateSpectralSupport psi
  rw [finiteObserverUnionWeight_pureStateObserverMatrix,
    finiteObserverUnionWeight_pureStateObserverMatrix]
  constructor
  · rintro ⟨hij, hpos | hpos⟩
    · have hiNorm : ‖psi i‖ ≠ 0 := by
        intro hi
        simp [hi] at hpos
      have hjNorm : ‖psi j‖ ≠ 0 := by
        intro hj
        simp [hj] at hpos
      exact ⟨hij, by simpa [pureStateSpectralSupport] using hiNorm,
        by simpa [pureStateSpectralSupport] using hjNorm⟩
    · have hjNorm : ‖psi j‖ ≠ 0 := by
        intro hj
        simp [hj] at hpos
      have hiNorm : ‖psi i‖ ≠ 0 := by
        intro hi
        simp [hi] at hpos
      exact ⟨hij, by simpa [pureStateSpectralSupport] using hiNorm,
        by simpa [pureStateSpectralSupport] using hjNorm⟩
  · rintro ⟨hij, hi, hj⟩
    have hiNorm : 0 < ‖psi i‖ := by
      rw [norm_pos_iff]
      simpa [pureStateSpectralSupport] using hi
    have hjNorm : 0 < ‖psi j‖ := by
      rw [norm_pos_iff]
      simpa [pureStateSpectralSupport] using hj
    exact ⟨hij, Or.inl (mul_pos (sq_pos_of_pos hiNorm) (sq_pos_of_pos hjNorm))⟩

/-- Exact pure-projector identity: Hilbert--Schmidt displacement is twice survival-fidelity loss. -/
theorem pureStateObserver_distanceSq_eq_two_mul_fidelityDeficit
    {d : ℕ} (psi : Fin d → ℂ)
    (hpsi : ∑ i, ‖psi i‖ ^ (2 : ℕ) = 1)
    (z : Fin d → ℂ) (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverDistanceSq (fun _ : Fin 1 => 1) z
        (fun _ => pureStateObserverMatrix psi) =
      2 * (1 - ‖projectiveWeightedPhaseAmplitude
        (fun i => ‖psi i‖ ^ (2 : ℕ)) z‖ ^ (2 : ℕ)) := by
  have hpair :
      finiteQuantumObserverDistanceSq (fun _ : Fin 1 => 1) z
          (fun _ => pureStateObserverMatrix psi) =
        projectiveWeightedPairwiseEnergy (fun i => ‖psi i‖ ^ (2 : ℕ)) z := by
    rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy]
    unfold finiteQuantumObserverPhaseEnergy projectiveWeightedPairwiseEnergy
    simp_rw [finiteObserverUnionWeight_pureStateObserverMatrix psi]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [finiteQuantumObserverPhase]
    have hrewrite : z i * star (z j) - 1 = (z i - z j) * star (z j) := by
      rw [sub_mul]
      have hj : z j * star (z j) = 1 := by
        change z j * (starRingEnd ℂ) (z j) = 1
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit j]
        norm_num
      rw [hj]
    rw [hrewrite, norm_mul, norm_star, hunit j, mul_one]
  rw [hpair, projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    (fun i => ‖psi i‖ ^ (2 : ℕ)) z hpsi hunit]

/-- Pure-state specialization: exact exponent is half of support size minus two, including all
ambient isolated energy sectors. -/
theorem HasUniversalFiniteObserverFirstReturnLaw.pureState
    {d : ℕ} {energy : Fin d → ℝ}
    (h : HasUniversalFiniteObserverFirstReturnLaw energy)
    (psi : Fin d → ℂ)
    (hsupport : (pureStateSpectralSupport psi).Nonempty)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (finiteQuantumObserverReturnTime (fun _ : Fin 1 => 1)
            (fun _ => pureStateObserverMatrix psi) energy t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((pureStateSpectralSupport psi).card - 2 : ℕ) / 2 : ℝ)) := by
  have hraw := h.singleMatrix (pureStateObserverMatrix psi) ht₀
  have hcard : Fintype.card
      (graphNonRoot (finiteObserverCoherenceGraph (fun _ : Fin 1 => 1)
        (fun _ => pureStateObserverMatrix psi))) =
      (pureStateSpectralSupport psi).card - 1 := by
    rw [pureStateObserver_coherenceGraph_eq_localizedSupport,
      card_graphNonRoot]
    simpa only [Fintype.card_fin] using
      finiteLocalizedSpectralSupportGraph_rank
        (pureStateSpectralSupport psi) hsupport
  have hsub : (pureStateSpectralSupport psi).card - 1 - 1 =
      (pureStateSpectralSupport psi).card - 2 := by omega
  simpa only [hcard, hsub] using hraw

/-- Matrix displacement of one observer under diagonal Hamiltonian evolution. -/
def finiteQuantumObserverDisplacementMatrix
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    (finiteQuantumObserverPhase
      (finiteObserverHamiltonianVertexPhase t energy) i j - 1) * B i j

/-- Unsquared trace-radius signal for one matrix observer. -/
def finiteQuantumObserverNuclearSignal
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t : ℝ) : ℝ :=
  finiteMatrixNuclearNorm (finiteQuantumObserverDisplacementMatrix B energy t)

/-- First return in nuclear (trace) radius. -/
def finiteQuantumObserverNuclearReturnTime
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t₀ epsilon : ℝ) : ℝ :=
  scalarSignalReturnTime (finiteQuantumObserverNuclearSignal B energy) t₀ epsilon

/-- First return of squared nuclear displacement. -/
def finiteQuantumObserverNuclearSqReturnTime
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t₀ delta : ℝ) : ℝ :=
  scalarSignalReturnTime
    (fun t => finiteQuantumObserverNuclearSignal B energy t ^ (2 : ℕ)) t₀ delta

theorem finiteMatrixHilbertSchmidtSq_observerDisplacement
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t : ℝ) :
    finiteMatrixHilbertSchmidtSq
        (finiteQuantumObserverDisplacementMatrix B energy t) =
      finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
        (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B) := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq,
    finiteQuantumObserverPhaseEnergy]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show finiteObserverUnionWeight (fun _ : Fin 1 => 1) (fun _ => B) i j =
      ‖B i j‖ ^ (2 : ℕ) by simp [finiteObserverUnionWeight]]
  simp only [finiteQuantumObserverDisplacementMatrix, norm_mul, mul_pow]
  ring

theorem observerDisplacement_hilbertSchmidtSq_le_nuclearSq_le
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t : ℝ) :
    let reference := finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
      (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B)
    reference ≤ finiteQuantumObserverNuclearSignal B energy t ^ (2 : ℕ) ∧
      finiteQuantumObserverNuclearSignal B energy t ^ (2 : ℕ) ≤ d * reference := by
  dsimp only
  let K := finiteQuantumObserverDisplacementMatrix B energy t
  have hHS : finiteMatrixHilbertSchmidtSq K =
      finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
        (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B) :=
    finiteMatrixHilbertSchmidtSq_observerDisplacement B energy t
  have hHSnonneg : 0 ≤ finiteMatrixHilbertSchmidtSq K := by
    rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
    positivity
  constructor
  · rw [← hHS]
    exact finiteMatrixHilbertSchmidtSq_le_nuclearNorm_sq K
  · calc
      finiteQuantumObserverNuclearSignal B energy t ^ (2 : ℕ) ≤
          (K.rank : ℝ) * finiteMatrixHilbertSchmidtSq K :=
        finiteMatrixNuclearNorm_sq_le_rank_mul_hilbertSchmidtSq K
      _ ≤ (d : ℝ) * finiteMatrixHilbertSchmidtSq K := by
        have hrank : K.rank ≤ d := by
          simpa using Matrix.rank_le_card_width K
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hrank) hHSnonneg
      _ = d * finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
          (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B) := by
        rw [hHS]

/-- Every positive Hilbert--Schmidt threshold has a return after an arbitrary positive cutoff. -/
theorem eventually_singleMatrixObserverReturnSet_nonempty
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∀ᶠ delta : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (scalarSignalReturnSet
        (fun t => finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
          (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B))
        t₀ delta).Nonempty := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  let G := finiteObserverCoherenceGraph (fun _ : Fin 1 => 1)
    (fun _ i j => B i j)
  let mass := finiteObserverSelectedDirectedWeightMass G
    (fun _ : Fin 1 => 1) (fun _ i j => B i j)
  let C := 4 * (2 * Real.pi) ^ (2 : ℕ) * mass
  have hmass : 0 ≤ mass := by
    exact finiteObserverSelectedDirectedWeightMass_nonneg G
      (fun _ : Fin 1 => 1) (fun _ i j => B i j) (fun _ => by norm_num)
  have hC : 0 ≤ C := by positivity
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨Q, hQ⟩ := exists_nat_one_div_lt
    (div_pos hdelta hCp)
  let x : ℝ := 1 / ((Q : ℝ) + 1)
  have hxsmall : x < delta / (C + 1) := by simpa [x] using hQ
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ (show 0 < (Q : ℝ) + 1 by positivity)]
    norm_num
  have hxSq : x ^ (2 : ℕ) ≤ x := by nlinarith
  have hCdelta : (C + 1) * x < delta := by
    calc
      (C + 1) * x < (C + 1) * (delta / (C + 1)) :=
        mul_lt_mul_of_pos_left hxsmall hCp
      _ = delta := by field_simp [hCp.ne']
  have hboundCore : C * x ^ (2 : ℕ) < delta := by
    calc
      C * x ^ (2 : ℕ) ≤ C * x := mul_le_mul_of_nonneg_left hxSq hC
      _ < (C + 1) * x := by nlinarith
      _ < delta := hCdelta
  have hbound :
      4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) * mass < delta := by
    calc
      4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) * mass = C * x ^ (2 : ℕ) := by
        dsimp [C, x]
        ring
      _ < delta := hboundCore
  obtain ⟨n, hn0, _hnQ, _hexit0, hnAfter, _hnDeadline, _hexit, hdist⟩ :=
    exists_finiteQuantumObserver_postExit_fullCoherence_rateDistortion
      (fun _ : Fin 1 => 1) (fun _ i j => B i j) (fun _ => by norm_num)
      energy Q (t₀ + 1) t₀ 0 (by linarith) ht₀.le (by linarith) (by
        rw [show (0 : ℝ) ^ (2 : ℕ) = 0 by norm_num]
        change 0 ≤ finiteQuantumObserverDistanceSq (fun _ : Fin 1 => 1)
          (finiteObserverHamiltonianVertexPhase t₀ energy)
          (fun _ i j => B i j)
        rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy]
        exact finiteQuantumObserverPhaseEnergy_nonneg
          (fun _ : Fin 1 => 1)
          (finiteObserverHamiltonianVertexPhase t₀ energy)
          (fun _ i j => B i j) (fun _ => by norm_num))
  refine ⟨(n : ℝ) * (t₀ + 1), hnAfter.le, ?_⟩
  rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy] at hdist
  change finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
      (finiteObserverHamiltonianVertexPhase ((n : ℝ) * (t₀ + 1)) energy)
      (fun _ i j => B i j) ≤
    4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) * mass at hdist
  exact lt_of_le_of_lt hdist hbound

/-- Squared nuclear displacement has the same first-return exponent as squared
Hilbert--Schmidt displacement. -/
theorem HasUniversalFiniteObserverFirstReturnLaw.singleMatrixNuclearSq
    {d : ℕ} {energy : Fin d → ℝ}
    (h : HasUniversalFiniteObserverFirstReturnLaw energy)
    (hd : 0 < d) (B : Matrix (Fin d) (Fin d) ℂ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (finiteQuantumObserverNuclearSqReturnTime B energy t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((Fintype.card
        (graphNonRoot (finiteObserverCoherenceGraph
          (fun _ : Fin 1 => 1) (fun _ => B))) - 1 : ℕ) : ℝ) / 2)) := by
  let reference : ℝ → ℝ := fun t =>
    finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
      (finiteObserverHamiltonianVertexPhase t energy) (fun _ => B)
  let signal : ℝ → ℝ := fun t =>
    finiteQuantumObserverNuclearSignal B energy t ^ (2 : ℕ)
  have hcompare : ∀ t, (1 : ℝ) * reference t ≤ signal t ∧
      signal t ≤ (d : ℝ) * reference t := by
    intro t
    simpa only [one_mul, reference, signal] using
      observerDisplacement_hilbertSchmidtSq_le_nuclearSq_le B energy t
  have href := h.singleMatrix B ht₀
  have htransfer := tendsto_log_scalarSignalReturnTime_of_comparable
    signal reference (a := 1) (b := d) (t₀ := t₀)
    (by norm_num) (by exact_mod_cast hd) ht₀ hcompare
    (by simpa only [reference] using
      eventually_singleMatrixObserverReturnSet_nonempty B energy ht₀)
    (by simpa only [reference, finiteQuantumObserverReturnTime] using href)
  simpa only [signal, finiteQuantumObserverNuclearSqReturnTime] using htransfer

theorem finiteQuantumObserverNuclearReturnTime_eq_sq
    {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (t₀ : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    finiteQuantumObserverNuclearReturnTime B energy t₀ epsilon =
      finiteQuantumObserverNuclearSqReturnTime B energy t₀ (epsilon ^ (2 : ℕ)) := by
  unfold finiteQuantumObserverNuclearReturnTime
    finiteQuantumObserverNuclearSqReturnTime scalarSignalReturnTime
  apply congrArg sInf
  ext t
  simp only [scalarSignalReturnSet, Set.mem_setOf_eq]
  have hnonneg : 0 ≤ finiteQuantumObserverNuclearSignal B energy t :=
    finiteMatrixNuclearNorm_nonneg _
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨ht, (sq_lt_sq₀ hnonneg hepsilon.le).mpr he⟩
  · rintro ⟨ht, he⟩
    exact ⟨ht, (sq_lt_sq₀ hnonneg hepsilon.le).mp he⟩

theorem tendsto_sq_nhdsGT_zero :
    Tendsto (fun epsilon : ℝ => epsilon ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hbase : Tendsto (fun epsilon : ℝ => epsilon ^ (2 : ℕ))
        (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ (2 : ℕ))) := tendsto_id.pow 2
    simpa using hbase.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact sq_pos_of_pos (by simpa only [Set.mem_Ioi] using hepsilon)

/-- Replacing a squared threshold by its radius doubles the logarithmic exponent. -/
theorem tendsto_log_returnTime_square
    {returnTime : ℝ → ℝ} {alpha : ℝ}
    (h : Tendsto
      (fun delta : ℝ => Real.log (returnTime delta) / Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds alpha)) :
    Tendsto
      (fun epsilon : ℝ =>
        Real.log (returnTime (epsilon ^ (2 : ℕ))) / Real.log (1 / epsilon))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * alpha)) := by
  have hcomp := h.comp tendsto_sq_nhdsGT_zero
  have hscaled : Tendsto
      (fun epsilon : ℝ => (2 : ℝ) *
        (Real.log (returnTime (epsilon ^ (2 : ℕ))) /
          Real.log (1 / (epsilon ^ (2 : ℕ)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * alpha)) :=
    tendsto_const_nhds.mul hcomp
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with epsilon hepsilon hepsilonOne
  have hlogpos : 0 < Real.log (1 / epsilon) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hepsilon]
    linarith [hepsilonOne.2]
  have hlogsq : Real.log (1 / (epsilon ^ (2 : ℕ))) =
      2 * Real.log (1 / epsilon) := by
    rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    ring
  rw [hlogsq]
  field_simp [hlogpos.ne']

/-- Nuclear trace-radius specialization.  Unsquared radius doubles the squared
Hilbert--Schmidt exponent from `(capacity - 1)/2` to `capacity - 1`. -/
theorem HasUniversalFiniteObserverFirstReturnLaw.singleMatrixNuclear
    {d : ℕ} {energy : Fin d → ℝ}
    (h : HasUniversalFiniteObserverFirstReturnLaw energy)
    (hd : 0 < d) (B : Matrix (Fin d) (Fin d) ℂ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun epsilon : ℝ => Real.log
          (finiteQuantumObserverNuclearReturnTime B energy t₀ epsilon) /
        Real.log (1 / epsilon))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((Fintype.card
        (graphNonRoot (finiteObserverCoherenceGraph
          (fun _ : Fin 1 => 1) (fun _ => B))) - 1 : ℕ) : ℝ))) := by
  have hsq := h.singleMatrixNuclearSq hd B ht₀
  have hscaled := tendsto_log_returnTime_square hsq
  have hlimit : (2 : ℝ) *
      (((Fintype.card
        (graphNonRoot (finiteObserverCoherenceGraph
          (fun _ : Fin 1 => 1) (fun _ => B))) - 1 : ℕ) : ℝ) / 2) =
      ((Fintype.card
        (graphNonRoot (finiteObserverCoherenceGraph
          (fun _ : Fin 1 => 1) (fun _ => B))) - 1 : ℕ) : ℝ) := by ring
  rw [hlimit] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  rw [finiteQuantumObserverNuclearReturnTime_eq_sq B energy t₀ hepsilon]

end

end RHTower
