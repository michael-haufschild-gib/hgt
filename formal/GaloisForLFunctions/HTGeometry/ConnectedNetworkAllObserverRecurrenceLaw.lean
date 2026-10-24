import GaloisForLFunctions.HTGeometry.ConnectedGraphSpectralAffineEscape
import GaloisForLFunctions.HTGeometry.QuditPathChainRecurrenceExponent
import GaloisForLFunctions.RHTower.StaticLocalAllObserverFirstReturnLaw

/-!
# Simultaneous observer recurrence on connected interaction networks

Almost every Hamiltonian in the full local Hermitian space of a connected
finite interaction graph obeys the exact continuous-time first-return law for
every finite matrix observer family, selected after the Hamiltonian. The
exceptional set is independent of the observers. The same theorem holds for
connected support-contained interaction hypergraphs and heterogeneous factors.

For coherence-graph capacity `r`, the exponent is `max(r - 1, 0) / 2`.
The subtraction accounts for the continuous clock; the factor one half
converts phase radius to squared Hilbert--Schmidt displacement.
-/

open Set Filter MeasureTheory Topology RHTower
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The affine maximal-spectrum set describes the actual affine matrix,
independently of the polynomial presentation used to prove genericity. -/
theorem mem_realAffineHermitianMaximalSet_iff
    {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (P : Fin N → Matrix I I ℂ)
    (hbase : base.IsHermitian) (hP : ∀ a, (P a).IsHermitian) (p : Fin N → ℝ) :
    p ∈ realAffineHermitianMaximalSet base P hbase hP ↔
      MaximallyProjectiveEnergy (realAffineMatrix_isHermitian base P hbase hP p).eigenvalues := by
  let hpoly : ((realAffineMatrixPolynomial base P).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact realAffineMatrix_isHermitian base P hbase hP p
  change MaximallyProjectiveEnergy hpoly.eigenvalues ↔ _
  have heq : hpoly.eigenvalues =
      (realAffineMatrix_isHermitian base P hbase hP p).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
    exact congrArg Matrix.charpoly (eval_realAffineMatrixPolynomial base P p)
  rw [heq]

/-- One maximal-spectrum witness and real spectral escape discharge both the
simple-spectrum condition and all observer arithmetic conditions almost everywhere. -/
theorem ae_simple_maximal_universalObserverLaw
    {N D : ℕ} [NeZero N] {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian)
    (hescape : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    (p₀ : Fin N → ℝ)
    (hmax₀ : MaximallyProjectiveEnergy
      (isHermitian_spectralEnsembleMatrix hP p₀).eigenvalues) :
    ∀ᵐ p, p ∈ simpleEnsembleLocus hP ∧
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP p).eigenvalues ∧
      HasUniversalFiniteObserverFirstReturnLaw (sortedEnsembleSpectrum hP p) := by
  have heig : ∀ p,
      (realAffineMatrix_isHermitian 0 P Matrix.isHermitian_zero hP p).eigenvalues =
        (isHermitian_spectralEnsembleMatrix hP p).eigenvalues := by
    intro p
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
    exact congrArg Matrix.charpoly (realAffineMatrix_zero_eq_spectralEnsembleMatrix P p)
  have hmaxAffine : MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian 0 P Matrix.isHermitian_zero hP p₀).eigenvalues := by
    rw [heig]
    exact hmax₀
  have hnull := (realAffineHermitianMaximalSet_dense_residual_fullMeasure
    0 P Matrix.isHermitian_zero hP p₀ hmaxAffine).2.2
  have haeMax : ∀ᵐ p, p ∈ realAffineHermitianMaximalSet 0 P Matrix.isHermitian_zero hP :=
    ae_iff.mpr hnull
  filter_upwards [haeMax, ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus hP hescape]
    with p hp hobs
  have hmax := (mem_realAffineHermitianMaximalSet_iff
    0 P Matrix.isHermitian_zero hP p).mp hp
  rw [heig] at hmax
  exact ⟨hmax.injective, hmax, hobs hmax.injective⟩

/-- Canonical coordinates of an escaping Hermitian submodule inherit one
common conull event for all finite observers. Both mathematical inputs are
discharged below for the complete graph-local and hypergraph-local spaces. -/
theorem exists_submodule_ae_universalObserverLaw
    {I : Type} [Fintype I] [DecidableEq I] (hcard : 2 ≤ Fintype.card I)
    (L : Submodule ℝ (Matrix I I ℂ))
    (hself : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    (hescape : SpectrumEscapesAffineRelations (L : Set (Matrix I I ℂ)))
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (hmem : H ∈ L)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) :
    ∃ (e : I ≃ Fin (Fintype.card I))
      (P : Fin (Module.finrank ℝ L) → Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ)
      (hP : ∀ a, (P a).IsHermitian),
      (∀ a, P a = Matrix.reindex e e (realMatrixSubmoduleGenerator L a)) ∧
      ∀ᵐ p, p ∈ simpleEnsembleLocus hP ∧
        MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP p).eigenvalues ∧
        HasUniversalFiniteObserverFirstReturnLaw (sortedEnsembleSpectrum hP p) := by
  classical
  let e := Fintype.equivFin I
  let P : Fin (Module.finrank ℝ L) →
      Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
    fun a => Matrix.reindex e e (realMatrixSubmoduleGenerator L a)
  have hP : ∀ a, (P a).IsHermitian := fun a =>
    (Matrix.isHermitian_reindex_iff e).mpr
      (realMatrixSubmoduleGenerator_isHermitian L hself a)
  haveI : NeZero (Module.finrank ℝ L) := by
    obtain ⟨K, hKmem, hKne⟩ := exists_ne_zero_of_spectrumEscapes hcard hescape
    have hpos : 0 < Module.finrank ℝ L :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨K, hKmem⟩, fun h0 => hKne (congrArg Subtype.val h0)⟩
    exact ⟨by omega⟩
  have hfamily : SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)) := by
    refine hescape.ofSubmodule.reindex e ?_
    rintro M ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    ext i j
    simp [spectralEnsembleMatrix, realAffineMatrix, P, Matrix.reindex,
      Matrix.sum_apply, Matrix.smul_apply]
  obtain ⟨p₀, hp₀⟩ := exists_canonicalReindexedCoordinate_of_mem_submodule
    L e P (fun _ => rfl) H hmem
  have hmax₀ : MaximallyProjectiveEnergy
      (isHermitian_spectralEnsembleMatrix hP p₀).eigenvalues := by
    refine maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket _ _
      (fun j => hH.eigenvalues (e.symm j)) (maximallyProjectiveEnergy_equiv e.symm hmax) ?_
    intro j
    rw [hp₀, matrixCharpolyRelation_reindex]
    exact hermitianEigenvalue_matrixCharpolyRelation H hH (e.symm j)
  exact ⟨e, P, hP, fun _ => rfl,
    ae_simple_maximal_universalObserverLaw hP hfamily.toRealRelations p₀ hmax₀⟩

/-- Schrödinger and Heisenberg phase conventions have the same weighted
survival fidelity. -/
theorem norm_observerPhaseAmplitude_eq_spectralReturnAmplitude
    {D : ℕ} (E w : Fin D → ℝ) (t : ℝ) :
    ‖projectiveWeightedPhaseAmplitude w (finiteObserverHamiltonianVertexPhase t E)‖ =
      ‖spectralReturnAmplitude E w t‖ := by
  have hc : (starRingEnd ℂ)
      (projectiveWeightedPhaseAmplitude w (finiteObserverHamiltonianVertexPhase t E)) =
        spectralReturnAmplitude E w t := by
    simp only [projectiveWeightedPhaseAmplitude, spectralReturnAmplitude,
      finiteObserverHamiltonianVertexPhase, map_sum, map_mul, Complex.conj_ofReal,
      ← Complex.exp_conj, Complex.conj_I, Complex.ofReal_neg]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring
  rw [← hc]
  exact (norm_star _).symm

/-- Every normalized pure state inherits the exact fidelity-deficit exponent
from the universal matrix-observer law, including proper spectral supports. -/
theorem universalObserver_pureState_fidelityReturn
    {D : ℕ} {E : Fin D → ℝ}
    (h : HasUniversalFiniteObserverFirstReturnLaw E)
    (psi : Fin D → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ (2 : ℕ) = 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (fidelityReturnTime E (fun i => ‖psi i‖ ^ (2 : ℕ)) t₀ delta) /
        Real.log (1 / delta))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((pureStateSpectralSupport psi).card - 2 : ℕ) / 2 : ℝ)) := by
  classical
  have hsupport : (pureStateSpectralSupport psi).Nonempty := by
    by_contra hn
    have hz : ∀ i, psi i = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, by simp [pureStateSpectralSupport, hi]⟩
    have hbad : (0 : ℝ) = 1 := by simpa [hz] using hpsi
    exact zero_ne_one hbad
  have hscaled := tendsto_log_returnTime_scaled (c := 2) (by norm_num)
    (h.pureState psi hsupport ht₀)
  have hsignal (t : ℝ) :
      finiteQuantumObserverPhaseEnergy (fun _ : Fin 1 => 1)
        (finiteObserverHamiltonianVertexPhase t E)
        (fun _ => pureStateObserverMatrix psi) =
          2 * spectralReturnDeficit E (fun i => ‖psi i‖ ^ (2 : ℕ)) t := by
    rw [← finiteQuantumObserverDistanceSq_eq_phaseEnergy,
      pureStateObserver_distanceSq_eq_two_mul_fidelityDeficit psi hpsi _
        (finiteObserverHamiltonianVertexPhase_norm t E),
      norm_observerPhaseAmplitude_eq_spectralReturnAmplitude]
    rfl
  have htime (delta : ℝ) :
      finiteQuantumObserverReturnTime (fun _ : Fin 1 => 1)
        (fun _ => pureStateObserverMatrix psi) E t₀ (2 * delta) =
          fidelityReturnTime E (fun i => ‖psi i‖ ^ (2 : ℕ)) t₀ delta := by
    unfold finiteQuantumObserverReturnTime scalarSignalReturnTime fidelityReturnTime
    congr 1
    ext t
    simp only [scalarSignalReturnSet, fidelityReturnSet, Set.mem_setOf_eq, hsignal]
    constructor <;> rintro ⟨ht, hδ⟩ <;> exact ⟨ht, by linarith only [hδ]⟩
  simpa only [htime] using hscaled

/-- Every connected finite interaction graph, with arbitrary site dimensions
at least two, has a conull set in its full local coefficient space on which
all finite matrix observers obey the exact continuous-time exponent law. -/
theorem connectedGraph_ae_universalObserverFirstReturnLaw
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v)) :
    ∃ (e : (∀ v, A v) ≃ Fin (Fintype.card (∀ v, A v)))
      (P : Fin (Module.finrank ℝ (siteFactorLocalSubmodule A G)) →
        Matrix (Fin (Fintype.card (∀ v, A v))) (Fin (Fintype.card (∀ v, A v))) ℂ)
      (hP : ∀ a, (P a).IsHermitian),
      (∀ a, P a = Matrix.reindex e e (realMatrixSubmoduleGenerator (siteFactorLocalSubmodule A G) a)) ∧
      ∀ᵐ p, p ∈ simpleEnsembleLocus hP ∧
        MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP p).eigenvalues ∧
        HasUniversalFiniteObserverFirstReturnLaw (sortedEnsembleSpectrum hP p) := by
  classical
  letI (v : V) : Nontrivial (A v) := Fintype.one_lt_card_iff_nontrivial.mp (by have := hA v; omega)
  letI : Inhabited V := Classical.inhabited_of_nonempty inferInstance
  have hcard : 2 ≤ Fintype.card (∀ v, A v) :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨H, hH, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_siteFactorLocalSubmodule G hG A hA
  exact exists_submodule_ae_universalObserverLaw hcard (siteFactorLocalSubmodule A G)
    (siteFactorLocalSubmodule_le_selfAdjoint A G)
    (connectedGraph_spectrumEscapesAffineRelations G hG A hA) H hH hmem hmax

/-- Connected support-contained hypergraph interactions have the same
simultaneous observer law in their full Hermitian coefficient space. -/
theorem connectedHypergraph_ae_universalObserverFirstReturnLaw
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v))
    (𝔥 : Finset (Finset V)) (hconn : (twoSection 𝔥).Connected) :
    ∃ (e : (∀ v, A v) ≃ Fin (Fintype.card (∀ v, A v)))
      (P : Fin (Module.finrank ℝ (hypergraphLocalSubmodule A 𝔥)) →
        Matrix (Fin (Fintype.card (∀ v, A v))) (Fin (Fintype.card (∀ v, A v))) ℂ)
      (hP : ∀ a, (P a).IsHermitian),
      (∀ a, P a = Matrix.reindex e e (realMatrixSubmoduleGenerator (hypergraphLocalSubmodule A 𝔥) a)) ∧
      ∀ᵐ p, p ∈ simpleEnsembleLocus hP ∧
        MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP p).eigenvalues ∧
        HasUniversalFiniteObserverFirstReturnLaw (sortedEnsembleSpectrum hP p) := by
  classical
  letI (v : V) : Nontrivial (A v) := Fintype.one_lt_card_iff_nontrivial.mp (by have := hA v; omega)
  letI : Inhabited V := Classical.inhabited_of_nonempty inferInstance
  have hcard : 2 ≤ Fintype.card (∀ v, A v) :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨H, hH, hmem, hmax⟩ :=
    exists_maximallyProjective_mem_hypergraphLocalSubmodule A hA 𝔥 hconn
  exact exists_submodule_ae_universalObserverLaw hcard (hypergraphLocalSubmodule A 𝔥)
    (hypergraphLocalSubmodule_le_selfAdjoint A 𝔥)
    (connectedHypergraph_spectrumEscapesAffineRelations A 𝔥 hconn hA) H hH hmem hmax

end

end GaloisForLFunctions.HTGeometry
