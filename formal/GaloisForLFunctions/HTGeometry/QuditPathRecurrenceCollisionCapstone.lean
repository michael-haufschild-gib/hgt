import GaloisForLFunctions.HTGeometry.QuditPathChainRecurrenceExponent
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity

/-!
# One local qudit path simultaneously saturates recurrence and collision laws

The exact Hermitian onsite-plus-nearest-neighbour coefficient space on an open qudit path escapes
every affine real spectral relation.  Parameterwise escape witnesses make maximal projectivity
generic in that same coefficient family.  Intersecting this event with the two metric-extremality
events gives one Hamiltonian draw with maximal rank, both sharp first-hit exponents, all positive-
weight collision and moment floors, and no nonzero exact projective return.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Generic maximality from relation-by-relation escape.**  A real linear Hermitian family need
not supply one preselected maximally projective witness.  It is enough that, for each nonzero
balanced real spectral character, some simple root packet escapes all relabellings.  Each integer
character then has a nonzero polynomial obstruction, and the countable exceptional union is null. -/
theorem volume_notMaximallyProjective_eq_zero_of_spectrumEscapesRealRelations
    {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P))) :
    (volume : Measure (Fin N → ℝ))
        {θ | ¬ MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} = 0 := by
  classical
  have hgeneric :=
    complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure_of_witness
      (matrixCharacteristicElementaryPolynomial (spectralGenericMatrix P))
      (fun k hbalanced hk => by
        have hbalancedR : ∑ i, (k i : ℝ) = 0 := by
          exact_mod_cast hbalanced
        have hkR : (fun i => (k i : ℝ)) ≠ 0 := by
          intro hzero
          apply hk
          funext i
          show k i = 0
          have hi := congrFun hzero i
          have hi' : (k i : ℝ) = 0 := by simpa using hi
          exact_mod_cast hi'
        obtain ⟨H, ⟨p, hp⟩, E, hEinj, hroot, hescape⟩ :=
          hS (fun i => (k i : ℝ)) hbalancedR hkR
        refine ⟨p, ?_⟩
        rw [eval_complexSpectralCoefficientObstructionPullback]
        have hcoefficient :
            ∀ j,
              MvPolynomial.eval₂ (RingHom.id ℂ)
                  (fun t => (p t : ℂ))
                  (matrixCharacteristicElementaryPolynomial
                    (spectralGenericMatrix P) j) =
                MvPolynomial.eval₂ (Rat.castHom ℂ)
                  (fun a => (E a : ℂ))
                  (MvPolynomial.esymm (Fin D) ℚ (j.1 + 1)) := by
          intro j
          rw [eval_matrixCharacteristicElementaryPolynomial,
            map_spectralGenericMatrix_eq p, hp]
          exact matrixCharacteristicElementaryCoefficient_eq_rootPacket
            H (fun a => (E a : ℂ))
            (fun a b hab => hEinj (Complex.ofReal_injective hab))
            (fun i => hroot i) j
        simp_rw [hcoefficient]
        rw [eval₂_spectralRelationCoefficientPolynomial_complex_esymm,
          eval₂_spectralRelationOrbitPolynomial]
        have hreal : spectralRelationOrbitValue k E ≠ 0 :=
          (spectralRelationOrbitValue_ne_zero_iff k E).2 hescape
        intro hzero
        apply hreal
        apply Complex.ofReal_injective
        have hcast :
            ((spectralRelationOrbitValue k E : ℝ) : ℂ) =
              spectralRelationOrbitValueComplex k (fun a => (E a : ℂ)) := by
          unfold spectralRelationOrbitValue spectralRelationOrbitValueComplex
          push_cast
          rfl
        rw [hcast]
        exact hzero)
  have hbadEq :
      {θ : Fin N → ℝ | ¬ MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} =
        (polynomialMatrixProjectiveGenericSet (spectralGenericMatrix P))ᶜ := by
    ext θ
    exact not_congr (mem_genericSet_iff_maximallyProjective hP θ).symm
  rw [hbadEq]
  exact hgeneric.2.2

/-- **Every-chart same-Hamiltonian qudit-path recurrence--collision law.**  For arbitrary local
dimension, every nonempty preconnected open simple-spectrum chart of the exact Hermitian onsite-plus-
nearest-neighbour coefficient space has a common conull set on which one static Hamiltonian has
maximal projective rank, the two sharp return exponents, all positive-weight collision and moment
floors, and no nonzero exact anchored projective return. -/
theorem exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ e : ℕ, q ^ n = e + 3 ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin (e + 3))
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ)
        (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        (∃ U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
          IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP) ∧
        ∀ {U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ)},
          IsOpen U → IsPreconnected U → U.Nonempty →
          U ⊆ simpleEnsembleLocus hP →
          ∀ᵐ θ ∂volume, θ ∈ U →
            MaximallyProjectiveEnergy
                (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues ∧
            Tendsto
              (fun r : ℝ =>
                Real.log
                    (firstHit
                      (anchoredGapMap (2 * Real.pi)
                        (sortedEnsembleSpectrum hP θ) 0 Fin.succ) r) /
                  Real.log (1 / r))
              (𝓝[>] (0 : ℝ)) (𝓝 ((e + 2 : ℕ) : ℝ)) ∧
            Tendsto
              (fun r : ℝ =>
                Real.log
                    (firstHit
                      (anchoredGapRatioMap (sortedEnsembleSpectrum hP θ) 0 1
                        (fun k => k.succ.succ)) r) /
                  Real.log (1 / r))
              (𝓝[>] (0 : ℝ)) (𝓝 ((e + 1 : ℕ) : ℝ)) ∧
            (∀ weight : Fin (e + 3) → ℝ, (∀ i, 0 < weight i) →
              (∀ m : ℕ,
                fidelityReplicaCollisionMass weight
                    (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues m =
                  fidelityReplicaPermutationFloor weight m) ∧
              ∀ m : ℕ,
                Tendsto
                  (finiteSpectralSurvivalFidelityMean weight
                    (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues m)
                  atTop (𝓝 (fidelityReplicaPermutationFloor weight m : ℂ))) ∧
            ∀ t : ℝ,
              screwPhase
                  (projectiveFrequency
                    (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues 0) t = 0 →
                t = 0 := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily n q hn hq
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 3 := ⟨D - 3, by omega⟩
  letI := instP
  letI := instPd
  haveI := hNeZero
  refine ⟨e, hD, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hPHermitian, hprov,
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily, ?_⟩
  intro U hUopen hUconn hUne hUsimple
  have hDiscrete := ae_tendsto_log_firstHit_sortedGap
    (n := e + 2) (anchor := (0 : Fin (e + 3))) (ι := Fin.succ)
    (scale := 2 * Real.pi) (by omega) hPHermitian hfamily
    (Fin.succ_injective _) (fun k => Fin.succ_ne_zero k)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    hUopen hUconn hUne hUsimple
  have hWinding := ae_tendsto_log_firstHit_sortedGapRatio
    (n := e + 1) (anchor := (0 : Fin (e + 3))) (clock := (1 : Fin (e + 3)))
    (ι := fun k => k.succ.succ) (by omega) hPHermitian hfamily.toRealRelations
    (fun a b hab => Fin.succ_injective _ (Fin.succ_injective _ hab))
    (fun _ => Fin.succ_ne_zero _)
    (fun k => by
      have h1 : (1 : Fin (e + 3)) = Fin.succ (0 : Fin (e + 2)) := rfl
      rw [h1]
      intro hk
      exact Fin.succ_ne_zero k (Fin.succ_injective _ hk))
    (by exact zero_ne_one)
    hUopen hUconn hUne hUsimple
  have hmaxAE :
      ∀ᵐ θ : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ ∂volume,
        MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix hPHermitian θ).eigenvalues := by
    rw [ae_iff]
    exact volume_notMaximallyProjective_eq_zero_of_spectrumEscapesRealRelations
      hPHermitian hfamily.toRealRelations
  filter_upwards [hmaxAE, hDiscrete, hWinding] with θ hmax hdisc hwind hθU
  refine ⟨hmax, hdisc hθU, hwind hθU, ?_, ?_⟩
  · intro weight hweight
    exact ⟨
      (all_fidelityReplicaCollisionMass_eq_floor_iff hweight _).2 hmax,
      (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff hweight _).2 hmax⟩
  · exact hmax.no_nonzeroExactAnchoredReturn 0 (by simp)

end

end GaloisForLFunctions.HTGeometry
