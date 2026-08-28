import GaloisForLFunctions.HTGeometry.QuditPathRecurrenceCollisionCapstone
import GaloisForLFunctions.HTGeometry.OrbitFidelityRecurrenceExponent

/-!
# Physical first-return law for a generic nearest-neighbour qudit path

Spectral affine escape is upgraded from a phase-winding statement to the physical survival-fidelity
first return of every cyclic state.  Instantiating that bridge on the complete Hermitian onsite-plus-
nearest-neighbour coefficient space gives one conull set of static path Hamiltonians simultaneously
carrying maximal projective rank, sharp discrete and continuous return exponents, exact collision
floors, long-time moment laws and absence of nonzero exact projective returns.

The final capstone shifts site number and local dimension by two.  It therefore has no side
hypotheses: every pair of natural-number inputs names a nontrivial finite local many-body system.
-/

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N e : ℕ} {P : Fin N → Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ}

/-- Spectral affine escape forces the sharp physical first-return exponent for every cyclic state. -/
theorem ae_tendsto_log_orbitFidelityReturnTime_sortedSpectrum [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ θ, θ ∈ U →
      ∀ Ω : Fin (e + 3) → ℂ,
        finiteComplexInner Ω Ω = 1 →
        (∀ j, finiteComplexInner
          (hermitianEigenBasis (spectralEnsembleMatrix P θ)
            (isHermitian_spectralEnsembleMatrix hP θ) j) Ω ≠ 0) →
        ∀ {t₀ : ℝ}, 0 < t₀ →
          Tendsto
            (fun δ : ℝ => Real.log
                (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
              Real.log (1 / δ))
            (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
  have hnonVwa := ae_not_vwa_of_volume_eq_zero
    (theoremA_sortedGapRatio (n := e + 1) (by omega) hP hS
      (anchor := (0 : Fin (e + 3))) (clock := (1 : Fin (e + 3)))
      (ι := fun k => k.succ.succ)
      (fun a b hab => Fin.succ_injective _ (Fin.succ_injective _ hab))
      (fun _ => Fin.succ_ne_zero _)
      (fun k => by
        have h1 : (1 : Fin (e + 3)) = Fin.succ (0 : Fin (e + 2)) := rfl
        rw [h1]
        intro hk
        exact Fin.succ_ne_zero k (Fin.succ_injective _ hk))
      (by exact zero_ne_one) hU hUc hUne hUsimple)
  filter_upwards [hnonVwa] with θ hθ
  intro hθU Ω hΩ hcyc t₀ ht₀
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  let ρ : Fin (e + 3) ≃ Fin (e + 3) := (Tuple.sort hH.eigenvalues).symm
  have hsortedInj : Function.Injective (sortedEnsembleSpectrum hP θ) :=
    injective_sortedEnsembleSpectrum hP (hUsimple hθU)
  have hgapSorted : sortedEnsembleSpectrum hP θ 0 < sortedEnsembleSpectrum hP θ 1 := by
    refine lt_of_le_of_ne (monotone_sortedTuple _ (by simp)) ?_
    intro heq
    exact zero_ne_one (hsortedInj heq)
  have hgap : hH.eigenvalues (ρ.symm 0) < hH.eigenvalues (ρ.symm 1) := by
    exact hgapSorted
  have hnv : ¬ KleinbockMargulis.VWA
      (anchoredGapRatioMap (fun i => hH.eigenvalues (ρ.symm i)) 0 1
        (fun m => m.succ.succ)) := by
    exact hθ hθU
  exact tendsto_log_orbitFidelityReturnTime ρ
    (isOrthoEigenBasis_hermitian _ hH) hΩ hcyc hgap hnv ht₀

/-- Full same-Hamiltonian recurrence law for an onsite-plus-nearest-neighbour qudit path. -/
def QuditPathPhysicalRecurrenceCollisionLaw (n q : ℕ) : Prop :=
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
            (∀ Ω : Fin (e + 3) → ℂ,
              finiteComplexInner Ω Ω = 1 →
              (∀ j, finiteComplexInner
                (hermitianEigenBasis (spectralEnsembleMatrix P θ)
                  (isHermitian_spectralEnsembleMatrix hP θ) j) Ω ≠ 0) →
              ∀ {t₀ : ℝ}, 0 < t₀ →
                Tendsto
                  (fun δ : ℝ => Real.log
                      (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
                    Real.log (1 / δ))
                  (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2))) ∧
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
                t = 0

/-- Every nontrivial finite path and local dimension obeys the full physical recurrence law. -/
theorem quditPathPhysicalRecurrenceCollisionLaw_of_two_le
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    QuditPathPhysicalRecurrenceCollisionLaw n q := by
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
  have hPhysical := ae_tendsto_log_orbitFidelityReturnTime_sortedSpectrum
    hPHermitian hfamily.toRealRelations hUopen hUconn hUne hUsimple
  have hmaxAE :
      ∀ᵐ θ : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ ∂volume,
        MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix hPHermitian θ).eigenvalues := by
    rw [ae_iff]
    exact volume_notMaximallyProjective_eq_zero_of_spectrumEscapesRealRelations
      hPHermitian hfamily.toRealRelations
  filter_upwards [hmaxAE, hDiscrete, hWinding, hPhysical] with
      θ hmax hdisc hwind hphysical hθU
  refine ⟨hmax, hdisc hθU, hwind hθU, hphysical hθU, ?_, ?_⟩
  · intro weight hweight
    exact ⟨
      (all_fidelityReplicaCollisionMass_eq_floor_iff hweight _).2 hmax,
      (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff hweight _).2 hmax⟩
  · exact hmax.no_nonzeroExactAnchoredReturn 0 (by simp)

/-- **Closed local-many-body capstone.**  Site number and local dimension are shifted by two, so
the theorem has no side hypotheses: every pair of natural numbers specifies a nontrivial open path
whose same generic Hamiltonian obeys all recurrence, physical first-return and collision laws. -/
theorem universalQuditPathPhysicalRecurrenceCollisionLaw (n q : ℕ) :
    QuditPathPhysicalRecurrenceCollisionLaw (n + 2) (q + 2) :=
  quditPathPhysicalRecurrenceCollisionLaw_of_two_le (n + 2) (q + 2) (by omega) (by omega)

end

end GaloisForLFunctions.HTGeometry
