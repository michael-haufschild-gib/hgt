import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathGenericityLaw
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw

/-!
# Generic recurrence geometry on a nearest-neighbour qudit path

This module turns generic maximal projective spectrum into the exact
recurrence consequence used by the unified recurrence paper.  In the full
trace-zero onsite-plus-edge Hamiltonian space of an open `n`-site, `q`-level
path, the dense residual full-measure maximal set has no nonzero balanced
integer energy relation and has exactly `q ^ n - 1` independent anchored
phase directions. Its strict-return frequency is the exact Haar volume of a
`q ^ n - 1` dimensional phase box, while exact nonzero-time projective return
is absent.
-/

open Set SimpleGraph MeasureTheory Topology Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Generic static-path recurrence law.** For every open path of at least
two `q`-level sites, `q ≥ 2`, the full real trace-zero onsite-plus-edge
Hamiltonian space contains a dense residual full-measure set such that every
Hamiltonian in that set has zero nontrivial balanced integer energy kernel,
`q ^ n - 1` independent anchored phase directions, the exact corresponding
Haar return frequency, and no nonzero exact projective return. -/
theorem
    exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph =
          SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
      (letI : Fintype Z.PhysicalState := Z.physicalFintype
       letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
       let L := Z.tracelessLocalHamiltonianSubmodule
       let hL := Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
       let S := realHermitianSubmoduleMaximalSet L hL
       Dense S ∧ S ∈ residual (Fin (Module.finrank ℝ L) → ℝ) ∧
         volume Sᶜ = 0 ∧
         ∀ p ∈ S,
           let hH := realAffineMatrix_isHermitian
             0 (realMatrixSubmoduleGenerator L)
             Matrix.isHermitian_zero
             (realMatrixSubmoduleGenerator_isHermitian L hL) p
           MaximallyProjectiveEnergy hH.eigenvalues ∧
             ∀ reference : Z.PhysicalState,
               anchoredTemporalRank hH.eigenvalues reference = q ^ n - 1 ∧
               (∀ {ε : ℝ}, 0 < ε → ε < 2 →
                 Tendsto
                   (fun A =>
                     (finiteTorusPhaseProbabilityMeasure
                       (projectiveFrequency hH.eigenvalues reference) A :
                       Measure (UnitAddTorus
                         {i : Z.PhysicalState // i ≠ reference}))
                       (anchoredProjectiveReturnTarget ε))
                   atTop
                   (𝓝 (ENNReal.ofReal
                     (2 * Real.arcsin (ε / 2) / Real.pi) ^
                       (q ^ n - 1)))) ∧
               ∀ t : ℝ,
                 screwPhase
                   (projectiveFrequency hH.eigenvalues reference) t = 0 →
                 t = 0) := by
  obtain ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull⟩ :=
    exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure
      n q hn hq
  refine ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, ?_⟩
  intro p hp
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  let L := Z.tracelessLocalHamiltonianSubmodule
  let hL := Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
  let hH := realAffineMatrix_isHermitian
    0 (realMatrixSubmoduleGenerator L)
    Matrix.isHermitian_zero
    (realMatrixSubmoduleGenerator_isHermitian L hL) p
  have hmax : MaximallyProjectiveEnergy hH.eigenvalues := by
    unfold realHermitianSubmoduleMaximalSet at hp
    unfold realAffineHermitianMaximalSet at hp
    unfold polynomialHermitianMatrixMaximalSet at hp
    let hpoly :
        ((realAffineMatrixPolynomial
            0 (realMatrixSubmoduleGenerator L)).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).IsHermitian := by
      rw [eval_realAffineMatrixPolynomial]
      exact realAffineMatrix_isHermitian
        0 (realMatrixSubmoduleGenerator L)
        Matrix.isHermitian_zero
        (realMatrixSubmoduleGenerator_isHermitian L hL) p
    change MaximallyProjectiveEnergy hpoly.eigenvalues at hp
    have heigenvalues : hpoly.eigenvalues = hH.eigenvalues := by
      apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hpoly hH).2
      rw [eval_realAffineMatrixPolynomial]
    rw [heigenvalues] at hp
    exact hp
  refine ⟨hmax, ?_⟩
  intro reference
  have hstateCard : Fintype.card Z.spectral.State = q ^ n := by
    simpa [GoodObserverSpectralSystem.stateCard] using hstate
  have hphysicalCard : Fintype.card Z.PhysicalState = q ^ n := by
    rw [Z.realization.physicalCard_eq_stateCard]
    exact hstateCard
  refine ⟨?_, ?_, ?_⟩
  · rw [anchoredTemporalRank_eq_card_sub_one_of_maximallyProjective
      hH.eigenvalues hmax reference, hphysicalCard]
  · intro ε hε0 hε2
    simpa [hphysicalCard] using
      (maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency
        hH.eigenvalues hmax reference hε0 hε2)
  · apply hmax.no_nonzeroExactAnchoredReturn reference
    have hfour : 4 ≤ q ^ n := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
        _ ≤ q ^ n := Nat.pow_le_pow_left hq n
    omega

end

end GaloisForLFunctions.HTGeometry
