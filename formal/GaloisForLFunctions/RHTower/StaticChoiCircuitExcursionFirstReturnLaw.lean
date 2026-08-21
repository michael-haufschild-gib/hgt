import GaloisForLFunctions.HTGeometry.ContinuousFirstReturnGapLaw
import GaloisForLFunctions.RHTower.StaticChoiContinuousHardGapLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

/-!
# Complete-circuit excursion first returns for one static Hamiltonian

The complete finite circuit-capture set is closed along a static Choi orbit.  Maximal projective
spectral rank makes returns to the identity Choi channel syndetic.  Consequently, every continuous
interval avoiding the complete circuit dictionary lies inside one genuine excursion whose
endpoints are consecutive visits to that entire dictionary.

This theorem converts a hard block into a literal first re-entry statement.  It does not supply a
Brown-scale onset estimate; that remains a separate local-ensemble problem.
-/

open Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem continuous_pureStateTraceDistance_comp
    {ι : Type*} [Fintype ι]
    (psi : ℝ → EuclideanSpace ℂ ι) (hpsi : Continuous psi)
    (phi : EuclideanSpace ℂ ι) :
    Continuous (fun t => pureStateTraceDistance (psi t) phi) := by
  unfold pureStateTraceDistance
  fun_prop

/-- The capture times of any finite pure-state target dictionary along a continuous orbit form a
closed subset of physical time. -/
theorem isClosed_finite_pureStateTraceDistance_captureTimeSet
    {ι C : Type*} [Fintype ι] [Fintype C]
    (psi : ℝ → EuclideanSpace ℂ ι) (hpsi : Continuous psi)
    (target : C → EuclideanSpace ℂ ι) (eps : ℝ) :
    IsClosed {t | ∃ c, pureStateTraceDistance (psi t) (target c) ≤ eps} := by
  rw [show {t | ∃ c, pureStateTraceDistance (psi t) (target c) ≤ eps} =
      ⋃ c, {t | pureStateTraceDistance (psi t) (target c) ≤ eps} by
    ext t
    simp]
  exact isClosed_iUnion_of_finite fun c =>
    isClosed_le (continuous_pureStateTraceDistance_comp psi hpsi (target c)) continuous_const

/-- Continuity of the projective pure-Choi orbit in physical time. -/
theorem continuous_projectivePureChoiVector
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    Continuous (fun t =>
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))) := by
  let F := fun x : Fin (d + 1) → UnitAddCircle =>
    WithLp.toLp 2 fun ij : Fin (d + 1) × Fin (d + 1) =>
      (if ij.1 = ij.2 then ((Real.sqrt (d + 1 : ℝ))⁻¹ : ℂ) else 0) *
        fourier 1 (x ij.1)
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hflow : Continuous (fun t =>
      zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const
    · change Continuous (fun t =>
        ((t * zeroProjectiveFrequency energy j / (2 * Real.pi) : ℝ) : UnitAddCircle))
      fun_prop
  convert hF.comp hflow using 1
  funext t
  ext ij
  by_cases hij : ij.1 = ij.2 <;> simp [F, hij]

/-- A maximally projective static Choi orbit returns near its initial channel in every interval of
one fixed finite length. -/
theorem maximallyProjective_pureChoiRecurrence_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ, ∃ t ∈ Icc a (a + B),
      pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < eps := by
  let delta := Real.sqrt 2 * eps
  let U := zeroAnchoredChoiRecurrenceTarget d delta
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdelta : 0 < delta := mul_pos hsqrt heps
  obtain ⟨B, hB, hhits⟩ :=
    denseAddOrbit_open_hits_syndetically
      (projectivePhysicalPhaseFlowHom energy)
      (denseRange_projectivePhysicalPhaseFlowHom energy hmax)
      (isOpen_zeroAnchoredChoiRecurrenceTarget d delta)
      (zeroAnchoredChoiRecurrenceTarget_nonempty d hdelta)
  refine ⟨B, hB, fun a => ?_⟩
  obtain ⟨t, ht, htU⟩ := hhits a
  change projectivePhysicalPhaseFlow energy t ∈ U at htU
  refine ⟨t, ht, ?_⟩
  let psi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let phi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))
  have hpsi : ‖psi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hphi : ‖phi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hdist : dist (pureStateDensity psi) (pureStateDensity phi) < delta := by
    rw [pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d),
      pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d)]
    simpa [U, zeroAnchoredChoiRecurrenceTarget] using htU
  rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
    psi phi hpsi hphi] at hdist
  dsimp [delta] at hdist
  nlinarith

/-- **Complete-circuit excursion first-return law.** A continuous hard block for the complete
finite circuit dictionary is contained in a genuine excursion between consecutive visits to that
dictionary. The same maximally projective Hamiltonian supplies the two bracketing visits. -/
theorem maximallyProjective_pureChoiCircuitTarget_consecutiveVisitGaps
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {epsn epsw : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) :
    ∃ mesh B : ℝ, 0 < mesh ∧ 0 ≤ B ∧ ∀ {W : ℝ}, 0 ≤ W →
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) < mesh / (W + mesh) →
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
        A0 ≤ u ∧ tExit ∈ Icc (u - B) u ∧
          tReturn ∈ Icc (u + W) (u + W + B) ∧
          (∃ w, pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tExit)))
            (target w) ≤ epsn) ∧
          (∃ w, pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tReturn)))
            (target w) ≤ epsn) ∧
          tExit < tReturn ∧ W ≤ tReturn - tExit ∧
          ∀ t ∈ Ioo tExit tReturn,
            ¬ ∃ w, pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
              (target w) ≤ epsn := by
  let orbit : ℝ → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) := fun t =>
    fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let capture : Set ℝ :=
    {t | ∃ w, pureStateTraceDistance (orbit t) (target w) ≤ epsn}
  have horbit : Continuous orbit := continuous_projectivePureChoiVector energy
  have hcapture : IsClosed capture :=
    isClosed_finite_pureStateTraceDistance_captureTimeSet orbit horbit target epsn
  obtain ⟨mesh, hmesh, hhard⟩ :=
    maximallyProjective_pureChoiCircuitTargets_late_hard_intervals
      energy hmax s target htarget hgap hepsn.le
  obtain ⟨B, hB, hrec⟩ :=
    maximallyProjective_pureChoiRecurrence_syndetic energy hmax hepsn
  refine ⟨mesh, B, hmesh, hB, ?_⟩
  intro W hW hpack A0 hA0
  obtain ⟨u, hu, huHard⟩ := hhard hW hpack A0 hA0
  have hpre : ∃ t ∈ Icc (u - B) u, t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u - B)
    refine ⟨t, ⟨ht.1, ?_⟩, identity, ?_⟩
    · linarith [ht.2]
    · dsimp only [orbit]
      rw [hidentity]
      exact htRec.le
  have hpost : ∃ t ∈ Icc (u + W) (u + W + B), t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u + W)
    refine ⟨t, ht, identity, ?_⟩
    dsimp only [orbit]
    rw [hidentity]
    exact htRec.le
  have havoid : ∀ t ∈ Icc u (u + W), t ∉ capture := by
    intro t ht htCapture
    obtain ⟨w, hw⟩ := htCapture
    exact (not_le_of_gt (huHard t ht w)) hw
  obtain ⟨tExit, tReturn, htExit, htReturn,
      htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩ :=
    exists_consecutive_mem_separated_by_avoided_Icc
      hcapture hW hpre hpost havoid
  exact ⟨u, tExit, tReturn, hu, htExit, htReturn,
    htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩

/-- **Explicit complete-circuit first-reentry gap.**  The same conclusion with the hard-block
width controlled by the inverse completed occupation and the exact projective Choi speed. -/
theorem maximallyProjective_pureChoiCircuitTarget_explicit_consecutiveVisitGap
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {epsn epsw W : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) (hW : 0 ≤ W)
    (hpack :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / projectiveChoiSpeed energy) /
          (W + (epsw - epsn) / projectiveChoiSpeed energy)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
      A0 ≤ u ∧ tExit ∈ Icc (u - B) u ∧
        tReturn ∈ Icc (u + W) (u + W + B) ∧
        (∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tExit)))
          (target w) ≤ epsn) ∧
        (∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tReturn)))
          (target w) ≤ epsn) ∧
        tExit < tReturn ∧ W ≤ tReturn - tExit ∧
        ∀ t ∈ Ioo tExit tReturn,
          ¬ ∃ w, pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
            (target w) ≤ epsn := by
  let orbit : ℝ → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) := fun t =>
    fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let capture : Set ℝ :=
    {t | ∃ w, pureStateTraceDistance (orbit t) (target w) ≤ epsn}
  have horbit : Continuous orbit := continuous_projectivePureChoiVector energy
  have hcapture : IsClosed capture :=
    isClosed_finite_pureStateTraceDistance_captureTimeSet orbit horbit target epsn
  obtain ⟨B, hB, hrec⟩ :=
    maximallyProjective_pureChoiRecurrence_syndetic energy hmax hepsn
  refine ⟨B, hB, ?_⟩
  intro A0 hA0
  obtain ⟨u, hu, huHard⟩ :=
    maximallyProjective_pureChoiCircuitTargets_explicit_late_hard_intervals
      energy hmax s target htarget hgap hepsn.le hW hpack A0 hA0
  have hpre : ∃ t ∈ Icc (u - B) u, t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u - B)
    refine ⟨t, ⟨ht.1, ?_⟩, identity, ?_⟩
    · linarith [ht.2]
    · dsimp only [orbit]
      rw [hidentity]
      exact htRec.le
  have hpost : ∃ t ∈ Icc (u + W) (u + W + B), t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u + W)
    refine ⟨t, ht, identity, ?_⟩
    dsimp only [orbit]
    rw [hidentity]
    exact htRec.le
  have havoid : ∀ t ∈ Icc u (u + W), t ∉ capture := by
    intro t ht htCapture
    obtain ⟨w, hw⟩ := htCapture
    exact (not_le_of_gt (huHard t ht w)) hw
  obtain ⟨tExit, tReturn, htExit, htReturn,
      htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩ :=
    exists_consecutive_mem_separated_by_avoided_Icc
      hcapture hW hpre hpost havoid
  exact ⟨u, tExit, tReturn, hu, htExit, htReturn,
    htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩

end RHTower
