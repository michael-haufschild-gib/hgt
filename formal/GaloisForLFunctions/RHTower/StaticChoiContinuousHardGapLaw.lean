import GaloisForLFunctions.HTGeometry.CompletedOccupationHardGapLaw
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw

/-!
# Completed occupation produces continuous static-Choi hard intervals

For one fixed maximally projective Hamiltonian, the one-sided completed-time mass of a widened
finite circuit target bounds how often its Choi orbit can enter a narrower target.  Uniform
continuity gives every narrow hit a positive time thickness; the completed occupation-to-hard-gap
law then forces arbitrarily late continuous intervals avoiding the entire circuit dictionary.

This is a same-Hamiltonian statement.  No ensemble redraw or independent fixed-time sampling is
used.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Projective diagonal Choi-density orbit in physical time. -/
def projectiveChoiDensityFlow {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
  uniformPhaseDensity (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))

theorem finiteClockPhasePoint_zeroProjectiveFrequency
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    finiteClockPhasePoint (zeroProjectiveFrequency energy) t =
      projectivePhysicalPhaseFlow energy t := by
  rfl

/-- One-sided phase sampling is exactly the physical-time preimage probability. -/
theorem windowProbability_projectivePhase_preimage
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    {A : Set (Fin d → UnitAddCircle)} (hA : MeasurableSet A) (T : ℝ) :
    (windowProbabilityMeasure T : Measure ℝ)
        {t | projectivePhysicalPhaseFlow energy t ∈ A} =
      (clockPhaseWindowLaw (zeroProjectiveFrequency energy) T :
        Measure (UnitAddTorus (Fin d))) A := by
  rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous _).measurable hA]
  congr 1

/-- One-sided physical-time occupation of a closed projective target is at most Haar mass. -/
theorem limsup_windowProbability_projectivePhase_preimage_le_volume
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {A : Set (Fin d → UnitAddCircle)} (hA : IsClosed A) :
    atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
      {t | projectivePhysicalPhaseFlow energy t ∈ A}) ≤ volume A := by
  have hmain := oneSided_closedTarget_limsup_le_volume
    (zeroProjectiveFrequency energy)
    (maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax) hA
  simpa only [windowProbability_projectivePhase_preimage energy hA.measurableSet] using hmain

theorem uniformContinuous_projectivePhysicalPhaseFlow
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    UniformContinuous (projectivePhysicalPhaseFlow energy) := by
  have hcont : Continuous ⇑(projectivePhysicalPhaseFlowHom energy) := by
    change Continuous (projectivePhysicalPhaseFlow energy)
    unfold projectivePhysicalPhaseFlow
    fun_prop
  change UniformContinuous ⇑(projectivePhysicalPhaseFlowHom energy)
  exact uniformContinuous_addMonoidHom_of_continuous hcont

theorem uniformContinuous_projectiveChoiDensityFlow
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    UniformContinuous (projectiveChoiDensityFlow energy) := by
  let readout : (Fin d → UnitAddCircle) →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun x => uniformPhaseDensity (d + 1) (zeroAnchoredPhase d x)
  have hreadout : Continuous readout := by
    dsimp [readout]
    exact (continuous_uniformPhaseDensity (d + 1)).comp (by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · exact continuous_apply j)
  have huc : UniformContinuous
      (readout ∘ projectivePhysicalPhaseFlow energy) :=
    (CompactSpace.uniformContinuous_of_continuous hreadout).comp
      (uniformContinuous_projectivePhysicalPhaseFlow energy)
  change UniformContinuous (fun t =>
    uniformPhaseDensity (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
  exact huc

theorem projectiveChoiCircuitTarget_time_preimage
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (delta : ℝ) :
    {t | projectivePhysicalPhaseFlow energy t ∈
      zeroAnchoredPaddedCircuitTarget d s target delta} =
      {t | ∃ w, dist (projectiveChoiDensityFlow energy t) (target w) ≤ delta} := by
  ext t
  simp only [zeroAnchoredPaddedCircuitTarget, zeroAnchoredMetricBallTarget,
    projectiveChoiDensityFlow, Set.mem_setOf_eq, Set.mem_iUnion]

/-- **Same-Hamiltonian continuous projected-Choi hard intervals.**  The complete circuit-union
occupation bound forces arbitrarily late continuous hard blocks.  `mesh` is a strictly positive
time thickness obtained once from the fixed orbit and radius gap. -/
theorem maximallyProjective_projectedChoiCircuitTargets_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {epsn epsw : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ {W : ℝ}, 0 ≤ W →
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * epsw ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) <
        mesh / (W + mesh) →
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
        ∀ t ∈ Icc u (u + W), ∀ w,
          epsn < dist (projectiveChoiDensityFlow energy t) (target w) := by
  let b : ℝ := (Fintype.card gate : ℝ) ^ (s + 1) *
      (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
        Real.sqrt (Real.pi * (2 * epsw ^ 2) / 2) ^ ((d + 1 : ℕ) - 1))
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have huc := uniformContinuous_projectiveChoiDensityFlow energy
  obtain ⟨eta, heta, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (epsw - epsn) (sub_pos.mpr hgap)
  let mesh : ℝ := eta / 2
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  refine ⟨mesh, hmesh, ?_⟩
  intro W hW hpack A0 hA0
  let narrow : Set ℝ :=
    {t | ∃ w, dist (projectiveChoiDensityFlow energy t) (target w) ≤ epsn}
  let wide : Set ℝ :=
    {t | ∃ w, dist (projectiveChoiDensityFlow energy t) (target w) ≤ epsw}
  have hlimA := limsup_windowProbability_projectivePhase_preimage_le_volume
    energy hmax (isClosed_zeroAnchoredPaddedCircuitTarget d s target epsw)
  have hpre := projectiveChoiCircuitTarget_time_preimage energy s target epsw
  have hvolReal := measureReal_zeroAnchoredPaddedCircuitTarget_le d s target hepsw
  have hvolFinite : (volume : Measure (Fin d → UnitAddCircle))
      (zeroAnchoredPaddedCircuitTarget d s target epsw) ≠ ⊤ := measure_ne_top _ _
  have hlim : atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ) wide)
      ≤ ENNReal.ofReal b := by
    have hmeasure : (volume : Measure (Fin d → UnitAddCircle))
        (zeroAnchoredPaddedCircuitTarget d s target epsw) ≤ ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hvolFinite]
      exact ENNReal.ofReal_le_ofReal hvolReal
    rw [hpre] at hlimA
    simpa only [wide] using le_trans hlimA hmeasure
  have hthick : ∀ t ∈ narrow, Ioc t (t + mesh) ⊆ wide := by
    rintro t ⟨w, htw⟩ v hv
    refine ⟨w, ?_⟩
    have htvdist : dist v t < eta := by
      rw [Real.dist_eq]
      have hvsub : 0 < v - t := sub_pos.mpr hv.1
      rw [abs_of_pos hvsub]
      have hvle : v - t ≤ eta / 2 := by
        dsimp [mesh] at hv
        linarith [hv.2]
      linarith
    have horbit := hmod htvdist
    exact (calc
      dist (projectiveChoiDensityFlow energy v) (target w) ≤
          dist (projectiveChoiDensityFlow energy v) (projectiveChoiDensityFlow energy t) +
            dist (projectiveChoiDensityFlow energy t) (target w) := dist_triangle _ _ _
      _ < (epsw - epsn) + epsn := add_lt_add_of_lt_of_le horbit htw
      _ = epsw := by ring).le
  obtain ⟨u, hu, hdisj⟩ := exists_late_interval_disjoint_of_limsup_windowProbability_le
    narrow wide hmesh hW hb hthick hlim hpack A0 hA0
  refine ⟨u, hu, ?_⟩
  intro t ht w
  by_contra hnot
  push Not at hnot
  have hmem : t ∈ narrow := ⟨w, hnot⟩
  have : t ∈ Icc u (u + W) ∩ narrow := ⟨ht, hmem⟩
  rw [hdisj] at this
  exact this

/-- **Operational same-Hamiltonian continuous circuit-hard intervals.**  Every normalized padded
circuit word is missed in pure-state trace distance throughout arbitrarily late continuous blocks.
The circuit entropy is paid once through completed occupation, not once per time-grid point. -/
theorem maximallyProjective_pureChoiCircuitTargets_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {epsn epsw : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ {W : ℝ}, 0 ≤ W →
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) < mesh / (W + mesh) →
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
        ∀ t ∈ Icc u (u + W), ∀ w,
          epsn < pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
            (target w) := by
  let projectedTarget : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w => diagonalDensityRestriction (d + 1) (pureStateDensity (target w))
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨mesh, hmesh, hmain⟩ :=
    maximallyProjective_projectedChoiCircuitTargets_late_hard_intervals
      energy hmax s projectedTarget
      (epsn := Real.sqrt 2 * epsn) (epsw := Real.sqrt 2 * epsw)
      (by nlinarith) (mul_nonneg hsqrt.le hepsn)
  refine ⟨mesh, hmesh, ?_⟩
  intro W hW hpack A0 hA0
  obtain ⟨u, hu, hhard⟩ := hmain hW hpack A0 hA0
  refine ⟨u, hu, ?_⟩
  intro t ht w
  have hprojected := hhard t ht w
  let psi := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  have hpsi : ‖psi‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hcontract := dist_uniformPhaseDensity_projectedTarget_le_full
    (d + 1) (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
    (pureStateDensity (target w))
  have hfull : dist (projectiveChoiDensityFlow energy t) (projectedTarget w) ≤
      Real.sqrt 2 * pureStateTraceDistance psi (target w) := by
    dsimp only [projectiveChoiDensityFlow, projectedTarget]
    refine le_trans hcontract ?_
    rw [← pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d)]
    simpa only [psi] using le_of_eq
      (dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
        psi (target w) hpsi (htarget w))
  dsimp [projectedTarget] at hprojected
  nlinarith

end RHTower
