import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw

/-!
# Static quantum complexity alternates forever

This file combines the compact-group alternation theorem with projective
spectral density, circuit-target entropy, the full Choi-space projection, and
the exact operational trace metric.  The result is one ordered dynamical law:
after every time, a static Hamiltonian returns near the identity channel,
subsequently enters a circuit-hard regime, and subsequently returns near the
identity again.  One finite bound controls every leg forever.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

/-- Open recurrence neighborhood of the identity Choi state in projective
spectral phase space. -/
def zeroAnchoredChoiRecurrenceTarget (d : ℕ) (δ : ℝ) :
    Set (Fin d → UnitAddCircle) :=
  {x | dist
      (fullUniformPhaseChoiDensity (d + 1) (zeroAnchoredPhase d x))
      (fullUniformPhaseChoiDensity (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < δ}

theorem continuous_fullUniformPhaseChoiDensity (d : ℕ) :
    Continuous (fullUniformPhaseChoiDensity d) := by
  unfold fullUniformPhaseChoiDensity
  let F := fun x : Fin d → UnitAddCircle ↦
    WithLp.toLp 2 fun pq :
        ((Fin d × Fin d) × (Fin d × Fin d)) ↦
      (if pq.1.1 = pq.1.2 ∧ pq.2.1 = pq.2.2 then (1 : ℂ) else 0) *
        (((d : ℝ)⁻¹ : ℂ) * fourier 1 (x pq.1.1) *
          starRingEnd ℂ (fourier 1 (x pq.2.1)))
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  convert hF using 1
  funext x
  ext pq
  by_cases h : pq.1.1 = pq.1.2 ∧ pq.2.1 = pq.2.2 <;> simp [F, h]

theorem isOpen_zeroAnchoredChoiRecurrenceTarget (d : ℕ) (δ : ℝ) :
    IsOpen (zeroAnchoredChoiRecurrenceTarget d δ) := by
  rw [zeroAnchoredChoiRecurrenceTarget]
  apply isOpen_lt
  · apply Continuous.dist
    · exact (continuous_fullUniformPhaseChoiDensity (d + 1)).comp (by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_const
        · exact continuous_apply j)
    · exact continuous_const
  · exact continuous_const

theorem zeroAnchoredChoiRecurrenceTarget_nonempty
    (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (zeroAnchoredChoiRecurrenceTarget d δ).Nonempty := by
  refine ⟨0, ?_⟩
  simp [zeroAnchoredChoiRecurrenceTarget, hδ]

theorem diagonalDensityRestriction_pureStateDensity_fullUniformPhaseChoiVector
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    diagonalDensityRestriction d
        (pureStateDensity (fullUniformPhaseChoiVector d x)) =
      uniformPhaseDensity d x := by
  rw [pureStateDensity_fullUniformPhaseChoiVector hd]
  exact diagonalDensityRestriction_fullUniformPhaseChoiDensity d x

/-- **Quantum complexity alternation law.** A maximally projective static
Hamiltonian alternates forever between operational recurrence to the identity
channel and operational separation from every circuit of bounded word length.
One finite number bounds every low-to-high and high-to-low leg, uniformly
after every starting time. -/
theorem maximallyProjective_pureChoiComplexity_alternates_syndetically
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ (2 : ℕ)) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tLow ∈ Set.Icc a (a + L),
      ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
      ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow energy tLow)))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε ∧
        (∀ w : PaddedCircuitWord gate s,
          ε < pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow energy tHigh)))
            (target w)) ∧
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow energy tLow')))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε := by
  let δ := Real.sqrt 2 * ε
  let projectedTarget : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w ↦ diagonalDensityRestriction (d + 1) (pureStateDensity (target w))
  let U := zeroAnchoredChoiRecurrenceTarget d δ
  let V := (zeroAnchoredPaddedCircuitTarget d s projectedTarget δ)ᶜ
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hδ : 0 < δ := mul_pos hsqrt hε
  have hUopen : IsOpen U := isOpen_zeroAnchoredChoiRecurrenceTarget d δ
  have hUne : U.Nonempty := zeroAnchoredChoiRecurrenceTarget_nonempty d hδ
  have hVopen : IsOpen V :=
    (isClosed_zeroAnchoredPaddedCircuitTarget d s projectedTarget δ).isOpen_compl
  have hvolume : volume.real
      (zeroAnchoredPaddedCircuitTarget d s projectedTarget δ) < 1 :=
    (measureReal_zeroAnchoredPaddedCircuitTarget_le d s projectedTarget hδ).trans_lt
      hentropy
  have hVne : V.Nonempty :=
    compl_zeroAnchoredPaddedCircuitTarget_nonempty_of_volumeReal_lt_one
      d s projectedTarget δ hvolume
  have hprojectedIdentity : projectedTarget identityWord =
      uniformPhaseDensity (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)) := by
    simp only [projectedTarget]
    rw [hidentity]
    exact diagonalDensityRestriction_pureStateDensity_fullUniformPhaseChoiVector
      (Nat.succ_pos d) _
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    apply hxV
    apply Set.mem_iUnion.mpr
    refine ⟨identityWord, ?_⟩
    change dist
      (uniformPhaseDensity (d + 1) (zeroAnchoredPhase d x))
      (projectedTarget identityWord) ≤ δ
    rw [hprojectedIdentity]
    apply le_of_lt
    have hproj := (dist_uniformPhaseDensity_projectedTarget_le_full
      (d + 1) (zeroAnchoredPhase d x)
      (fullUniformPhaseChoiDensity (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))).trans_lt
      (show dist
        (fullUniformPhaseChoiDensity (d + 1) (zeroAnchoredPhase d x))
        (fullUniformPhaseChoiDensity (d + 1)
          (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < δ by
            simpa [U, zeroAnchoredChoiRecurrenceTarget] using hxU)
    rw [diagonalDensityRestriction_fullUniformPhaseChoiDensity] at hproj
    exact hproj
  obtain ⟨L, hL, halternates⟩ :=
    GaloisForLFunctions.HTGeometry.denseAddOrbit_disjoint_open_targets_alternate_syndetically
        (projectivePhysicalPhaseFlowHom energy)
        (denseRange_projectivePhysicalPhaseFlowHom energy hmax)
        hUopen hUne hVopen hVne hdisj
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨tLow, htLow, tHigh, htHigh, tLow', htLow',
      hLowU, hHighV, hLow'U⟩ := halternates a
  change projectivePhysicalPhaseFlow energy tLow ∈ U at hLowU
  change projectivePhysicalPhaseFlow energy tHigh ∈ V at hHighV
  change projectivePhysicalPhaseFlow energy tLow' ∈ U at hLow'U
  refine ⟨tLow, htLow, tHigh, htHigh, tLow', htLow', ?_, ?_, ?_⟩
  · let ψ := fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tLow))
    let φ := fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))
    have hψ : ‖ψ‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
    have hφ : ‖φ‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
    have hdist : dist (pureStateDensity ψ) (pureStateDensity φ) < δ := by
      rw [pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d),
        pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d)]
      simpa [U, zeroAnchoredChoiRecurrenceTarget] using hLowU
    rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance ψ φ hψ hφ] at hdist
    dsimp [δ] at hdist
    nlinarith
  · intro w
    have hprojected : δ < dist
        (uniformPhaseDensity (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tHigh)))
        (projectedTarget w) := by
      have hw : projectivePhysicalPhaseFlow energy tHigh ∉
          zeroAnchoredMetricBallTarget d (projectedTarget w) δ := by
        intro hmem
        apply hHighV
        exact Set.mem_iUnion.mpr ⟨w, hmem⟩
      change ¬ dist
        (uniformPhaseDensity (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tHigh)))
        (projectedTarget w) ≤ δ at hw
      exact lt_of_not_ge hw
    let ψ := fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tHigh))
    have hψ : ‖ψ‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
    have hfull : δ < dist (pureStateDensity ψ) (pureStateDensity (target w)) := by
      apply hprojected.trans_le
      change dist
        (uniformPhaseDensity (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tHigh)))
        (diagonalDensityRestriction (d + 1) (pureStateDensity (target w))) ≤ _
      rw [← diagonalDensityRestriction_pureStateDensity_fullUniformPhaseChoiVector
        (Nat.succ_pos d)]
      exact dist_diagonalDensityRestriction_le (d + 1) _ _
    rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
      ψ (target w) hψ (htarget w)] at hfull
    dsimp [δ] at hfull
    nlinarith
  · let ψ := fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tLow'))
    let φ := fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))
    have hψ : ‖ψ‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
    have hφ : ‖φ‖ = 1 := fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
    have hdist : dist (pureStateDensity ψ) (pureStateDensity φ) < δ := by
      rw [pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d),
        pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d)]
      simpa [U, zeroAnchoredChoiRecurrenceTarget] using hLow'U
    rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance ψ φ hψ hφ] at hdist
    dsimp [δ] at hdist
    nlinarith

end RHTower
