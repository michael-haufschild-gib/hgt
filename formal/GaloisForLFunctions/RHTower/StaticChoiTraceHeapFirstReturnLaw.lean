import GaloisForLFunctions.RHTower.StaticChoiCircuitExcursionFirstReturnLaw
import GaloisForLFunctions.RHTower.StaticChoiTraceHeapComplexityPlateau

/-!
# Trace-heap hard blocks and first returns

Local circuits contain many word schedules with the same endpoint because disjoint gates commute.
This file carries the exact trace-heap capacity through completed occupation, continuous hard
blocks, identity padding, and consecutive-capture extraction.  The resulting first re-entry law
applies to the complete circuit set of depth at most the stated budget and pays no free-word or
shorter-shell multiplier.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

section TraceHeapFirstReturn

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] [LinearOrder α] in
theorem projectiveTraceWordTarget_time_preimage
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (ell : ℕ)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (delta : ℝ) :
    {t | projectivePhysicalPhaseFlow energy t ∈
      zeroAnchoredTraceWordTarget d ell target delta} =
      {t | ∃ w, dist (projectiveChoiDensityFlow energy t) (target w) ≤ delta} := by
  ext t
  simp only [zeroAnchoredTraceWordTarget, zeroAnchoredMetricBallTarget,
    projectiveChoiDensityFlow, Set.mem_setOf_eq, Set.mem_iUnion]

/-- **Quantitative trace-heap hard blocks.**  Intrinsic heap capacity, rather than free-word
cardinality, controls arbitrarily late continuous avoidance intervals for one static spectrum. -/
theorem maximallyProjective_projectedTraceWords_explicit_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) (hW : 0 ≤ W)
    (hpack :
      (traceHeapCapacity α ell Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * epsw ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / (Real.sqrt 2 * projectiveChoiSpeed energy)) /
          (W + (epsw - epsn) / (Real.sqrt 2 * projectiveChoiSpeed energy))) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      ∀ t ∈ Set.Icc u (u + W), ∀ w,
        epsn < dist (projectiveChoiDensityFlow energy t) (target w) := by
  let b : ℝ := (traceHeapCapacity α ell Delta : ℝ) *
      (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
        Real.sqrt (Real.pi * (2 * epsw ^ 2) / 2) ^ ((d + 1 : ℕ) - 1))
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hspeed : 0 < projectiveChoiSpeed energy := projectiveChoiSpeed_pos energy
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let wide : Set ℝ := {t | ∃ w,
    dist (projectiveChoiDensityFlow energy t) (target w) ≤ epsw}
  have hlimA := limsup_windowProbability_projectivePhase_preimage_le_volume
    energy hmax (isClosed_zeroAnchoredTraceWordTarget d ell target epsw)
  have hpre := projectiveTraceWordTarget_time_preimage energy ell target epsw
  have hvolReal := measureReal_zeroAnchoredTraceWordTarget_le d independent hsymm ell Delta
    hdegree target htrace hepsw
  have hvolFinite : (volume : Measure (Fin d → UnitAddCircle))
      (zeroAnchoredTraceWordTarget d ell target epsw) ≠ ⊤ := measure_ne_top _ _
  have hlim : Filter.atTop.limsup
      (fun T => (windowProbabilityMeasure T : Measure ℝ) wide) ≤ ENNReal.ofReal b := by
    have hmeasure : (volume : Measure (Fin d → UnitAddCircle))
        (zeroAnchoredTraceWordTarget d ell target epsw) ≤ ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_toReal hvolFinite]
      exact ENNReal.ofReal_le_ofReal hvolReal
    rw [hpre] at hlimA
    simpa only [wide] using le_trans hlimA hmeasure
  have htargetSet :
      {t | ∃ z ∈ Set.range target,
        dist (projectiveChoiDensityFlow energy t) z ≤ epsw} = wide := by
    ext t
    simp only [wide, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, hz⟩
      exact ⟨w, hz⟩
    · rintro ⟨w, hw⟩
      exact ⟨target w, ⟨w, rfl⟩, hw⟩
  intro A0 hA0
  obtain ⟨u, hu, hdisj⟩ :=
    exists_late_interval_metric_hard_of_limsup_windowProbability_le
      (projectiveChoiDensityFlow energy) (Set.range target)
      (speed := Real.sqrt 2 * projectiveChoiSpeed energy)
      (epsn := epsn) (epsw := epsw) (W := W) (b := b)
      (mul_pos hsqrt hspeed)
      (dist_projectiveChoiDensityFlow_le energy)
      hgap hW hb (by rwa [htargetSet]) hpack A0 hA0
  refine ⟨u, hu, ?_⟩
  intro t ht w
  by_contra hnot
  push Not at hnot
  have hmem : t ∈ Set.Icc u (u + W) ∩
      {t | ∃ z ∈ Set.range target,
        dist (projectiveChoiDensityFlow energy t) z ≤ epsn} :=
    ⟨ht, target w, ⟨w, rfl⟩, hnot⟩
  rw [hdisj] at hmem
  exact hmem

/-- Operational pure-state version of the quantitative trace-heap hard-block law. -/
theorem maximallyProjective_pureTraceWords_explicit_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) (hW : 0 ≤ W)
    (hpack :
      (traceHeapCapacity α ell Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / projectiveChoiSpeed energy) /
          (W + (epsw - epsn) / projectiveChoiSpeed energy)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      ∀ t ∈ Set.Icc u (u + W), ∀ w,
        epsn < pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  let projectedTarget : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w => diagonalDensityRestriction (d + 1) (pureStateDensity (target w))
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htraceProjected : ∀ u v,
      GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
        projectedTarget u = projectedTarget v := by
    intro u v huv
    dsimp only [projectedTarget]
    rw [htrace u v huv]
  intro A0 hA0
  obtain ⟨u, hu, hhard⟩ :=
    maximallyProjective_projectedTraceWords_explicit_late_hard_intervals
      energy hmax independent hsymm ell Delta hdegree projectedTarget htraceProjected
      (epsn := Real.sqrt 2 * epsn) (epsw := Real.sqrt 2 * epsw) (W := W)
      (by nlinarith) (mul_nonneg hsqrt.le hepsn) hW (by
        have hsqrtNe : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt
        have hspeedNe : projectiveChoiSpeed energy ≠ 0 :=
          ne_of_gt (projectiveChoiSpeed_pos energy)
        convert hpack using 1
        all_goals field_simp [hsqrtNe, hspeedNe])
      A0 hA0
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
  nlinarith

/-- Norm preservation propagates from individual gate actions to every evaluated word. -/
theorem norm_wordEval_eq
    {X : Type*} [Norm X]
    (act : α → X → X) (hnorm : ∀ g x, ‖act g x‖ = ‖x‖)
    (w : List α) (x : X) :
    ‖GaloisForLFunctions.RHTower.wordEval act w x‖ = ‖x‖ := by
  induction w with
  | nil => rfl
  | cons g w ih =>
      rw [GaloisForLFunctions.RHTower.wordEval_cons, hnorm, ih]

/-- **Complete bounded-depth trace-heap hard blocks.**  Commutation invariance and identity
padding turn the exact-shell occupation estimate into continuous avoidance of every gate word of
length at most `budget`, without paying for shorter shells. -/
theorem maximallyProjective_commutingGateWordsAtMost_explicit_late_hard_intervals
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (budget Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (e : α) (he : ∀ x, act e x = x)
    (hnorm : ∀ g x, ‖act g x‖ = ‖x‖)
    (chi : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hchi : ‖chi‖ = 1)
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) (hW : 0 ≤ W)
    (hpack :
      (traceHeapCapacity α budget Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / projectiveChoiSpeed energy) /
          (W + (epsw - epsn) / projectiveChoiSpeed energy)) :
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      ∀ t ∈ Set.Icc u (u + W), ∀ w : List α, w.length ≤ budget →
        epsn < pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (GaloisForLFunctions.RHTower.wordEval act w chi) := by
  let target : List.Vector α budget →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w => GaloisForLFunctions.RHTower.wordEval act w.1 chi
  have htarget : ∀ w, ‖target w‖ = 1 := by
    intro w
    simpa only [target, hchi] using norm_wordEval_eq act hnorm w.1 chi
  have htrace : ∀ u v,
      GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 → target u = target v := by
    intro u v huv
    exact GaloisForLFunctions.RHTower.wordEval_eq_of_traceEq
      act independent hcomm huv chi
  intro A0 hA0
  obtain ⟨u, hu, hhard⟩ :=
    maximallyProjective_pureTraceWords_explicit_late_hard_intervals
      energy hmax independent hsymm budget Delta hdegree target htarget htrace
      hgap hepsn hW hpack A0 hA0
  refine ⟨u, hu, fun t ht w hw => ?_⟩
  obtain ⟨v, hv⟩ :=
    GaloisForLFunctions.RHTower.exists_vector_pad_wordEval act e he hw chi
  have := hhard t ht v
  simpa only [target, hv] using this

/-- **Complete bounded-depth first re-entry.**  For one maximally projective static Hamiltonian,
every trace-capacity-certified hard block is contained in a literal excursion between consecutive
visits to the entire circuit set of depth at most `budget`.  The gap is at least `W`. -/
theorem maximallyProjective_commutingGateWordsAtMost_explicit_consecutiveVisitGap
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (budget Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (e : α) (he : ∀ x, act e x = x)
    (hnorm : ∀ g x, ‖act g x‖ = ‖x‖)
    (chi : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hchi : ‖chi‖ = 1)
    (hinitial : chi = fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {epsn epsw W : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) (hW : 0 ≤ W)
    (hpack :
      (traceHeapCapacity α budget Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((d + 1 : ℕ) - 1)) <
        ((epsw - epsn) / projectiveChoiSpeed energy) /
          (W + (epsw - epsn) / projectiveChoiSpeed energy)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
      A0 ≤ u ∧ tExit ∈ Set.Icc (u - B) u ∧
        tReturn ∈ Set.Icc (u + W) (u + W + B) ∧
        (∃ w : List α, w.length ≤ budget ∧
          pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tExit)))
            (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ epsn) ∧
        (∃ w : List α, w.length ≤ budget ∧
          pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tReturn)))
            (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ epsn) ∧
        tExit < tReturn ∧ W ≤ tReturn - tExit ∧
        ∀ t ∈ Set.Ioo tExit tReturn,
          ¬ ∃ w : List α, w.length ≤ budget ∧
            pureStateTraceDistance
              (fullUniformPhaseChoiVector (d + 1)
                (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
              (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ epsn := by
  let orbit : ℝ → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) := fun t =>
    fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let target : List.Vector α budget →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
    fun w => GaloisForLFunctions.RHTower.wordEval act w.1 chi
  let capture : Set ℝ :=
    {t | ∃ w : List.Vector α budget,
      pureStateTraceDistance (orbit t) (target w) ≤ epsn}
  have horbit : Continuous orbit := continuous_projectivePureChoiVector energy
  have hcapture : IsClosed capture :=
    isClosed_finite_pureStateTraceDistance_captureTimeSet orbit horbit target epsn
  have htarget : ∀ w, ‖target w‖ = 1 := by
    intro w
    simpa only [target, hchi] using norm_wordEval_eq act hnorm w.1 chi
  have htrace : ∀ u v,
      GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 → target u = target v := by
    intro u v huv
    exact GaloisForLFunctions.RHTower.wordEval_eq_of_traceEq
      act independent hcomm huv chi
  obtain ⟨B, hB, hrec⟩ :=
    maximallyProjective_pureChoiRecurrence_syndetic energy hmax hepsn
  refine ⟨B, hB, ?_⟩
  intro A0 hA0
  obtain ⟨u, hu, hhard⟩ :=
    maximallyProjective_pureTraceWords_explicit_late_hard_intervals
      energy hmax independent hsymm budget Delta hdegree target htarget htrace
      hgap hepsn.le hW hpack A0 hA0
  let identityVector : List.Vector α budget :=
    ⟨List.replicate budget e, by simp⟩
  have hidentity : target identityVector = chi := by
    dsimp only [target, identityVector]
    exact GaloisForLFunctions.RHTower.wordEval_replicate_identity act e he budget chi
  have hpre : ∃ t ∈ Set.Icc (u - B) u, t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u - B)
    refine ⟨t, ⟨ht.1, by linarith [ht.2]⟩, identityVector, ?_⟩
    dsimp only [orbit]
    rw [hidentity, hinitial]
    exact htRec.le
  have hpost : ∃ t ∈ Set.Icc (u + W) (u + W + B), t ∈ capture := by
    obtain ⟨t, ht, htRec⟩ := hrec (u + W)
    refine ⟨t, ht, identityVector, ?_⟩
    dsimp only [orbit]
    rw [hidentity, hinitial]
    exact htRec.le
  have havoid : ∀ t ∈ Set.Icc u (u + W), t ∉ capture := by
    intro t ht htCapture
    obtain ⟨w, hw⟩ := htCapture
    exact (not_le_of_gt (hhard t ht w)) hw
  obtain ⟨tExit, tReturn, htExit, htReturn,
      htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩ :=
    exists_consecutive_mem_separated_by_avoided_Icc
      hcapture hW hpre hpost havoid
  refine ⟨u, tExit, tReturn, hu, htExit, htReturn, ?_, ?_, hlt, hwidth, ?_⟩
  · obtain ⟨w, hw⟩ := htExitCapture
    exact ⟨w.1, w.2.le, hw⟩
  · obtain ⟨w, hw⟩ := htReturnCapture
    exact ⟨w.1, w.2.le, hw⟩
  · intro t ht hshort
    obtain ⟨w, hwlen, hw⟩ := hshort
    obtain ⟨v, hv⟩ :=
      GaloisForLFunctions.RHTower.exists_vector_pad_wordEval act e he hwlen chi
    apply hbetween t ht
    refine ⟨v, ?_⟩
    dsimp only [target]
    rw [hv]
    exact hw

end TraceHeapFirstReturn

end RHTower
