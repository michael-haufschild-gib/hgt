import GaloisForLFunctions.HTGeometry.KleinGordonJointSmooth

/-!
# Clock probes for every smooth spacetime potential

A potential that depends on the time coordinate as well as on the point is cut off in space *and*
time around the event under consideration. The cut-off potential is a curve of Schwartz functions
which is bounded and Lipschitz in time after finitely many applications of `1 - (2π)⁻²Δ`, because
the corresponding function of the event is smooth and supported in a compact set of events.

The probe only has to solve the field equation near the event, so the cut-off is invisible: every
smooth potential — with no decay, smallness or time-independence hypothesis — has probes on open
regions.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped SchwartzMap FourierTransform ContDiff Laplacian

/-! ## The operator is linear -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem kgSchwartzOp_sub (f g : 𝓢(E, ℂ)) :
    kgSchwartzOp (f - g) = kgSchwartzOp f - kgSchwartzOp g := by
  rw [kgSchwartzOp, kgSchwartzOp, kgSchwartzOp, map_sub]

theorem kgSchwartzOp_iterate_sub (j : ℕ) (f g : 𝓢(E, ℂ)) :
    kgSchwartzOp^[j] (f - g) = kgSchwartzOp^[j] f - kgSchwartzOp^[j] g := by
  induction j generalizing f g with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      kgSchwartzOp_sub, ih]

end Linear

/-! ## The spacetime cut-off -/

section Cut

variable {d : ℕ}

/-- A smooth bump in the time coordinate. -/
noncomputable def kgTimeCutoff (t₀ : ℝ) : ContDiffBump t₀ := ⟨1, 2, one_pos, one_lt_two⟩

/-- The potential, cut off in space and in time around an event. -/
noncomputable def kgSpacetimeCut (P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ) (t₀ : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) → ℂ :=
  fun p => ((kgTimeCutoff t₀ p.1 * (kgCutoff x₀ p.2 * (P p + 1)) : ℝ) : ℂ)

variable {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} {t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}

theorem kgSpacetimeCut_apply (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    kgSpacetimeCut P t₀ x₀ p = ((kgTimeCutoff t₀ p.1 * (kgCutoff x₀ p.2 * (P p + 1)) : ℝ) : ℂ) :=
  rfl

theorem contDiff_kgSpacetimeCut (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (kgSpacetimeCut P t₀ x₀) := by
  refine Complex.ofRealCLM.contDiff.comp ?_
  refine ContDiff.mul ((kgTimeCutoff t₀).contDiff.comp contDiff_fst) ?_
  exact ((kgCutoff x₀).contDiff.comp contDiff_snd).mul (hP.add contDiff_const)

theorem kgSpacetimeCut_zero_of_space {p : ℝ × EuclideanSpace ℝ (Fin d)}
    (h : p.2 ∉ closedBall x₀ 2) : kgSpacetimeCut P t₀ x₀ p = 0 := by
  have hzero : kgCutoff x₀ p.2 = 0 := by
    refine (kgCutoff x₀).zero_of_le_dist ?_
    have : ¬ dist p.2 x₀ ≤ 2 := by simpa [Metric.mem_closedBall] using h
    exact le_of_lt (lt_of_not_ge this)
  rw [kgSpacetimeCut_apply, hzero]
  simp

theorem kgSpacetimeCut_zero_of_time {p : ℝ × EuclideanSpace ℝ (Fin d)}
    (h : p.1 ∉ closedBall t₀ 2) : kgSpacetimeCut P t₀ x₀ p = 0 := by
  have hzero : kgTimeCutoff t₀ p.1 = 0 := by
    refine (kgTimeCutoff t₀).zero_of_le_dist ?_
    have : ¬ dist p.1 t₀ ≤ 2 := by simpa [Metric.mem_closedBall] using h
    exact le_of_lt (lt_of_not_ge this)
  rw [kgSpacetimeCut_apply, hzero]
  simp

/-- Off a compact set of events the cut-off potential vanishes. -/
theorem kgSpacetimeCut_zero_of_notMem {p : ℝ × EuclideanSpace ℝ (Fin d)}
    (h : p ∉ closedBall t₀ 2 ×ˢ closedBall x₀ 2) : kgSpacetimeCut P t₀ x₀ p = 0 := by
  by_cases ht : p.1 ∈ closedBall t₀ 2
  · exact kgSpacetimeCut_zero_of_space (fun hx => h ⟨ht, hx⟩)
  · exact kgSpacetimeCut_zero_of_time ht

/-- The curve of Schwartz functions cut out of a smooth potential. -/
noncomputable def kgSpacetimeCurve (hP : ContDiff ℝ ∞ P) (t₀ : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (t : ℝ) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := by
  refine HasCompactSupport.toSchwartzMap
    (f := fun x : EuclideanSpace ℝ (Fin d) => kgSpacetimeCut P t₀ x₀ (t, x)) ?_ ?_
  · refine HasCompactSupport.intro (isCompact_closedBall x₀ 2) fun x hx => ?_
    exact kgSpacetimeCut_zero_of_space (p := (t, x)) hx
  · have hsl : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin d) => ((t, x) : ℝ × _) := by fun_prop
    exact (contDiff_kgSpacetimeCut hP).comp hsl

theorem kgSpacetimeCurve_apply (hP : ContDiff ℝ ∞ P) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    kgSpacetimeCurve hP t₀ x₀ t x = kgSpacetimeCut P t₀ x₀ (t, x) := rfl

theorem kgSpacetimeCurve_real (hP : ContDiff ℝ ∞ P) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (starRingEnd ℂ) (kgSpacetimeCurve hP t₀ x₀ t x) = kgSpacetimeCurve hP t₀ x₀ t x := by
  rw [kgSpacetimeCurve_apply, kgSpacetimeCut_apply, Complex.conj_ofReal]

theorem kgSpacetimeCurve_support (hP : ContDiff ℝ ∞ P) (t : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ closedBall x₀ 2) :
    kgSpacetimeCurve hP t₀ x₀ t x = 0 := by
  rw [kgSpacetimeCurve_apply]
  exact kgSpacetimeCut_zero_of_space (p := (t, x)) hx

/-- Near the event the cut-off is invisible. -/
theorem kgSpacetimeCurve_re (hP : ContDiff ℝ ∞ P) {t : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (ht : t ∈ ball t₀ 1) (hx : x ∈ ball x₀ 1) :
    (kgSpacetimeCurve hP t₀ x₀ t x).re - 1 = P (t, x) := by
  have htime : kgTimeCutoff t₀ t = 1 :=
    (kgTimeCutoff t₀).one_of_mem_closedBall (ball_subset_closedBall ht)
  have hspace : kgCutoff x₀ x = 1 :=
    (kgCutoff x₀).one_of_mem_closedBall (ball_subset_closedBall hx)
  rw [kgSpacetimeCurve_apply, kgSpacetimeCut_apply, htime, hspace, Complex.ofReal_re]
  ring

end Cut

/-! ## Probes for every smooth potential -/

section SpacetimeProbe

variable {d N : ℕ}

/-- **Every smooth spacetime potential is locally the potential of an admissible family**: cut off
in space and time near the event, it becomes a curve of Schwartz potentials whose decay functional is
bounded and Lipschitz in time by compactness. -/
theorem exists_locally_kgChartPotential_of_smooth_spacetime
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P) :
    ∀ y₀ : Fin (d + 1) → ℝ, ∃ (B : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
      (W : Set (Fin (d + 1) → ℝ)), IsRealFamily B ∧ IsOpen W ∧ y₀ ∈ W ∧
        Set.EqOn (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) (kgChartPotential B) W := by
  intro y₀
  set t₀ : ℝ := y₀ 0 with ht₀
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set Φ : ℝ → 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := kgSpacetimeCurve hP t₀ x₀ with hΦ
  set K : Set (EuclideanSpace ℝ (Fin d)) := closedBall x₀ 2 with hK
  set S : Set (ℝ × EuclideanSpace ℝ (Fin d)) := closedBall t₀ 2 ×ˢ K with hS
  have hScompact : IsCompact S := (isCompact_closedBall t₀ 2).prod (isCompact_closedBall x₀ 2)
  have hcut : ContDiff ℝ ∞ (kgSpacetimeCut P t₀ x₀) := contDiff_kgSpacetimeCut hP
  have hcutzero : ∀ p : ℝ × EuclideanSpace ℝ (Fin d), p ∉ S → kgSpacetimeCut P t₀ x₀ p = 0 :=
    fun p hp => kgSpacetimeCut_zero_of_notMem hp
  -- the orders of the construction
  set m : ℕ := d + 1 with hm
  set j : ℕ := N + m with hj
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m := by
    rw [finrank_euclideanSpace_fin, hm]
    push_cast
    linarith
  have hjle : N + m ≤ 2 * j := by omega
  -- the pointwise identification of the operator
  have hcoe : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)),
      (kgSchwartzOp^[j] (Φ t)) x
        = (kgFunOp^[j] fun y : EuclideanSpace ℝ (Fin d) => kgSpacetimeCut P t₀ x₀ (t, y)) x := by
    intro t x
    exact congrFun (coe_kgSchwartzOp_iterate j (Φ t)) x
  -- the uniform and Lipschitz bounds
  obtain ⟨C, hC⟩ := exists_bound_kgFunOp_iterate hcut hScompact hcutzero j
  obtain ⟨L, hL0, hLb⟩ := exists_lipschitz_kgFunOp_iterate hcut hScompact hcutzero j
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKfin : volume K ≠ ⊤ := (measure_closedBall_lt_top).ne
  have hvol : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hsupp : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), x ∉ K → Φ t x = 0 :=
    fun t x hx => kgSpacetimeCurve_support hP t hx
  have hM : ∀ t : ℝ, (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t)) v‖)
      ≤ C * (volume K).toReal := by
    intro t
    refine integral_kgSchwartzOp_le isClosed_closedBall hKmeas hKfin (hsupp t) j fun x => ?_
    rw [hcoe t x]
    exact hC t x
  have hL : ∀ t t' : ℝ, (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖)
      ≤ L * (volume K).toReal * |t - t'| := by
    intro t t'
    have hsuppSub : ∀ x : EuclideanSpace ℝ (Fin d), x ∉ K → (Φ t - Φ t') x = 0 := by
      intro x hx
      rw [sub_apply, hsupp t x hx, hsupp t' x hx, sub_zero]
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
        ‖(kgSchwartzOp^[j] (Φ t - Φ t')) x‖ ≤ L * |t - t'| := by
      intro x
      rw [kgSchwartzOp_iterate_sub, sub_apply, hcoe t x, hcoe t' x]
      exact hLb t t' x
    have hbase := integral_kgSchwartzOp_le isClosed_closedBall hKmeas hKfin hsuppSub j hpt
    refine hbase.trans_eq ?_
    ring
  have hreal : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), (starRingEnd ℂ) (Φ t x) = Φ t x :=
    fun t x => kgSpacetimeCurve_real hP t x
  refine ⟨WienerFamily.ofSchwartzCurve (N := N) hdim hjle hM (mul_nonneg hL0 hvol) hL,
    {y : Fin (d + 1) → ℝ | y 0 ∈ ball t₀ 1} ∩ (kgSpatial d) ⁻¹' (ball x₀ 1),
    isRealFamily_ofSchwartzCurve hdim hjle hM (mul_nonneg hL0 hvol) hL hreal,
    (isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_kgSpatial d)), ⟨?_, ?_⟩, ?_⟩
  · exact mem_ball_self one_pos
  · exact mem_ball_self one_pos
  · intro z hz
    have htime : z 0 ∈ ball t₀ 1 := hz.1
    have hspace : kgSpatial d z ∈ ball x₀ 1 := hz.2
    show P (z 0, kgSpatial d z) = kgChartPotential _ z
    rw [kgChartPotential, kgPotential_ofSchwartzCurve]
    exact (kgSpacetimeCurve_re hP htime hspace).symm

/-- **Clock probes for every smooth spacetime potential**, with no decay, smallness or
time-independence hypothesis. -/
theorem openProbes_of_smooth_spacetime
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hP : ContDiff ℝ ∞ P) :
    OpenProbes (kgWaveOp d) (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) :=
  openProbes_of_locally_kgChartPotential (N := N) hN
    (exists_locally_kgChartPotential_of_smooth_spacetime hP)

end SpacetimeProbe

end GaloisForLFunctions.HTGeometry
