import GaloisForLFunctions.HTGeometry.KleinGordonChartSecond
import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential
import GaloisForLFunctions.HTGeometry.ClockPotentialLocalDetermination

/-!
# The clock probe

The construction reaches the corpus's interface here. On the chart `Fin (d+1) → ℝ` with the Minkowski
signature the divergence-form d'Alembertian is the alternating sum of the pure second coordinate
derivatives, those derivatives are the ones the field equation relates, and the equation says

`□u = (1 - V)u`,

that is, `u` solves the potential-dressed wave equation for the potential `V - 1`. Since the field is
nonzero on a neighbourhood of the chosen event, it is a clock probe there.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {d N : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
  (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)

/-! ## The signature of the chart -/

/-- The Minkowski signature of the chart. -/
noncomputable def kgEps (d : ℕ) : Fin (d + 1) → ℝ := fun j => if j = 0 then -1 else 1

theorem kgEps_ne_zero (d : ℕ) : ∀ j : Fin (d + 1), kgEps d j ≠ 0 := by
  intro j
  rw [kgEps]
  by_cases hj : j = 0
  · rw [if_pos hj]
    norm_num
  · rw [if_neg hj]
    norm_num

theorem kgEps_zero (d : ℕ) : kgEps d 0 = -1 := by
  rw [kgEps, if_pos rfl]

theorem kgEps_succ (d : ℕ) (i : Fin d) : kgEps d i.succ = 1 := by
  rw [kgEps, if_neg (Fin.succ_ne_zero i)]

/-- The wave operator of the chart. -/
noncomputable def kgWaveOp (d : ℕ) : ((Fin (d + 1) → ℝ) → ℝ) → (Fin (d + 1) → ℝ) → ℝ :=
  (SmoothPseudoMetric.ofSignature (kgEps d) (kgEps_ne_zero d)).chart.dalembert

/-- The potential of the chart: the potential of the density, rescaled and shifted by the mass. -/
noncomputable def kgChartPotential (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
    (y : Fin (d + 1) → ℝ) : ℝ := (kgPotential (a.density (y 0)) (kgSpatial d y)).re - 1

/-! ## The pure second derivatives -/

theorem hasDerivAt_kgSynthesis_flowDensityDeriv
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => kgSynthesis (kgFlowDensityDeriv a G₀ r) x)
      (kgSynthesis (kgFlowDensityDeriv2 a G₀ t) x) t := by
  have hdimN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  exact hasDerivAt_kgSynthesis_time (N := K) hdimK
    (fun r => (continuous_kgFlowDensityDeriv_freq a G₀ r).aestronglyMeasurable)
    (fun r => (continuous_kgFlowDensityDeriv2 a G₀ r).aestronglyMeasurable)
    (fun r ξ => hasDerivAt_kgFlowDensityDeriv a G₀ ξ r)
    (fun T => ⟨kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T,
      fun r hr ξ => norm_kgFlowDensityDeriv2_le_weight a G₀ rfl hr ξ⟩)
    x t (integrable_kgFlowDensityDeriv a G₀ hdimN t)

theorem deriv_deriv_kgRealField_time_eq
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    deriv (deriv fun r : ℝ => kgRealField a G₀ r x) t
      = (kgSynthesis (kgFlowDensityDeriv2 a G₀ t) x).re := by
  have hfirst : (deriv fun r : ℝ => kgRealField a G₀ r x)
      = fun r : ℝ => (kgSynthesis (kgFlowDensityDeriv a G₀ r) x).re := by
    funext r
    show deriv (fun q : ℝ => (kgFlowField a G₀ q x).re) r = _
    rw [deriv_re_eq (fun q => differentiableAt_kgFlowField_time a G₀ hN x q) r,
      (hasDerivAt_kgFlowField hN a G₀ x r).deriv]
    rfl
  rw [hfirst]
  exact (hasDerivAt_re (hasDerivAt_kgSynthesis_flowDensityDeriv a G₀ hN x t)).deriv

theorem deriv_deriv_kgRealField_dir_eq
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (t : ℝ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    deriv (deriv fun s : ℝ => kgRealField a G₀ t (x + s • v)) 0
      = (kgSynthesis (kgDirDensity v (kgDirDensity v (kgFlowDensity a G₀ t))) x).re := by
  have hmeas : AEStronglyMeasurable (kgFlowDensity a G₀ t)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable
  have hint := integrable_kgFlowDensity a G₀ hN t
  have h1 := integrable_kgFreq_mul_kgFlowDensity a G₀ hN t
  have h2 := integrable_kgFreq_sq_mul_kgFlowDensity a G₀ hN t
  have hfirst : (deriv fun s : ℝ => kgRealField a G₀ t (x + s • v))
      = fun s : ℝ => (kgSynthesis (kgDirDensity v (kgFlowDensity a G₀ t)) (x + s • v)).re := by
    funext s
    show deriv (fun q : ℝ => (kgFlowField a G₀ t (x + q • v)).re) s = _
    rw [deriv_re_eq (fun q => differentiableAt_kgFlowField_dir a G₀ hN t x v q) s,
      deriv_kgFlowField_dir_eq a G₀ hN t x v s]
  rw [hfirst]
  have hsecond := hasDerivAt_re (hasDerivAt_kgSynthesis_dir_dir hmeas h1 h2 x v v 0)
  rw [hsecond.deriv]
  congr 2
  rw [zero_smul, add_zero]

/-! ## The coordinate second derivatives -/

theorem coordPartial_coordPartial_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ) :
    coordPartial 0 (coordPartial 0 (kgChartField a G₀)) y
      = deriv (deriv fun r : ℝ => kgRealField a G₀ r (kgSpatial d y)) (y 0) := by
  have hcp : coordPartial 0 (kgChartField a G₀) = kgChartTimePartial a G₀ := by
    funext z
    rw [coordPartial_kgChartField a G₀ hN 0 z, kgChartPartial_zero]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (kgChartTimePartial a G₀)
    (kgChartTimeSecond a G₀) Set.univ (isC1OnPi_kgChartTimePartial a G₀ hN) y
    (Set.mem_univ y)).fderiv, piToCLM_single, kgChartTimeSecond,
    deriv_deriv_kgRealField_time_eq a G₀ hN]
  rfl

theorem coordPartial_coordPartial_succ
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ)
    (i : Fin d) :
    coordPartial i.succ (coordPartial i.succ (kgChartField a G₀)) y
      = deriv (deriv fun s : ℝ =>
          kgRealField a G₀ (y 0) (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))) 0 := by
  have hcp : coordPartial i.succ (kgChartField a G₀) = kgChartSpacePartial a G₀ i := by
    funext z
    rw [coordPartial_kgChartField a G₀ hN i.succ z, kgChartPartial_succ]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (kgChartSpacePartial a G₀ i)
    (kgChartSpaceSecond a G₀ i) Set.univ (isC1OnPi_kgChartSpacePartial a G₀ hN i) y
    (Set.mem_univ y)).fderiv, piToCLM_single, kgChartSpaceSecond, Fin.cases_succ,
    deriv_deriv_kgRealField_dir_eq a G₀ hN]
  rfl

/-! ## The probe -/

/-- **The chart field solves the potential-dressed wave equation.** -/
theorem kgWaveOp_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hreal : IsRealFamily a) (y : Fin (d + 1) → ℝ) :
    kgWaveOp d (kgChartField a G₀) y + kgChartPotential a y * kgChartField a G₀ y = 0 := by
  have hwave := kgRealField_wave_equation_unit a G₀ hN hreal
    (EuclideanSpace.basisFun (Fin d) ℝ) (y 0) (kgSpatial d y)
  have hdir : ∀ i : Fin d,
      deriv (deriv fun s : ℝ => kgRealField a G₀ (y 0)
        (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • EuclideanSpace.basisFun (Fin d) ℝ i))) 0
      = coordPartial i.succ (coordPartial i.succ (kgChartField a G₀)) y := by
    intro i
    rw [coordPartial_coordPartial_succ a G₀ hN y i, kgDir_eq_basisFun]
  have hsum : (∑ i : Fin d, deriv (deriv fun s : ℝ => kgRealField a G₀ (y 0)
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • EuclideanSpace.basisFun (Fin d) ℝ i))) 0)
      = ∑ i : Fin d, coordPartial i.succ (coordPartial i.succ (kgChartField a G₀)) y :=
    Finset.sum_congr rfl fun i _ => hdir i
  rw [hsum] at hwave
  have htime : deriv (deriv fun r : ℝ => kgRealField a G₀ r (kgSpatial d y)) (y 0)
      = coordPartial 0 (coordPartial 0 (kgChartField a G₀)) y :=
    (coordPartial_coordPartial_zero a G₀ hN y).symm
  rw [htime] at hwave
  have hfield : kgChartField a G₀ y = kgRealField a G₀ (y 0) (kgSpatial d y) := rfl
  rw [kgWaveOp, ofSignature_dalembert_of_differentiableAt (kgEps d) (kgEps_ne_zero d)
    (fun j => differentiableAt_coordPartial_kgChartField a G₀ hN j y), Fin.sum_univ_succ,
    kgEps_zero, kgChartPotential, hfield]
  have heps : ∀ i : Fin d, (kgEps d i.succ)⁻¹
      * coordPartial i.succ (coordPartial i.succ (kgChartField a G₀)) y
      = coordPartial i.succ (coordPartial i.succ (kgChartField a G₀)) y := by
    intro i
    rw [kgEps_succ, inv_one, one_mul]
  rw [Finset.sum_congr rfl fun i _ => heps i]
  rw [hwave]
  ring

/-- **The chart field is a clock probe**: it solves the wave equation for the potential `V - 1`
everywhere, and it is nonzero on a neighbourhood of the chosen event. -/
theorem solvesPotentialWaveOn_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hreal : IsRealFamily a) (region : Set (Fin (d + 1) → ℝ)) :
    SolvesPotentialWaveOn (kgWaveOp d) (kgChartPotential a) (kgChartField a G₀) region :=
  fun y _ => kgWaveOp_kgChartField a G₀ hN hreal y

/-! ## The event and the local probes -/

/-- The chart point of a spatial event at time zero. -/
noncomputable def kgChartEvent (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) : Fin (d + 1) → ℝ :=
  Fin.cons 0 (fun i : Fin d => (2 * Real.pi) * (EuclideanSpace.equiv (Fin d) ℝ x₀) i)

theorem kgChartEvent_zero (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) :
    kgChartEvent d x₀ 0 = 0 := by
  rw [kgChartEvent, Fin.cons_zero]

theorem kgSpatial_kgChartEvent (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) :
    kgSpatial d (kgChartEvent d x₀) = x₀ := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hcoord : (fun i : Fin d => kgChartEvent d x₀ i.succ)
      = (2 * Real.pi) • (EuclideanSpace.equiv (Fin d) ℝ x₀) := by
    funext i
    rw [kgChartEvent, Fin.cons_succ]
    rfl
  rw [kgSpatial, hcoord, map_smul, smul_smul, inv_mul_cancel₀ hpi, one_smul]
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm_apply_apply x₀

/-- **The probe is nonzero on a neighbourhood of the event, in the chart.** -/
theorem eventually_kgChartField_ne_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∀ᶠ y in nhds (kgChartEvent d x₀),
      kgChartField a (kgConjChar x₀) y ≠ 0 := by
  have hmap : Filter.Tendsto (fun y : Fin (d + 1) → ℝ => ((y 0, kgSpatial d y) :
      ℝ × EuclideanSpace ℝ (Fin d))) (nhds (kgChartEvent d x₀)) (nhds (0, x₀)) := by
    have hcont : Filter.Tendsto (fun y : Fin (d + 1) → ℝ => ((y 0, kgSpatial d y) :
        ℝ × EuclideanSpace ℝ (Fin d))) (nhds (kgChartEvent d x₀))
        (nhds ((kgChartEvent d x₀ 0, kgSpatial d (kgChartEvent d x₀)))) :=
      (continuous_chartPoint d).continuousAt
    rw [kgChartEvent_zero, kgSpatial_kgChartEvent] at hcont
    exact hcont
  exact hmap.eventually (eventually_kgRealField_ne_zero a hN x₀)

/-- **Clock probes for the potential of an admissible density**, on a neighbourhood of any
prescribed event: the corpus's local-probe interface. -/
theorem exists_localProbesOn_kgChartPotential
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hreal : IsRealFamily a) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ region : Set (Fin (d + 1) → ℝ), IsOpen region ∧ kgChartEvent d x₀ ∈ region ∧
      LocalProbesOn (kgWaveOp d) (kgChartPotential a) region := by
  obtain ⟨region, hsub, hopen, hmem⟩ :=
    mem_nhds_iff.mp (eventually_kgChartField_ne_zero a hN x₀)
  refine ⟨region, hopen, hmem, fun y hy => ?_⟩
  exact ⟨kgChartField a (kgConjChar x₀),
    kgWaveOp_kgChartField a (kgConjChar x₀) hN hreal y, hsub hy⟩

end GaloisForLFunctions.HTGeometry
