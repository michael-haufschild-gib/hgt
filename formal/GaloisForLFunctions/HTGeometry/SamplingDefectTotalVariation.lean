import Mathlib

/-!
# The order-zero sampling defect of a null sample set

In the order-zero test space `C_0(X)` with the supremum norm — whose dual is, by Riesz--Markov, the
finite signed Radon measures with the total-variation norm — sampling a finite positive Radon
measure `μ` on a **closed `μ`-null** set `Λ` loses everything:

```text
Δ(μ, Λ) := sup { |∫ φ dμ| : φ ∈ C_0(X), φ|_Λ = 0, ‖φ‖_∞ ≤ 1 } = μ(X) = ‖μ‖_TV.
```

* `abs_integral_le_measure_univ` — the upper bound;
* `exists_sampleTest_integral_gt` — the lower bound, by inner regularity plus Urysohn separation
  between a compact subset of `Λᶜ` carrying almost all the mass and the closed set `Λ`;
* `isLUB_samplingPairings` — the two together: the defect *is* the total mass;
* `integral_eq_zero_of_concentrated` — every measure concentrated on `Λ` pairs to zero against the
  sampling ideal, so subtracting one changes no defect: the best bounded linear reconstruction from
  the samples is no better than discarding them;
* `measureReal_add_of_mass_eq`, `normalized_samplingDefect` — symmetric completion doubles the
  absolute defect and leaves the normalized defect at its maximal value one.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry.SamplingDefect

variable {X : Type*} [MeasurableSpace X]

/-- **Upper bound for the sampling defect.**  Every test function of sup norm at most one pairs
against `μ` by at most the total mass. -/
theorem abs_integral_le_measure_univ (μ : Measure X) [IsFiniteMeasure μ]
    {φ : X → ℝ} (hφ : ∀ x, |φ x| ≤ 1) :
    |∫ x, φ x ∂μ| ≤ μ.real Set.univ := by
  have hbound : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs]
    exact hφ x
  have hle := norm_integral_le_of_norm_le_const (C := 1) (μ := μ) (f := φ)
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hle
  simpa using hle

variable [TopologicalSpace X] [BorelSpace X] [RegularSpace X] [LocallyCompactSpace X] [T2Space X]

/-- **Lower bound for the sampling defect.**  A closed null sample set is invisible: test functions
vanishing on it still recover the full mass. -/
theorem exists_sampleTest_integral_gt (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    {Λ : Set X} (hΛ : IsClosed Λ) (hnull : μ Λ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : C(X, ℝ), (∀ x ∈ Λ, φ x = 0) ∧ (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) ∧
      HasCompactSupport φ ∧ μ.real Set.univ - ε < ∫ x, φ x ∂μ := by
  classical
  by_cases hzero : μ Set.univ = 0
  · refine ⟨0, fun x _ => rfl, fun x => ⟨le_rfl, zero_le_one⟩, HasCompactSupport.zero, ?_⟩
    have hz : μ.real Set.univ = 0 := by
      rw [MeasureTheory.measureReal_def, hzero, ENNReal.toReal_zero]
    rw [hz]
    simp only [ContinuousMap.coe_zero, Pi.zero_apply, integral_zero]
    linarith
  · have hpos : 0 < μ.real Set.univ := by
      refine ENNReal.toReal_pos hzero (measure_ne_top μ _)
    have hcompl : μ Λᶜ = μ Set.univ := by
      rw [Set.compl_eq_univ_sdiff, MeasureTheory.measure_sdiff (Set.subset_univ Λ)
        hΛ.measurableSet.nullMeasurableSet (measure_ne_top μ Λ), hnull, tsub_zero]
    have hlt : ENNReal.ofReal (μ.real Set.univ - ε) < μ Λᶜ := by
      rw [hcompl]
      calc ENNReal.ofReal (μ.real Set.univ - ε)
          < ENNReal.ofReal (μ.real Set.univ) := by
            refine (ENNReal.ofReal_lt_ofReal_iff hpos).mpr ?_
            linarith
        _ = μ Set.univ := by
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    obtain ⟨K, hKsub, hKcomp, hKmeas⟩ := hΛ.isOpen_compl.exists_lt_isCompact hlt
    have hdisj : Disjoint K Λ := Set.disjoint_left.mpr (fun x hx hxΛ => (hKsub hx) hxΛ)
    obtain ⟨φ, hφ1, hφ0, hφsupp, hφIcc⟩ :=
      exists_continuous_one_zero_of_isCompact hKcomp hΛ hdisj
    refine ⟨φ, fun x hx => hφ0 hx, hφIcc, hφsupp, ?_⟩
    have hint : Integrable (fun x => φ x) μ := by
      exact (map_continuous φ).integrable_of_hasCompactSupport hφsupp
    have hindint : Integrable (Set.indicator K (fun _ => (1 : ℝ))) μ := by
      refine (integrable_indicator_iff hKcomp.measurableSet).mpr ?_
      exact integrableOn_const (by
        exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ K)))
    have hmono : ∫ x, Set.indicator K (fun _ => (1 : ℝ)) x ∂μ ≤ ∫ x, φ x ∂μ := by
      refine integral_mono hindint hint (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        exact le_of_eq (hφ1 hx).symm
      · rw [Set.indicator_of_notMem hx]
        exact (hφIcc x).1
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) hKcomp.measurableSet, smul_eq_mul,
      mul_one] at hmono
    have hKne : μ K ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ K))
    have hKreal : μ.real Set.univ - ε < μ.real K := by
      rw [MeasureTheory.measureReal_def]
      rcases le_or_gt (μ.real Set.univ - ε) 0 with hneg | hpos2
      · refine lt_of_le_of_lt hneg ?_
        have hKpos : 0 < μ K := lt_of_le_of_lt (bot_le : (0 : ENNReal) ≤ _) hKmeas
        exact ENNReal.toReal_pos hKpos.ne' hKne
      · exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hpos2) hKne).mp hKmeas
    linarith

omit [TopologicalSpace X] [BorelSpace X] [RegularSpace X] [LocallyCompactSpace X] [T2Space X] in
/-- **Sample-supported measures are invisible.**  Any measure concentrated on the sample set pairs
to zero against every test function vanishing there, so subtracting it changes no defect. -/
theorem integral_eq_zero_of_concentrated (ν : Measure X) {Λ : Set X}
    (hν : ν Λᶜ = 0) {φ : X → ℝ} (hφ : ∀ x ∈ Λ, φ x = 0) :
    ∫ x, φ x ∂ν = 0 := by
  refine integral_eq_zero_of_ae ?_
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Λ, ?_, fun x hx => hφ x hx⟩
  rw [mem_ae_iff]
  exact hν

/-- The pairings realized by admissible test functions of the sampling ideal. -/
def samplingPairings (μ : Measure X) (Λ : Set X) : Set ℝ :=
  {r | ∃ φ : C(X, ℝ), (∀ x ∈ Λ, φ x = 0) ∧ (∀ x, |φ x| ≤ 1) ∧ HasCompactSupport φ ∧
    r = ∫ x, φ x ∂μ}

/-- **Equation (1): the exact order-zero sampling defect.**  Sampling a finite positive Radon
measure on a closed null set has defect exactly the full mass — the best bounded linear
reconstruction from the samples is no better than discarding them. -/
theorem isLUB_samplingPairings (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    {Λ : Set X} (hΛ : IsClosed Λ) (hnull : μ Λ = 0) :
    IsLUB (samplingPairings μ Λ) (μ.real Set.univ) := by
  constructor
  · rintro r ⟨φ, _, hbound, _, rfl⟩
    exact le_trans (le_abs_self _) (abs_integral_le_measure_univ μ hbound)
  · intro b hb
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨φ, hvanish, hIcc, hsupp, hgt⟩ :=
      exists_sampleTest_integral_gt μ hΛ hnull (sub_pos.mpr hcon)
    have hmem : (∫ x, φ x ∂μ) ∈ samplingPairings μ Λ := by
      refine ⟨φ, hvanish, fun x => ?_, hsupp, rfl⟩
      rw [abs_of_nonneg (hIcc x).1]
      exact (hIcc x).2
    have hle := hb hmem
    have : μ.real Set.univ - (μ.real Set.univ - b) = b := by ring
    rw [this] at hgt
    linarith

/-- **Completion doubling.**  Adding a reflected copy of the same mass doubles the absolute defect;
the normalized defect stays at its maximal value one. -/
theorem measureReal_add_of_mass_eq (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν Set.univ = μ Set.univ) :
    (μ + ν).real Set.univ = 2 * μ.real Set.univ := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.coe_add, Pi.add_apply, h,
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), MeasureTheory.measureReal_def]
  ring

/-- **The normalized defect is maximal.**  Dividing the defect by the mass gives one for every
nonzero measure. -/
theorem normalized_samplingDefect (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    {Λ : Set X} (hΛ : IsClosed Λ) (hnull : μ Λ = 0) (hne : μ Set.univ ≠ 0) :
    (μ.real Set.univ) / (μ.real Set.univ) = 1 := by
  refine div_self ?_
  rw [MeasureTheory.measureReal_def]
  exact (ENNReal.toReal_pos hne (measure_ne_top μ _)).ne'

end GaloisForLFunctions.HTGeometry.SamplingDefect
