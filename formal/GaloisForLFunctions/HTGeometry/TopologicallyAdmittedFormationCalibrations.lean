import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedCompactEffectProperness
import GaloisForLFunctions.HTGeometry.GammaSixGlobalPolarity
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen

/-!
# Two arithmetic calibrations of the compact-effect formation law

**Gamma-six occupancy source.**  Push the labelled Gamma-six formation through coordinatewise
occupancy `k ↦ 1_{k ≠ 0}` onto the compact Cantor product `Bool^{GammaSixLabel}`.  Every coordinate
occupancy probability lies strictly between `0` and `1`, so every nonempty cylinder has positive
mass and both reflected laws have full support; off the centre the finite-occupancy event separates
them.

**Prime-Poisson torus source.**  On the compact prime torus each one-prime Poisson law has a
positive density against Haar measure, so the product laws have full support, and away from the
critical grade the reflected laws are mutually singular.

In both sources every nonneutral finite target is formed exactly at every depth by a measurable
kernel whose effects are continuous nowhere, while every family of continuous effects forming it at
unbounded depth fails to be equicontinuous.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance topologicallyAdmittedFormationCalibrationsLocalInst : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

/-- Infinite products of full-support probability laws have full support. -/
theorem isOpenPosMeasure_infinitePi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, OpensMeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsOpenPosMeasure] :
    (Measure.infinitePi μ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  have hpos : Measure.infinitePi μ ((I : Set ι).pi u) ≠ 0 := by
    rw [Measure.infinitePi_pi μ (fun i hi => (hu i hi).1.measurableSet)]
    exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      (hu i hi).1.measure_ne_zero (μ i) ⟨x i, (hu i hi).2⟩
  exact fun h0 => hpos (measure_mono_null hsub h0)

/-! ## The Gamma-six occupancy source -/

section GammaSix

/-- Coordinatewise occupancy `k ↦ 1_{k ≠ 0}`. -/
def gammaSixOccupancy (k : GammaSixLabel → ℕ) : GammaSixLabel → Bool := fun l => decide (k l ≠ 0)

theorem measurable_gammaSixOccupancy : Measurable gammaSixOccupancy :=
  measurable_pi_lambda _ fun l => (measurable_of_countable (fun n : ℕ => decide (n ≠ 0))).comp
    (measurable_pi_apply l)

/-- The Gamma-six occupancy law on the Cantor product. -/
def gammaSixOccupancyLaw (δ : ℝ) : Measure (GammaSixLabel → Bool) :=
  (gammaSixLaw δ).map gammaSixOccupancy

instance (δ : ℝ) : IsProbabilityMeasure (gammaSixOccupancyLaw δ) :=
  Measure.isProbabilityMeasure_map measurable_gammaSixOccupancy.aemeasurable

/-- **Full support.**  Every nonempty cylinder of the Cantor product has positive occupancy mass. -/
theorem isOpenPosMeasure_gammaSixOccupancyLaw (δ : ℝ) :
    (gammaSixOccupancyLaw δ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨b, hb⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU b hb
  set C : Set (GammaSixLabel → Bool) := (I : Set GammaSixLabel).pi fun l => {b l} with hC
  have hCU : C ⊆ U := fun c hc => hsub fun l hl => by
    have : c l = b l := hc l hl
    rw [this]
    exact (hu l hl).2
  have hCm : MeasurableSet C := MeasurableSet.pi I.countable_toSet fun l _ =>
    measurableSet_singleton _
  have hpre : gammaSixOccupancy ⁻¹' C
      = (I : Set GammaSixLabel).pi fun l => {n : ℕ | decide (n ≠ 0) = b l} := by
    ext k
    simp [hC, gammaSixOccupancy, Set.mem_pi]
  have hpos : gammaSixOccupancyLaw δ C ≠ 0 := by
    rw [gammaSixOccupancyLaw, Measure.map_apply measurable_gammaSixOccupancy hCm, hpre,
      gammaSixLaw, Measure.infinitePi_pi _ (fun l _ => (Set.to_countable _).measurableSet)]
    refine Finset.prod_ne_zero_iff.mpr fun l _ => ?_
    have hr : 0 < gammaSixForward (l.1 + 3) δ := gammaSixForward_pos _ _
    cases hbl : b l
    · have hset : {n : ℕ | decide (n ≠ 0) = false} = {0} := by
        ext n
        simp
      rw [hset, poissonMeasure_singleton]
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      exact Real.exp_pos _
    · have hset : {n : ℕ | decide (n ≠ 0) = true} = ({0} : Set ℕ)ᶜ := by
        ext n
        simp
      rw [hset, gammaSix_occupancyMass]
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      have : Real.exp (-gammaSixForward (l.1 + 3) δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
  exact fun h0 => hpos (measure_mono_null hCU h0)

/-- The finite-occupancy event of the Cantor product. -/
def cantorFiniteOccupancy : Set (GammaSixLabel → Bool) := {b | {l | b l = true}.Finite}

theorem measurableSet_cantorFiniteOccupancy : MeasurableSet cantorFiniteOccupancy := by
  let g : (GammaSixLabel → Bool) → (GammaSixLabel → ℕ) := fun b l => if b l then 1 else 0
  have hg : Measurable g := measurable_pi_lambda _ fun l =>
    (measurable_of_countable (fun c : Bool => if c then (1 : ℕ) else 0)).comp
      (measurable_pi_apply l)
  have hpre : cantorFiniteOccupancy = g ⁻¹' {k | (occupiedSet k).Finite} := by
    ext b
    simp [cantorFiniteOccupancy, occupiedSet, g]
  rw [hpre]
  exact hg (measurableSet_finiteOccupancy gammaSixLabelEquiv)

theorem gammaSixOccupancy_preimage_finite :
    gammaSixOccupancy ⁻¹' cantorFiniteOccupancy = {k | (occupiedSet k).Finite} := by
  ext k
  simp [cantorFiniteOccupancy, gammaSixOccupancy, occupiedSet]

theorem gammaSixOccupancyLaw_mutuallySingular_of_pos {δ : ℝ} (hδ : 0 < δ) :
    (gammaSixOccupancyLaw δ).MutuallySingular (gammaSixOccupancyLaw (-δ)) := by
  refine ⟨cantorFiniteOccupancy, measurableSet_cantorFiniteOccupancy, ?_, ?_⟩
  · rw [gammaSixOccupancyLaw, Measure.map_apply measurable_gammaSixOccupancy
      measurableSet_cantorFiniteOccupancy, gammaSixOccupancy_preimage_finite, gammaSixLaw,
      finiteOccupancy_eq_compl,
      MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteOccupancy gammaSixLabelEquiv)]
    exact measure_infiniteOccupancy_eq_one _ gammaSixLabelEquiv
      (tsum_gammaSix_occupancy_eq_top hδ)
  · rw [gammaSixOccupancyLaw, Measure.map_apply measurable_gammaSixOccupancy
      measurableSet_cantorFiniteOccupancy.compl, Set.preimage_compl,
      gammaSixOccupancy_preimage_finite, gammaSixLaw,
      show ({k : GammaSixLabel → ℕ | (occupiedSet k).Finite}ᶜ)
        = {k : GammaSixLabel → ℕ | (occupiedSet k).Infinite} from by
      rw [finiteOccupancy_eq_compl, compl_compl]]
    exact measure_infiniteOccupancy_eq_zero _ gammaSixLabelEquiv
      (tsum_gammaSix_occupancy_ne_top hδ)

/-- **Calibration 9.1.**  Off the centre the two reflected occupancy laws on the compact Cantor
product have full support and are mutually singular. -/
theorem gammaSixOccupancyLaw_mutuallySingular {δ : ℝ} (hδ : δ ≠ 0) :
    (gammaSixOccupancyLaw δ).MutuallySingular (gammaSixOccupancyLaw (-δ)) := by
  rcases lt_or_gt_of_ne hδ with h | h
  · have h' : 0 < -δ := by linarith
    have := gammaSixOccupancyLaw_mutuallySingular_of_pos h'
    rw [neg_neg] at this
    exact this.symm
  · exact gammaSixOccupancyLaw_mutuallySingular_of_pos h

end GammaSix

/-! ## The prime-Poisson torus source -/

section PrimeTorus

/-- Full support is transported by a homeomorphism. -/
theorem isOpenPosMeasure_map_homeomorph' {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X)
    [μ.IsOpenPosMeasure] (h : X ≃ₜ Y) : (μ.map h).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [Measure.map_apply h.measurable hU.measurableSet]
  exact (hU.preimage h.continuous).measure_ne_zero μ (hne.preimage h.surjective)

theorem isOpenPosMeasure_circleLebesgue : circleLebesgue.IsOpenPosMeasure := by
  unfold circleLebesgue
  exact isOpenPosMeasure_map_homeomorph' _ _

/-- The one-prime Poisson law has full support on the circle. -/
theorem isOpenPosMeasure_circlePoissonMeasure (a : CirclePoissonParameter) :
    (circlePoissonMeasure a).IsOpenPosMeasure := by
  haveI := isOpenPosMeasure_circleLebesgue
  refine ⟨fun U hU hne => ?_⟩
  have hdens : Measurable (circlePoissonDensity a) :=
    (ENNReal.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)).measurable
  have hsupp : Function.support (circlePoissonDensity a) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true, circlePoissonDensity, ne_eq,
      ENNReal.ofReal_eq_zero, not_le]
    exact poissonKernel_pos (c := 0) (R := 1)
      (by rw [mem_sphere_iff_norm, sub_zero, Circle.norm_coe]) a.2
  rw [circlePoissonMeasure, withDensity_apply _ hU.measurableSet]
  refine (((setLIntegral_pos_iff hdens).mpr ?_)).ne'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos circleLebesgue hne

theorem isOpenPosMeasure_addCirclePoisson (a : CirclePoissonParameter) :
    ((addCirclePoissonProbabilityMeasure a : ProbabilityMeasure UnitAddCircle) :
      Measure UnitAddCircle).IsOpenPosMeasure := by
  haveI : ((circlePoissonProbabilityMeasure a : ProbabilityMeasure Circle) :
      Measure Circle).IsOpenPosMeasure := isOpenPosMeasure_circlePoissonMeasure a
  rw [addCirclePoissonProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
  exact isOpenPosMeasure_map_homeomorph' _ _

/-- The product Poisson law has full support on the torus. -/
theorem isOpenPosMeasure_torusPoissonMeasure {I : Type*} (a : I → CirclePoissonParameter) :
    (torusPoissonMeasure a).IsOpenPosMeasure := by
  haveI := fun i => isOpenPosMeasure_addCirclePoisson (a i)
  unfold torusPoissonMeasure
  exact isOpenPosMeasure_infinitePi _

/-- **Calibration 9.2.**  Away from the critical grade the reflected prime-Poisson laws on the
compact prime torus have full support and are mutually singular. -/
theorem primePoissonMeasure_reflection_calibration (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hwall : σ ≠ 1 / 2) :
    (primePoissonMeasure σ t hσ).IsOpenPosMeasure ∧
      (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).IsOpenPosMeasure ∧
      (primePoissonMeasure σ t hσ).MutuallySingular
        (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) :=
  ⟨isOpenPosMeasure_torusPoissonMeasure _, isOpenPosMeasure_torusPoissonMeasure _,
    primePoissonMeasure_reflection_mutuallySingular_of_ne_half σ t hσ hσ1 hwall⟩

end PrimeTorus

/-! ## Consequences in both sources -/

section Consequences

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- In the Gamma-six occupancy source every nonneutral finite target is formed exactly at every
positive depth by a measurable kernel with an effect continuous nowhere. -/
theorem gammaSix_measurable_formation {δ : ℝ} (hδ : δ ≠ 0) (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {d : ℕ} (hd : 0 < d) :
    ∃ K : ProbabilityTheory.Kernel (GammaSixLabel → Bool) (Fin d → Y),
      ProbabilityTheory.IsMarkovKernel K ∧ IsExactFormation (gammaSixOccupancyLaw δ) K p₀ ∧
        IsExactFormation (gammaSixOccupancyLaw (-δ)) K p₁ ∧
        ∃ B : Set (Fin d → Y), MeasurableSet B ∧ ∀ x, ¬ ContinuousAt (formationEffect K B) x := by
  haveI := isOpenPosMeasure_gammaSixOccupancyLaw δ
  haveI := isOpenPosMeasure_gammaSixOccupancyLaw (-δ)
  have hPQ := gammaSixOccupancyLaw_mutuallySingular hδ
  obtain ⟨h₀, h₁⟩ := isExactFormation_singularWitnessFormation hPQ p₀ p₁ d
  exact ⟨_, inferInstance, h₀, h₁, exists_nowhere_continuous_singularWitnessFormation hPQ p₀ p₁
    hne hd⟩

/-- In the Gamma-six occupancy source every family of continuous effects forming a nonneutral
target at unbounded depth fails to be equicontinuous. -/
theorem gammaSix_not_equicontinuous (δ : ℝ) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {F : Set C(GammaSixLabel → Bool, ℝ)}
    (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N,
      FormsInFamily (gammaSixOccupancyLaw δ) (gammaSixOccupancyLaw (-δ)) p₀ p₁ F d) :
    ¬ Equicontinuous fun f : F =>
      ((f : C(GammaSixLabel → Bool, ℝ)) : (GammaSixLabel → Bool) → ℝ) := by
  haveI := isOpenPosMeasure_gammaSixOccupancyLaw δ
  haveI := isOpenPosMeasure_gammaSixOccupancyLaw (-δ)
  exact not_equicontinuous_of_formsInFamily _ _ p₀ p₁ hne hb hform

/-- In the prime-Poisson torus source every nonneutral finite target is formed exactly at every
positive depth by a measurable kernel with an effect continuous nowhere. -/
theorem primeTorus_measurable_formation (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hwall : σ ≠ 1 / 2) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁]
    (hne : p₀ ≠ p₁) {d : ℕ} (hd : 0 < d) :
    ∃ K : ProbabilityTheory.Kernel (Nat.Primes → UnitAddCircle) (Fin d → Y),
      ProbabilityTheory.IsMarkovKernel K ∧ IsExactFormation (primePoissonMeasure σ t hσ) K p₀ ∧
        IsExactFormation (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) K p₁ ∧
        ∃ B : Set (Fin d → Y), MeasurableSet B ∧ ∀ x, ¬ ContinuousAt (formationEffect K B) x := by
  obtain ⟨h₁, h₂, hPQ⟩ := primePoissonMeasure_reflection_calibration σ t hσ hσ1 hwall
  obtain ⟨e₀, e₁⟩ := isExactFormation_singularWitnessFormation hPQ p₀ p₁ d
  exact ⟨_, inferInstance, e₀, e₁, exists_nowhere_continuous_singularWitnessFormation hPQ p₀ p₁
    hne hd⟩

/-- In the prime-Poisson torus source every family of continuous effects forming a nonneutral
target at unbounded depth fails to be equicontinuous. -/
theorem primeTorus_not_equicontinuous (σ t : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁)
    {F : Set C(Nat.Primes → UnitAddCircle, ℝ)} (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily (primePoissonMeasure σ t hσ)
      (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)) p₀ p₁ F d) :
    ¬ Equicontinuous fun f : F =>
      ((f : C(Nat.Primes → UnitAddCircle, ℝ)) : (Nat.Primes → UnitAddCircle) → ℝ) := by
  haveI : (primePoissonMeasure σ t hσ).IsOpenPosMeasure := isOpenPosMeasure_torusPoissonMeasure _
  haveI : (primePoissonMeasure (1 - σ) t (sub_pos.mpr hσ1)).IsOpenPosMeasure :=
    isOpenPosMeasure_torusPoissonMeasure _
  exact not_equicontinuous_of_formsInFamily _ _ p₀ p₁ hne hb hform

end Consequences

end GaloisForLFunctions.HTGeometry
