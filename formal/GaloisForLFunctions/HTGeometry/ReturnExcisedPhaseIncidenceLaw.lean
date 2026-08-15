import GaloisForLFunctions.HTGeometry.TorusReplicaMomentBound
import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw

/-!
# Return-excised phase incidence at every replica order

Removing one common heavy spectral sector costs at most a factor four in the capture threshold, and
the surviving light orbit has replica fidelity moment at most the replica factorial times the cap to
the replica order.  Feeding that moment into the occupied-endpoint optimal design bounds the phase
mass of every capture event by the mass of the independently fixed return set plus the replica
moment divided by the replica threshold.

Both the heavy sector and the return set are chosen before any target is estimated, so the bound is
quenched: it holds pointwise for every target family and every replica order.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section Regularity

theorem continuous_phaseOrbit_apply (q : d → ℝ) (j : d) :
    Continuous fun x : d → ℝ => phaseOrbit q x j :=
  continuous_const.mul (continuous_charLift _)

theorem continuous_finiteComplexInner_phaseOrbit (q : d → ℝ) (z : d → ℂ) :
    Continuous fun x : d → ℝ => finiteComplexInner (phaseOrbit q x) z := by
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact (Complex.continuous_conj.comp (continuous_phaseOrbit_apply q j)).mul continuous_const

theorem continuous_fidelity_phaseOrbit (q : d → ℝ) (z : d → ℂ) :
    Continuous fun x : d → ℝ => finitePureStateFidelity (phaseOrbit q x) z :=
  ((continuous_finiteComplexInner_phaseOrbit q z).norm).pow 2

theorem fidelity_phaseOrbit_nonneg (q : d → ℝ) (z : d → ℂ) (x : d → ℝ) :
    0 ≤ finitePureStateFidelity (phaseOrbit q x) z := sq_nonneg _

theorem fidelity_phaseOrbit_le_one {q : d → ℝ} (hq : ∀ j, 0 ≤ q j) (hqsum : ∑ j, q j ≤ 1)
    {z : d → ℂ} (hz : ∑ j, ‖z j‖ ^ 2 ≤ 1) (x : d → ℝ) :
    finitePureStateFidelity (phaseOrbit q x) z ≤ 1 := by
  have hbase := norm_finiteComplexInner_le (phaseOrbit q x) z
  rw [sum_normSq_phaseOrbit hq x] at hbase
  have h1 : Real.sqrt (∑ j, q j) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hqsum
  have h2 : Real.sqrt (∑ j, ‖z j‖ ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hz
  have hle : ‖finiteComplexInner (phaseOrbit q x) z‖ ≤ 1 :=
    le_trans hbase (by nlinarith [Real.sqrt_nonneg (∑ j, q j),
      Real.sqrt_nonneg (∑ j, ‖z j‖ ^ 2)])
  rw [finitePureStateFidelity]
  nlinarith [norm_nonneg (finiteComplexInner (phaseOrbit q x) z)]

theorem integrableOn_box_fidelity_pow {q : d → ℝ} (hq : ∀ j, 0 ≤ q j) (hqsum : ∑ j, q j ≤ 1)
    {z : d → ℂ} (hz : ∑ j, ‖z j‖ ^ 2 ≤ 1) (r : ℕ) :
    IntegrableOn (fun x => finitePureStateFidelity (phaseOrbit q x) z ^ r) (torusBox d) volume := by
  haveI := isFiniteMeasure_restrict_torusBox (d := d)
  refine Integrable.of_bound
    (((continuous_fidelity_phaseOrbit q z).pow r).aestronglyMeasurable) 1 ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (pow_nonneg (fidelity_phaseOrbit_nonneg q z x) r)]
  exact pow_le_one₀ (fidelity_phaseOrbit_nonneg q z x)
    (fidelity_phaseOrbit_le_one hq hqsum hz x)

end Regularity

section Assembly

variable {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]

/-- **Return-excised quenched phase-incidence law.**  Every capture event on the spectral phase
torus is bounded by the mass of the independently fixed return set plus the replica moment of the
light orbit divided by the replica threshold. -/
theorem measureReal_capture_le_return_add_replicaMoment
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {R Q : Set (d → ℝ)} (hR : MeasurableSet R) (hQ : MeasurableSet Q)
    (hcap : ∀ x ∈ Q \ R, ∃ c, a ≤ finitePureStateFidelity (phaseOrbit p x) (z c))
    (r : ℕ) :
    (volume.restrict (torusBox d)).real Q ≤
      (volume.restrict (torusBox d)).real R +
        (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
          (16 * occupationCollision p / a ^ 2) ^ r := by
  classical
  haveI := isFiniteMeasure_restrict_torusBox (d := d)
  set μ : Measure (d → ℝ) := volume.restrict (torusBox d) with hμ
  set τ : ℝ := 4 * occupationCollision p / a with hτdef
  set q : d → ℝ := lightWeights p τ with hqdef
  have hq : ∀ j, 0 ≤ q j := lightWeights_nonneg hp τ
  have hτ0 : 0 ≤ τ := by
    rw [hτdef]
    have : (0 : ℝ) ≤ occupationCollision p := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  have hqle : ∀ j, q j ≤ τ := lightWeights_le τ hτ0
  have hqsum : ∑ j, q j ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) hpsum
    rw [hqdef, lightWeights]
    split <;> [exact hp j; exact le_rfl]
  -- the heavy-sector transfer
  have hheavy : ∑ j, heavyWeights p τ j ≤ a / 4 := sum_heavyWeights_le hp ha
  have htransfer : ∀ x ∈ Q \ R, ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c) := by
    intro x hx
    obtain ⟨c, hc⟩ := hcap x hx
    exact ⟨c, fidelity_lightWeights_ge hp ha hheavy (hznorm c) hc⟩
  -- the design law on the return complement
  have hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity (phaseOrbit q x) (z c) ^ r) (μ.restrict Rᶜ) := by
    intro c
    refine Integrable.mono_measure ?_ (Measure.restrict_le_self)
    exact integrableOn_box_fidelity_pow hq hqsum (hznorm c) r
  obtain ⟨w, hw, hfirst, -⟩ := measure_completeTargetCapture_le_optimalDesignMoments
    (μ := μ) (r := r) z (fun x => phaseOrbit q x) hz (a / 4) (by positivity) R hR hint
  -- the replica moment on the box dominates the moment on the return complement
  have hmoment : ∀ c, (∫ x, finitePureStateFidelity (phaseOrbit q x) (z c) ^ r ∂(μ.restrict Rᶜ))
      ≤ (r.factorial : ℝ) * τ ^ r := by
    intro c
    refine le_trans (integral_mono_measure Measure.restrict_le_self ?_
      (integrableOn_box_fidelity_pow hq hqsum (hznorm c) r)) ?_
    · filter_upwards with x
      exact pow_nonneg (fidelity_phaseOrbit_nonneg q (z c) x) r
    · exact integral_box_fidelity_pow_le hq hqle hτ0 (hznorm c) r
  have hsum : (∑ c, w c * ∫ x, finitePureStateFidelity (phaseOrbit q x) (z c) ^ r
      ∂(μ.restrict Rᶜ)) ≤ (r.factorial : ℝ) * τ ^ r := by
    calc (∑ c, w c * ∫ x, finitePureStateFidelity (phaseOrbit q x) (z c) ^ r ∂(μ.restrict Rᶜ))
        ≤ ∑ c, w c * ((r.factorial : ℝ) * τ ^ r) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hmoment c) (hw.1 c)
      _ = (r.factorial : ℝ) * τ ^ r := by
          rw [← Finset.sum_mul, hw.2, one_mul]
  -- transfer the capture event
  have hsubset : Q \ R ⊆ {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} ∩ Rᶜ := by
    intro x hx
    exact ⟨htransfer x hx, hx.2⟩
  have hmeasE : MeasurableSet {x : d → ℝ | ∃ c,
      a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} := by
    have : {x : d → ℝ | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} =
        ⋃ c : C, {x : d → ℝ | a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iUnion fun c =>
      measurableSet_le measurable_const (continuous_fidelity_phaseOrbit q (z c)).measurable
  have hQR : μ.real Q ≤ μ.real R + (μ.restrict Rᶜ).real
      {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} := by
    have hcover : Q ⊆ R ∪ (Q \ R) := fun x hx => by
      by_cases hxR : x ∈ R
      · exact Or.inl hxR
      · exact Or.inr ⟨hx, hxR⟩
    have h1 : μ.real Q ≤ μ.real R + μ.real (Q \ R) := by
      refine le_trans (measureReal_mono hcover (by
        exact ne_of_lt (measure_lt_top μ _))) ?_
      exact measureReal_union_le R (Q \ R)
    have h2 : μ.real (Q \ R) ≤ (μ.restrict Rᶜ).real
        {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} := by
      rw [Measure.real, Measure.real, Measure.restrict_apply hmeasE]
      refine ENNReal.toReal_mono (by exact ne_of_lt (measure_lt_top μ _)) ?_
      exact measure_mono hsubset
    linarith
  -- combine
  have hthr : (0 : ℝ) < (a / 4) ^ r := by positivity
  have hkey : (μ.restrict Rᶜ).real
      {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} ≤
      (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) * τ ^ r / (a / 4) ^ r := by
    rw [le_div_iff₀ hthr]
    have hfr : (0 : ℝ) ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) := Nat.cast_nonneg _
    calc (μ.restrict Rᶜ).real
          {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} * (a / 4) ^ r
        = (a / 4) ^ r * (μ.restrict Rᶜ).real
            {x | ∃ c, a / 4 ≤ finitePureStateFidelity (phaseOrbit q x) (z c)} := by ring
      _ ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) *
            ∑ c, w c * ∫ x, finitePureStateFidelity (phaseOrbit q x) (z c) ^ r
              ∂(μ.restrict Rᶜ) := hfirst
      _ ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * ((r.factorial : ℝ) * τ ^ r) :=
          mul_le_mul_of_nonneg_left hsum hfr
      _ = (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) * τ ^ r := by ring
  have hscale : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) * τ ^ r /
      (a / 4) ^ r =
      (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision p / a ^ 2) ^ r := by
    rw [hτdef, ← div_pow]
    congr 2
    field_simp
    ring
  rw [← hscale]
  linarith

end Assembly

end GaloisForLFunctions.HTGeometry
