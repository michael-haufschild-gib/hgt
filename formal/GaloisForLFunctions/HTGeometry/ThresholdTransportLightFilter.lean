import GaloisForLFunctions.HTGeometry.PhaseOrbitGradient
import GaloisForLFunctions.HTGeometry.ReplicaReporterExpectation

/-!
# Threshold transport across a common light filter

Discarding the heavy components of a phase orbit moves every overlap amplitude by at most the
discarded norm, hence moves the square root of the complete incidence score by at most that same
slack, uniformly in the target family.

A threshold event for the unfiltered score is therefore contained in the correspondingly relaxed
threshold event for the filtered score, and conversely.  Combining those two inclusions with the
bracketing of the bounded replica reporter mean turns the low-influence estimate for the filtered
score into a two-sided estimate for the unfiltered threshold probability, with an error that is the
exponential replica deficit alone.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance thresholdTransportLightFilterLocalInst1 : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance thresholdTransportLightFilterLocalInst2 :
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance thresholdTransportLightFilterLocalInst3 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Transport

open UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {Z : Type*} [Fintype Z] [Nonempty Z]

set_option linter.unusedSectionVars false

theorem completeSqrtScore_nonneg (u : d → V) (z : Z → V) (x : d → ℝ) :
    0 ≤ completeSqrtScore u z x := by
  refine le_trans (norm_nonneg (overlapAmp u (z (Classical.arbitrary Z)) x)) ?_
  exact le_finiteMax (fun w : Z => sqrtScore u (z w)) x (Classical.arbitrary Z)

theorem completeSqrtScore_eq_sqrt (u : d → V) (z : Z → V) (x : d → ℝ) :
    completeSqrtScore u z x = Real.sqrt (completeScore u z x) := by
  rw [← completeSqrtScore_sq u z x, Real.sqrt_sq (completeSqrtScore_nonneg u z x)]

/-- Every point of the unit torus is the image of a real phase vector. -/
theorem torusProj_surjective : Function.Surjective (torusProj : (d → ℝ) → UnitAddTorus d) := by
  intro t
  choose x hx using fun j : d => QuotientAddGroup.mk_surjective (t j)
  exact ⟨x, funext hx⟩

/-- **Filtering moves the root score by at most the discarded norm.**  Uniformly in the target
family, the square roots of the unfiltered and filtered complete incidence scores differ by at most
the slack determined by the collision weight and the cutoff. -/
theorem abs_sqrt_completeScore_sub_le (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {τ ρ : ℝ} (hτ : 0 < τ)
    (hρ : 0 ≤ ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (x : d → ℝ) :
    |Real.sqrt (completeScore u z x) -
      Real.sqrt (completeScore (lightFamily u τ) z x)| ≤ ρ := by
  have hdiff : ∀ y : d → ℝ, ‖phaseOrbit u y - phaseOrbit (lightFamily u τ) y‖ ≤ ρ := by
    intro y
    have hsq := norm_sq_phaseOrbit_sub_lightFamily_le u horth hτ y
    have hle : (∑ j : d, ‖u j‖ ^ 4) / τ ≤ ρ ^ 2 := by
      rw [div_le_iff₀ hτ]
      exact hC
    have hnn : (0 : ℝ) ≤ ‖phaseOrbit u y - phaseOrbit (lightFamily u τ) y‖ := norm_nonneg _
    nlinarith [hsq, hle, hnn, hρ]
  have h := abs_completeSqrtScore_sub_le u z hz hdiff x
  rwa [completeSqrtScore_eq_sqrt, completeSqrtScore_eq_sqrt] at h

/-- The torus form of the previous bound. -/
theorem abs_sqrt_torusCompleteScore_sub_le (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {τ ρ : ℝ} (hτ : 0 < τ)
    (hρ : 0 ≤ ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (t : UnitAddTorus d) :
    |Real.sqrt (torusCompleteScore u z t) -
      Real.sqrt (torusCompleteScore (lightFamily u τ) z t)| ≤ ρ := by
  obtain ⟨x, rfl⟩ := torusProj_surjective t
  rw [torusCompleteScore_torusProj, torusCompleteScore_torusProj]
  exact abs_sqrt_completeScore_sub_le u z horth hτ hρ hC hz x

theorem torusCompleteScore_mem_unitInterval (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1) (t : UnitAddTorus d) :
    0 ≤ torusCompleteScore u z t ∧ torusCompleteScore u z t ≤ 1 := by
  obtain ⟨x, rfl⟩ := torusProj_surjective t
  rw [torusCompleteScore_torusProj]
  exact completeScore_mem_unitInterval u z x
    fun w y => norm_overlapAmp_le_one u (z w) y horth hu (hz w)

/-- The complete incidence score is nonnegative. -/
theorem torusCompleteScore_nonneg (u : d → V) (z : Z → V) (t : UnitAddTorus d) :
    0 ≤ torusCompleteScore u z t := by
  rw [torusCompleteScore, finiteMax]
  refine le_trans ?_ (Finset.le_sup' (fun w : Z => torusScore u (z w) t)
    (Finset.mem_univ (Classical.arbitrary Z)))
  rw [torusScore]
  positivity

/-- **Threshold inclusion, upward.**  An unfiltered incidence event is contained in the filtered
incidence event at the threshold relaxed by the slack. -/
theorem threshold_subset_light (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {τ ρ a₀ : ℝ} (hτ : 0 < τ)
    (hρ : 0 ≤ ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (ha₀ : ρ ≤ Real.sqrt a₀) :
    {t : UnitAddTorus d | a₀ ≤ torusCompleteScore u z t} ⊆
      {t : UnitAddTorus d |
        (Real.sqrt a₀ - ρ) ^ 2 ≤ torusCompleteScore (lightFamily u τ) z t} := by
  intro t ht
  have hfull : a₀ ≤ torusCompleteScore u z t := ht
  have hsqrt : Real.sqrt a₀ ≤ Real.sqrt (torusCompleteScore u z t) :=
    Real.sqrt_le_sqrt hfull
  have hgap := abs_sqrt_torusCompleteScore_sub_le u z horth hτ hρ hC hz t
  have hgap' : Real.sqrt (torusCompleteScore u z t) -
      Real.sqrt (torusCompleteScore (lightFamily u τ) z t) ≤ ρ :=
    le_trans (le_abs_self _) hgap
  have hlow : Real.sqrt a₀ - ρ ≤ Real.sqrt (torusCompleteScore (lightFamily u τ) z t) := by
    linarith
  have hpos : (0 : ℝ) ≤ Real.sqrt a₀ - ρ := by linarith
  have hscore : 0 ≤ torusCompleteScore (lightFamily u τ) z t :=
    torusCompleteScore_nonneg (lightFamily u τ) z t
  have hsq : (Real.sqrt a₀ - ρ) ^ 2 ≤
      Real.sqrt (torusCompleteScore (lightFamily u τ) z t) ^ 2 := by
    nlinarith [hlow, hpos, Real.sqrt_nonneg (torusCompleteScore (lightFamily u τ) z t)]
  show (Real.sqrt a₀ - ρ) ^ 2 ≤ torusCompleteScore (lightFamily u τ) z t
  rwa [Real.sq_sqrt hscore] at hsq

/-- **Threshold inclusion, downward.**  A filtered incidence event is contained in the unfiltered
incidence event at the threshold tightened by the slack. -/
theorem light_threshold_subset (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {τ ρ b : ℝ} (hτ : 0 < τ)
    (hρ : 0 ≤ ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ) (hz : ∀ w : Z, ‖z w‖ ≤ 1) :
    {t : UnitAddTorus d | b ≤ torusCompleteScore (lightFamily u τ) z t} ⊆
      {t : UnitAddTorus d | max (Real.sqrt b - ρ) 0 ^ 2 ≤ torusCompleteScore u z t} := by
  intro t ht
  have hlight : b ≤ torusCompleteScore (lightFamily u τ) z t := ht
  have hsqrt : Real.sqrt b ≤ Real.sqrt (torusCompleteScore (lightFamily u τ) z t) :=
    Real.sqrt_le_sqrt hlight
  have hgap := abs_sqrt_torusCompleteScore_sub_le u z horth hτ hρ hC hz t
  have hgap' : Real.sqrt (torusCompleteScore (lightFamily u τ) z t) -
      Real.sqrt (torusCompleteScore u z t) ≤ ρ := by
    have := neg_le_of_abs_le hgap
    linarith
  have hlow : Real.sqrt b - ρ ≤ Real.sqrt (torusCompleteScore u z t) := by linarith
  have hnn : (0 : ℝ) ≤ Real.sqrt (torusCompleteScore u z t) := Real.sqrt_nonneg _
  have hmax : max (Real.sqrt b - ρ) 0 ≤ Real.sqrt (torusCompleteScore u z t) :=
    max_le hlow hnn
  have hmax0 : (0 : ℝ) ≤ max (Real.sqrt b - ρ) 0 := le_max_right _ _
  show max (Real.sqrt b - ρ) 0 ^ 2 ≤ torusCompleteScore u z t
  have hscore : 0 ≤ torusCompleteScore u z t := torusCompleteScore_nonneg u z t
  have hsq : max (Real.sqrt b - ρ) 0 ^ 2 ≤ Real.sqrt (torusCompleteScore u z t) ^ 2 := by
    nlinarith [hmax, hmax0, hnn]
  rwa [Real.sq_sqrt hscore] at hsq

/-- **Threshold transport, upper bound.**  The unfiltered incidence probability at a physical
fidelity threshold is bounded by the mean of the light-filtered bounded replica reporter divided by
one minus the exponential replica deficit. -/
theorem measure_threshold_le_integral_lightReporter (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    {τ ρ a₀ b : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ)
    (ha₀ : ρ ^ 2 < a₀) (ha₀1 : a₀ ≤ 1) (hb : 0 < b) (hba : b < (Real.sqrt a₀ - ρ) ^ 2)
    (r : ℕ) :
    (1 - replicaDeficit r ((Real.sqrt a₀ - ρ) ^ 2) b) *
        (volume {t : UnitAddTorus d | a₀ ≤ torusCompleteScore u z t}).toReal ≤
      ∫ t : UnitAddTorus d, binomialTail r
        (replicaThreshold r ((Real.sqrt a₀ - ρ) ^ 2) b)
        (torusCompleteScore (lightFamily u τ) z t) := by
  have hsqrt_pos : ρ < Real.sqrt a₀ := by
    have hlt : Real.sqrt (ρ ^ 2) < Real.sqrt a₀ := Real.sqrt_lt_sqrt (by positivity) ha₀
    rwa [Real.sqrt_sq hρ.le] at hlt
  have hsqrt_le : Real.sqrt a₀ ≤ 1 := by
    have := Real.sqrt_le_sqrt ha₀1
    rwa [Real.sqrt_one] at this
  have ha_lt_one : (Real.sqrt a₀ - ρ) ^ 2 < 1 := by
    have h1 : Real.sqrt a₀ - ρ < 1 := by linarith
    have h2 : 0 < Real.sqrt a₀ - ρ := by linarith
    nlinarith [h1, h2]
  have hlight : ∀ w : Z, ∀ y : d → ℝ, ‖overlapAmp (lightFamily u τ) (z w) y‖ ≤ 1 := by
    intro w y
    exact norm_overlapAmp_le_one (lightFamily u τ) (z w) y (orthogonal_lightFamily u τ horth)
      (sum_norm_lightFamily_sq_le u τ hu) (hz w)
  have hY0 : ∀ t : UnitAddTorus d, 0 ≤ torusCompleteScore (lightFamily u τ) z t := fun t =>
    (torusCompleteScore_mem_unitInterval (lightFamily u τ) z (orthogonal_lightFamily u τ horth)
      (sum_norm_lightFamily_sq_le u τ hu) hz t).1
  have hY1 : ∀ t : UnitAddTorus d, torusCompleteScore (lightFamily u τ) z t ≤ 1 := fun t =>
    (torusCompleteScore_mem_unitInterval (lightFamily u τ) z (orthogonal_lightFamily u τ horth)
      (sum_norm_lightFamily_sq_le u τ hu) hz t).2
  have hYmeas : Measurable (torusCompleteScore (lightFamily u τ) z) :=
    (continuous_torusCompleteScore (lightFamily u τ) z).measurable
  have hmain := replicaDeficit_mul_measure_le_integral (Ω := UnitAddTorus d)
    (ν := (volume : Measure (UnitAddTorus d))) hYmeas hY0 hY1 (r := r) hb hba ha_lt_one
  refine le_trans ?_ hmain
  have hsub := threshold_subset_light u z horth hτ hρ.le hC hz hsqrt_pos.le
  have hmono : (volume {t : UnitAddTorus d | a₀ ≤ torusCompleteScore u z t}).toReal ≤
      (volume {t : UnitAddTorus d |
        (Real.sqrt a₀ - ρ) ^ 2 ≤ torusCompleteScore (lightFamily u τ) z t}).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hdef : 0 ≤ 1 - replicaDeficit r ((Real.sqrt a₀ - ρ) ^ 2) b := by
    have := replicaDeficit_le_one r ((Real.sqrt a₀ - ρ) ^ 2) b
    linarith
  exact mul_le_mul_of_nonneg_left hmono hdef

/-- **Threshold transport, lower bound.**  The mean of the light-filtered bounded replica reporter
is bounded by the unfiltered incidence probability at the tightened threshold plus the exponential
replica deficit. -/
theorem integral_lightReporter_le_measure_threshold (u : d → V) (z : Z → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    {τ ρ a b : ℝ} (hτ : 0 < τ) (hρ : 0 ≤ ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * τ)
    (hba : b < a) (ha : a < 1) (r : ℕ) :
    (∫ t : UnitAddTorus d, binomialTail r (replicaThreshold r a b)
        (torusCompleteScore (lightFamily u τ) z t)) ≤
      (volume {t : UnitAddTorus d |
        max (Real.sqrt b - ρ) 0 ^ 2 ≤ torusCompleteScore u z t}).toReal +
        replicaDeficit r a b := by
  have hY0 : ∀ t : UnitAddTorus d, 0 ≤ torusCompleteScore (lightFamily u τ) z t := fun t =>
    (torusCompleteScore_mem_unitInterval (lightFamily u τ) z (orthogonal_lightFamily u τ horth)
      (sum_norm_lightFamily_sq_le u τ hu) hz t).1
  have hY1 : ∀ t : UnitAddTorus d, torusCompleteScore (lightFamily u τ) z t ≤ 1 := fun t =>
    (torusCompleteScore_mem_unitInterval (lightFamily u τ) z (orthogonal_lightFamily u τ horth)
      (sum_norm_lightFamily_sq_le u τ hu) hz t).2
  have hYmeas : Measurable (torusCompleteScore (lightFamily u τ) z) :=
    (continuous_torusCompleteScore (lightFamily u τ) z).measurable
  have hmain := integral_le_measure_add_replicaDeficit (Ω := UnitAddTorus d)
    (ν := (volume : Measure (UnitAddTorus d))) hYmeas hY0 hY1 (r := r) hba ha
  refine le_trans hmain ?_
  have hsub := light_threshold_subset u z horth hτ hρ hC hz (b := b)
  have hmono : (volume {t : UnitAddTorus d |
      b ≤ torusCompleteScore (lightFamily u τ) z t}).toReal ≤
      (volume {t : UnitAddTorus d |
        max (Real.sqrt b - ρ) 0 ^ 2 ≤ torusCompleteScore u z t}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  linarith


/-- The cutoff calibrated to a collision weight and a prescribed slack. -/
def collisionCutoff (C ρ : ℝ) : ℝ := C / ρ ^ 2

theorem collisionCutoff_pos {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) : 0 < collisionCutoff C ρ := by
  rw [collisionCutoff]
  positivity

theorem sum_norm_pow_four_le_calibrated (u : d → V) {C ρ : ℝ} (hρ : 0 < ρ)
    (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ C) :
    ∑ j : d, ‖u j‖ ^ 4 ≤ ρ ^ 2 * collisionCutoff C ρ := by
  rw [collisionCutoff]
  have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
  rw [mul_div_cancel₀ C (ne_of_gt hρ2)]
  exact hC

/-- **Discarded weight at the calibrated cutoff.**  Retaining only the components of weight at most
the calibrated cutoff discards at most the squared slack. -/
theorem norm_sq_phaseOrbit_sub_calibrated_le (u : d → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {C ρ : ℝ} (hC0 : 0 < C)
    (hρ : 0 < ρ) (hC : ∑ j : d, ‖u j‖ ^ 4 ≤ C) (x : d → ℝ) :
    ‖phaseOrbit u x - phaseOrbit (lightFamily u (collisionCutoff C ρ)) x‖ ^ 2 ≤ ρ ^ 2 := by
  refine le_trans (norm_sq_phaseOrbit_sub_lightFamily_le u horth
    (collisionCutoff_pos hC0 hρ) x) ?_
  rw [div_le_iff₀ (collisionCutoff_pos hC0 hρ)]
  exact sum_norm_pow_four_le_calibrated u hρ hC

/-- **Light-filtered influence at the calibrated cutoff.**  The variance of the light-filtered
bounded replica reporter is at most four times the squared replica order times the collision weight
divided by the squared slack, with no dependence on the number of targets. -/
theorem variance_calibrated_reporter_le [DecidableEq V] (u : d → V) (z : Z → V) {B : ℝ → ℝ}
    (hB : Continuous B) {B' : ℝ → ℝ} (hBderiv : ∀ s : ℝ, HasDerivAt B (B' s) s) {r C ρ : ℝ}
    (hr : 0 ≤ r) (hC0 : 0 < C) (hρ : 0 < ρ)
    (hB'bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → |B' s| ≤ r)
    (hBlip : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |B a - B b| ≤ r * |a - b|)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1) :
    (∫ t : UnitAddTorus d,
        ‖torusReporterMap (lightFamily u (collisionCutoff C ρ)) z hB t‖ ^ 2) -
        ‖∫ t : UnitAddTorus d,
          torusReporterMap (lightFamily u (collisionCutoff C ρ)) z hB t‖ ^ 2 ≤
      4 * r ^ 2 * (C / ρ ^ 2) :=
  variance_lightFamily_reporter_le u z hB hBderiv hr (collisionCutoff_pos hC0 hρ).le
    hB'bound hBlip horth hu hz

/-- **Collision-controlled influence.**  A collision weight inversely proportional to the dimension
makes the light-filtered variance inversely proportional to the dimension. -/
theorem variance_calibrated_reporter_le_of_collision [DecidableEq V] (u : d → V) (z : Z → V)
    {B : ℝ → ℝ} (hB : Continuous B) {B' : ℝ → ℝ} (hBderiv : ∀ s : ℝ, HasDerivAt B (B' s) s)
    {r C ρ c D : ℝ} (hr : 0 ≤ r) (hC0 : 0 < C) (hρ : 0 < ρ) (hD : 0 < D) (hcD : C ≤ c / D)
    (hB'bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → |B' s| ≤ r)
    (hBlip : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |B a - B b| ≤ r * |a - b|)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1) :
    (∫ t : UnitAddTorus d,
        ‖torusReporterMap (lightFamily u (collisionCutoff C ρ)) z hB t‖ ^ 2) -
        ‖∫ t : UnitAddTorus d,
          torusReporterMap (lightFamily u (collisionCutoff C ρ)) z hB t‖ ^ 2 ≤
      4 * c * r ^ 2 / (ρ ^ 2 * D) := by
  refine le_trans (variance_calibrated_reporter_le u z hB hBderiv hr hC0 hρ hB'bound hBlip
    horth hu hz) ?_
  have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
  have hCD : C * D ≤ c := by
    rw [← le_div_iff₀ hD]
    exact hcD
  have hr2 : (0 : ℝ) ≤ 4 * r ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2 * D)]
  have hexp : 4 * r ^ 2 * (C / ρ ^ 2) * (ρ ^ 2 * D) = 4 * r ^ 2 * (C * D) := by
    field_simp
  rw [hexp]
  nlinarith [hCD, hr2]

end Transport

end

end GaloisForLFunctions.HTGeometry
