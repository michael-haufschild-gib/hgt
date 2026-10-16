import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGeneralTemporalTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWSourceBoundaryNullAdmission
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Full retarded response on its two compact source triangles

The ingoing onset and the physical radial wall reduce the direct and image
source domains to compact triangles in source null coordinates. The factor
one quarter retains both the causal-kernel normalization and the null Jacobian.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower.D4BMPWRetardedTriangle
open D4BMJointSource D4BMModularCore D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCausalPeierls
open D4BMFullAngularReconstruction
open D4BMGeneralTemporalTransposition

noncomputable section
set_option autoImplicit false

private def nullChart : Event ≃ₜ Event where
  toFun z := ((z.1 + z.2) / 2, (z.1 - z.2) / 2)
  invFun z := (z.1 + z.2, z.1 - z.2)
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem nullChart_volume :
    Measure.map nullChart volume = (2 : ℝ≥0∞) • (volume : Measure Event) := by
  let N : Event → Event := fun p => (-p.1, p.2)
  have hn : MeasurePreserving N (volume : Measure Event) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id volume)
  have he : (nullChart : Event → Event) = N ∘ pastVertex 0 0 := by
    funext z
    ext <;> dsimp [nullChart, N, pastVertex] <;> ring
  rw [he, ← Measure.map_map hn.measurable (by unfold pastVertex; fun_prop),
    pastVertex_volume, Measure.map_smul, hn.map_eq]

private theorem integral_nullChart (F : Event → ℂ) :
    (∫ z : Event, F (nullChart z)) = 2 * (∫ z : Event, F z) := by
  have h := nullChart.toMeasurableEquiv.measurableEmbedding.integral_map F (μ := volume)
  change (∫ z : Event, F z ∂Measure.map nullChart volume) =
    ∫ z : Event, F (nullChart z) at h
  rw [nullChart_volume, integral_smul_measure] at h
  simpa only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat] using h.symm

/-- The full angular source sampled on a direct or reflected source triangle. -/
def triangleDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (image : Bool) (p r X k : ℝ) (z : Event) : ℂ :=
  angularMean q branch (Real.arcosh (max 1
    (invariant ((p + r - z.1 - z.2) / 2) ((p - r) / 2)
      (if image then -((z.1 - z.2) / 2) else (z.1 - z.2) / 2)))) X k *
    timeReducedCoefficient (physicalRate q b) a
      ((z.1 + z.2) / 2) ((z.1 - z.2) / 2)

theorem triangleDensity_continuous (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (image : Bool) (p r X k : ℝ) :
    Continuous (triangleDensity q branch b a image p r X k) := by
  have hi : Continuous (fun z : Event =>
      invariant ((p + r - z.1 - z.2) / 2) ((p - r) / 2)
        (if image then -((z.1 - z.2) / 2) else (z.1 - z.2) / 2)) := by
    cases image <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      unfold invariant
      apply Continuous.div <;> try fun_prop
      intro z
      exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hr := Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
    (fun z => le_max_left (1 : ℝ) _)
  have hc : Continuous (fun z : Event => ((z.1 + z.2) / 2, (z.1 - z.2) / 2)) := by
    fun_prop
  have hf := (timeReducedCoefficient_joint_continuous (physicalRate q b) a).comp hc
  exact ((angularMean_smooth q branch X k).continuous.comp hr).mul hf

private def triangleSet (p r : ℝ) : Set Event :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ p ∧ z.1 ≤ z.2 ∧ z.2 ≤ r}

private theorem triangleSet_measurable (p r : ℝ) : MeasurableSet (triangleSet p r) := by
  unfold triangleSet
  exact ((measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))))

private theorem triangleSet_integrable (F : Event → ℂ) (hF : Continuous F)
    (p r : ℝ) : Integrable ((triangleSet p r).indicator F) := by
  apply IntegrableOn.integrable_indicator _ (triangleSet_measurable p r)
  apply (hF.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc 0 p ×ˢ Icc 0 r))).mono_set
  intro z hz
  exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.1.trans hz.2.2.1, hz.2.2.2⟩⟩

private theorem triangleSet_integral (F : Event → ℂ) (hF : Continuous F)
    (p r : ℝ) (hp : 0 ≤ p) (hpr : p ≤ r) :
    (∫ z : Event, (triangleSet p r).indicator F z) =
      ∫ u in (0 : ℝ)..p, ∫ v in u..r, F (u, v) := by
  have hi := triangleSet_integrable F hF p r
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  have hs (u : ℝ) : (fun v => (triangleSet p r).indicator F (u, v)) =
      (Icc 0 p).indicator (fun u => (Icc u r).indicator (fun v => F (u, v))) u := by
    funext v
    have hm : (u, v) ∈ triangleSet p r ↔ u ∈ Icc 0 p ∧ v ∈ Icc u r := by
      change (0 ≤ u ∧ u ≤ p ∧ u ≤ v ∧ v ≤ r) ↔ _
      simp only [mem_Icc]
      tauto
    by_cases hu : u ∈ Icc 0 p <;> by_cases hv : v ∈ Icc u r <;>
      simp [Set.indicator, hm, hu, hv]
  simp_rw [hs]
  have he (u : ℝ) : (∫ v, (Icc 0 p).indicator
      (fun u => (Icc u r).indicator (fun v => F (u, v))) u v) =
      (Icc 0 p).indicator (fun u => ∫ v in Icc u r, F (u, v)) u := by
    by_cases hu : u ∈ Icc 0 p
    · simp only [Set.indicator_of_mem hu, integral_indicator measurableSet_Icc]
    · simp only [Set.indicator_of_notMem hu, Pi.zero_apply, integral_zero]
  simp_rw [he]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hp]
  apply intervalIntegral.integral_congr
  intro u hu
  have hur : u ≤ r := (show u ∈ Icc 0 p by simpa [uIcc_of_le hp] using hu).2.trans hpr
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hur]

private theorem direct_gate (p r u v : ℝ) :
    |(p - r) / 2 - (u - v) / 2| ≤ (p + r) / 2 - (u + v) / 2 ↔
      u ≤ p ∧ v ≤ r := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem image_gate (p r u v : ℝ) :
    |(p - r) / 2 + (u - v) / 2| ≤ (p + r) / 2 - (u + v) / 2 ↔
      u ≤ r ∧ v ≤ p := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private def eventDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (p r X k : ℝ) (z : Event) : ℂ :=
  (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator
    (fun z => angularDirichletKernel q branch ((p + r) / 2 - z.1)
      ((p - r) / 2) z.2 X k *
      timeReducedCoefficient (physicalRate q b) a z.1 z.2) z

private theorem eventDensity_chart (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (p r X k : ℝ) (hpr : p ≤ r) (z : Event) :
    eventDensity q branch b a p r X k (nullChart z) =
      ((triangleSet p r).indicator (triangleDensity q branch b a false p r X k) z -
        (triangleSet p p).indicator (triangleDensity q branch b a true p r X k) z) / 2 := by
  let f := timeReducedCoefficient (physicalRate q b) a
    ((z.1 + z.2) / 2) ((z.1 - z.2) / 2)
  by_cases hz : z.1 < 0
  · have hf : f = 0 := timeReducedCoefficient_zero_before_onset _ _ _ _ (by linarith)
    have hd : z ∉ triangleSet p r := fun h => (not_lt_of_ge h.1) hz
    have hi : z ∉ triangleSet p p := fun h => (not_lt_of_ge h.1) hz
    simp only [Set.indicator_of_notMem hd, Set.indicator_of_notMem hi, sub_self, zero_div]
    unfold eventDensity
    by_cases he : nullChart z ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)
    · rw [Set.indicator_of_mem he]
      change _ * f = 0
      rw [hf, mul_zero]
    · exact Set.indicator_of_notMem he _
  · have hz0 : 0 ≤ z.1 := le_of_not_gt hz
    by_cases hv : z.1 < z.2
    · have he : nullChart z ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ) := by
        change 0 < (z.1 + z.2) / 2 ∧ (z.1 - z.2) / 2 < 0
        constructor <;> linarith
      rw [eventDensity, Set.indicator_of_mem he]
      change angularDirichletKernel q branch ((p + r) / 2 - (z.1 + z.2) / 2)
        ((p - r) / 2) ((z.1 - z.2) / 2) X k * f = _
      unfold angularDirichletKernel
      simp only [direct_gate, image_gate]
      by_cases hd : z.1 ≤ p ∧ z.2 ≤ r <;> by_cases hi : z.1 ≤ r ∧ z.2 ≤ p
      all_goals
        have htd : z ∈ triangleSet p r ↔ z.1 ≤ p ∧ z.2 ≤ r := by
          simp only [triangleSet, mem_setOf_eq, hz0, hv.le, true_and]
        have hti : z ∈ triangleSet p p ↔ z.1 ≤ r ∧ z.2 ≤ p := by
          change (0 ≤ z.1 ∧ z.1 ≤ p ∧ z.1 ≤ z.2 ∧ z.2 ≤ p) ↔ _
          constructor
          · rintro ⟨_, hu, _, hvp⟩
            exact ⟨hu.trans hpr, hvp⟩
          · rintro ⟨_, hvp⟩
            exact ⟨hz0, hv.le.trans hvp, hv.le, hvp⟩
        simp only [hd, hi, and_self, ↓reduceIte]
        simp only [Set.indicator, htd, hti, hd, hi, and_self, triangleDensity,
          Bool.false_eq_true, ↓reduceIte]
        have htime : (p + r) / 2 - (z.1 + z.2) / 2 =
            (p + r - z.1 - z.2) / 2 := by ring
        try rw [htime]
        try
          rw [max_eq_right (invariant_causal ⟨_, _, _, by
            rw [← htime, direct_gate]; exact hd⟩)]
        try
          rw [max_eq_right (invariant_causal ⟨_, _, _, by
            rw [sub_neg_eq_add, ← htime, image_gate]; exact hi⟩)]
        dsimp only [f]
        ring
    · have he : nullChart z ∉ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ) := by
        intro h
        have hh : (z.1 - z.2) / 2 < 0 := h.2
        exact hv (by linarith)
      rw [eventDensity, Set.indicator_of_notMem he]
      by_cases heq : z.1 = z.2
      · have hf : f = 0 := by
          dsimp [f]
          rw [heq, sub_self, zero_div, timeReducedCoefficient_zero_at_radial_wall]
        have hden (image : Bool) : triangleDensity q branch b a image p r X k z = 0 := by
          change _ * f = 0
          rw [hf, mul_zero]
        simp [Set.indicator, hden]
      · have hgt : z.2 < z.1 := lt_of_le_of_ne (le_of_not_gt hv) (Ne.symm heq)
        have hd : z ∉ triangleSet p r := fun h => (not_lt_of_ge h.2.2.1) hgt
        have hi : z ∉ triangleSet p p := fun h => (not_lt_of_ge h.2.2.1) hgt
        simp [Set.indicator_of_notMem hd, Set.indicator_of_notMem hi]

/-- The exact two compact triangles of the full, branch-dependent retarded source. -/
theorem fullRetardedResponse_eq_triangles (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (p r X k : ℝ) (hp : 0 ≤ p) (hpr : p ≤ r) :
    fullRetardedResponse q branch b a ((p + r) / 2) ((p - r) / 2) X k =
      ((∫ u in (0 : ℝ)..p, ∫ v in u..r,
        triangleDensity q branch b a false p r X k (u, v)) -
      (∫ u in (0 : ℝ)..p, ∫ v in u..p,
        triangleDensity q branch b a true p r X k (u, v))) / 4 := by
  have h := integral_nullChart (eventDensity q branch b a p r X k)
  simp_rw [eventDensity_chart q branch b a p r X k hpr] at h
  rw [integral_div, integral_sub
    (triangleSet_integrable _ (triangleDensity_continuous q branch b a false p r X k) p r)
    (triangleSet_integrable _ (triangleDensity_continuous q branch b a true p r X k) p p),
    triangleSet_integral _ (triangleDensity_continuous q branch b a false p r X k) p r hp hpr,
    triangleSet_integral _ (triangleDensity_continuous q branch b a true p r X k) p p hp le_rfl]
      at h
  have he : (∫ z : Event, eventDensity q branch b a p r X k z) =
      fullRetardedResponse q branch b a ((p + r) / 2) ((p - r) / 2) X k := by
    simp only [eventDensity]
    rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Iio)]
    rw [fullRetardedResponse, eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  rw [he] at h
  linear_combination -(1 / 2 : ℂ) * h

end
end RHTower.D4BMPWRetardedTriangle
