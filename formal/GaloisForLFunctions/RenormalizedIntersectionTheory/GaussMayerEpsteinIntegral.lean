import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinEndpointBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeightMeasurability
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-! Absolute convergence and spectral holomorphy of the actual Epstein
Cauchy integral on the source half-plane. Uniform Gaussian height estimates
and height reciprocity supply explicit integrable endpoint powers. -/

open Complex Real Set Filter Topology MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerEpsteinQuadrants MayerEpsteinHeightGrowth
open MayerEpsteinEndpointBounds MayerEpsteinHeightMeasurability
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinIntegral

/-- The unnormalized, actual Cauchy average of the Poisson-defined Epstein field. -/
def average (w : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cauchyWeight w t*epsteinField w (a/t)

private def endpointMajorant (η C₀ Cinf a t : ℝ) : ℝ :=
  if 0 < t then if t ≤ a then C₀*t^(-1+η) else Cinf*t^(-1-η) else 0

private theorem endpointMajorant_integrable {η a : ℝ} (hη : 0 < η) (ha : 0 < a)
    (C₀ Cinf : ℝ) : IntegrableOn (endpointMajorant η C₀ Cinf a) (Ioi 0) := by
  have hsmall : IntegrableOn (fun t : ℝ => t^(-1+η)) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (by linarith only [hη]))
  have hlarge : IntegrableOn (fun t : ℝ => t^(-1-η)) (Ioi a) :=
    (integrableOn_Ioi_rpow_iff ha).mpr (by linarith only [hη])
  have hs : IntegrableOn (endpointMajorant η C₀ Cinf a) (Ioc 0 a) :=
    MeasureTheory.IntegrableOn.congr_fun (hsmall.const_mul C₀)
      (fun t ht => by simp only [endpointMajorant,if_pos ht.1,if_pos ht.2]) measurableSet_Ioc
  have hl : IntegrableOn (endpointMajorant η C₀ Cinf a) (Ioi a) :=
    MeasureTheory.IntegrableOn.congr_fun (hlarge.const_mul Cinf)
      (fun t ht => by
        have hpos : 0 < t := ha.trans ht
        have hnot : ¬ t ≤ a := not_le.mpr (show a < t from ht)
        simp only [endpointMajorant,if_pos hpos,if_neg hnot])
      measurableSet_Ioi
  have hu : Ioc (0 : ℝ) a ∪ Ioi a=Ioi 0 := by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact ha.trans h
    · intro ht
      by_cases h : t ≤ a
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hu]
  exact hs.union hl

private theorem integrand_zero {a t : ℝ} (ha : 0 < a) (ht : ¬ 0 < t) (w : ℂ) :
    cauchyWeight w t*epsteinField w (a/t)=0 := by
  have hy : ¬ 0 < a/t := not_lt.mpr (div_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt ht))
  rw [epsteinField,dif_neg hy,mul_zero]

private theorem measurable_integrand {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) (a : ℝ) :
    Measurable (fun t : ℝ => cauchyWeight w t*epsteinField w (a/t)) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hq : Measurable (cauchyWeight w) := by unfold cauchyWeight; fun_prop
  exact hq.mul ((measurable_epsteinField hw0 hw2).comp (measurable_const.div measurable_id))

private theorem locally_uniform_majorant {w₀ : ℂ} (hw₀ : 0 < w₀.re) (hw₂ : w₀ ≠ 2)
    {a : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, ∃ B : ℝ → ℝ, 0 < r ∧ IntegrableOn B (Ioi 0) ∧
      ∀ w ∈ Metric.ball w₀ r, 0 < w.re ∧ w ≠ 2 ∧
        ∀ t : ℝ, ‖cauchyWeight w t*epsteinField w (a/t)‖ ≤ B t := by
  obtain ⟨η,β,C,r,hη0,hη1,hβ,hC,hr,hball⟩ := locally_bounded_growthCoefficient hw₀ hw₂
  have hcont : Continuous (fun w : ℂ => a^(-w.re-1+η)) := by
    simp only [Real.rpow_def_of_pos ha]
    fun_prop
  have hevent : ∀ᶠ w in 𝓝 w₀, a^(-w.re-1+η) < a^(-w₀.re-1+η)+1 :=
    hcont.continuousAt.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
  obtain ⟨r',hr',hcoeff⟩ := Metric.eventually_nhds_iff.mp hevent
  let A : ℝ := a^(-w₀.re-1+η)+1
  refine ⟨min r r',endpointMajorant η (C*a^(1-η)) (C*A) a,lt_min hr hr',
    endpointMajorant_integrable hη0 ha _ _,?_⟩
  intro w hw
  have hwr : w ∈ Metric.ball w₀ r := Metric.ball_subset_ball (min_le_left _ _) hw
  have hwr' : w ∈ Metric.ball w₀ r' := Metric.ball_subset_ball (min_le_right _ _) hw
  obtain ⟨hηw,hwβ,hw2,hcw⟩ := hball w hwr
  have hcwa : a^(-w.re-1+η) ≤ A := (hcoeff hwr').le
  refine ⟨hη0.trans_le hηw,hw2,?_⟩
  intro t
  by_cases ht : 0 < t
  · by_cases hta : t ≤ a
    · rw [endpointMajorant,if_pos ht,if_pos hta]
      exact (small_endpoint hw2 hη0 hη1 hηw hβ hwβ ht hta).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcw (Real.rpow_nonneg ha.le _))
          (Real.rpow_nonneg ht.le _))
    · rw [endpointMajorant,if_pos ht,if_neg hta]
      exact (large_endpoint hw2 hη0 hη1 hηw hβ hwβ ha (le_of_not_ge hta)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hcw hcwa (Real.rpow_nonneg ha.le _) hC.le)
          (Real.rpow_nonneg ht.le _))
  · rw [integrand_zero ha ht, norm_zero,endpointMajorant,if_neg ht]

/-- The continued Epstein Cauchy average converges absolutely throughout the source half-plane. -/
theorem average_integrable {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyWeight w t*epsteinField w (a/t)) (Ioi 0) := by
  obtain ⟨r,B,hr,hB,hbound⟩ := locally_uniform_majorant hw hw2 ha
  exact hB.mono' (measurable_integrand hw hw2 a).aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound w (Metric.mem_ball_self hr)).2.2)

/-- Local domination by the two endpoint powers makes the actual average holomorphic. -/
theorem differentiableAt_average {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) : DifferentiableAt ℂ (fun v => average v a) w := by
  obtain ⟨r,B,hr,hB,hbound⟩ := locally_uniform_majorant hw hw2 ha
  apply GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
    (F := fun (v : ℂ) (t : ℝ) => cauchyWeight v t*epsteinField v (a/t))
    (μ := volume.restrict (Ioi 0)) (bound := B) hr
  · intro v hv
    exact (measurable_integrand (hbound v hv).1 (hbound v hv).2.1 a).aestronglyMeasurable
  · intro t v hv
    by_cases ht : 0 < t
    · exact ((differentiable_cauchyWeight t v).mul
        (MayerEpsteinReciprocity.differentiableAt_epsteinField (hbound v hv).1
          (hbound v hv).2.1 (div_pos ha ht))).differentiableWithinAt
    · have he : (fun z : ℂ => cauchyWeight z t*epsteinField z (a/t))=fun _ => 0 :=
        funext (integrand_zero ha ht)
      rw [he]
      exact (differentiableAt_const (0 : ℂ)).differentiableWithinAt
  · intro t v hv
    exact (hbound v hv).2.2 t
  · exact hB

#print axioms locally_uniform_majorant
#print axioms average_integrable
#print axioms differentiableAt_average
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinIntegral
