import GaloisForLFunctions.HTGeometry.LeafCauchyTransform
import GaloisForLFunctions.HTGeometry.StieltjesTransformPick
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Local boundedness of the Poisson transform forces absolute continuity

This module supplies a local Stieltjes--Perron substitute needed by matrix-semicircle arguments.
If the Poisson transform of a finite positive measure is uniformly bounded above the real axis on
neighborhoods of compact subsets of an open set, then the measure restricted to that open set is
absolutely continuous with respect to Lebesgue measure.

The proof is quantitative. A compact null set is surrounded by an arbitrarily small open set. A
single Poisson scale whose metric thickening remains in that set gives, by Fubini, an upper bound
for its mass by the Lebesgue volume of the open set. Inner regularity then handles every measurable
null set. No boundary-limit or differentiation theorem is assumed.
-/

open Filter Topology MeasureTheory Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unnormalized real-line Poisson kernel, using the Stieltjes convention of
`HTGeometry.stieltjesTransform_im_eq_poisson`. -/
def realPoissonKernel (y t x : ℝ) : ℝ := y / ((t - x) ^ 2 + y ^ 2)

theorem realPoissonKernel_nonneg {y : ℝ} (hy : 0 < y) (t x : ℝ) :
    0 ≤ realPoissonKernel y t x := by
  unfold realPoissonKernel
  positivity

theorem realPoissonKernel_le_inv {y : ℝ} (hy : 0 < y) (t x : ℝ) :
    realPoissonKernel y t x ≤ y⁻¹ := by
  unfold realPoissonKernel
  have hden : y ^ 2 ≤ (t - x) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (t - x)]
  have hpos : 0 < y ^ 2 := sq_pos_of_pos hy
  calc
    y / ((t - x) ^ 2 + y ^ 2) ≤ y / y ^ 2 :=
      div_le_div_of_nonneg_left hy.le hpos hden
    _ = y⁻¹ := by field_simp

theorem realPoissonKernel_ge_half_inv_of_mem_ball
    {y : ℝ} (hy : 0 < y) (t x : ℝ) (hx : x ∈ Metric.ball t y) :
    (2 * y)⁻¹ ≤ realPoissonKernel y t x := by
  rw [Metric.mem_ball, Real.dist_eq] at hx
  unfold realPoissonKernel
  have hsq : (t - x) ^ 2 < y ^ 2 := by
    rw [← sq_abs (t - x), sq_lt_sq₀ (abs_nonneg _) hy.le]
    simpa [abs_sub_comm] using hx
  have hdenpos : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
  have hdenle : (t - x) ^ 2 + y ^ 2 ≤ 2 * y ^ 2 := by linarith
  calc
    (2 * y)⁻¹ = y / (2 * y ^ 2) := by field_simp
    _ ≤ y / ((t - x) ^ 2 + y ^ 2) :=
      div_le_div_of_nonneg_left hy.le hdenpos hdenle

theorem integral_ball_half_inv {y t : ℝ} (hy : 0 < y) :
    (∫ _x : ℝ in Metric.ball t y, (2 * y)⁻¹) = 1 := by
  rw [integral_const]
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_ball, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- Every centered ball at its own radius captures at least one unit of unnormalized Poisson
mass. The deliberately coarse lower bound is exactly what the compact-null-set proof needs. -/
theorem integral_ball_realPoissonKernel_ge_one {y t : ℝ} (hy : 0 < y) :
    1 ≤ ∫ x : ℝ in Metric.ball t y, realPoissonKernel y t x := by
  rw [← integral_ball_half_inv hy]
  have hfin : volume (Metric.ball t y) < ⊤ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_lt_top
  have hconst : IntegrableOn (fun _x : ℝ => (2 * y)⁻¹) (Metric.ball t y) volume :=
    IntegrableOn.of_bound hfin (by fun_prop) ‖(2 * y)⁻¹‖ (by simp)
  have hcont : Continuous (realPoissonKernel y t) := by
    unfold realPoissonKernel
    apply Continuous.div₀ continuous_const (by fun_prop)
    intro x hzero
    nlinarith [sq_nonneg (t - x), sq_pos_of_pos hy]
  have hkernel : IntegrableOn (realPoissonKernel y t) (Metric.ball t y) volume :=
    IntegrableOn.of_bound hfin hcont.aestronglyMeasurable y⁻¹ (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg hy t x)]
      exact realPoissonKernel_le_inv hy t x)
  refine integral_mono_ae (μ := volume.restrict (Metric.ball t y)) hconst hkernel ?_
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
  exact realPoissonKernel_ge_half_inv_of_mem_ball hy t x hx

/-- Quantitative compact-set estimate behind local absolute continuity. -/
theorem compact_mass_toReal_le_of_poisson_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {K O : Set ℝ} (hK : IsCompact K) (hO : IsOpen O)
    {y C : ℝ} (hy : 0 < y) (hthick : Metric.thickening y K ⊆ O)
    (hOvol : volume O < ⊤)
    (hbound : ∀ x ∈ O, ∫ t : ℝ, realPoissonKernel y t x ∂μ ≤ C) :
    (μ K).toReal ≤ (volume O).toReal * C := by
  let μK : Measure ℝ := μ.restrict K
  let νO : Measure ℝ := volume.restrict O
  letI : IsFiniteMeasure μK := by
    refine IsFiniteMeasure.mk ?_
    exact measure_lt_top _ _
  letI : IsFiniteMeasure νO := by
    refine IsFiniteMeasure.mk ?_
    simpa [νO, Measure.restrict_apply MeasurableSet.univ] using hOvol
  have hcont : Continuous (fun p : ℝ × ℝ => realPoissonKernel y p.1 p.2) := by
    unfold realPoissonKernel
    apply Continuous.div₀ continuous_const (by fun_prop)
    intro p hzero
    nlinarith [sq_nonneg (p.1 - p.2), sq_pos_of_pos hy]
  have hprod : Integrable (fun p : ℝ × ℝ => realPoissonKernel y p.1 p.2)
      (μK.prod νO) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable y⁻¹ ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg hy p.1 p.2)]
    exact realPoissonKernel_le_inv hy p.1 p.2
  have hleft : (μ K).toReal ≤
      ∫ t, ∫ x, realPoissonKernel y t x ∂νO ∂μK := by
    have hone : Integrable (fun _t : ℝ => (1 : ℝ)) μK := integrable_const _
    have hsections := hprod.integral_prod_left
    have hpoint : ∀ᵐ t ∂μK, (1 : ℝ) ≤
        ∫ x, realPoissonKernel y t x ∂νO := by
      filter_upwards [self_mem_ae_restrict hK.measurableSet] with t ht
      have hOint : IntegrableOn (realPoissonKernel y t) O volume := by
        have hcontt : Continuous (realPoissonKernel y t) := by
          unfold realPoissonKernel
          apply Continuous.div₀ continuous_const (by fun_prop)
          intro x hzero
          nlinarith [sq_nonneg (t - x), sq_pos_of_pos hy]
        refine IntegrableOn.of_bound hOvol hcontt.aestronglyMeasurable y⁻¹ ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg hy t x)]
        exact realPoissonKernel_le_inv hy t x
      have hball : Metric.ball t y ⊆ O :=
        (Metric.ball_subset_thickening ht y).trans hthick
      exact (integral_ball_realPoissonKernel_ge_one hy).trans
        (setIntegral_mono_set hOint
          (ae_of_all _ (realPoissonKernel_nonneg hy t)) hball.eventuallyLE)
    have hm := integral_mono_ae hone hsections hpoint
    simpa [μK, Measure.real, Measure.restrict_apply MeasurableSet.univ] using hm
  have hswap : (∫ t, ∫ x, realPoissonKernel y t x ∂νO ∂μK) =
      ∫ x, ∫ t, realPoissonKernel y t x ∂μK ∂νO := integral_integral_swap hprod
  rw [hswap] at hleft
  have hright : (∫ x, ∫ t, realPoissonKernel y t x ∂μK ∂νO) ≤
      ∫ _x, C ∂νO := by
    refine integral_mono_ae hprod.integral_prod_right (integrable_const _) ?_
    filter_upwards [self_mem_ae_restrict hO.measurableSet] with x hx
    have hμint : Integrable (realPoissonKernel y · x) μ := by
      have hcx : Continuous (realPoissonKernel y · x) := by
        unfold realPoissonKernel
        apply Continuous.div₀ continuous_const (by fun_prop)
        intro t hzero
        nlinarith [sq_nonneg (t - x), sq_pos_of_pos hy]
      refine Integrable.of_bound hcx.aestronglyMeasurable y⁻¹ ?_
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg hy t x)]
      exact realPoissonKernel_le_inv hy t x
    have hrestrict : (∫ t, realPoissonKernel y t x ∂μK) ≤
        ∫ t, realPoissonKernel y t x ∂μ := by
      exact setIntegral_le_integral hμint
        (ae_of_all _ (realPoissonKernel_nonneg hy · x))
    exact hrestrict.trans (hbound x hx)
  exact hleft.trans (hright.trans_eq (by
    rw [integral_const]
    simp [νO, Measure.real, Measure.restrict_apply MeasurableSet.univ, mul_comm]))

/-- **Local bounded-Poisson absolute-continuity theorem.** Uniform bounds need only hold on a
possibly different neighborhood of each compact subset. -/
theorem absolutelyContinuous_restrict_of_locally_bounded_poisson
    (μ : Measure ℝ) [IsFiniteMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    (hlocal : ∀ K : Set ℝ, IsCompact K → K ⊆ U →
      ∃ W : Set ℝ, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∃ C y₀ : ℝ, 0 < y₀ ∧
          ∀ x ∈ W, ∀ y : ℝ, 0 < y → y < y₀ →
            ∫ t : ℝ, realPoissonKernel y t x ∂μ ≤ C) :
    μ.restrict U ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk (fun A hA hAvol => ?_)
  rw [Measure.restrict_apply hA]
  have hAU : MeasurableSet (A ∩ U) := hA.inter hU.measurableSet
  rw [hAU.measure_eq_iSup_isCompact μ]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKA hK
  have hKvol : volume K = 0 := measure_mono_null (hKA.trans inter_subset_left) hAvol
  by_cases hKempty : K = ∅
  · simp [hKempty]
  obtain ⟨W, hWopen, hKW, _hWU, C, y₀, hy₀, hbound⟩ :=
    hlocal K hK (hKA.trans inter_subset_right)
  let D : ℝ := max C 0 + 1
  have hD : 0 < D := by dsimp [D]; linarith [le_max_right C 0]
  have hCD : C ≤ D := by dsimp [D]; linarith [le_max_left C 0]
  have hreal : (μ K).toReal = 0 := by
    apply le_antisymm ?_ ENNReal.toReal_nonneg
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hratio : 0 < ε / D := div_pos hε hD
    have hKlt : volume K < ENNReal.ofReal (ε / D) := by
      rw [hKvol]
      exact ENNReal.ofReal_pos.mpr hratio
    obtain ⟨V, hKV, hVopen, hVvol⟩ := K.exists_isOpen_lt_of_lt _ hKlt
    let O : Set ℝ := V ∩ W
    have hOopen : IsOpen O := hVopen.inter hWopen
    have hKO : K ⊆ O := fun x hx => ⟨hKV hx, hKW hx⟩
    have hOvol : volume O < ENNReal.ofReal (ε / D) :=
      lt_of_le_of_lt (measure_mono inter_subset_left) hVvol
    obtain ⟨δ, hδ, hthickδ⟩ := hK.exists_thickening_subset_open hOopen hKO
    let y : ℝ := min (δ / 2) (y₀ / 2)
    have hy : 0 < y := by dsimp [y]; positivity
    have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hyy₀ : y < y₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hthicky : Metric.thickening y K ⊆ O :=
      (Metric.thickening_mono hyδ.le K).trans hthickδ
    have hmass := compact_mass_toReal_le_of_poisson_bound μ hK hOopen hy hthicky
      (hOvol.trans ENNReal.ofReal_lt_top)
      (fun x hx => (hbound x hx.2 y hy hyy₀).trans hCD)
    have hOreal : (volume O).toReal < ε / D := by
      rw [← ENNReal.toReal_ofReal hratio.le]
      exact (ENNReal.toReal_lt_toReal (ne_of_lt (hOvol.trans ENNReal.ofReal_lt_top))
        ENNReal.ofReal_ne_top).mpr hOvol
    have hstrict : (μ K).toReal < ε := by
      calc
        (μ K).toReal ≤ (volume O).toReal * D := hmass
        _ < (ε / D) * D := mul_lt_mul_of_pos_right hOreal hD
        _ = ε := div_mul_cancel₀ ε hD.ne'
    linarith
  exact ((ENNReal.toReal_eq_zero_iff (μ K)).mp hreal).resolve_right
    (measure_ne_top μ K)

/-- The imaginary part of the Stieltjes transform at `x + iy` is exactly the real Poisson
transform used above. -/
theorem stieltjesTransform_im_eq_realPoissonKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x y : ℝ) (hy : y ≠ 0) :
    (∫ t : ℝ, ((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im =
      ∫ t : ℝ, realPoissonKernel y t x ∂μ := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hz : z.im ≠ 0 := by simpa [z] using hy
  rw [HTGeometry.stieltjesTransform_im_eq_poisson z
    (HTGeometry.integrable_cauchy_kernel μ hz)]
  refine integral_congr_ae (ae_of_all μ (fun t => ?_))
  simp [z, realPoissonKernel]

/-- Stieltjes-transform formulation of local bounded-Poisson absolute continuity. -/
theorem absolutelyContinuous_restrict_of_locally_bounded_stieltjes
    (μ : Measure ℝ) [IsFiniteMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    (hlocal : ∀ K : Set ℝ, IsCompact K → K ⊆ U →
      ∃ W : Set ℝ, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∃ C y₀ : ℝ, 0 < y₀ ∧
          ∀ x ∈ W, ∀ y : ℝ, 0 < y → y < y₀ →
            (∫ t : ℝ, ((t : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ ∂μ).im ≤ C) :
    μ.restrict U ≪ volume := by
  apply absolutelyContinuous_restrict_of_locally_bounded_poisson μ hU
  intro K hK hKU
  obtain ⟨W, hWopen, hKW, hWU, C, y₀, hy₀, hbound⟩ := hlocal K hK hKU
  refine ⟨W, hWopen, hKW, hWU, C, y₀, hy₀, fun x hx y hy hyy₀ => ?_⟩
  rw [← stieltjesTransform_im_eq_realPoissonKernel μ x y hy.ne']
  exact hbound x hx y hy hyy₀

end

end GaloisForLFunctions.HTGeometry
