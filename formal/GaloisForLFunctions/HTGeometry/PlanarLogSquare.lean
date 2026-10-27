import GaloisForLFunctions.HTGeometry.PlanarLogNormIntegrability
import GaloisForLFunctions.HTGeometry.LogWeightedGeometricSum

/-!
# Quadratic planar logarithmic kernels

The positive part of `log(S / ‖z‖)` has a globally integrable square.
Polar coordinates bound its radial weight uniformly on `(0,S]`.
Translation and measure restriction give the same bound for any pole and disc.
-/

open MeasureTheory Metric Set Real
open scoped ENNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Positive logarithmic kernel, totalized to zero at its pole. -/
def planarLogKernel (S : ℝ) (z : ℂ) : ℝ := max 0 (Real.log (S / ‖z‖))

/-- The polar Jacobian absorbs the square of the logarithmic singularity. -/
lemma radial_log_square_weight_le {S r : ℝ} (hr : 0 < r)
    (hrS : r ≤ S) : r * Real.log (S / r) ^ 2 ≤ 4 * S := by
  have hratio : 1 ≤ S / r := (one_le_div hr).2 hrS
  have h := mul_le_mul_of_nonneg_left
    (GaloisForLFunctions.HTGeometry.sq_log_le_four_mul hratio) hr.le
  calc
    r * Real.log (S / r) ^ 2 ≤ r * (4 * (S / r)) := h
    _ = 4 * S := by field_simp

/-- A uniform whole-plane bound from the radial weight and angular length. -/
lemma lintegral_planarLogKernel_sq_le {S : ℝ} (hS : 0 < S) :
    (∫⁻ z : ℂ, ENNReal.ofReal (planarLogKernel S z ^ 2)) ≤
      ENNReal.ofReal (8 * Real.pi * S ^ 2) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hbound : ∀ p : ℝ × ℝ, p ∈ polarCoord.target →
      ENNReal.ofReal p.1 •
        ENNReal.ofReal (planarLogKernel S (Complex.polarCoord.symm p) ^ 2) ≤
      (Ioc (0 : ℝ) S ×ˢ Ioo (-Real.pi) Real.pi).indicator
        (fun _ => ENNReal.ofReal (4 * S)) p := by
    rintro ⟨r, θ⟩ hp
    rw [polarCoord_target] at hp
    obtain ⟨hr, hθ⟩ := hp
    simp only [mem_Ioi] at hr
    have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = r := by
      simp [Complex.polarCoord_symm_apply, abs_of_pos hr]
    by_cases hrS : r ≤ S
    · rw [indicator_of_mem (mk_mem_prod (mem_Ioc.mpr ⟨hr, hrS⟩) hθ)]
      have hlog : 0 ≤ Real.log (S / r) := Real.log_nonneg ((one_le_div hr).2 hrS)
      simp only [planarLogKernel, hnorm, max_eq_right hlog, smul_eq_mul]
      rw [← ENNReal.ofReal_mul hr.le]
      exact ENNReal.ofReal_le_ofReal (radial_log_square_weight_le hr hrS)
    · have hlog : Real.log (S / r) ≤ 0 :=
        Real.log_nonpos (div_nonneg hS.le hr.le) ((div_le_one hr).2 (lt_of_not_ge hrS).le)
      have hz : planarLogKernel S (Complex.polarCoord.symm (r, θ)) = 0 := by
        rw [planarLogKernel, hnorm, max_eq_left hlog]
      rw [hz]
      simp
  calc
    (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (planarLogKernel S (Complex.polarCoord.symm p) ^ 2)) ≤
        ∫⁻ p in polarCoord.target,
          (Ioc (0 : ℝ) S ×ˢ Ioo (-Real.pi) Real.pi).indicator
            (fun _ => ENNReal.ofReal (4 * S)) p :=
      setLIntegral_mono' polarCoord.open_target.measurableSet hbound
    _ ≤ ∫⁻ p : ℝ × ℝ,
        (Ioc (0 : ℝ) S ×ˢ Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (4 * S)) p := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (4 * S) * volume (Ioc (0 : ℝ) S ×ˢ Ioo (-Real.pi) Real.pi) := by
      rw [lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
      simp [lintegral_const, Measure.restrict_apply]
    _ = ENNReal.ofReal (8 * Real.pi * S ^ 2) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
      simp only [sub_zero]
      rw [← ENNReal.ofReal_mul hS.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * S)]
      congr 1
      ring

/-- Squared positive logarithmic kernels are integrable on the plane. -/
lemma integrable_planarLogKernel_sq {S : ℝ} (hS : 0 < S) :
    Integrable (fun z : ℂ => planarLogKernel S z ^ 2) := by
  constructor
  · have hm : Measurable (fun z : ℂ => planarLogKernel S z ^ 2) := by
      unfold planarLogKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    have he (z : ℂ) : ‖planarLogKernel S z ^ 2‖ₑ =
        ENNReal.ofReal (planarLogKernel S z ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    simp_rw [he]
    exact (lintegral_planarLogKernel_sq_le hS).trans_lt ENNReal.ofReal_lt_top

/-- The Bochner integral obeys the same quadratic-radius bound. -/
lemma integral_planarLogKernel_sq_le {S : ℝ} (hS : 0 < S) :
    (∫ z : ℂ, planarLogKernel S z ^ 2) ≤ 8 * Real.pi * S ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _)
    (integrable_planarLogKernel_sq hS).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_planarLogKernel_sq_le hS)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 8 * Real.pi * S ^ 2)] using h

/-- Translation preserves integrability, including discs through the pole. -/
lemma integrable_planarLogKernel_sq_sub {S : ℝ} (hS : 0 < S) (a : ℂ) :
    Integrable (fun z : ℂ => planarLogKernel S (z - a) ^ 2) := by
  have hmp : MeasurePreserving (fun z : ℂ => z + -a) volume volume :=
    measurePreserving_add_right volume (-a)
  have hme : MeasurableEmbedding (fun z : ℂ => z + -a) :=
    (MeasurableEquiv.addRight (-a)).measurableEmbedding
  have hint : IntegrableOn (fun z : ℂ => planarLogKernel S z ^ 2) univ :=
    (integrable_planarLogKernel_sq hS).integrableOn
  have h := (hmp.integrableOn_comp_preimage hme).mpr hint
  simpa only [preimage_univ, integrableOn_univ, Function.comp_def, sub_eq_add_neg] using h

/-- The bound is independent of both the pole and the integrating disc. -/
lemma integral_planarLogKernel_sq_on_disc_le {S : ℝ} (hS : 0 < S)
    (a c : ℂ) (R : ℝ) :
    (∫ z in closedBall c R, planarLogKernel S (z - a) ^ 2) ≤ 8 * Real.pi * S ^ 2 := by
  have hmp : MeasurePreserving (fun z : ℂ => z + -a) volume volume :=
    measurePreserving_add_right volume (-a)
  have hme : MeasurableEmbedding (fun z : ℂ => z + -a) :=
    (MeasurableEquiv.addRight (-a)).measurableEmbedding
  calc
    (∫ z in closedBall c R, planarLogKernel S (z - a) ^ 2) ≤
        ∫ z : ℂ, planarLogKernel S (z - a) ^ 2 :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun z => sq_nonneg _)
        (integrable_planarLogKernel_sq_sub hS a)
    _ = ∫ z : ℂ, planarLogKernel S z ^ 2 := by
      simpa only [sub_eq_add_neg] using
        hmp.integral_comp hme (fun z : ℂ => planarLogKernel S z ^ 2)
    _ ≤ _ := integral_planarLogKernel_sq_le hS

end GaloisForLFunctions.HTGeometry
