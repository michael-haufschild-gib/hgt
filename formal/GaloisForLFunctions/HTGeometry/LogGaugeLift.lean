import GaloisForLFunctions.HTGeometry.BoundedReweightingControl
import GaloisForLFunctions.HTGeometry.MultiplicativeGaugePerturbation

/-!
# Lifting the multiplicative gauge to `L^∞`

The multiplicative gauge chart is pointwise: a multiplicative factor `1 + x` with `|x| ≤ 1/2`
corresponds to an additive parameter change `log (1 + x)` of size at most `2 |x|`.

This module lifts that to the Banach space of bounded reweightings.  A gauge `h` of `L^∞` norm at
most one half yields an honest `L^∞` element `log (1 + h)`, whose norm is at most `2 ‖h‖`.  No
finiteness of the base measure is used: at exponent `∞` an almost-everywhere bound *is* a norm
bound.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- At exponent `∞` an almost-everywhere bound is a norm bound, with no finiteness hypothesis. -/
theorem norm_toLp_le_of_ae_bound (μ : Measure α)
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) :
    ‖(memLp_top_of_bound hf C hfC).toLp f‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  have hle : eLpNormEssSup f μ ≤ ENNReal.ofReal C :=
    eLpNormEssSup_le_of_ae_bound hfC
  have hne : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (eLpNormEssSup f μ).toReal
      ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono hne hle
    _ = C := ENNReal.toReal_ofReal hC

/-- A bounded gauge of size at most one half has a bounded logarithm. -/
theorem memLp_top_log_one_add (μ : Measure α) (h : Lp ℝ ⊤ μ) (hh : ‖h‖ ≤ 1 / 2) :
    MemLp (fun t => Real.log (1 + h t)) ⊤ μ := by
  have hmeas : AEStronglyMeasurable (fun t => Real.log (1 + h t)) μ := by
    have hbase : AEMeasurable (fun t => 1 + h t) μ :=
      ((Lp.aestronglyMeasurable h).aemeasurable).const_add 1
    exact (Real.measurable_log.comp_aemeasurable hbase).aestronglyMeasurable
  refine memLp_top_of_bound hmeas (2 * ‖h‖) ?_
  filter_upwards [ae_norm_le_norm_Lp_top μ h] with t ht
  have habs : |h t| ≤ 1 / 2 := le_trans (by simpa [Real.norm_eq_abs] using ht) hh
  have hbound := abs_log_one_add_le_two_mul habs
  have hle : |h t| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using ht
  calc ‖Real.log (1 + h t)‖
      = |Real.log (1 + h t)| := Real.norm_eq_abs _
    _ ≤ 2 * |h t| := hbound
    _ ≤ 2 * ‖h‖ := by linarith

/-- The additive parameter change induced by a bounded multiplicative gauge. -/
def logOneAddLp (μ : Measure α) (h : Lp ℝ ⊤ μ) (hh : ‖h‖ ≤ 1 / 2) : Lp ℝ ⊤ μ :=
  (memLp_top_log_one_add μ h hh).toLp _

theorem logOneAddLp_coeFn (μ : Measure α) (h : Lp ℝ ⊤ μ) (hh : ‖h‖ ≤ 1 / 2) :
    logOneAddLp μ h hh =ᵐ[μ] fun t => Real.log (1 + h t) :=
  MemLp.coeFn_toLp _

/-- **The logarithmic gauge is uniformly small.**  A multiplicative gauge of `L^∞` norm at most one
half induces an additive parameter change of norm at most twice as large. -/
theorem norm_logOneAddLp_le (μ : Measure α) (h : Lp ℝ ⊤ μ) (hh : ‖h‖ ≤ 1 / 2) :
    ‖logOneAddLp μ h hh‖ ≤ 2 * ‖h‖ := by
  have hmeas : AEStronglyMeasurable (fun t => Real.log (1 + h t)) μ := by
    have hbase : AEMeasurable (fun t => 1 + h t) μ :=
      ((Lp.aestronglyMeasurable h).aemeasurable).const_add 1
    exact (Real.measurable_log.comp_aemeasurable hbase).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ‖Real.log (1 + h t)‖ ≤ 2 * ‖h‖ := by
    filter_upwards [ae_norm_le_norm_Lp_top μ h] with t ht
    have habs : |h t| ≤ 1 / 2 := le_trans (by simpa [Real.norm_eq_abs] using ht) hh
    have hle : |h t| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using ht
    calc ‖Real.log (1 + h t)‖
        = |Real.log (1 + h t)| := Real.norm_eq_abs _
      _ ≤ 2 * |h t| := abs_log_one_add_le_two_mul habs
      _ ≤ 2 * ‖h‖ := by linarith
  have hzero : (0 : ℝ) ≤ 2 * ‖h‖ := by positivity
  have hkey := norm_toLp_le_of_ae_bound μ hmeas hzero hbound
  have hcongr : logOneAddLp μ h hh =
      (memLp_top_of_bound hmeas (2 * ‖h‖) hbound).toLp _ := by
    apply Lp.ext
    exact (logOneAddLp_coeFn μ h hh).trans (MemLp.coeFn_toLp _).symm
  rw [hcongr]
  exact hkey

end

end GaloisForLFunctions.HTGeometry
