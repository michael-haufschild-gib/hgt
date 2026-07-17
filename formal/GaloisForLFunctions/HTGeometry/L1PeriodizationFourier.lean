import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of an L1 periodization

For an integrable complex function on the real line, its integer periodization exists almost
everywhere on a unit cell and its `m`-th Fourier coefficient is exactly the Euclidean Fourier
transform at `m`.  Continuity and pointwise absolute convergence are not assumed.  The proof uses
absolute summability of the cellwise `L1` norms, followed by the exact partition of the real line
into integer translates of the unit interval.

This is the measure-theoretic coefficient calculation needed by endpoint-safe Poisson--Muntz
specializations.
-/

open Real MeasureTheory Set intervalIntegral Filter Topology Function
open scoped FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The integer periodization of a real-line function, interpreted by the ordinary topological
sum.  For an `L1` function this sum is absolutely convergent for almost every point of a unit
cell. -/
def l1Periodization (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, f (x + k)

/-- **L1 periodization coefficient theorem.**  The Fourier coefficient on the unit cell of the
integer periodization is the Euclidean Fourier transform at the corresponding integer. -/
theorem integral_unit_l1Periodization_mul_fourier_eq
    {f : ℝ → ℂ} (hf : Integrable f) (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) * l1Periodization f x =
      𝓕 f m := by
  let e : ℝ → ℂ := fun x => fourier (-m) (x : UnitAddCircle)
  let F : ℤ → ℝ → ℂ := fun k x => e x * f (x + k)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hecont : Continuous e := by
    dsimp only [e]
    fun_prop
  have henorm : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    simp [e, Complex.norm_exp]
  have headd : ∀ (k : ℤ) (x : ℝ), e (x + k) = e x := by
    intro k x
    have hp : Periodic e 1 :=
      Periodic.comp (fun y => AddCircle.coe_add_period 1 y) (fourier (-m))
    simpa only [mul_one] using hp.int_mul k x
  have hEF : Integrable (fun x => e x * f x) := by
    exact hf.bdd_mul hecont.aestronglyMeasurable
      (Eventually.of_forall fun x => (henorm x).le)
  have hglobal := hEF.hasSum_intervalIntegral_comp_add_int
  have hFint : ∀ k : ℤ, Integrable (F k) μ := by
    intro k
    have hshift : Integrable (fun x : ℝ => f (x + k)) := hf.comp_add_right k
    have hshiftμ : Integrable (fun x : ℝ => f (x + k)) μ := hshift.restrict
    exact hshiftμ.bdd_mul hecont.aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => (henorm x).le)
  have hnormInt (k : ℤ) :
      ∫ x, ‖F k x‖ ∂μ = ∫ x in (0 : ℝ)..1, ‖f (x + k)‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    change (∫ x in Set.Ioc (0 : ℝ) 1, ‖F k x‖) = _
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [F, norm_mul, henorm, one_mul]
  have hFsum : Summable fun k : ℤ => ∫ x, ‖F k x‖ ∂μ := by
    have hbase := hf.norm.hasSum_intervalIntegral_comp_add_int.summable
    exact hbase.congr (fun k => (hnormInt k).symm)
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
  have hglobal' : HasSum (fun k : ℤ => ∫ x, F k x ∂μ)
      (∫ x, e x * f x) := by
    apply HasSum.congr_fun hglobal
    intro k
    rw [intervalIntegral.integral_of_le zero_le_one]
    change (∫ x in Set.Ioc (0 : ℝ) 1, F k x) =
      ∫ x in Set.Ioc (0 : ℝ) 1, (fun x => e x * f x) (x + k)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [F, headd]
  have hperiod : (fun x : ℝ => ∑' k : ℤ, F k x) =
      fun x => e x * l1Periodization f x := by
    funext x
    simp only [F, l1Periodization]
    rw [tsum_mul_left]
  have hidentity : (∫ x, e x * l1Periodization f x ∂μ) =
      ∫ x, e x * f x := by
    rw [← hperiod]
    exact hswap.unique hglobal'
  change (∫ x, e x * l1Periodization f x ∂μ) = _
  rw [hidentity]
  rw [fourier_real_eq_integral_exp_smul]
  congr 1 with x : 1
  rw [smul_eq_mul]
  dsimp only [e]
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
