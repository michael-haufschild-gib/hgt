import GaloisForLFunctions.HTGeometry.LaurentAnnulus
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exterior inverse in the Laurent winding argument

The inner Laurent part becomes a convergent power series in w = 1 / z.
Its negative exponential is analytic on the full inverse disc and never
vanishes. This pays the exterior extension and coefficient decay needed
at the geometric evaluation point of the canonical q-chain.
The analytic mechanism is classical; this module is a prerequisite for L1.
-/

open Complex Set Filter
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry

def quantizationInvertedLaurentSeries (f : ℂ → ℂ) (r : ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (annulusLaurentCoeff f 0 r)

def quantizationExteriorInverse (f : ℂ → ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(w * (quantizationInvertedLaurentSeries f r).sum w))

theorem quantizationExteriorInverse_ne_zero (f : ℂ → ℂ) (r : ℝ) (w : ℂ) :
    quantizationExteriorInverse f r w ≠ 0 := Complex.exp_ne_zero _

theorem quantizationInvertedLaurentSeries_radius {f : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    ENNReal.ofNNReal (⟨r⁻¹, (inv_pos.mpr hr).le⟩ : NNReal) ≤
      (quantizationInvertedLaurentSeries f r).radius := by
  apply (quantizationInvertedLaurentSeries f r).le_radius_of_bound (M * r)
  intro n
  rw [quantizationInvertedLaurentSeries, FormalMultilinearSeries.ofScalars_norm]
  change ‖annulusLaurentCoeff f 0 r n‖ * (r⁻¹) ^ n ≤ M * r
  calc
    _ ≤ (r ^ n * M * r) * (r⁻¹) ^ n :=
      mul_le_mul_of_nonneg_right (norm_annulusLaurentCoeff_le hr.le hM hf n) (by positivity)
    _ = M * r := by
      rw [inv_pow]
      calc (r ^ n * M * r) * (r ^ n)⁻¹ = (r ^ n * (r ^ n)⁻¹) * (M * r) := by ring
           _ = M * r := by rw [mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hr)), one_mul]

theorem analyticOnNhd_quantizationExteriorInverse {f : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    AnalyticOnNhd ℂ (quantizationExteriorInverse f r) (Metric.ball 0 r⁻¹) := by
  have hrad := quantizationInvertedLaurentSeries_radius hr hM hf
  have hpos : 0 < (quantizationInvertedLaurentSeries f r).radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (show (0 : NNReal) <
      ⟨r⁻¹, (inv_pos.mpr hr).le⟩ from inv_pos.mpr hr)) hrad
  have han := ((quantizationInvertedLaurentSeries f r).hasFPowerSeriesOnBall hpos).analyticOnNhd
  intro w hw
  have hw' : w ∈ Metric.eball (0 : ℂ) (quantizationInvertedLaurentSeries f r).radius := by
    rw [mem_eball_zero_iff]
    apply lt_of_lt_of_le _ hrad
    have hnorm : ‖w‖ < r⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact_mod_cast hnorm
  exact ((analyticAt_id.mul (han w hw')).neg).cexp

theorem quantizationExteriorInverse_eq {f : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hfc : ContinuousOn f (Metric.sphere 0 r))
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) {z : ℂ} (hz : r < ‖z‖) :
    quantizationExteriorInverse f r z⁻¹ = Complex.exp (-laurentInner f 0 r z) := by
  have hrad := quantizationInvertedLaurentSeries_radius hr hM hf
  have hw : z⁻¹ ∈ Metric.eball (0 : ℂ) (quantizationInvertedLaurentSeries f r).radius := by
    rw [mem_eball_zero_iff]
    apply lt_of_lt_of_le _ hrad
    have hnorm : ‖z⁻¹‖ < r⁻¹ := by rw [norm_inv]; exact (inv_lt_inv₀ (lt_trans hr hz) hr).mpr hz
    exact_mod_cast hnorm
  have hs := ((quantizationInvertedLaurentSeries f r).hasSum hw).mul_left z⁻¹
  have hi := hasSum_laurentInner hr hM hfc hf (by simpa only [sub_zero] using hz)
  have he : z⁻¹ * (quantizationInvertedLaurentSeries f r).sum z⁻¹ = laurentInner f 0 r z := by
    apply HasSum.unique hs
    apply hi.congr
    intro n
    simp only [quantizationInvertedLaurentSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      sub_zero, smul_eq_mul, pow_succ, mul_inv_rev, inv_pow]
    ac_rfl
  exact congrArg (fun a : ℂ => Complex.exp (-a)) he

/-- Multiplicative Laurent factorization, retaining the exterior extension explicitly. -/
theorem quantization_laurent_factorization {f : ℂ → ℂ} {a b r R : ℝ}
    (ha : 0 < a) (har : a < r) (hrR : r < R) (hRb : R < b)
    (hf : DifferentiableOn ℂ f (annulusAt 0 a b))
    {z : ℂ} (hz1 : r < ‖z‖) (hz2 : ‖z‖ < R) :
    quantizationExteriorInverse f r z⁻¹ * Complex.exp (f z) =
      Complex.exp (laurentOuter f 0 R z) := by
  have hcont : ContinuousOn f (Metric.sphere 0 r) :=
    hf.continuousOn.mono (sphere_subset_annulusAt har (hrR.trans hRb))
  have hr : 0 < r := ha.trans har
  obtain ⟨M, hM, hbound⟩ := exists_bound_on_sphere hr.le hcont
  rw [quantizationExteriorInverse_eq hr hM hcont hbound hz1, ← Complex.exp_add]
  congr 1
  rw [laurent_decomposition ha har hrR hRb hf
    (by simpa only [sub_zero] using hz1) (by simpa only [sub_zero] using hz2)]
  ring

/-- The exterior inverse has exponentially decaying Taylor coefficients on every smaller disc. -/
theorem quantizationExteriorInverse_coefficients {f : ℂ → ℂ} {r M R : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (hR0 : 0 < R) (hR : R < r⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ n : ℕ, ‖outerCoeff (quantizationExteriorInverse f r) R n‖ ≤ A / R ^ n) ∧
      ∀ w : ℂ, ‖w‖ < R → HasSum
        (fun n : ℕ => outerCoeff (quantizationExteriorInverse f r) R n * w ^ n)
        (quantizationExteriorInverse f r w) := by
  have han := analyticOnNhd_quantizationExteriorInverse hr hM hf
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 r⁻¹ := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz.trans_lt hR
  have hcont := han.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub)
  obtain ⟨A, hA, hbound⟩ := exists_bound_on_sphere hR0.le hcont
  refine ⟨A, hA, fun n => norm_outerCoeff_le hR0 hA hbound n, fun w hw => ?_⟩
  have hseries := (han.differentiableOn.mono hsub).hasFPowerSeriesOnBall
    (R := ⟨R, hR0.le⟩) (by exact_mod_cast hR0)
  have hw' : w ∈ Metric.eball (0 : ℂ) (ENNReal.ofNNReal (⟨R, hR0.le⟩ : NNReal)) := by
    rw [mem_eball_zero_iff]
    exact_mod_cast hw
  have hs := hseries.hasSum hw'
  simp only [zero_add] at hs
  change HasSum (fun n => (cauchyPowerSeries (quantizationExteriorInverse f r) 0 R n)
    (fun _ => w)) (quantizationExteriorInverse f r w) at hs
  simpa only [zero_add, cauchyPowerSeries_diag (quantizationExteriorInverse f r) hR0, smul_eq_mul, mul_comm] using hs

end RHTower.WeilSpectral
