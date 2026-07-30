import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

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
open scoped ENNReal FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A countable Bochner series is integrable when every term is integrable and the integrals of
the term norms are summable.  This packages the Tonelli domination needed for L1
periodizations. -/
theorem integrable_tsum_of_summable_integral_norm
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] {μ : Measure α} {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x => ∑' i, F i x) μ := by
  let B : α → ℝ≥0∞ := fun x => ∑' i, ‖F i x‖ₑ
  have hFiMeas : ∀ i, AEMeasurable (fun x => ‖F i x‖ₑ) μ := by
    intro i
    exact (hF_int i).aestronglyMeasurable.enorm
  have hBMeas : AEMeasurable B μ := by
    exact AEMeasurable.tsum hFiMeas
  have hBfinite : (∫⁻ x, B x ∂μ) ≠ ∞ := by
    dsimp only [B]
    rw [lintegral_tsum hFiMeas]
    have hi (i : ι) :
        (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F i x)))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hBint : Integrable (fun x => (B x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hBMeas hBfinite
  have hsumMeas : AEStronglyMeasurable (fun x => ∑' i, F i x) μ := by
    exact (AEMeasurable.tsum fun i => (hF_int i).aemeasurable).aestronglyMeasurable
  apply hBint.mono' hsumMeas
  have hBne : ∀ᵐ x ∂μ, B x ≠ ∞ :=
    (ae_lt_top' hBMeas hBfinite).mono fun x hx => hx.ne
  filter_upwards [hBne] with x hx
  have hnormSummable : Summable fun i => ‖F i x‖ := by
    have hnn : Summable fun i => ‖F i x‖₊ := by
      apply ENNReal.tsum_coe_ne_top_iff_summable.1
      simpa only [B, enorm_eq_nnnorm] using hx
    exact NNReal.summable_coe.2 hnn
  calc
    ‖∑' i, F i x‖ ≤ ∑' i, ‖F i x‖ := norm_tsum_le_tsum_norm hnormSummable
    _ = (B x).toReal := by
      dsimp only [B]
      rw [ENNReal.tsum_toReal_eq (fun i => enorm_ne_top)]
      simp only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- The integer periodization of a real-line function, interpreted by the ordinary topological
sum.  For an `L1` function this sum is absolutely convergent for almost every point of a unit
cell. -/
def l1Periodization (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, f (x + k)

/-- The L1 periodization is pointwise one-periodic, including at points where the topological
series is assigned its nonsummable default value. -/
theorem l1Periodization_periodic (f : ℝ → ℂ) :
    Periodic (l1Periodization f) 1 := by
  intro x
  unfold l1Periodization
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => f (x + k))
  calc
    (∑' k : ℤ, f (x + 1 + k)) =
        ∑' k : ℤ, f (x + (Equiv.addRight (1 : ℤ)) k) := by
      apply tsum_congr
      intro k
      simp only [Equiv.coe_addRight]
      push_cast
      congr 1
      ring
    _ = ∑' k : ℤ, f (x + k) := h

/-- The periodization of an L1 function is itself integrable on the standard unit cell. -/
theorem integrableOn_Ioc_l1Periodization
    {f : ℝ → ℂ} (hf : Integrable f) :
    IntegrableOn (l1Periodization f) (Ioc (0 : ℝ) 1) := by
  let F : ℤ → ℝ → ℂ := fun k x => f (x + k)
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hFint : ∀ k : ℤ, Integrable (F k) μ := by
    intro k
    exact (hf.comp_add_right k).restrict
  have hnormInt (k : ℤ) :
      ∫ x, ‖F k x‖ ∂μ = ∫ x in (0 : ℝ)..1, ‖f (x + k)‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
  have hFsum : Summable fun k : ℤ => ∫ x, ‖F k x‖ ∂μ := by
    have hbase := hf.norm.hasSum_intervalIntegral_comp_add_int.summable
    exact hbase.congr (fun k => (hnormInt k).symm)
  change Integrable (l1Periodization f) μ
  rw [show l1Periodization f = (fun x => ∑' k : ℤ, f (x + k)) by
    funext x
    rfl]
  exact integrable_tsum_of_summable_integral_norm hFint hFsum

/-- L1 periodizations are interval-integrable on every unit cell. -/
theorem intervalIntegrable_l1Periodization_unitCell
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    IntervalIntegrable (l1Periodization f) volume x (x + 1) := by
  have h0 : IntervalIntegrable (l1Periodization f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (integrableOn_Ioc_l1Periodization hf)
  exact (l1Periodization_periodic f).intervalIntegrable₀ one_ne_zero h0 x (x + 1)

/-- Scaling a real-line function by a nonzero signed aperture reads its Fourier transform at the
correspondingly dilated frequency, with the exact absolute Jacobian. -/
theorem fourier_comp_div_eq_abs_smul
    {f : ℝ → ℂ} {a : ℝ} (ha : a ≠ 0) (w : ℝ) :
    𝓕 (fun x => f (x / a)) w = |a| • 𝓕 f (a * w) := by
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun y =>
    Complex.exp (↑(-2 * Real.pi * y * (a * w)) * Complex.I) • f y
  have hfun :
      (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I) • f (x / a)) =
      fun x : ℝ => g (x / a) := by
    funext x
    dsimp only [g]
    congr 2
    push_cast
    field_simp [ha]
  rw [hfun, Measure.integral_comp_div]

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

/-- The L1 periodization coefficient identity on the centered unit cell. -/
theorem integral_centered_l1Periodization_mul_fourier_eq
    {f : ℝ → ℂ} (hf : Integrable f) (m : ℤ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      fourier (-m) (x : UnitAddCircle) * l1Periodization f x =
      𝓕 f m := by
  let e : ℝ → ℂ := fun x => fourier (-m) (x : UnitAddCircle)
  have heperiodic : Periodic e 1 :=
    Periodic.comp (fun y => AddCircle.coe_add_period 1 y) (fourier (-m))
  have hperiodic : Periodic (fun x => e x * l1Periodization f x) 1 :=
    heperiodic.mul (l1Periodization_periodic f)
  have hshift := hperiodic.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num at hshift
  change (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
    e x * l1Periodization f x) = _
  rw [hshift, intervalIntegral.integral_of_le zero_le_one]
  exact integral_unit_l1Periodization_mul_fourier_eq hf m

/-- **Scaled L1 periodization coefficient theorem.**  Periodizing `x ↦ f (x / a)` packages the
Euclidean Fourier samples at the dilated frequencies `a * m`, with the exact Jacobian `a`. -/
theorem integral_unit_scaled_l1Periodization_mul_fourier_eq
    {f : ℝ → ℂ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-m) (x : UnitAddCircle) *
        l1Periodization (fun y => f (y / a)) x =
      a • 𝓕 f (a * (m : ℝ)) := by
  rw [integral_unit_l1Periodization_mul_fourier_eq (hf.comp_div ha.ne') m]
  rw [fourier_comp_div_eq_abs_smul ha.ne' m, abs_of_pos ha]

/-- The scaled coefficient identity on the centered unit cell. -/
theorem integral_centered_scaled_l1Periodization_mul_fourier_eq
    {f : ℝ → ℂ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      fourier (-m) (x : UnitAddCircle) *
        l1Periodization (fun y => f (y / a)) x =
      a • 𝓕 f (a * (m : ℝ)) := by
  rw [integral_centered_l1Periodization_mul_fourier_eq (hf.comp_div ha.ne') m]
  rw [fourier_comp_div_eq_abs_smul ha.ne' m, abs_of_pos ha]

/-- The real-valued L1 periodization used by Poisson--Muntz sampling. -/
def realL1Periodization (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℤ, f (x + k)

/-- Complexification commutes exactly with real periodization. -/
theorem ofReal_realL1Periodization (f : ℝ → ℝ) (x : ℝ) :
    (realL1Periodization f x : ℂ) =
      l1Periodization (fun y => (f y : ℂ)) x := by
  exact Complex.ofReal_tsum (fun k : ℤ => f (x + k))

/-- The real L1 periodization is pointwise one-periodic. -/
theorem realL1Periodization_periodic (f : ℝ → ℝ) :
    Periodic (realL1Periodization f) 1 := by
  intro x
  apply Complex.ofReal_injective
  rw [ofReal_realL1Periodization, ofReal_realL1Periodization]
  exact l1Periodization_periodic (fun y => (f y : ℂ)) x

/-- A real L1 periodization is integrable on the standard unit cell. -/
theorem integrableOn_Ioc_realL1Periodization
    {f : ℝ → ℝ} (hf : Integrable f) :
    IntegrableOn (realL1Periodization f) (Ioc (0 : ℝ) 1) := by
  have hc := integrableOn_Ioc_l1Periodization
    (hf.ofReal : Integrable fun x => (f x : ℂ))
  have hr := hc.re
  have hfun :
      (fun x => Complex.re (l1Periodization (fun y => (f y : ℂ)) x)) =
        realL1Periodization f := by
    funext x
    rw [← ofReal_realL1Periodization]
    exact Complex.ofReal_re _
  rw [← hfun]
  exact hr

/-- Real L1 periodizations are interval-integrable on every unit cell. -/
theorem intervalIntegrable_realL1Periodization_unitCell
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    IntervalIntegrable (realL1Periodization f) volume x (x + 1) := by
  have h0 : IntervalIntegrable (realL1Periodization f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (integrableOn_Ioc_realL1Periodization hf)
  exact (realL1Periodization_periodic f).intervalIntegrable₀ one_ne_zero h0 x (x + 1)

/-- The centered scaled Fourier coefficient of a real L1 periodization is the corresponding
sample of the Fourier transform of its complexification. -/
theorem integral_centered_scaled_realL1Periodization_mul_fourier_eq
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      fourier (-m) (x : UnitAddCircle) *
        (realL1Periodization (fun y => f (y / a)) x : ℂ) =
      a • 𝓕 (fun y => (f y : ℂ)) (a * (m : ℝ)) := by
  simpa only [ofReal_realL1Periodization] using
    integral_centered_scaled_l1Periodization_mul_fourier_eq
      (hf.ofReal : Integrable fun x => (f x : ℂ)) ha m

end GaloisForLFunctions.HTGeometry
