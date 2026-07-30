import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.RHTower.PoissonAbelBoundary

/-!
# The Poisson--Muntz Abel mean-defect law

For an even real `L1` source, the one-sided Abel sum of its positive Fourier samples is
controlled by the boundary value of the scaled periodization.  There is exactly one correction:
the zero-frequency mean.  In particular, a zero-mean source cancels the whole defect.

The theorem is stated at a symmetric Lebesgue point, so no continuity or endpoint convention is
hidden in the periodization.
-/

open Real MeasureTheory Set intervalIntegral Filter Topology Function
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The real periodization at aperture `a`: first dilate the source, then sum its integer
translates. -/
def poissonMuntzScaledPeriodization (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  realL1Periodization (fun y => f (y / a)) x

/-- The angular form of the scaled periodization on `[-π, π]`. -/
def poissonMuntzAngularDatum (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  poissonMuntzScaledPeriodization f a (t / (2 * Real.pi))

/-- The positive-frequency Abel tail, indexed so that the first term is the sample at `a`. -/
def poissonMuntzAbelSum (f : ℝ → ℝ) (a r : ℝ) : ℂ :=
  ∑' n : ℕ, (r : ℂ) ^ (n + 1) *
    𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ))

/-- The angular datum is interval-integrable for every positive aperture. -/
theorem intervalIntegrable_poissonMuntzAngularDatum
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (poissonMuntzAngularDatum f a) volume (-Real.pi) Real.pi := by
  have hscaled : Integrable (fun y : ℝ => f (y / a)) := hf.comp_div ha.ne'
  have hcell : IntervalIntegrable
      (realL1Periodization (fun y => f (y / a))) volume
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    convert intervalIntegrable_realL1Periodization_unitCell
      hscaled (-(1 / 2 : ℝ)) using 1
    norm_num
  have hcomp := hcell.comp_mul_left (c := (2 * Real.pi)⁻¹)
  convert hcomp using 1
  · funext t
    simp only [poissonMuntzAngularDatum, poissonMuntzScaledPeriodization, div_eq_mul_inv]
    rw [mul_comm]
  · field_simp [Real.pi_ne_zero]
  · field_simp [Real.pi_ne_zero]

/-- Continuity at zero discharges the symmetric-Lebesgue boundary condition exactly. -/
theorem tendsto_symmetricLebesgueAverage_of_continuousAt
    {φ : ℝ → ℝ} (hφint : IntervalIntegrable φ volume (-Real.pi) Real.pi)
    (hφ : ContinuousAt φ 0) :
    Tendsto (fun s : ℝ =>
      ((∫ t in (0 : ℝ)..s,
        (|φ t - φ 0| + |φ (-t) - φ 0|)) / s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let q : ℝ → ℝ := fun t => |φ t - φ 0| + |φ (-t) - φ 0|
  have hnegφ : ContinuousAt (fun t => φ (-t)) 0 := by
    simpa only [Function.comp_apply] using!
      hφ.comp_of_eq continuousAt_neg neg_zero
  have hq : ContinuousAt q 0 := by
    dsimp only [q]
    exact (hφ.sub continuousAt_const).abs.add
      (hnegφ.sub continuousAt_const).abs
  have hq0 : q 0 = 0 := by simp [q]
  have hnegint : IntervalIntegrable (fun t => φ (-t)) volume (-Real.pi) Real.pi := by
    simpa only [neg_neg] using ((IntervalIntegrable.iff_comp_neg).mp hφint).symm
  have hconst : IntervalIntegrable (fun _ : ℝ => φ 0) volume (-Real.pi) Real.pi :=
    _root_.intervalIntegrable_const
  have hqint : IntervalIntegrable q volume (-Real.pi) Real.pi := by
    exact (hφint.sub hconst).abs.add (hnegint.sub hconst).abs
  have hqon : IntegrableOn q (uIoc (-Real.pi) Real.pi) volume :=
    intervalIntegrable_iff.mp hqint
  have hset : uIoc (-Real.pi) Real.pi ∈ 𝓝 (0 : ℝ) := by
    rw [uIoc_of_le (by linarith [Real.pi_pos])]
    exact mem_of_superset
      (isOpen_Ioo.mem_nhds (by constructor <;> linarith [Real.pi_pos]))
      Ioo_subset_Ioc_self
  have hmeas : StronglyMeasurableAtFilter q (𝓝 (0 : ℝ)) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      (MeasureTheory.Integrable.aestronglyMeasurable hqon) hset
  have hderiv : HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, q t) 0 0 := by
    have h := intervalIntegral.integral_hasDerivAt_right
      (a := (0 : ℝ)) (b := (0 : ℝ)) (f := q)
      IntervalIntegrable.refl hmeas hq
    simpa only [hq0] using h
  have hslope := hderiv.tendsto_slope_zero_right
  simpa [slope, q, div_eq_mul_inv, mul_comm] using hslope

/-- Continuous scaled periodization supplies Poisson--Muntz's symmetric-Lebesgue input. -/
theorem tendsto_poissonMuntz_symmetricLebesgueAverage_of_continuousAt
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a)
    (hcont : ContinuousAt (poissonMuntzScaledPeriodization f a) 0) :
    Tendsto (fun s : ℝ =>
      ((∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_symmetricLebesgueAverage_of_continuousAt
    (intervalIntegrable_poissonMuntzAngularDatum hf ha)
  unfold poissonMuntzAngularDatum
  have hscale : ContinuousAt (fun t : ℝ => t / (2 * Real.pi)) 0 :=
    continuousAt_id.div_const (2 * Real.pi)
  simpa only [Function.comp_apply] using!
    hcont.comp_of_eq hscale (by norm_num)

/-- On the angular scale, the integer Fourier character is the ordinary phase
`exp(i t) ^ m`. -/
theorem fourier_apply_div_two_pi (m : ℤ) (t : ℝ) :
    fourier m ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) =
      Complex.exp (t * Complex.I) ^ m := by
  rw [fourier_coe_apply, ← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The normalized angular coefficient of the scaled periodization is the Euclidean Fourier
sample at the oppositely signed lattice frequency. -/
theorem normalized_integral_poissonMuntzAngularDatum_mul_phase_eq
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp (t * Complex.I) ^ m * (poissonMuntzAngularDatum f a t : ℂ) =
      a • 𝓕 (fun x => (f x : ℂ)) (a * (-(m : ℝ))) := by
  let F : ℝ → ℂ := fun x =>
    fourier m (x : UnitAddCircle) *
      (realL1Periodization (fun y => f (y / a)) x : ℂ)
  have hchange := intervalIntegral.integral_comp_div
    (a := -Real.pi) (b := Real.pi) F
    (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  have hfun : (fun t : ℝ =>
      Complex.exp (t * Complex.I) ^ m * (poissonMuntzAngularDatum f a t : ℂ)) =
      fun t : ℝ => F (t / (2 * Real.pi)) := by
    funext t
    simp only [F, poissonMuntzAngularDatum, poissonMuntzScaledPeriodization]
    rw [fourier_apply_div_two_pi]
  rw [hfun, hchange]
  have hcoeff := integral_centered_scaled_realL1Periodization_mul_fourier_eq
    hf ha (-m)
  have hcoeff' :
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F x =
        a • 𝓕 (fun x => (f x : ℂ)) (a * (-(m : ℝ))) := by
    simpa only [F, neg_neg, Int.cast_neg] using hcoeff
  rw [show -Real.pi / (2 * Real.pi) = -(1 / 2 : ℝ) by
        field_simp [Real.pi_ne_zero],
      show Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) by
        field_simp [Real.pi_ne_zero],
      hcoeff']
  simp only [Complex.real_smul]
  field_simp [Real.pi_ne_zero]
  push_cast
  ring_nf

/-- Reflection invariance of a real source passes exactly to its Euclidean Fourier transform. -/
theorem even_fourier_ofReal {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (𝓕 (fun x => (f x : ℂ))) := by
  let g : ℝ → ℂ := fun x => (f x : ℂ)
  have hg : g ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) = g := by
    funext x
    change (f (-x) : ℂ) = (f x : ℂ)
    exact congrArg (fun y : ℝ => (y : ℂ)) (hf x)
  intro w
  have hreflect := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) g w
  rw [hg] at hreflect
  exact hreflect.symm

/-- For an even source the signed frequency in the angular coefficient can be removed. -/
theorem normalized_integral_poissonMuntzAngularDatum_mul_phase_eq_of_even
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp (t * Complex.I) ^ m * (poissonMuntzAngularDatum f a t : ℂ) =
      (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) (a * (m : ℝ)) := by
  rw [normalized_integral_poissonMuntzAngularDatum_mul_phase_eq hf ha m]
  simp only [Complex.real_smul]
  rw [show a * -(m : ℝ) = -(a * (m : ℝ)) by ring_nf,
    even_fourier_ofReal heven]

/-- The Abel-weighted bilateral lattice sample attached to the scaled source. -/
def poissonMuntzBilateralSampleTerm (f : ℝ → ℝ) (a r : ℝ) (m : ℤ) : ℂ :=
  (r : ℂ) ^ m.natAbs *
    ((a : ℂ) * 𝓕 (fun x => (f x : ℂ)) (a * (m : ℝ)))

/-- Fourier coefficient extraction rewrites the angular Poisson average as the bilateral sampled
Fourier series. -/
theorem poissonAbelFourierAverage_poissonMuntzAngularDatum_eq_tsum
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) (r : ℝ) :
    poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r =
      ∑' m : ℤ, poissonMuntzBilateralSampleTerm f a r m := by
  rw [poissonAbelFourierAverage, ← tsum_mul_left]
  apply tsum_congr
  intro m
  have hcoeff :=
    normalized_integral_poissonMuntzAngularDatum_mul_phase_eq_of_even
      hf heven ha m
  calc
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          angularPoissonFourierTerm r t m *
            (poissonMuntzAngularDatum f a t : ℂ) =
        (r : ℂ) ^ m.natAbs *
          ((2 * Real.pi : ℂ)⁻¹ *
            ∫ t in (-Real.pi)..Real.pi,
              Complex.exp (t * Complex.I) ^ m *
                (poissonMuntzAngularDatum f a t : ℂ)) := by
      calc
        (2 * Real.pi : ℂ)⁻¹ *
            ∫ t in (-Real.pi)..Real.pi,
              angularPoissonFourierTerm r t m *
                (poissonMuntzAngularDatum f a t : ℂ) =
            (2 * Real.pi : ℂ)⁻¹ *
              ((r : ℂ) ^ m.natAbs *
                ∫ t in (-Real.pi)..Real.pi,
                  Complex.exp (t * Complex.I) ^ m *
                    (poissonMuntzAngularDatum f a t : ℂ)) := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_congr (fun t _ => by
            simp only [angularPoissonFourierTerm, semilocalBilateralPoissonTerm]
            ac_rfl)
        _ = _ := by ac_rfl
    _ = poissonMuntzBilateralSampleTerm f a r m := by
      rw [hcoeff]
      rfl

/-- The bilateral sampled series is absolutely summable throughout the open Abel disc. -/
theorem summable_poissonMuntzBilateralSampleTerm
    (f : ℝ → ℝ) (a : ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (poissonMuntzBilateralSampleTerm f a r) := by
  let C : ℝ := |a| * ∫ x : ℝ, ‖(f x : ℂ)‖
  have hmajor : Summable fun m : ℤ => r ^ m.natAbs * C :=
    (summable_int_pow_natAbs hr0 hr1).mul_right C
  apply hmajor.of_norm_bounded
  intro m
  have hfourier :
      ‖𝓕 (fun x => (f x : ℂ)) (a * (m : ℝ))‖ ≤
        ∫ x : ℝ, ‖(f x : ℂ)‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (fun x => (f x : ℂ)) (a * (m : ℝ))
  simp only [poissonMuntzBilateralSampleTerm, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hr0, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hfourier (abs_nonneg a))
    (pow_nonneg hr0 m.natAbs)

/-- A positive shifted bilateral term is the aperture times the corresponding one-sided Abel
term. -/
theorem poissonMuntzBilateralSampleTerm_nat_succ
    (f : ℝ → ℝ) (a r : ℝ) (n : ℕ) :
    poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) =
      (a : ℂ) * ((r : ℂ) ^ (n + 1) *
        𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ))) := by
  unfold poissonMuntzBilateralSampleTerm
  rw [Int.natAbs_natCast]
  push_cast
  ring_nf

/-- Evenness identifies the negative and positive shifted bilateral terms pointwise. -/
theorem poissonMuntzBilateralSampleTerm_neg_add_one
    {f : ℝ → ℝ} (heven : Function.Even f) (a r : ℝ) (n : ℕ) :
    poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) =
      poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) := by
  have hfreq :
      𝓕 (fun x => (f x : ℂ)) (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) =
        𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ)) := by
    rw [show a * ((-((n : ℤ) + 1) : ℤ) : ℝ) =
        -(a * (n + 1 : ℝ)) by push_cast; ring_nf]
    exact even_fourier_ofReal heven (a * (n + 1 : ℝ))
  unfold poissonMuntzBilateralSampleTerm
  rw [hfreq]
  congr 2
  simp

/-- The positive shifted half of the bilateral series is exactly `a` times the one-sided Abel
sum. -/
theorem tsum_poissonMuntzBilateralSampleTerm_nat_succ
    (f : ℝ → ℝ) (a r : ℝ) :
    ∑' n : ℕ,
        poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) =
      (a : ℂ) * poissonMuntzAbelSum f a r := by
  rw [poissonMuntzAbelSum, ← tsum_mul_left]
  exact tsum_congr (poissonMuntzBilateralSampleTerm_nat_succ f a r)

/-- The negative half has the same sum as the positive half for an even source. -/
theorem tsum_poissonMuntzBilateralSampleTerm_neg_add_one
    {f : ℝ → ℝ} (heven : Function.Even f) (a r : ℝ) :
    ∑' n : ℕ,
        poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) =
      (a : ℂ) * poissonMuntzAbelSum f a r := by
  rw [tsum_congr (poissonMuntzBilateralSampleTerm_neg_add_one heven a r)]
  exact tsum_poissonMuntzBilateralSampleTerm_nat_succ f a r

/-- The bilateral sampled series splits into the zero mode and twice the one-sided Abel tail. -/
theorem tsum_poissonMuntzBilateralSampleTerm_eq_zero_add_two_mul_abel
    {f : ℝ → ℝ} (heven : Function.Even f) (a : ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' m : ℤ, poissonMuntzBilateralSampleTerm f a r m =
      (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0 +
        2 * (a : ℂ) * poissonMuntzAbelSum f a r := by
  have hbil := summable_poissonMuntzBilateralSampleTerm f a hr0 hr1
  have hpos : Summable fun n : ℕ =>
      poissonMuntzBilateralSampleTerm f a r (n : ℤ) := by
    simpa only [Function.comp_apply] using! hbil.comp_injective (fun m n h => by omega)
  have hneg : Summable fun n : ℕ =>
      poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) := by
    simpa only [Function.comp_apply] using! hbil.comp_injective (fun m n h => by omega)
  have hsplit :
      (∑' n : ℕ, poissonMuntzBilateralSampleTerm f a r (n : ℤ)) =
        poissonMuntzBilateralSampleTerm f a r 0 +
          ∑' n : ℕ,
            poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) := by
    simpa using (hpos.sum_add_tsum_nat_add 1).symm
  calc
    (∑' m : ℤ, poissonMuntzBilateralSampleTerm f a r m) =
        (∑' n : ℕ, poissonMuntzBilateralSampleTerm f a r (n : ℤ)) +
          ∑' n : ℕ,
            poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) :=
      tsum_of_nat_of_neg_add_one hpos hneg
    _ = _ := by
      rw [hsplit, tsum_poissonMuntzBilateralSampleTerm_nat_succ,
        tsum_poissonMuntzBilateralSampleTerm_neg_add_one heven]
      simp only [poissonMuntzBilateralSampleTerm, Int.natAbs_zero,
        pow_zero, Int.cast_zero, one_mul]
      ring_nf

/-- **Exact Poisson--Muntz Abel decomposition.**  Inside the open Abel disc, the Poisson boundary
average is the zero-frequency mean plus twice the positive sampled tail. -/
theorem poissonAbelFourierAverage_poissonMuntzAngularDatum_eq_zero_add_two_mul_abel
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r =
      (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0 +
        2 * (a : ℂ) * poissonMuntzAbelSum f a r := by
  rw [poissonAbelFourierAverage_poissonMuntzAngularDatum_eq_tsum hf heven ha r]
  exact tsum_poissonMuntzBilateralSampleTerm_eq_zero_add_two_mul_abel
    heven a hr0 hr1

/-- Solving the exact decomposition isolates the unique mean defect at every interior Abel
radius. -/
theorem poissonMuntzAbelSum_eq_meanDefect
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    poissonMuntzAbelSum f a r =
      (poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r -
        (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0) /
          (2 * (a : ℂ)) := by
  rw [poissonAbelFourierAverage_poissonMuntzAngularDatum_eq_zero_add_two_mul_abel
    hf heven ha hr0 hr1]
  field_simp [ha.ne']
  ring_nf

/-- The one-sided sampled Abel series is absolutely summable at every radius in `[0,1)`. -/
theorem summable_poissonMuntzAbelTerm
    (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (r : ℂ) ^ (n + 1) *
      𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ)) := by
  have hbil := summable_poissonMuntzBilateralSampleTerm f a hr0 hr1
  have hshift : Summable fun n : ℕ =>
      poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) := by
    simpa only [Function.comp_apply] using!
      hbil.comp_injective (fun m n h => by omega)
  have hscaled := hshift.mul_left (a : ℂ)⁻¹
  apply hscaled.congr
  intro n
  rw [poissonMuntzBilateralSampleTerm_nat_succ]
  field_simp [ha.ne']

/-- **Poisson--Muntz Abel mean-defect theorem.**  At a symmetric Lebesgue point, the one-sided
positive Fourier tail converges to half the periodized boundary value after subtracting the unique
zero-frequency mean defect. -/
theorem tendsto_poissonMuntzAbelSum_meanDefect
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => poissonMuntzAbelSum f a r)
      (𝓝[<] 1)
      (𝓝 ((((poissonMuntzScaledPeriodization f a 0 : ℝ) : ℂ) -
        (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0) /
          (2 * (a : ℂ)))) := by
  have hangular : IntervalIntegrable
      (poissonMuntzAngularDatum f a) volume (-Real.pi) Real.pi :=
    intervalIntegrable_poissonMuntzAngularDatum hf ha
  have havg := tendsto_poissonAbelFourierAverage_of_symmLebesgue hangular hleb
  have htrans : Tendsto
      (fun r : ℝ =>
        (poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r -
          (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0) /
            (2 * (a : ℂ)))
      (𝓝[<] 1)
      (𝓝 ((((poissonMuntzAngularDatum f a 0 : ℝ) : ℂ) -
        (a : ℂ) * 𝓕 (fun x => (f x : ℂ)) 0) /
          (2 * (a : ℂ)))) :=
    (havg.sub tendsto_const_nhds).div_const (2 * (a : ℂ))
  have h0r : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r :=
    ((isOpen_Ioi.eventually_mem (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds).mono (fun r hr => hr.le)
  have h1r : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1 :=
    eventually_of_mem self_mem_nhdsWithin (fun r hr => Set.mem_Iio.1 hr)
  have htail := htrans.congr' (by
    filter_upwards [h0r, h1r] with r hr0 hr1
    exact (poissonMuntzAbelSum_eq_meanDefect hf heven ha hr0 hr1).symm)
  simpa only [poissonMuntzAngularDatum, zero_div] using htail

/-- A zero-mean source cancels the sole defect in the Abel boundary law. -/
theorem tendsto_poissonMuntzAbelSum_of_integral_eq_zero
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ x : ℝ, f x = 0)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => poissonMuntzAbelSum f a r)
      (𝓝[<] 1)
      (𝓝 (((poissonMuntzScaledPeriodization f a 0 : ℝ) : ℂ) /
        (2 * (a : ℂ)))) := by
  have hzero : 𝓕 (fun x => (f x : ℂ)) 0 = 0 := by
    rw [fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    have hcoe : (∫ x : ℝ, (f x : ℂ)) = (((∫ x : ℝ, f x) : ℝ) : ℂ) :=
      integral_ofReal (X := ℝ) (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    rw [hcoe, hmean]
    rfl
  simpa only [hzero, mul_zero, sub_zero] using
    tendsto_poissonMuntzAbelSum_meanDefect hf heven ha hleb

/-- Splitting the integer periodization at the origin gives the center plus twice the positive
physical lattice tail. -/
theorem poissonMuntzScaledPeriodization_zero_eq_zero_add_two_tsum
    {f : ℝ → ℝ} (heven : Function.Even f) {a : ℝ}
    (htail : Summable fun n : ℕ => f ((n + 1 : ℝ) / a)) :
    poissonMuntzScaledPeriodization f a 0 =
      f 0 + 2 * ∑' n : ℕ, f ((n + 1 : ℝ) / a) := by
  have hpos : Summable fun n : ℕ => f ((n : ℝ) / a) := by
    apply (summable_nat_add_iff 1).1
    simpa only [Nat.cast_add, Nat.cast_one] using htail
  have hneg : Summable fun n : ℕ =>
      f (((-((n : ℤ) + 1) : ℤ) : ℝ) / a) := by
    apply htail.congr
    intro n
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_div]
      using (heven ((n + 1 : ℝ) / a)).symm
  have hhead :
      (∑' n : ℕ, f ((n : ℝ) / a)) =
        f 0 + ∑' n : ℕ, f ((n + 1 : ℝ) / a) := by
    simpa only [Finset.sum_range_one, Nat.cast_zero, zero_div, Nat.cast_add,
      Nat.cast_one] using (hpos.sum_add_tsum_nat_add 1).symm
  have hnegative :
      (∑' n : ℕ, f (((-((n : ℤ) + 1) : ℤ) : ℝ) / a)) =
        ∑' n : ℕ, f ((n + 1 : ℝ) / a) := by
    apply tsum_congr
    intro n
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_div]
      using heven ((n + 1 : ℝ) / a)
  unfold poissonMuntzScaledPeriodization realL1Periodization
  simp only [zero_add]
  rw [tsum_of_nat_of_neg_add_one]
  · rw [show (∑' n : ℕ, f (((n : ℤ) : ℝ) / a)) =
          ∑' n : ℕ, f ((n : ℝ) / a) by rfl,
        hhead, hnegative]
    simp only [two_mul, add_assoc]
  · simpa only [Int.cast_natCast] using hpos
  · exact hneg

/-- A compactly supported source has a literal finite cutoff on every positive physical lattice. -/
theorem exists_poissonMuntzPhysicalLattice_cutoff_of_hasCompactSupport
    {f : ℝ → ℝ} (hcompact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f ((n + 1 : ℝ) / a) = 0 := by
  obtain ⟨B, hB⟩ := hcompact.isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (a * B)
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hx
  have hsupp : (n + 1 : ℝ) / a ∈ Function.support f := by
    simpa only [Function.mem_support] using hx
  have hxt : (n + 1 : ℝ) / a ∈ tsupport f := subset_tsupport f hsupp
  have hbound := hB _ hxt
  have hNlt : N < n + 1 := by omega
  have hcast : (N : ℝ) < (n + 1 : ℕ) := by exact_mod_cast hNlt
  have hlarge : B < (n + 1 : ℝ) / a := by
    apply (lt_div_iff₀ ha).2
    rw [mul_comm]
    exact hN.trans (by exact_mod_cast hcast)
  have hxnonneg : 0 ≤ (n + 1 : ℝ) / a := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hxnonneg] at hbound
  exact (not_lt_of_ge hbound) hlarge

/-- The sampled positive physical lattice of a compactly supported source has finite support. -/
theorem finite_support_poissonMuntzPhysicalLattice_of_hasCompactSupport
    {f : ℝ → ℝ} (hcompact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) :
    (Function.support fun n : ℕ => f ((n + 1 : ℝ) / a)).Finite := by
  obtain ⟨N, hN⟩ :=
    exists_poissonMuntzPhysicalLattice_cutoff_of_hasCompactSupport hcompact ha
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra hnot
  have hnN : N ≤ n := Nat.le_of_not_gt hnot
  exact hn (hN n hnN)

/-- Compact support makes the positive physical lattice tail summable. -/
theorem summable_poissonMuntzPhysicalLattice_of_hasCompactSupport
    {f : ℝ → ℝ} (hcompact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => f ((n + 1 : ℝ) / a) := by
  obtain ⟨N, hN⟩ :=
    exists_poissonMuntzPhysicalLattice_cutoff_of_hasCompactSupport hcompact ha
  apply (summable_nat_add_iff N).1
  apply (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr
  intro n
  symm
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hN (n + N) (by omega)

/-- Compact support discharges the summability hypothesis in the exact physical-lattice split. -/
theorem poissonMuntzScaledPeriodization_zero_eq_zero_add_two_tsum_of_hasCompactSupport
    {f : ℝ → ℝ} (heven : Function.Even f) (hcompact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) :
    poissonMuntzScaledPeriodization f a 0 =
      f 0 + 2 * ∑' n : ℕ, f ((n + 1 : ℝ) / a) :=
  poissonMuntzScaledPeriodization_zero_eq_zero_add_two_tsum heven
    (summable_poissonMuntzPhysicalLattice_of_hasCompactSupport hcompact ha)

/-- **Physical Poisson--Muntz Abel boundary law.**  For an even zero-mean source, the Abel tail
converges to the center-plus-lattice expression whenever the physical tail is summable. -/
theorem tendsto_poissonMuntzAbelSum_physicalLattice_of_integral_eq_zero
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ x : ℝ, f x = 0)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s)
      (𝓝[>] 0) (𝓝 0))
    (htail : Summable fun n : ℕ => f ((n + 1 : ℝ) / a)) :
    Tendsto (fun r : ℝ => poissonMuntzAbelSum f a r)
      (𝓝[<] 1)
      (𝓝 (((f 0 + 2 * (∑' n : ℕ, f ((n + 1 : ℝ) / a)) : ℝ) : ℂ) /
        (2 * (a : ℂ)))) := by
  have h := tendsto_poissonMuntzAbelSum_of_integral_eq_zero
    hf heven ha hmean hleb
  rw [poissonMuntzScaledPeriodization_zero_eq_zero_add_two_tsum heven htail] at h
  exact h

/-- Square-root normalization gives the endpoint-safe one-sided Poisson--Muntz formula. -/
theorem tendsto_sqrt_mul_poissonMuntzAbelSum_physicalLattice_of_integral_eq_zero
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ x : ℝ, f x = 0)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s)
      (𝓝[>] 0) (𝓝 0))
    (htail : Summable fun n : ℕ => f ((n + 1 : ℝ) / a)) :
    Tendsto (fun r : ℝ => (Real.sqrt a : ℂ) * poissonMuntzAbelSum f a r)
      (𝓝[<] 1)
      (𝓝 ((f 0 : ℂ) / (2 * (Real.sqrt a : ℂ)) +
        ((∑' n : ℕ, f ((n + 1 : ℝ) / a)) : ℂ) /
          (Real.sqrt a : ℂ))) := by
  have hbase := tendsto_poissonMuntzAbelSum_physicalLattice_of_integral_eq_zero
    hf heven ha hmean hleb htail
  have hscaled := hbase.const_mul (Real.sqrt a : ℂ)
  have hsqrt : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have ha_sqrt : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by
    exact_mod_cast (Real.sq_sqrt ha.le).symm
  have htarget :
      (Real.sqrt a : ℂ) *
          (((f 0 + 2 * (∑' n : ℕ, f ((n + 1 : ℝ) / a)) : ℝ) : ℂ) /
            (2 * (a : ℂ))) =
        (f 0 : ℂ) / (2 * (Real.sqrt a : ℂ)) +
          ((∑' n : ℕ, f ((n + 1 : ℝ) / a)) : ℂ) /
            (Real.sqrt a : ℂ) := by
    rw [ha_sqrt]
    field_simp [hsqrt]
    push_cast
    ring
  rw [htarget] at hscaled
  exact hscaled

/-- Compact support discharges the physical-tail hypothesis in the square-root boundary law. -/
theorem tendsto_sqrt_mul_poissonMuntzAbelSum_physicalLattice_of_compactSupport
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    (hcompact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ x : ℝ, f x = 0)
    (hleb : Tendsto
      (fun s => (∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f a t - poissonMuntzAngularDatum f a 0| +
          |poissonMuntzAngularDatum f a (-t) - poissonMuntzAngularDatum f a 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => (Real.sqrt a : ℂ) * poissonMuntzAbelSum f a r)
      (𝓝[<] 1)
      (𝓝 ((f 0 : ℂ) / (2 * (Real.sqrt a : ℂ)) +
        ((∑' n : ℕ, f ((n + 1 : ℝ) / a)) : ℂ) /
          (Real.sqrt a : ℂ))) :=
  tendsto_sqrt_mul_poissonMuntzAbelSum_physicalLattice_of_integral_eq_zero
    hf heven ha hmean hleb
      (summable_poissonMuntzPhysicalLattice_of_hasCompactSupport hcompact ha)

end RHTower
