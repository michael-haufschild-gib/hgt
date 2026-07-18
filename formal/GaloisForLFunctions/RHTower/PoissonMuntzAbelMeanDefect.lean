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
  ring

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
  rw [show a * -(m : ℝ) = -(a * (m : ℝ)) by ring,
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
            ring)
        _ = _ := by ring
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
  ring

/-- Evenness identifies the negative and positive shifted bilateral terms pointwise. -/
theorem poissonMuntzBilateralSampleTerm_neg_add_one
    {f : ℝ → ℝ} (heven : Function.Even f) (a r : ℝ) (n : ℕ) :
    poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) =
      poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) := by
  have hfreq :
      𝓕 (fun x => (f x : ℂ)) (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) =
        𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ)) := by
    rw [show a * ((-((n : ℤ) + 1) : ℤ) : ℝ) =
        -(a * (n + 1 : ℝ)) by push_cast; ring]
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
    simpa only [Function.comp_apply] using hbil.comp_injective (fun m n h => by omega)
  have hneg : Summable fun n : ℕ =>
      poissonMuntzBilateralSampleTerm f a r (-((n : ℤ) + 1)) := by
    simpa only [Function.comp_apply] using hbil.comp_injective (fun m n h => by omega)
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
      ring

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
  ring

/-- The one-sided sampled Abel series is absolutely summable at every radius in `[0,1)`. -/
theorem summable_poissonMuntzAbelTerm
    (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (r : ℂ) ^ (n + 1) *
      𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ)) := by
  have hbil := summable_poissonMuntzBilateralSampleTerm f a hr0 hr1
  have hshift : Summable fun n : ℕ =>
      poissonMuntzBilateralSampleTerm f a r ((n + 1 : ℕ) : ℤ) := by
    simpa only [Function.comp_apply] using
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

end RHTower
