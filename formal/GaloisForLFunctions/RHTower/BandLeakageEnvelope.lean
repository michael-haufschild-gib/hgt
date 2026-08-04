import GaloisForLFunctions.RHTower.BandKaiserContinuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The exponential leakage envelope of the band operator

The Kaiser–Bessel trial closes the concentration argument quantitatively.  Its spectral density beyond
the band edge obeys a Cauchy envelope, and a shifted-and-scaled Cauchy kernel has an aperture-free
integral over the whole line:

```text
∫ 8/(1 + (a xi - b)²) d xi = 8 pi / a.
```

Folding the envelope in the frequency variable costs only a second copy of the same kernel, so the
trial's *entire* out-of-band spectral mass is at most `8` — a constant, independent of the aperture.
Its in-band energy, on the other hand, grows exponentially: the mean of the trial over the band is
`2 sinh(c)/c`, and the squared-mean inequality turns that into

```text
∫_(-1)^1 K_c² >= (2 sinh(c)/c)²/2.
```

Feeding both into the variational bound gives the leakage envelope

```text
1 - ‖B_c‖ <= 64 c² e^(-2c)      (c >= 1),
```

which is the sharp exponential rate for the band operator: the loss of the best band-limited
concentration is exponentially small in the aperture, with a polynomial correction.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-! ## The shifted Cauchy kernel on the line -/

/-- A shifted and scaled Cauchy kernel is integrable on the line. -/
theorem integrable_cauchyShift {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Integrable (fun ξ : ℝ => 8 / (1 + (a * ξ - b) ^ 2)) (volume : Measure ℝ) := by
  have h0 : Integrable (fun u : ℝ => 8 * (1 + u ^ 2)⁻¹) (volume : Measure ℝ) :=
    integrable_inv_one_add_sq.const_mul 8
  have h1 : Integrable (fun u : ℝ => 8 * (1 + (u - b) ^ 2)⁻¹) (volume : Measure ℝ) :=
    h0.comp_sub_right b
  have h2 : Integrable (fun ξ : ℝ => 8 * (1 + (a * ξ - b) ^ 2)⁻¹) (volume : Measure ℝ) :=
    h1.comp_mul_left' ha
  refine h2.congr ?_
  filter_upwards with ξ
  rw [div_eq_mul_inv]

/-- **The aperture-free integral of a shifted Cauchy kernel.**  Scaling contributes `a⁻¹` and the
shift contributes nothing, by translation invariance of the volume. -/
theorem integral_cauchyShift {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ ξ : ℝ, 8 / (1 + (a * ξ - b) ^ 2)) = 8 * Real.pi / a := by
  have hshift : (∫ u : ℝ, 8 * (1 + (u - b) ^ 2)⁻¹) = 8 * Real.pi := by
    have h : (∫ u : ℝ, (1 + (u - b) ^ 2)⁻¹) = ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
      integral_sub_right_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) b
    rw [MeasureTheory.integral_const_mul, h, integral_univ_inv_one_add_sq]
  have hscale : (∫ ξ : ℝ, 8 * (1 + (a * ξ - b) ^ 2)⁻¹)
      = |a⁻¹| • ∫ u : ℝ, 8 * (1 + (u - b) ^ 2)⁻¹ :=
    Measure.integral_comp_mul_left (fun u : ℝ => 8 * (1 + (u - b) ^ 2)⁻¹) a
  simp only [div_eq_mul_inv]
  rw [hscale, hshift, abs_of_pos (inv_pos.mpr ha), smul_eq_mul]
  ring

/-- The two-sided Cauchy envelope in the frequency variable. -/
def cauchyPair (c ξ : ℝ) : ℝ :=
  8 / (1 + (2 * Real.pi * ξ - c) ^ 2) + 8 / (1 + (2 * Real.pi * ξ + c) ^ 2)

theorem cauchyPair_nonneg (c ξ : ℝ) : 0 ≤ cauchyPair c ξ := by
  rw [cauchyPair]
  have h1 : (0 : ℝ) ≤ 8 / (1 + (2 * Real.pi * ξ - c) ^ 2) := by positivity
  have h2 : (0 : ℝ) ≤ 8 / (1 + (2 * Real.pi * ξ + c) ^ 2) := by positivity
  linarith

/-- **The folded envelope is dominated by the two-sided one.**  Whichever sign the frequency has, one
of the two shifted kernels reproduces the folded envelope exactly and the other is nonnegative. -/
theorem folded_cauchy_le_pair (c ξ : ℝ) :
    8 / (1 + (|2 * Real.pi * ξ| - c) ^ 2) ≤ cauchyPair c ξ := by
  rw [cauchyPair]
  rcases abs_cases (2 * Real.pi * ξ) with ⟨habs, _⟩ | ⟨habs, _⟩
  · rw [habs]
    have h2 : (0 : ℝ) ≤ 8 / (1 + (2 * Real.pi * ξ + c) ^ 2) := by positivity
    linarith
  · rw [habs]
    have hsq : (-(2 * Real.pi * ξ) - c) ^ 2 = (2 * Real.pi * ξ + c) ^ 2 := by ring
    rw [hsq]
    have h1 : (0 : ℝ) ≤ 8 / (1 + (2 * Real.pi * ξ - c) ^ 2) := by positivity
    linarith

theorem integrable_cauchyPair (c : ℝ) : Integrable (cauchyPair c) (volume : Measure ℝ) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have h1 : Integrable (fun ξ : ℝ => 8 / (1 + (2 * Real.pi * ξ - c) ^ 2)) (volume : Measure ℝ) :=
    integrable_cauchyShift hpi c
  have h2 : Integrable (fun ξ : ℝ => 8 / (1 + (2 * Real.pi * ξ - -c) ^ 2)) (volume : Measure ℝ) :=
    integrable_cauchyShift hpi (-c)
  have h2' : Integrable (fun ξ : ℝ => 8 / (1 + (2 * Real.pi * ξ + c) ^ 2)) (volume : Measure ℝ) := by
    refine h2.congr ?_
    filter_upwards with ξ
    rw [sub_neg_eq_add]
  exact h1.add h2'

/-- **The total mass of the two-sided envelope is `8`.**  Each shifted kernel contributes `8 pi/(2 pi)`,
independently of the aperture. -/
theorem integral_cauchyPair (c : ℝ) : (∫ ξ : ℝ, cauchyPair c ξ) = 8 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : (∫ ξ : ℝ, 8 / (1 + (2 * Real.pi * ξ - c) ^ 2)) = 8 * Real.pi / (2 * Real.pi) :=
    integral_cauchyShift hpi c
  have hcongr : (∫ ξ : ℝ, 8 / (1 + (2 * Real.pi * ξ + c) ^ 2))
      = ∫ ξ : ℝ, 8 / (1 + (2 * Real.pi * ξ - -c) ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards with ξ
    rw [sub_neg_eq_add]
  have h2 : (∫ ξ : ℝ, 8 / (1 + (2 * Real.pi * ξ + c) ^ 2)) = 8 * Real.pi / (2 * Real.pi) := by
    rw [hcongr, integral_cauchyShift hpi (-c)]
  have hint1 : Integrable (fun ξ : ℝ => 8 / (1 + (2 * Real.pi * ξ - c) ^ 2)) (volume : Measure ℝ) :=
    integrable_cauchyShift (by positivity) c
  have hint2 : Integrable (fun ξ : ℝ => 8 / (1 + (2 * Real.pi * ξ + c) ^ 2)) (volume : Measure ℝ) := by
    refine (integrable_cauchyShift (a := 2 * Real.pi) (by positivity) (-c)).congr ?_
    filter_upwards with ξ
    rw [sub_neg_eq_add]
  simp only [cauchyPair]
  rw [MeasureTheory.integral_add hint1 hint2, h1, h2]
  field_simp
  norm_num

/-! ## The out-of-band mass of the trial is an absolute constant -/

/-- Outside the frequency window the scaled frequency exceeds the aperture. -/
theorem lt_abs_of_notMem_window {c ξ : ℝ}
    (h : ξ ∉ Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi))) :
    c < |2 * Real.pi * ξ| := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [mem_Icc] at h
  have habs : c / (2 * Real.pi) < |ξ| := by
    rcases not_and_or.mp h with h1 | h1
    · have hlt : ξ < -(c / (2 * Real.pi)) := lt_of_not_ge h1
      have hneg : c / (2 * Real.pi) < -ξ := by linarith
      exact lt_of_lt_of_le hneg (neg_le_abs ξ)
    · have hlt : c / (2 * Real.pi) < ξ := lt_of_not_ge h1
      exact lt_of_lt_of_le hlt (le_abs_self ξ)
  rw [div_lt_iff₀ hpi] at habs
  rw [abs_mul, abs_of_pos hpi]
  linarith

/-- **The trial's out-of-band spectral mass is at most `8`.**  Pointwise the density is under the
folded Cauchy envelope, the envelope is under the two-sided one, and the two-sided one has total mass
`8` on the whole line. -/
theorem integral_tail_kaiser_le {c : ℝ} (hc : 0 ≤ c) :
    (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
        ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2) ≤ 8 := by
  have hmeas : MeasurableSet (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ :=
    measurableSet_Icc.compl
  have hdens : Integrable (fun ξ : ℝ => ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2)
      (volume : Measure ℝ) :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hpair : Integrable (cauchyPair c) (volume : Measure ℝ) := integrable_cauchyPair c
  have hstep : (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
      ‖𝓕 (bandTrunc (kaiserTrial c)) ξ‖ ^ 2)
      ≤ ∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ, cauchyPair c ξ := by
    refine setIntegral_mono_on hdens.integrableOn hpair.integrableOn hmeas fun ξ hξ => ?_
    have hout : c < |2 * Real.pi * ξ| := lt_abs_of_notMem_window hξ
    exact le_trans (norm_sq_fourier_bandTrunc_kaiser_le hc hout) (folded_cauchy_le_pair c ξ)
  have htotal : (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ, cauchyPair c ξ)
      ≤ ∫ ξ : ℝ, cauchyPair c ξ :=
    setIntegral_le_integral hpair (Filter.Eventually.of_forall (cauchyPair_nonneg c))
  rw [integral_cauchyPair c] at htotal
  linarith

/-! ## The in-band energy of the trial -/

/-- **The squared mean is at most the mean square.**  Expanding the nonnegative integral of
`(f - mean)²` gives the interval form of Cauchy–Schwarz against the constant `1`. -/
theorem sq_intervalIntegral_le {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hlen : 0 < b - a := by linarith
  set I : ℝ := ∫ x in a..b, f x with hI
  set S : ℝ := ∫ x in a..b, f x ^ 2 with hS
  set m : ℝ := I / (b - a) with hm
  have hint1 : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have hint2 : IntervalIntegrable (fun x => 2 * m * f x) volume a b :=
    ((continuous_const.mul hf)).intervalIntegrable a b
  have hint3 : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume a b :=
    continuous_const.intervalIntegrable a b
  have hnn : 0 ≤ ∫ x in a..b, (f x - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  have hexp : (∫ x in a..b, (f x - m) ^ 2) = S - 2 * m * I + m ^ 2 * (b - a) := by
    have hpt : ∀ x ∈ Set.uIcc a b, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := by
      intro x _
      ring
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_add (hint1.sub hint2) hint3,
      intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hclear : S - 2 * m * I + m ^ 2 * (b - a) = S - I ^ 2 / (b - a) := by
    rw [hm]
    field_simp
    ring
  rw [hclear, sub_nonneg, div_le_iff₀ hlen] at hnn
  linarith

/-- The mean of the trial over the band is the hyperbolic sine quotient at the aperture. -/
theorem integral_kaiserTrial {c : ℝ} (hc : 0 < c) :
    (∫ x in (-1 : ℝ)..1, kaiserTrial c x) = 2 * Real.sinh c / c := by
  have h0 : (0 : ℝ) ^ 2 < c ^ 2 := by
    have hpos : (0 : ℝ) < c ^ 2 := by positivity
    simpa using hpos
  have h := integral_kaiserTrial_cos_of_lt (c := c) (ω := 0) h0
  have hL : (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (0 * x))
      = ∫ x in (-1 : ℝ)..1, kaiserTrial c x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [zero_mul, Real.cos_zero, mul_one]
  have hsqrt : Real.sqrt (c ^ 2 - 0 ^ 2) = c := by
    rw [show c ^ 2 - (0 : ℝ) ^ 2 = c ^ 2 by ring, Real.sqrt_sq hc.le]
  rw [hL, hsqrt] at h
  exact h

/-- **The in-band energy of the trial grows exponentially.**  By the squared-mean inequality it is at
least half the square of the mean `2 sinh(c)/c`. -/
theorem energy_kaiserTrial_ge {c : ℝ} (hc : 0 < c) :
    (2 * Real.sinh c / c) ^ 2 / 2 ≤ ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 := by
  have h := sq_intervalIntegral_le (a := -1) (b := 1) (by norm_num) (continuous_kaiserTrial c)
  rw [integral_kaiserTrial hc, show (1 : ℝ) - -1 = 2 by norm_num] at h
  linarith

theorem energy_kaiserTrial_pos {c : ℝ} (hc : 0 < c) :
    0 < ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 := by
  have hs : 0 < Real.sinh c := by
    have hlt : Real.exp (-c) < Real.exp c := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.sinh_eq]
    linarith
  have hq : 0 < 2 * Real.sinh c / c := div_pos (by linarith) hc
  have h0 : 0 < (2 * Real.sinh c / c) ^ 2 / 2 := div_pos (pow_pos hq 2) two_pos
  exact lt_of_lt_of_le h0 (energy_kaiserTrial_ge hc)

/-- The trial is a nonzero band class, so it is admissible in the variational bound. -/
theorem bandClass_kaiserTrial_ne_zero {c : ℝ} (hc : 0 < c) :
    bandClass (kaiserTrial c) (continuous_kaiserTrial c) ≠ 0 := by
  intro h
  have hnorm : ‖bandClass (kaiserTrial c) (continuous_kaiserTrial c)‖ ^ 2 = 0 := by
    rw [h, norm_zero]
    norm_num
  rw [norm_sq_bandClass] at hnorm
  have hpos := energy_kaiserTrial_pos hc
  rw [hnorm] at hpos
  exact lt_irrefl 0 hpos

/-! ## The leakage envelope -/

/-- **The leakage envelope in closed form.**  The out-of-band mass of the trial is at most `8` and its
in-band energy at least `(2 sinh(c)/c)²/2`, so the variational bound closes with an aperture-free
numerator. -/
theorem one_sub_norm_bandOperatorL2_mul_sinh_le {c : ℝ} (hc : 0 < c) :
    (1 - ‖bandOperatorL2 c‖) * (2 * Real.sinh c / c) ^ 2 ≤ 16 := by
  have hcont := continuous_kaiserTrial c
  have hEge := energy_kaiserTrial_ge hc
  have hEpos := energy_kaiserTrial_pos hc
  have hvar := one_sub_norm_bandOperatorL2_le c (kaiserTrial c) hcont
    (bandClass_kaiserTrial_ne_zero hc)
  rw [leakage_eq_spectral_tail hc hcont] at hvar
  have htail := integral_tail_kaiser_le (c := c) hc.le
  rcases le_or_gt (1 - ‖bandOperatorL2 c‖) 0 with hL | hL
  · have hsq : (0 : ℝ) ≤ (2 * Real.sinh c / c) ^ 2 := sq_nonneg _
    nlinarith [hL, hsq]
  · -- the deficit is positive: clear the denominator of the Rayleigh bound
    rw [le_div_iff₀ hEpos] at hvar
    have hmul : (1 - ‖bandOperatorL2 c‖) * ((2 * Real.sinh c / c) ^ 2 / 2)
        ≤ (1 - ‖bandOperatorL2 c‖) * ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 :=
      mul_le_mul_of_nonneg_left hEge hL.le
    nlinarith [hvar, hmul, htail]

/-- **The exponential leakage envelope.**  For apertures at least `1` the loss of the best band
concentration is exponentially small: `1 - ‖B_c‖ <= 64 c² e^(-2c)`. -/
theorem one_sub_norm_bandOperatorL2_le_exp {c : ℝ} (hc : 1 ≤ c) :
    1 - ‖bandOperatorL2 c‖ ≤ 64 * c ^ 2 * Real.exp (-(2 * c)) := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hmain := one_sub_norm_bandOperatorL2_mul_sinh_le hcpos
  -- the trial mean dominates a pure exponential
  have hexpge : (2 : ℝ) ≤ Real.exp c := by
    have h := Real.add_one_le_exp c
    linarith
  have hnegle : Real.exp (-c) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hsinh : Real.exp c / 2 ≤ 2 * Real.sinh c := by
    have hs : 2 * Real.sinh c = Real.exp c - Real.exp (-c) := by
      rw [Real.sinh_eq]
      ring
    rw [hs]
    linarith
  have hexp2 : Real.exp (2 * c) = Real.exp c * Real.exp c := by
    rw [show 2 * c = c + c by ring, Real.exp_add]
  have hsqle : (Real.exp c / 2) ^ 2 ≤ (2 * Real.sinh c) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsinh 2
  have hI2 : Real.exp (2 * c) ≤ (2 * Real.sinh c / c) ^ 2 * (4 * c ^ 2) := by
    have hid : (2 * Real.sinh c / c) ^ 2 * (4 * c ^ 2) = 16 * Real.sinh c ^ 2 := by
      field_simp
      ring
    rw [hid, hexp2]
    nlinarith [hsqle]
  -- and the envelope follows from the closed-form bound
  rw [show (64 : ℝ) * c ^ 2 * Real.exp (-(2 * c)) = 64 * c ^ 2 / Real.exp (2 * c) by
    rw [Real.exp_neg]
    ring]
  rw [le_div_iff₀ (Real.exp_pos _)]
  rcases le_or_gt (1 - ‖bandOperatorL2 c‖) 0 with hL | hL
  · have hexppos : 0 < Real.exp (2 * c) := Real.exp_pos _
    nlinarith [hL, hexppos, sq_nonneg c]
  · have hstep1 : (1 - ‖bandOperatorL2 c‖) * Real.exp (2 * c)
        ≤ (1 - ‖bandOperatorL2 c‖) * ((2 * Real.sinh c / c) ^ 2 * (4 * c ^ 2)) :=
      mul_le_mul_of_nonneg_left hI2 hL.le
    have hstep2 : (1 - ‖bandOperatorL2 c‖) * ((2 * Real.sinh c / c) ^ 2 * (4 * c ^ 2))
        = ((1 - ‖bandOperatorL2 c‖) * (2 * Real.sinh c / c) ^ 2) * (4 * c ^ 2) := by
      ring
    have hstep3 : ((1 - ‖bandOperatorL2 c‖) * (2 * Real.sinh c / c) ^ 2) * (4 * c ^ 2)
        ≤ 16 * (4 * c ^ 2) := mul_le_mul_of_nonneg_right hmain (by positivity)
    rw [hstep2] at hstep1
    linarith

end GaloisForLFunctions.RHTower

end
