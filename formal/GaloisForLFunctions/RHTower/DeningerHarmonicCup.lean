import GaloisForLFunctions.RHTower.DeningerHarmonicMode

/-!
# The cup pairing and the power correspondence of the harmonic modes

The leafwise cup trace pairs the mode of frequency `μ` with the mode of frequency `-μ`, and
nothing else: the pointwise wedge of the two chiral vectors is `2 i ε`, and the radial integral of
the squared profile is `1 / (2|μ|)`, so the pairing is `i / μ`.  Pairing a mode against the star of
its conjugate gives the positive number `1 / |μ|`.

The power correspondence pulls back along `r ↦ q r` and multiplies coefficients by `q`.  On modes
it is the arithmetic shift of frequencies `μ ↦ q μ`, of weight one for the cup pairing, and after
the normalization `e = |μ|^{1/2} α` it becomes an isometry up to the factor `q^{1/2}`.

* `deningerMode_cup` : the mode pairing `i / μ`.
* `deningerMode_cupStar` : positivity of the star pairing.
* `deningerPowerPullback_mode` : the power shift `F_q^* α_μ = q α_{qμ}`.
* `deningerPowerPullback_normalizedMode` : the centered-unitary normalization.
* `deningerPowerPullback_cup` : weight one of the cup pairing.
-/

namespace RHTower

open MeasureTheory Set

section Cup

/-- The mode of the opposite frequency has the same profile and the opposite chirality. -/
theorem deningerMode_neg {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) :
    deningerMode (-μ) r
      = ((deningerModeProfile μ r : ℂ),
          Complex.I * (deningerFreqSign μ : ℂ) * (deningerModeProfile μ r : ℂ)) := by
  have hprof : deningerModeProfile (-μ) r = deningerModeProfile μ r := by
    rw [deningerModeProfile, deningerModeProfile, abs_neg]
  refine Prod.ext ?_ ?_
  · show (deningerModeProfile (-μ) r : ℂ) = (deningerModeProfile μ r : ℂ)
    rw [hprof]
  · show -(Complex.I * (deningerFreqSign (-μ) : ℂ)) * (deningerModeProfile (-μ) r : ℂ)
        = Complex.I * (deningerFreqSign μ : ℂ) * (deningerModeProfile μ r : ℂ)
    rw [hprof, deningerFreqSign_neg hμ]
    push_cast
    ring

/-- **The pointwise mode cup pairing**: the wedge of the two opposite chiral vectors. -/
theorem deningerMode_wedge_neg {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) :
    deningerCxWedge (deningerMode μ r) (deningerMode (-μ) r)
      = (2 * Complex.I * (deningerFreqSign μ : ℂ)) * ((deningerModeProfile μ r ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerCxWedge, deningerMode_neg hμ, deningerMode_fst, deningerMode_snd]
  push_cast
  ring

/-- The nonzero sign as a complex number. -/
private theorem deningerFreqSign_cx_ne_zero (μ : ℝ) : (deningerFreqSign μ : ℂ) ≠ 0 := by
  intro h
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  rw [h, mul_zero] at hsq
  exact zero_ne_one hsq

/-- **The cup pairing of opposite modes** is `i / μ`. -/
theorem deningerMode_cup {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ), deningerCxWedge (deningerMode μ r) (deningerMode (-μ) r)
      = Complex.I / (μ : ℂ) := by
  have hcast : ((|μ| : ℝ) : ℂ) = (deningerFreqSign μ : ℂ) * (μ : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_abs hμ)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      fun r _ => deningerMode_wedge_neg hμ r,
    integral_const_mul, integral_complex_ofReal, deningerModeProfile_integral hμ]
  rw [show ((1 / (2 * |μ|) : ℝ) : ℂ) = 1 / (2 * ((|μ| : ℝ) : ℂ)) by push_cast; ring, hcast]
  have hsign := deningerFreqSign_cx_ne_zero μ
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  field_simp

/-- **The star pairing is positive**: pairing a mode against the star of its conjugate gives
`1 / |μ|`. -/
theorem deningerMode_cupStar {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ),
        deningerCxWedge (deningerMode μ r) (deningerCxStar (deningerMode (-μ) r))
      = ((1 / |μ| : ℝ) : ℂ) := by
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      deningerCxWedge (deningerMode μ r) (deningerCxStar (deningerMode (-μ) r))
        = (2 : ℂ) * ((deningerModeProfile μ r ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro r _
    rw [deningerCxStar, deningerCxWedge, deningerMode_neg hμ, deningerMode_fst, deningerMode_snd]
    have hI : Complex.I ^ (2 : ℕ) = -1 := Complex.I_sq
    push_cast
    linear_combination ((deningerModeProfile μ r : ℂ) ^ (2 : ℕ)) * hsq
      - ((deningerFreqSign μ : ℂ) ^ (2 : ℕ) * (deningerModeProfile μ r : ℂ) ^ (2 : ℕ)) * hI
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_complex_ofReal, deningerModeProfile_integral hμ]
  have habs : ((|μ| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr hμ
  push_cast
  field_simp

/-- **The star pairing is strictly positive**, which is the local Hodge positivity. -/
theorem deningerMode_cupStar_pos {μ : ℝ} (hμ : μ ≠ 0) : 0 < 1 / |μ| := by
  have : 0 < |μ| := abs_pos.mpr hμ
  positivity

end Cup

section PowerShift

/-- The power pullback of a leafwise one-form along `F_q (r) = q r`, which multiplies both
coefficients by `q`. -/
noncomputable def deningerPowerPullback (q : ℝ) (α : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  (q : ℂ) • α (q * r)

/-- **The power shift**: the pullback sends the mode of frequency `μ` to `q` times the mode of
frequency `q μ`, which is the arithmetic shift `a ↦ q a` on Kummer characters. -/
theorem deningerPowerPullback_mode {μ q : ℝ} (hq : 0 < q) (r : ℝ) :
    deningerPowerPullback q (deningerMode μ) r = (q : ℂ) • deningerMode (q * μ) r := by
  rw [deningerPowerPullback, deningerMode_scale hq]

/-- The normalized mode `e = |μ|^{1/2} α`. -/
noncomputable def deningerNormalizedMode (μ : ℝ) (r : ℝ) : ℂ × ℂ :=
  ((Real.sqrt |μ| : ℂ)) • deningerMode μ r

/-- **The normalized mode is a unit vector.** -/
theorem deningerNormalizedMode_normSq {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ),
        (‖(deningerNormalizedMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerNormalizedMode μ r).2‖ ^ (2 : ℕ)) = 1 := by
  have habs : (0 : ℝ) < |μ| := abs_pos.mpr hμ
  have hnorm : ‖((Real.sqrt |μ| : ℝ) : ℂ)‖ = Real.sqrt |μ| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      ‖(deningerNormalizedMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerNormalizedMode μ r).2‖ ^ (2 : ℕ)
        = |μ| * (‖(deningerMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerMode μ r).2‖ ^ (2 : ℕ)) := by
    intro r _
    rw [deningerNormalizedMode]
    show ‖((Real.sqrt |μ| : ℝ) : ℂ) * (deningerMode μ r).1‖ ^ (2 : ℕ)
        + ‖((Real.sqrt |μ| : ℝ) : ℂ) * (deningerMode μ r).2‖ ^ (2 : ℕ)
      = |μ| * (‖(deningerMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerMode μ r).2‖ ^ (2 : ℕ))
    rw [norm_mul, norm_mul, hnorm, mul_pow, mul_pow, Real.sq_sqrt habs.le]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    deningerMode_normSq hμ]
  field_simp

/-- **The centered power correspondence**: after normalization the pullback is the frequency shift
up to the factor `q^{1/2}`. -/
theorem deningerPowerPullback_normalizedMode {μ q : ℝ} (hq : 0 < q) (r : ℝ) :
    deningerPowerPullback q (deningerNormalizedMode μ) r
      = ((Real.sqrt q : ℝ) : ℂ) • deningerNormalizedMode (q * μ) r := by
  have hqabs : |q * μ| = q * |μ| := by
    rw [abs_mul, abs_of_pos hq]
  have hsqrt : Real.sqrt |q * μ| = Real.sqrt q * Real.sqrt |μ| := by
    rw [hqabs, Real.sqrt_mul hq.le]
  rw [deningerPowerPullback, deningerNormalizedMode, deningerNormalizedMode,
    deningerMode_scale hq, hsqrt, smul_smul, smul_smul]
  congr 1
  have h : ((q : ℝ) : ℂ) = ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt hq.le).symm
  rw [h]
  push_cast
  ring

/-- **Weight one of the cup pairing under the power correspondence.** -/
theorem deningerPowerPullback_cup {μ q : ℝ} (hμ : μ ≠ 0) (hq : 0 < q) :
    ∫ r in Ioi (0 : ℝ), deningerCxWedge (deningerPowerPullback q (deningerMode μ) r)
        (deningerPowerPullback q (deningerMode (-μ)) r)
      = (q : ℂ) * ∫ r in Ioi (0 : ℝ),
          deningerCxWedge (deningerMode μ r) (deningerMode (-μ) r) := by
  have hqμ : q * μ ≠ 0 := mul_ne_zero (ne_of_gt hq) hμ
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      deningerCxWedge (deningerPowerPullback q (deningerMode μ) r)
          (deningerPowerPullback q (deningerMode (-μ)) r)
        = ((q : ℂ) * (q : ℂ))
            * deningerCxWedge (deningerMode (q * μ) r) (deningerMode (-(q * μ)) r) := by
    intro r _
    rw [deningerPowerPullback_mode hq, deningerPowerPullback, deningerMode_scale hq,
      show q * -μ = -(q * μ) by ring, deningerCxWedge_smul_left, deningerCxWedge_smul_right]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    deningerMode_cup hqμ, deningerMode_cup hμ]
  have hqc : (q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hq
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  push_cast
  field_simp

end PowerShift

end RHTower
