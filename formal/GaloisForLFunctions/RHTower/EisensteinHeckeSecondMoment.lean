import GaloisForLFunctions.RHTower.EisensteinHeckeResonantMoment

/-!
# The second Hecke moment of a truncated resonant state

For a resonant parameter `u` (`Λ(1+2u) = 0`, `Re u < 0`, `Im u > 0`), every prime `p` and every
height `Y ≥ p`, the `L²` norm of the Hecke transform of the truncation is

`∫_𝒟 |T_pΛ^Y E_u|² = (2 + p^{2u} + p^{2ū}) · ∫_𝒟 |Λ^Y E_u|²`.

Together with the first moment `(p^u + p^{ū})` this identifies the Hecke data of the truncated
resonant state, exactly and at every height, with the first two moments of the Breit–Wigner
(Cauchy) profile of the resonance: the variance is `2(1 − p^{2 Re u})`.  The proof expands
`T_pΛ^Y E_u = (p^u + p^{-u})Λ^Y E_u + R_p` and evaluates the three pieces: the norm of the
truncation, the band integral of the remainder against the truncation, and the `L²` norm of the
remainder on its two bands.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Height functions on the fundamental domain -/

theorem measureReal_unitIcc : (volume : Measure ℝ).real unitIcc = 1 := by
  rw [measureReal_def, unitIcc, Real.volume_Icc]
  norm_num

/-- A function of the height alone, supported on a band between heights `≥ 1`, integrates over
`𝒟` to its height integral against `dy/y²`. -/
theorem setIntegral_fd_height {Y₁ Y₂ : ℝ} (hY : 1 ≤ Y₁) (h : ℝ → ℂ)
    (hh : ContinuousOn h (Icc Y₁ Y₂)) :
    ∫ z in fd, (if Y₁ < z.im ∧ z.im ≤ Y₂ then h z.im else 0) =
      ∫ y in Ioc Y₁ Y₂, h y / ((y : ℝ) : ℂ) ^ 2 := by
  have hY0 : 0 < Y₁ := by linarith
  have hind : (fun z : ℍ => if Y₁ < z.im ∧ z.im ≤ Y₂ then h z.im else 0) =
      {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂}.indicator
        (fun z => (fun q : ℝ × ℝ => h q.2) (z.re, z.im)) := by
    funext z
    by_cases hz : Y₁ < z.im ∧ z.im ≤ Y₂
    · rw [if_pos hz, Set.indicator_of_mem (show z ∈ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
    · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y₁ < z.im ∧ z.im ≤ Y₂} from hz)]
  rw [hind, setIntegral_indicator (measurableSet_band Y₁ Y₂),
    setIntegral_fd_band_eq hY (fun q : ℝ × ℝ => h q.2)]
  have hcont : ContinuousOn (fun q : ℝ × ℝ => h q.2 / ((q.2 : ℝ) : ℂ) ^ 2)
      (unitIcc ×ˢ Icc Y₁ Y₂) := by
    have hc : ContinuousOn (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn
    have hh' : ContinuousOn (fun q : ℝ × ℝ => h q.2) (unitIcc ×ˢ Icc Y₁ Y₂) :=
      hh.comp continuous_snd.continuousOn (fun q hq => hq.2)
    refine hh'.div (hc.pow 2) ?_
    intro q hq
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hY0 hq.2.1)))
  rw [setIntegral_bandRect_eq_iterated hcont]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  simp only
  rw [setIntegral_const, measureReal_unitIcc, one_smul]

/-! ## The remainder on the two bands for a resonant state -/

theorem sqrt_inv_mul_cpow_half_sub {p : ℕ} (hp : 0 < p) (u : ℂ) :
    (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u) = (p : ℂ) ^ (-u) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC, ← sqrt_eq_cpow_half p]
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
    exact_mod_cast this.ne'
  push_cast
  field_simp

theorem lowerBandRemainder_resonant {p : ℕ} (hp : 0 < p) {u : ℂ} (hA : msA u = 0) (y : ℝ) :
    lowerBandRemainder p u y = -(msB u * (y : ℂ) ^ (1 / 2 - u) * (p : ℂ) ^ (-u)) := by
  rw [lowerBandRemainder_of_msA_eq_zero p hA, sqrt_inv_mul_cpow_half_sub hp]

theorem upperBandRemainder_resonant {p : ℕ} (hp : 0 < p) {u : ℂ} (hA : msA u = 0) (y : ℝ) :
    upperBandRemainder p u y = msB u * (y : ℂ) ^ (1 / 2 - u) * (p : ℂ) ^ u := by
  unfold upperBandRemainder
  rw [lowerBandRemainder_resonant hp hA, cuspConstantPart_eq_msAB, hA]
  ring

theorem half_sub_re (u : ℂ) : ((1 : ℂ) / 2 - u).re = 1 / 2 - u.re := by
  rw [Complex.sub_re]
  norm_num

theorem rpow_half_sub_sq {y : ℝ} (hy : 0 < y) (u : ℂ) :
    (y ^ ((1 : ℂ) / 2 - u).re) ^ (2 : ℕ) = y ^ (1 - 2 * u.re) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, half_sub_re]
  congr 1
  push_cast
  ring

theorem rpow_re_sq {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x ^ w.re) ^ (2 : ℕ) = x ^ (2 * w.re) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

theorem norm_sq_lowerBandRemainder_resonant {p : ℕ} (hp : 0 < p) {u : ℂ} (hA : msA u = 0)
    {y : ℝ} (hy : 0 < y) :
    ‖lowerBandRemainder p u y‖ ^ 2 =
      ‖msB u‖ ^ 2 * (p : ℝ) ^ (-2 * u.re) * y ^ (1 - 2 * u.re) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [lowerBandRemainder_resonant hp hA, norm_neg, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_natCast_cpow_of_pos hp, mul_pow, mul_pow,
    rpow_half_sub_sq hy, rpow_re_sq hpR]
  simp only [Complex.neg_re]
  ring_nf

theorem norm_sq_upperBandRemainder_resonant {p : ℕ} (hp : 0 < p) {u : ℂ} (hA : msA u = 0)
    {y : ℝ} (hy : 0 < y) :
    ‖upperBandRemainder p u y‖ ^ 2 =
      ‖msB u‖ ^ 2 * (p : ℝ) ^ (2 * u.re) * y ^ (1 - 2 * u.re) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [upperBandRemainder_resonant hp hA, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_natCast_cpow_of_pos hp, mul_pow, mul_pow,
    rpow_half_sub_sq hy, rpow_re_sq hpR]
  ring

/-! ## The `L²` norm of the remainder -/

theorem rpow_band_integral {a b : ℝ} (hab : a ≤ b) {r : ℝ} (hr : -1 < r) (c : ℝ) :
    ∫ y in Ioc a b, c * y ^ r = c * ((b ^ (r + 1) - a ^ (r + 1)) / (r + 1)) := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hr)]

theorem ofReal_normSq_div_sq_eq {y : ℝ} (hy : 0 < y) (c r : ℝ) :
    ((c * y ^ (1 - r) : ℝ) : ℂ) / ((y : ℝ) : ℂ) ^ 2 = ((c * y ^ (-1 - r) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_div]
  congr 1
  rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hy]
  congr 2
  ring

/-- The `L²` norm of the Hecke remainder of a resonant state over `𝒟`. -/
theorem setIntegral_fd_normSq_heckeRemainder {p : ℕ} (hp : 0 < p) {u : ℂ}
    (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ) =
      ((‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (-2 * u.re) *
        ((p : ℝ) ^ (-2 * u.re) - (p : ℝ) ^ (2 * u.re)) : ℝ) : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hYp : 0 < Y / p := by positivity
  have hYp1 : 1 ≤ Y / p := by rw [le_div_iff₀ hpR]; linarith
  have hY1 : 1 ≤ Y := by linarith
  have hYpY : Y / p ≤ Y := by
    rw [div_le_iff₀ hpR]
    nlinarith
  have hYYp : Y ≤ Y * p := by nlinarith
  -- pointwise decomposition into the two bands
  have hpt : ∀ z : ℍ, ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ) =
      (if Y / p < z.im ∧ z.im ≤ Y then ((‖lowerBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) +
      (if Y < z.im ∧ z.im ≤ Y * p then ((‖upperBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) := by
    intro z
    by_cases h1 : z.im ≤ Y / p
    · rw [heckeRemainder_eq_zero_of_le hp u hY0 h1, if_neg (by intro h; linarith [h.1]),
        if_neg (by intro h; linarith [h.1]), norm_zero]
      norm_num
    by_cases h2 : z.im ≤ Y
    · rw [heckeRemainder_eq_lowerBand hp u hY0 (lt_of_not_ge h1) h2,
        if_pos ⟨lt_of_not_ge h1, h2⟩, if_neg (by intro h; linarith [h.1]), add_zero]
    by_cases h3 : z.im ≤ Y * p
    · rw [heckeRemainder_eq_upperBand hp u hY0 (lt_of_not_ge h2) h3,
        if_neg (by intro h; linarith [h.2]), if_pos ⟨lt_of_not_ge h2, h3⟩, zero_add]
    · rw [heckeRemainder_eq_zero_of_gt hp u hY0 (lt_of_not_ge h3),
        if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2]), norm_zero]
      norm_num
  rw [setIntegral_congr_fun isClosed_fd.measurableSet (fun z _ => hpt z)]
  -- continuity of the two band functions
  have hcl : ContinuousOn (fun y : ℝ => ((‖lowerBandRemainder p u y‖ ^ 2 : ℝ) : ℂ)) (Icc (Y / p) Y) :=
    Complex.continuous_ofReal.comp_continuousOn
      (((continuousOn_lowerBandRemainder p u hYp).norm).pow 2)
  have hcu : ContinuousOn (fun y : ℝ => ((‖upperBandRemainder p u y‖ ^ 2 : ℝ) : ℂ)) (Icc Y (Y * p)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (((continuousOn_upperBandRemainder p u hY0).norm).pow 2)
  -- integrability of the two brackets on `𝒟`
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcl
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu
  have hm1 : Measurable (fun z : ℍ => if Y / p < z.im ∧ z.im ≤ Y then
      ((‖lowerBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) :=
    Measurable.ite (measurableSet_band _ _)
      (Complex.measurable_ofReal.comp ((measurable_lowerBandRemainder_im p u).norm.pow_const 2))
      measurable_const
  have hm2 : Measurable (fun z : ℍ => if Y < z.im ∧ z.im ≤ Y * p then
      ((‖upperBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) :=
    Measurable.ite (measurableSet_band _ _)
      (Complex.measurable_ofReal.comp ((measurable_upperBandRemainder_im p u).norm.pow_const 2))
      measurable_const
  have hi1 : IntegrableOn (fun z : ℍ => if Y / p < z.im ∧ z.im ≤ Y then
      ((‖lowerBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm1.aestronglyMeasurable
      (M := max C₁ 0) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z _ => ?_)
    by_cases hz : Y / p < z.im ∧ z.im ≤ Y
    · rw [if_pos hz]
      exact (hC₁ z.im ⟨hz.1.le, hz.2⟩).trans (le_max_left _ _)
    · rw [if_neg hz, norm_zero]; exact le_max_right _ _
  have hi2 : IntegrableOn (fun z : ℍ => if Y < z.im ∧ z.im ≤ Y * p then
      ((‖upperBandRemainder p u z.im‖ ^ 2 : ℝ) : ℂ) else 0) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm2.aestronglyMeasurable
      (M := max C₂ 0) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z _ => ?_)
    by_cases hz : Y < z.im ∧ z.im ≤ Y * p
    · rw [if_pos hz]
      exact (hC₂ z.im ⟨hz.1.le, hz.2⟩).trans (le_max_left _ _)
    · rw [if_neg hz, norm_zero]; exact le_max_right _ _
  rw [integral_add hi1 hi2, setIntegral_fd_height hYp1 _ hcl, setIntegral_fd_height hY1 _ hcu]
  -- the two band integrals in closed form
  have hr : -1 < -1 - 2 * u.re := by linarith
  have hlow : ∫ y in Ioc (Y / p) Y, ((‖lowerBandRemainder p u y‖ ^ 2 : ℝ) : ℂ) / ((y : ℝ) : ℂ) ^ 2 =
      (((‖msB u‖ ^ 2 * (p : ℝ) ^ (-2 * u.re)) *
        ((Y ^ (-1 - 2 * u.re + 1) - (Y / p) ^ (-1 - 2 * u.re + 1)) / (-1 - 2 * u.re + 1)) : ℝ) : ℂ) := by
    rw [← rpow_band_integral hYpY hr, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans hYp hy.1
    rw [norm_sq_lowerBandRemainder_resonant hp hA hy0,
      ofReal_normSq_div_sq_eq hy0 (‖msB u‖ ^ 2 * (p : ℝ) ^ (-2 * u.re)) (2 * u.re)]
  have hup : ∫ y in Ioc Y (Y * p), ((‖upperBandRemainder p u y‖ ^ 2 : ℝ) : ℂ) / ((y : ℝ) : ℂ) ^ 2 =
      (((‖msB u‖ ^ 2 * (p : ℝ) ^ (2 * u.re)) *
        (((Y * p) ^ (-1 - 2 * u.re + 1) - Y ^ (-1 - 2 * u.re + 1)) / (-1 - 2 * u.re + 1)) : ℝ) : ℂ) := by
    rw [← rpow_band_integral hYYp hr, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have hy0 : 0 < y := lt_trans hY0 hy.1
    rw [norm_sq_upperBandRemainder_resonant hp hA hy0,
      ofReal_normSq_div_sq_eq hy0 (‖msB u‖ ^ 2 * (p : ℝ) ^ (2 * u.re)) (2 * u.re)]
  rw [hlow, hup, ← Complex.ofReal_add]
  congr 1
  have he : -1 - 2 * u.re + 1 = -2 * u.re := by ring
  rw [he, Real.div_rpow hY0.le hpR.le, Real.mul_rpow hY0.le hpR.le]
  have hpp : (p : ℝ) ^ (-2 * u.re) * (p : ℝ) ^ (2 * u.re) = 1 := by
    rw [← Real.rpow_add hpR]; simp
  have hpne : (p : ℝ) ^ (-2 * u.re) ≠ 0 := (Real.rpow_pos_of_pos hpR _).ne'
  have hA' : (p : ℝ) ^ (-2 * u.re) * (Y ^ (-2 * u.re) - Y ^ (-2 * u.re) / (p : ℝ) ^ (-2 * u.re)) =
      Y ^ (-2 * u.re) * ((p : ℝ) ^ (-2 * u.re) - 1) := by
    field_simp
  have hB' : (p : ℝ) ^ (2 * u.re) * (Y ^ (-2 * u.re) * (p : ℝ) ^ (-2 * u.re) - Y ^ (-2 * u.re)) =
      Y ^ (-2 * u.re) * (1 - (p : ℝ) ^ (2 * u.re)) := by
    linear_combination Y ^ (-2 * u.re) * hpp
  calc ‖msB u‖ ^ 2 * (p : ℝ) ^ (-2 * u.re) *
        ((Y ^ (-2 * u.re) - Y ^ (-2 * u.re) / (p : ℝ) ^ (-2 * u.re)) / (-2 * u.re)) +
      ‖msB u‖ ^ 2 * (p : ℝ) ^ (2 * u.re) *
        ((Y ^ (-2 * u.re) * (p : ℝ) ^ (-2 * u.re) - Y ^ (-2 * u.re)) / (-2 * u.re))
      = (‖msB u‖ ^ 2 * ((p : ℝ) ^ (-2 * u.re) *
          (Y ^ (-2 * u.re) - Y ^ (-2 * u.re) / (p : ℝ) ^ (-2 * u.re))) +
        ‖msB u‖ ^ 2 * ((p : ℝ) ^ (2 * u.re) *
          (Y ^ (-2 * u.re) * (p : ℝ) ^ (-2 * u.re) - Y ^ (-2 * u.re)))) / (-2 * u.re) := by ring
    _ = _ := by rw [hA', hB']; ring

/-! ## The second moment -/

/-- **The second Hecke moment of a truncated resonant state.**  For `Λ(1+2u) = 0`, `Re u < 0`,
`Im u > 0`, every prime `p` and every height `Y ≥ p`,
`∫_𝒟 |T_pΛ^Y E_u|² = (2 + p^{2u} + p^{2ū}) · ∫_𝒟 |Λ^Y E_u|²`. -/
theorem heckeSecondMoment_resonant {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    ((∫ z in fd, ‖heckeTruncated p u Y z‖ ^ 2 : ℝ) : ℂ) =
      (2 + (p : ℂ) ^ (2 * u) + (p : ℂ) ^ (2 * (starRingEnd ℂ) u)) *
        ((∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    linarith
  have him : ((starRingEnd ℂ) u).im ≠ 0 := by simp; exact hu.2.ne'
  set lam : ℂ := (p : ℂ) ^ u + (p : ℂ) ^ (-u) with hlam
  -- pointwise expansion of `|λτ + R|²`
  have hpt : ∀ z : ℍ, ((‖heckeTruncated p u Y z‖ ^ 2 : ℝ) : ℂ) =
      lam * (starRingEnd ℂ) lam * ((‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) +
      ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ) +
      ((starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
        truncatedLineModel (-(starRingEnd ℂ) u) Y z) +
       (starRingEnd ℂ) ((starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
        truncatedLineModel (-(starRingEnd ℂ) u) Y z))) := by
    intro z
    have hT := heckeTruncated_eq hp u Y z
    rw [← hlam] at hT
    have e1 : ((‖heckeTruncated p u Y z‖ ^ 2 : ℝ) : ℂ) =
        heckeTruncated p u Y z * (starRingEnd ℂ) (heckeTruncated p u Y z) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
    have e2 : ((‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) =
        truncatedLineModel u Y z * (starRingEnd ℂ) (truncatedLineModel u Y z) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
    have e3 : ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ) =
        heckeRemainder p u Y z.im * (starRingEnd ℂ) (heckeRemainder p u Y z.im) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
    have e4 : truncatedLineModel (-(starRingEnd ℂ) u) Y z =
        (starRingEnd ℂ) (truncatedLineModel u Y z) := by
      rw [truncatedLineModel_neg him, ← truncatedLineModel_conj]
    rw [e1, e2, e3, e4, hT]
    simp only [map_add, map_mul, Complex.conj_conj]
    ring
  rw [← integral_complex_ofReal, setIntegral_congr_fun isClosed_fd.measurableSet (fun z _ => hpt z)]
  -- integrability of the pieces on `𝒟`
  obtain ⟨M, hM0, hM⟩ := exists_bound_heckeRemainder hp0 u hY0
  have hmτ : Measurable (fun z : ℍ => ((‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_truncatedLineModel u Y).norm.pow_const 2)
  have hmR : Measurable (fun z : ℍ => ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_heckeRemainder_im p u Y).norm.pow_const 2)
  have hmX : Measurable (fun z : ℍ => (starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
      truncatedLineModel (-(starRingEnd ℂ) u) Y z)) :=
    measurable_const.mul ((measurable_heckeRemainder_im p u Y).mul
      (measurable_truncatedLineModel _ Y))
  have hi1 : IntegrableOn (fun z : ℍ => lam * (starRingEnd ℂ) lam *
      ((‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ)) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      (measurable_const.mul hmτ).aestronglyMeasurable
      (M := ‖lam * (starRingEnd ℂ) lam‖ * truncBound' u Y ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_truncatedLineModel_le_truncBound' u hY1 hz
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (norm_nonneg _)
  have hi2 : IntegrableOn (fun z : ℍ => ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ)) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hmR.aestronglyMeasurable
      (M := M ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z _ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM z.im) 2
  have hbound3 : ∀ z ∈ fd, ‖(starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
      truncatedLineModel (-(starRingEnd ℂ) u) Y z)‖ ≤
      ‖(starRingEnd ℂ) lam‖ * (M * truncBound' (-(starRingEnd ℂ) u) Y) := by
    intro z hz
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hM z.im) (norm_truncatedLineModel_le_truncBound' _ hY1 hz) (norm_nonneg _) hM0)
      (norm_nonneg _)
  have hi3 : IntegrableOn (fun z : ℍ => (starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
      truncatedLineModel (-(starRingEnd ℂ) u) Y z)) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hmX.aestronglyMeasurable
      (M := ‖(starRingEnd ℂ) lam‖ * (M * truncBound' (-(starRingEnd ℂ) u) Y)) ?_
    exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall hbound3)
  have hi4 : IntegrableOn (fun z : ℍ => (starRingEnd ℂ) ((starRingEnd ℂ) lam *
      (heckeRemainder p u Y z.im * truncatedLineModel (-(starRingEnd ℂ) u) Y z))) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      (Complex.continuous_conj.measurable.comp hmX).aestronglyMeasurable
      (M := ‖(starRingEnd ℂ) lam‖ * (M * truncBound' (-(starRingEnd ℂ) u) Y)) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [Complex.norm_conj]
    exact hbound3 z hz
  have hi12 : IntegrableOn (fun z : ℍ => lam * (starRingEnd ℂ) lam *
      ((‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) + ((‖heckeRemainder p u Y z.im‖ ^ 2 : ℝ) : ℂ)) fd :=
    hi1.add hi2
  have hi34 : IntegrableOn (fun z : ℍ => (starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
      truncatedLineModel (-(starRingEnd ℂ) u) Y z) +
      (starRingEnd ℂ) ((starRingEnd ℂ) lam * (heckeRemainder p u Y z.im *
        truncatedLineModel (-(starRingEnd ℂ) u) Y z))) fd :=
    hi3.add hi4
  rw [integral_add hi12 hi34, integral_add hi1 hi2, integral_add hi3 hi4,
    integral_const_mul, integral_complex_ofReal, setIntegral_fd_normSq_heckeRemainder hp0 hre hA hY,
    integral_conj, integral_const_mul, setIntegral_heckeRemainder_mul_trunc hp0 u _ hY,
    resonant_band_integral hp0 hu hre hA hY, integral_norm_sq_of_msA_eq_zero hu hre hA hY1]
  -- the scalar identities in `q = p^u`, `q' = p^{ū}`
  set q : ℂ := (p : ℂ) ^ u with hq
  set q' : ℂ := (p : ℂ) ^ ((starRingEnd ℂ) u) with hq'
  have hqne : q ≠ 0 := by
    intro h
    exact hpC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hq'ne : q' ≠ 0 := by
    intro h
    exact hpC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hconjq : (starRingEnd ℂ) q = q' := by
    rw [hq, hq', Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
      Complex.conj_natCast]
  have hqinv : (p : ℂ) ^ (-u) = q⁻¹ := by rw [hq, Complex.cpow_neg]
  have hlamq : lam = q + q⁻¹ := by rw [hlam, hqinv]
  have hconjlam : (starRingEnd ℂ) lam = q' + q'⁻¹ := by
    rw [hlamq, map_add, map_inv₀, hconjq]
  have hs : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u) = q⁻¹ := by
    rw [sqrt_inv_mul_cpow_half_sub hp0, hqinv]
  have hPplus : (((p : ℝ) ^ (2 * u.re) : ℝ) : ℂ) = q * q' := by
    rw [Complex.ofReal_cpow hpR.le, hq, hq', ← Complex.cpow_add _ _ hpC]
    push_cast
    congr 1
    apply Complex.ext
    · simp
      ring
    · simp
  have hPminus : (((p : ℝ) ^ (-2 * u.re) : ℝ) : ℂ) = (q * q')⁻¹ := by
    rw [Complex.ofReal_cpow hpR.le, ← hPplus, Complex.ofReal_cpow hpR.le, ← Complex.cpow_neg]
    push_cast
    congr 1
    ring
  have hdiv : (Y / p) ^ (-2 * u.re) = Y ^ (-2 * u.re) / (p : ℝ) ^ (-2 * u.re) :=
    Real.div_rpow hY0.le hpR.le _
  have hq2 : (p : ℂ) ^ (2 * u) = q ^ 2 := by
    rw [hq, show (2 : ℂ) * u = ((2 : ℕ) : ℂ) * u by push_cast; ring, Complex.cpow_nat_mul]
  have hq'2 : (p : ℂ) ^ (2 * (starRingEnd ℂ) u) = q' ^ 2 := by
    rw [hq', show (2 : ℂ) * (starRingEnd ℂ) u = ((2 : ℕ) : ℂ) * (starRingEnd ℂ) u by push_cast; ring,
      Complex.cpow_nat_mul]
  have hre2 : ((-2 * u.re : ℝ) : ℂ) ≠ 0 := by
    have : (-2 * u.re : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hconjq' : (starRingEnd ℂ) q' = q := by rw [← hconjq, Complex.conj_conj]
  rw [hdiv, hs, hconjlam, hlamq, hq2, hq'2]
  push_cast
  rw [hPplus, hPminus]
  simp only [map_mul, map_add, map_sub, map_neg, map_div₀, map_inv₀, map_pow, Complex.conj_ofReal,
    hconjq, hconjq', map_ofNat]
  field_simp
  ring

/-- The second Hecke moment in real form: `∫_𝒟 |T_pΛ^Y E_u|² = (2 + 2 Re(p^{2u}))·∫_𝒟 |Λ^Y E_u|²`,
so the Hecke variance of the truncated resonant state is `2(1 − p^{2 Re u})`. -/
theorem heckeSecondMoment_resonant_re {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, ‖heckeTruncated p u Y z‖ ^ 2 =
      (2 + 2 * ((p : ℂ) ^ (2 * u)).re) * ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 := by
  have h := heckeSecondMoment_resonant hp hu hre hA hY
  have hconj : (p : ℂ) ^ (2 * (starRingEnd ℂ) u) = (starRingEnd ℂ) ((p : ℂ) ^ (2 * u)) := by
    rw [show (2 : ℂ) * (starRingEnd ℂ) u = (starRingEnd ℂ) (2 * u) by rw [map_mul, map_ofNat],
      Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
      Complex.conj_natCast]
  rw [hconj, add_assoc, Complex.add_conj] at h
  have h' := congrArg Complex.re h
  simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h'

end

end RHTower
