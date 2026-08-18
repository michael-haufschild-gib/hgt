import GaloisForLFunctions.RHTower.ProlateRiccatiRatioBounds

/-!
# The two elementary masses of the band error control

The error control of the sharp amplitude transport is a sum of terms weighted by `1/y` and
`1/(1-y)`.  Against the WKB measure the two `1/y` terms integrate elementarily:

```text
∫ dy / (y² sqrt(y² - s))  =  [ sqrt(y² - s) / (s y) ] ,
∫ dy / (y² - s)^{3/2}     =  [ -y / (s sqrt(y² - s)) ] ,
```

and both telescope to something `s`-free.  The first is bounded by `1/a²` on `[a, b]` — the pole at
`s` cancels against the numerator — and the second by `a/(s sqrt(a² - s))`.  At the rescaled
matching point `a = K/sqrt c` with `s ≍ μ/c` these are `c/K²` and `c K/(μ sqrt(K² - μ))`, so after
the `1/c` prefactors of the error control they are `O(1/K²)` and `O(1/K)`: both vanish as the
matching point is pushed out, uniformly in the bandwidth.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

theorem hasDerivAt_sqrt_sub_div {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (hys : s < y ^ 2) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - s) / (s * t))
      (1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) y := by
  have hpos : (0 : ℝ) < y ^ 2 - s := by linarith
  have hsq : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 hpos
  have hsq2 : Real.sqrt (y ^ 2 - s) ^ 2 = y ^ 2 - s := Real.sq_sqrt hpos.le
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).sub_const s
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - s))
      (2 * y / (2 * Real.sqrt (y ^ 2 - s))) y := h1.sqrt hpos.ne'
  have h3 : HasDerivAt (fun t : ℝ => s * t) s y := by
    have := (hasDerivAt_id y).const_mul s
    refine this.congr_deriv ?_
    ring
  have h4 := h2.div h3 (by positivity)
  refine h4.congr_deriv ?_
  field_simp
  nlinarith [hsq2, hsq, hpos]

theorem hasDerivAt_neg_div_sqrt {s y : ℝ} (hs : 0 < s) (hys : s < y ^ 2) :
    HasDerivAt (fun t : ℝ => -(t / (s * Real.sqrt (t ^ 2 - s))))
      (1 / (Real.sqrt (y ^ 2 - s)) ^ 3) y := by
  have hpos : (0 : ℝ) < y ^ 2 - s := by linarith
  have hsq : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 hpos
  have hsq2 : Real.sqrt (y ^ 2 - s) ^ 2 = y ^ 2 - s := Real.sq_sqrt hpos.le
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).sub_const s
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - s))
      (2 * y / (2 * Real.sqrt (y ^ 2 - s))) y := h1.sqrt hpos.ne'
  have h3 : HasDerivAt (fun t : ℝ => s * Real.sqrt (t ^ 2 - s))
      (s * (2 * y / (2 * Real.sqrt (y ^ 2 - s)))) y := h2.const_mul s
  have h4 := (hasDerivAt_id y).div h3 (by positivity)
  have h5 := h4.neg
  refine h5.congr_deriv ?_
  simp only [id_eq]
  field_simp
  nlinarith [hsq2, hsq, hpos]

/-- **The first elementary mass.**  On any interval beyond the turning point the integral is bounded
by `1/a²`, with no dependence on the separation. -/
theorem integral_inv_sq_mul_sqrt_le {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (has : s < a ^ 2)
    (hab : a ≤ b) :
    (∫ y in a..b, 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) ≤ 1 / a ^ 2 := by
  have hmono : ∀ y ∈ uIcc a b, 0 < y ∧ s < y ^ 2 := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    refine ⟨hy0, ?_⟩
    nlinarith [hya, ha]
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - s) / (s * t))
        (1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) y := by
    intro y hy
    obtain ⟨hy0, hys⟩ := hmono y hy
    exact hasDerivAt_sqrt_sub_div hs hy0 hys
  have hcont : ContinuousOn (fun y : ℝ => 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) (uIcc a b) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuousOn_pow 2).mul (Real.continuous_sqrt.comp_continuousOn
        (((continuousOn_pow 2).sub continuousOn_const)))
    · intro y hy
      obtain ⟨hy0, hys⟩ := hmono y hy
      have h1 : (0 : ℝ) < y ^ 2 := by positivity
      have h2 : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
      positivity
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s)))
      volume a b := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  -- the telescoped value is at most `1/a²`
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hbs : s < b ^ 2 := by nlinarith [hab, ha]
  have hsa : 0 < Real.sqrt (a ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
  have hsb : 0 < Real.sqrt (b ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
  have hsa2 : Real.sqrt (a ^ 2 - s) ^ 2 = a ^ 2 - s := Real.sq_sqrt (by linarith)
  have hsb2 : Real.sqrt (b ^ 2 - s) ^ 2 = b ^ 2 - s := Real.sq_sqrt (by linarith)
  have hble : Real.sqrt (b ^ 2 - s) / (s * b) ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith [hsb2, hsb, hb0]
  have hua : Real.sqrt (a ^ 2 - s) ≤ a := by nlinarith [hsa2, hsa, ha]
  have hkey' : (a - Real.sqrt (a ^ 2 - s)) * a ≤ s := by nlinarith [hsa2, hua, hsa, ha]
  have hage : 1 / s - Real.sqrt (a ^ 2 - s) / (s * a) ≤ 1 / a ^ 2 := by
    have hval : 1 / s - Real.sqrt (a ^ 2 - s) / (s * a)
        = (a - Real.sqrt (a ^ 2 - s)) / (s * a) := by
      field_simp
    rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey', ha, hs]
  linarith [hble, hage]

/-- **The second elementary mass.**  Its telescoped value is bounded by the left endpoint term. -/
theorem integral_inv_pow_sqrt_le {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (has : s < a ^ 2)
    (hab : a ≤ b) :
    (∫ y in a..b, 1 / (Real.sqrt (y ^ 2 - s)) ^ 3) ≤ a / (s * Real.sqrt (a ^ 2 - s)) := by
  have hmono : ∀ y ∈ uIcc a b, 0 < y ∧ s < y ^ 2 := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    refine ⟨hy0, ?_⟩
    nlinarith [hya, ha]
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => -(t / (s * Real.sqrt (t ^ 2 - s))))
        (1 / (Real.sqrt (y ^ 2 - s)) ^ 3) y := by
    intro y hy
    obtain ⟨hy0, hys⟩ := hmono y hy
    exact hasDerivAt_neg_div_sqrt hs hys
  have hcont : ContinuousOn (fun y : ℝ => 1 / (Real.sqrt (y ^ 2 - s)) ^ 3) (uIcc a b) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((Real.continuous_sqrt.comp_continuousOn
        (((continuousOn_pow 2).sub continuousOn_const)))).pow 3
    · intro y hy
      obtain ⟨hy0, hys⟩ := hmono y hy
      have h2 : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
      positivity
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (Real.sqrt (y ^ 2 - s)) ^ 3)
      volume a b := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hbs : s < b ^ 2 := by nlinarith [hab, ha]
  have hsb : 0 < Real.sqrt (b ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
  have hnn : 0 ≤ b / (s * Real.sqrt (b ^ 2 - s)) := by positivity
  linarith [hnn]


/-- **The third elementary mass.**  The integrand is decreasing, so the integral is at most the
length times its value at the left endpoint. -/
theorem integral_inv_sqrt_le {s a b : ℝ} (ha : 0 < a) (has : s < a ^ 2)
    (hab : a ≤ b) :
    (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s)) ≤ (b - a) / Real.sqrt (a ^ 2 - s) := by
  have hsa : 0 < Real.sqrt (a ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
  have hmono : ∀ y ∈ Icc a b, 1 / Real.sqrt (y ^ 2 - s) ≤ 1 / Real.sqrt (a ^ 2 - s) := by
    intro y hy
    have hya : a ≤ y := hy.1
    have hsq : a ^ 2 ≤ y ^ 2 := by nlinarith [hya, ha]
    have hle : Real.sqrt (a ^ 2 - s) ≤ Real.sqrt (y ^ 2 - s) := Real.sqrt_le_sqrt (by linarith)
    exact one_div_le_one_div_of_le hsa hle
  have hcont : ContinuousOn (fun y : ℝ => 1 / Real.sqrt (y ^ 2 - s)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn ((continuousOn_pow 2).sub continuousOn_const))
      fun y hy => ?_
    have hya : a ≤ y := hy.1
    have hsq : a ^ 2 ≤ y ^ 2 := by nlinarith [hya, ha]
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  have hint : IntervalIntegrable (fun y : ℝ => 1 / Real.sqrt (y ^ 2 - s)) volume a b :=
    hcont.intervalIntegrable
  have hle := intervalIntegral.integral_mono_on hab hint
    ((continuous_const : Continuous fun _ : ℝ => 1 / Real.sqrt (a ^ 2 - s)).intervalIntegrable _ _)
    hmono
  have hval : (∫ _y in a..b, 1 / Real.sqrt (a ^ 2 - s)) = (b - a) / Real.sqrt (a ^ 2 - s) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rwa [hval] at hle


theorem intervalIntegrable_errorPieces {s a b : ℝ} (ha : 0 < a) (has : s < a ^ 2) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) volume a b ∧
      IntervalIntegrable (fun y : ℝ => 1 / Real.sqrt (y ^ 2 - s) ^ 3) volume a b ∧
      IntervalIntegrable (fun y : ℝ => 1 / Real.sqrt (y ^ 2 - s)) volume a b := by
  have hmem : ∀ y ∈ uIcc a b, 0 < y ∧ s < y ^ 2 := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hya : a ≤ y := hy.1
    have hy0 : 0 < y := lt_of_lt_of_le ha hya
    exact ⟨hy0, by nlinarith [hya, ha]⟩
  have hsqrt : ContinuousOn (fun y : ℝ => Real.sqrt (y ^ 2 - s)) (uIcc a b) :=
    Real.continuous_sqrt.comp_continuousOn ((continuousOn_pow 2).sub continuousOn_const)
  have hne : ∀ y ∈ uIcc a b, Real.sqrt (y ^ 2 - s) ≠ 0 := by
    intro y hy
    obtain ⟨_, hys⟩ := hmem y hy
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  refine ⟨?_, ?_, ?_⟩
  · refine (ContinuousOn.div continuousOn_const ((continuousOn_pow 2).mul hsqrt)
      fun y hy => ?_).intervalIntegrable
    obtain ⟨hy0, hys⟩ := hmem y hy
    have h1 : (0 : ℝ) < y ^ 2 := by positivity
    have h2 : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
    exact (mul_pos h1 h2).ne'
  · refine (ContinuousOn.div continuousOn_const (hsqrt.pow 3) fun y hy => ?_).intervalIntegrable
    obtain ⟨_, hys⟩ := hmem y hy
    have h2 : 0 < Real.sqrt (y ^ 2 - s) := Real.sqrt_pos.2 (by linarith)
    exact (pow_pos h2 3).ne'
  · exact (ContinuousOn.div continuousOn_const hsqrt hne).intervalIntegrable

/-- **The full error majorant integrates to the three masses.** -/
theorem integral_errorMajorant_le {s a b C₁ C₂ : ℝ} (hs : 0 < s) (ha : 0 < a) (has : s < a ^ 2)
    (hab : a ≤ b) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    (∫ y in a..b, (2 * (1 / (y ^ 2 * Real.sqrt (y ^ 2 - s)))
        + C₁ * (1 / Real.sqrt (y ^ 2 - s) ^ 3) + C₂ * (1 / Real.sqrt (y ^ 2 - s))))
      ≤ 2 * (1 / a ^ 2) + C₁ * (a / (s * Real.sqrt (a ^ 2 - s)))
        + C₂ * ((b - a) / Real.sqrt (a ^ 2 - s)) := by
  obtain ⟨hi1, hi2, hi3⟩ := intervalIntegrable_errorPieces ha has hab
  have hsplit : (∫ y in a..b, (2 * (1 / (y ^ 2 * Real.sqrt (y ^ 2 - s)))
        + C₁ * (1 / Real.sqrt (y ^ 2 - s) ^ 3) + C₂ * (1 / Real.sqrt (y ^ 2 - s))))
      = 2 * (∫ y in a..b, 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s)))
        + C₁ * (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s) ^ 3)
        + C₂ * (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s)) := by
    rw [intervalIntegral.integral_add ((hi1.const_mul 2).add (hi2.const_mul C₁))
      (hi3.const_mul C₂), intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul C₁),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  have h1 : (∫ y in a..b, 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) ≤ 1 / a ^ 2 :=
    integral_inv_sq_mul_sqrt_le hs ha has hab
  have h2 : (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s) ^ 3) ≤ a / (s * Real.sqrt (a ^ 2 - s)) :=
    integral_inv_pow_sqrt_le hs ha has hab
  have h3 : (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s)) ≤ (b - a) / Real.sqrt (a ^ 2 - s) :=
    integral_inv_sqrt_le ha has hab
  have hm1 : 2 * (∫ y in a..b, 1 / (y ^ 2 * Real.sqrt (y ^ 2 - s))) ≤ 2 * (1 / a ^ 2) := by
    linarith [h1]
  have hm2 : C₁ * (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s) ^ 3)
      ≤ C₁ * (a / (s * Real.sqrt (a ^ 2 - s))) := mul_le_mul_of_nonneg_left h2 hC₁
  have hm3 : C₂ * (∫ y in a..b, 1 / Real.sqrt (y ^ 2 - s))
      ≤ C₂ * ((b - a) / Real.sqrt (a ^ 2 - s)) := mul_le_mul_of_nonneg_left h3 hC₂
  linarith [hm1, hm2, hm3]

end GaloisForLFunctions.RHTower

end
