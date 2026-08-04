import GaloisForLFunctions.RHTower.ProlateWKBSubsolution

/-!
# The WKB exponent of the prolate equation is at most the aperture

The tunneling exponent of the prolate equation is the WKB integral

```text
∫ sqrt((chi + c² y²)/(1 - y²)) dy.
```

Because the eigenvalue parameter `chi` is nonpositive, the integrand is dominated by its `chi = 0` value
`c y / sqrt(1 - y²)`, whose antiderivative is elementary: `-c sqrt(1 - y²)`.  Hence over any subinterval of
the right half band

```text
∫_a^b sqrt((chi + c² y²)/(1 - y²)) dy <= c (sqrt(1-a²) - sqrt(1-b²)) <= c,
```

and the bound is sharp — at `chi = 0`, `a = 0`, `b = 1` it is an equality.

Combined with the outer-band comparison this gives an *explicit* endpoint bound with the correct exponential
rate: on the outer band a positive solution satisfies `Phi(b) >= Phi(a) e^(-c)`.  Through the exact endpoint
identity `(4)` that `e^(-c)` on the eigenfunction is the `e^(-2c)` of the leakage.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set intervalIntegral MeasureTheory

open _root_.RHTower

/-! ## The dominating profile and its antiderivative -/

/-- For a nonpositive eigenvalue parameter the WKB profile is dominated by its `chi = 0` value. -/
theorem prolateWKB_le_of_nonpos {c χ y : ℝ} (hc : 0 ≤ c) (hy : y ∈ Ioo (-1 : ℝ) 1) (hy0 : 0 ≤ y)
    (hχ : χ ≤ 0) : prolateWKB c χ y ≤ c * y / Real.sqrt (1 - y ^ 2) := by
  have hp : 0 < 1 - y ^ 2 := by
    have h1 : -1 < y := hy.1
    have h2 : y < 1 := hy.2
    nlinarith
  have hsp : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr hp
  have hmono : (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) ≤ (c * y) ^ 2 / (1 - y ^ 2) := by
    have hnum : χ + c ^ 2 * y ^ 2 ≤ (c * y) ^ 2 := by nlinarith
    have hinv := mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hp))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hinv
  have hstep : prolateWKB c χ y ≤ Real.sqrt ((c * y) ^ 2 / (1 - y ^ 2)) := by
    rw [prolateWKB]
    exact Real.sqrt_le_sqrt hmono
  have hval : Real.sqrt ((c * y) ^ 2 / (1 - y ^ 2)) = c * y / Real.sqrt (1 - y ^ 2) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  rw [hval] at hstep
  exact hstep

/-- The elementary antiderivative of the dominating profile. -/
theorem hasDerivAt_negMulSqrt {c y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => -c * Real.sqrt (1 - t ^ 2))
      (c * y / Real.sqrt (1 - y ^ 2)) y := by
  have hp : 0 < 1 - y ^ 2 := by
    have h1 : -1 < y := hy.1
    have h2 : y < 1 := hy.2
    nlinarith
  have hsp : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr hp
  have hinner : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have hsqrt := hinner.sqrt (ne_of_gt hp)
  have hscaled := hsqrt.const_mul (-c)
  refine hscaled.congr_deriv ?_
  field_simp

/-! ## The bound on the WKB exponent -/

/-- **The WKB exponent is at most the aperture.**  Over any subinterval of the right half band the WKB
integral is bounded by `c (sqrt(1-a²) - sqrt(1-b²))`, hence by `c`. -/
theorem integral_prolateWKB_le {c χ a b : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) (ha0 : 0 ≤ a)
    (ha : -1 < a) (hb : b < 1) (hχ : χ ≤ 0) :
    (∫ t in a..b, prolateWKB c χ t)
      ≤ c * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)) := by
  have hsubIoo : ∀ t ∈ Icc a b, t ∈ Ioo (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hpne : ∀ t ∈ Icc a b, (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro t ht
    have h := hsubIoo t ht
    have h1 : -1 < t := h.1
    have h2 : t < 1 := h.2
    nlinarith
  -- the dominating profile is interval integrable
  have hcont : ContinuousOn (fun t : ℝ => c * t / Real.sqrt (1 - t ^ 2)) (Icc a b) := by
    refine ContinuousOn.div (by fun_prop) (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
      fun t ht => ?_
    have h := hsubIoo t ht
    have hp : 0 < 1 - t ^ 2 := by
      have h1 : -1 < t := h.1
      have h2 : t < 1 := h.2
      nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint2 : IntervalIntegrable (fun t : ℝ => c * t / Real.sqrt (1 - t ^ 2)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hcont.integrableOn_compact isCompact_Icc
  have hint1 : IntervalIntegrable (prolateWKB c χ) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (continuousOn_prolateWKB hpne).integrableOn_compact isCompact_Icc
  -- compare, then evaluate by the fundamental theorem of calculus
  have hcmp : (∫ t in a..b, prolateWKB c χ t)
      ≤ ∫ t in a..b, c * t / Real.sqrt (1 - t ^ 2) := by
    refine intervalIntegral.integral_mono_on hab hint1 hint2 fun t ht => ?_
    exact prolateWKB_le_of_nonpos hc (hsubIoo t ht) (le_trans ha0 ht.1) hχ
  have hFTC : (∫ t in a..b, c * t / Real.sqrt (1 - t ^ 2))
      = -c * Real.sqrt (1 - b ^ 2) - -c * Real.sqrt (1 - a ^ 2) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -c * Real.sqrt (1 - t ^ 2)) (fun t ht => ?_) hint2
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_negMulSqrt (hsubIoo t ht)
  rw [hFTC] at hcmp
  calc (∫ t in a..b, prolateWKB c χ t)
      ≤ -c * Real.sqrt (1 - b ^ 2) - -c * Real.sqrt (1 - a ^ 2) := hcmp
    _ = c * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)) := by ring

theorem integral_prolateWKB_le_aperture {c χ a b : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) (ha0 : 0 ≤ a)
    (ha : -1 < a) (hb : b < 1) (hχ : χ ≤ 0) :
    (∫ t in a..b, prolateWKB c χ t) ≤ c := by
  have hmain := integral_prolateWKB_le hc hab ha0 ha hb hχ
  have h1 : Real.sqrt (1 - a ^ 2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - a ^ 2 ≤ 1 by nlinarith [sq_nonneg a])
    rwa [Real.sqrt_one] at h
  have h2 : 0 ≤ Real.sqrt (1 - b ^ 2) := Real.sqrt_nonneg _
  have hstep : c * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)) ≤ c * 1 := by
    refine mul_le_mul_of_nonneg_left ?_ hc
    linarith
  linarith [hmain, hstep]

/-! ## The explicit endpoint bound at the correct rate -/

/-- **The explicit outer-band endpoint bound.**  On the outer band a positive solution of the prolate
equation loses at most the factor `e^(-c)`. -/
theorem exp_neg_aperture_le_endpoint {c χ a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hc : 0 ≤ c) (hab : a ≤ b) (ha0 : (0 : ℝ) ≤ a) (ha : -1 < a) (hb : b < 1) (hχ : χ ≤ 0)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a b, 0 < χ + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a b, c ^ 2 * (1 - 2 * y ^ 2) ≤ χ)
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c χ b) :
    Φ a * Real.exp (-c) ≤ Φ b := by
  have hmain := le_endpoint_prolateWKB hsm heig hab ha0 ha hb hpos hQ houter hinit
  have hbound := integral_prolateWKB_le_aperture (χ := χ) hc hab ha0 ha hb hχ
  have hexp : Real.exp (-c) ≤ Real.exp (-∫ t in a..b, prolateWKB c χ t) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hΦa : 0 < Φ a := hpos a (left_mem_Icc.mpr hab)
  calc Φ a * Real.exp (-c) ≤ Φ a * Real.exp (-∫ t in a..b, prolateWKB c χ t) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hΦa)
    _ ≤ Φ b := hmain

end GaloisForLFunctions.RHTower

end
