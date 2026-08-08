import GaloisForLFunctions.RHTower.VanDerCorputIBP

/-!
# The exterior oscillatory primitive

An oscillatory integral over an unbounded range is bounded uniformly in the endpoint as soon as the
antiderivative datum of the integration by parts decays like `1/x` and its derivative like `1/x²`.
The boundary terms are then bounded by the value at the left endpoint and the remaining integral by
the convergent tail `∫ x⁻² `, both independently of the right endpoint.

This is the exterior counterpart of the bounded-radius primitive: there the uniformity came from the
range being bounded, here it comes from the decay of the amplitude over frequency.
-/

noncomputable section

open MeasureTheory intervalIntegral Complex Set

namespace RHTower

/-- The convergent inverse-square tail from `2` is at most `1/2`. -/
theorem integral_inv_sq_le {X : ℝ} (hX : 2 ≤ X) :
    (∫ x in (2 : ℝ)..X, (x ^ 2)⁻¹) ≤ 1 / 2 := by
  have hpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have h := (hasDerivAt_inv (hpos x hx)).neg
    rwa [neg_neg] at h
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume 2 X := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_pow 2) fun x hx => ?_
    exact pow_ne_zero 2 (hpos x hx)
  have hftc : (∫ x in (2 : ℝ)..X, (x ^ 2)⁻¹) = -X⁻¹ - -(2 : ℝ)⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hXinv : 0 < X⁻¹ := inv_pos.mpr hXpos
  rw [hftc]
  norm_num
  linarith

/-- **The exterior primitive is uniformly bounded.**  With an antiderivative datum decaying like
`K/x` and a derivative decaying like `K/x²`, the oscillatory integral from `2` to any endpoint is
bounded by `3K/2`, with no dependence on the endpoint. -/
theorem norm_integral_cexp_le_of_decay
    {X K : ℝ} (hX : 2 ≤ X) (hK : 0 ≤ K) {φ φ' : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (Set.uIcc (2 : ℝ) X))
    (hAc : ContinuousOn A (Set.uIcc (2 : ℝ) X))
    (hrel : ∀ x ∈ Set.uIcc (2 : ℝ) X, B x * (Complex.I * (φ' x : ℂ)) = A x)
    (hBdecay : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖B x‖ ≤ K / x)
    (hB'decay : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖B' x‖ ≤ K * (x ^ 2)⁻¹) :
    ‖∫ t in (2 : ℝ)..X, A t * Complex.exp (Complex.I * φ t)‖ ≤ 3 * K / 2 := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hmain := norm_integral_cexp_le_of_antiderivative hX hφ hB hB'c hAc hrel
  -- the boundary terms
  have hbX : ‖B X‖ ≤ K / 2 := by
    refine le_trans (hBdecay X Set.right_mem_uIcc) ?_
    exact div_le_div_of_nonneg_left hK (by norm_num) hX
  have hb2 : ‖B 2‖ ≤ K / 2 := hBdecay 2 Set.left_mem_uIcc
  -- the remaining integral
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖B' t‖) volume 2 X := hB'c.norm.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => K * (t ^ 2)⁻¹) volume 2 X := by
    refine (ContinuousOn.mul continuousOn_const ?_).intervalIntegrable
    refine ContinuousOn.inv₀ (continuousOn_pow 2) fun x hx => ?_
    rw [Set.uIcc_of_le hX] at hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1))
  have htail : (∫ t in (2 : ℝ)..X, ‖B' t‖) ≤ K / 2 := by
    have hmono : (∫ t in (2 : ℝ)..X, ‖B' t‖) ≤ ∫ t in (2 : ℝ)..X, K * (t ^ 2)⁻¹ := by
      refine intervalIntegral.integral_mono_on hX hi1 hi2 fun t ht => ?_
      exact hB'decay t (Set.uIcc_of_le hX ▸ ht)
    have hconst : (∫ t in (2 : ℝ)..X, K * (t ^ 2)⁻¹) = K * ∫ t in (2 : ℝ)..X, (t ^ 2)⁻¹ :=
      intervalIntegral.integral_const_mul K _
    have hbase := integral_inv_sq_le hX
    have : K * (∫ t in (2 : ℝ)..X, (t ^ 2)⁻¹) ≤ K * (1 / 2) :=
      mul_le_mul_of_nonneg_left hbase hK
    rw [hconst] at hmono
    linarith
  linarith [hmain, hbX, hb2, htail]

/-- **The exterior primitive with a scaled phase.**  If the profile `A/ξ'` and its derivative decay
like `C/x` and `C/x²`, then the oscillatory integral with phase `± c ξ` is bounded by `3C/(2c)`,
uniformly in the endpoint.  The frequency parameter `c` is gained because the antiderivative datum
is the profile divided by `± i c`. -/
theorem norm_integral_cexp_le_of_profile
    {X C c eps : ℝ} (hX : 2 ≤ X) (hC : 0 ≤ C) (hc : 0 < c) (heps : |eps| = 1)
    {ξ ξ' : ℝ → ℝ} {A P P' : ℝ → ℂ}
    (hξ : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt ξ (ξ' x) x)
    (hP : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt P (P' x) x)
    (hP'c : ContinuousOn P' (Set.uIcc (2 : ℝ) X))
    (hAc : ContinuousOn A (Set.uIcc (2 : ℝ) X))
    (hrel : ∀ x ∈ Set.uIcc (2 : ℝ) X, P x * (ξ' x : ℂ) = A x)
    (hPd : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖P x‖ ≤ C / x)
    (hP'd : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖P' x‖ ≤ C * (x ^ 2)⁻¹) :
    ‖∫ t in (2 : ℝ)..X, A t * Complex.exp (Complex.I * ((eps * c * ξ t : ℝ) : ℂ))‖
      ≤ 3 * C / (2 * c) := by
  have hepsne : eps ≠ 0 := by
    intro h
    rw [h, abs_zero] at heps
    exact absurd heps (by norm_num)
  have hscale : |eps * c| = c := by
    rw [abs_mul, heps, one_mul, abs_of_pos hc]
  have hne : (Complex.I * ((eps * c : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by
      exact_mod_cast (mul_ne_zero hepsne (ne_of_gt hc)))
  have hnormden : ‖Complex.I * ((eps * c : ℝ) : ℂ)‖ = c := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hscale]
  set d : ℂ := Complex.I * ((eps * c : ℝ) : ℂ) with hd
  have hφ : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      HasDerivAt (fun s : ℝ => eps * c * ξ s) (eps * c * ξ' x) x :=
    fun x hx => (hξ x hx).const_mul (eps * c)
  have hB : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt (fun s : ℝ => P s / d) (P' x / d) x :=
    fun x hx => (hP x hx).div_const d
  have hB'c : ContinuousOn (fun x : ℝ => P' x / d) (Set.uIcc (2 : ℝ) X) :=
    hP'c.div_const d
  have hrel' : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      (P x / d) * (Complex.I * ((eps * c * ξ' x : ℝ) : ℂ)) = A x := by
    intro x hx
    have hcast : ((eps * c * ξ' x : ℝ) : ℂ) = ((eps * c : ℝ) : ℂ) * (ξ' x : ℂ) := by
      push_cast
      ring
    have hcne : ((eps * c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero hepsne (ne_of_gt hc)
    rw [hcast, ← hrel x hx, hd]
    field_simp
  have hK : (0 : ℝ) ≤ C / c := by positivity
  have hxpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    linarith [hx.1]
  have hBd : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖P x / d‖ ≤ (C / c) / x := by
    intro x hx
    have hx0 := hxpos x hx
    rw [norm_div, hd, hnormden]
    calc ‖P x‖ / c ≤ (C / x) / c := by gcongr; exact hPd x hx
      _ = (C / c) / x := by ring
  have hB'd : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖P' x / d‖ ≤ (C / c) * (x ^ 2)⁻¹ := by
    intro x hx
    have hx0 := hxpos x hx
    rw [norm_div, hd, hnormden]
    calc ‖P' x‖ / c ≤ (C * (x ^ 2)⁻¹) / c := by gcongr; exact hP'd x hx
      _ = (C / c) * (x ^ 2)⁻¹ := by ring
  have hmain := norm_integral_cexp_le_of_decay (K := C / c) hX hK hφ hB hB'c hAc hrel' hBd hB'd
  have hval : 3 * (C / c) / 2 = 3 * C / (2 * c) := by
    field_simp
  rwa [hval] at hmain


end RHTower
