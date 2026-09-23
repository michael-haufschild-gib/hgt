import GaloisForLFunctions.RHTower.ExteriorProfileBounds

/-!
# The exterior primitive with a free left endpoint

The exterior estimate is stated over `[2, X]`, which fixes the gain at `1/(2c)`.  Over `[L, X]`
with `L > 0` the same integration by parts gives `3C/(Lc)`: two boundary terms `C/L` and a tail
`∫_L^X C/t² = C/L - C/X`.

The free endpoint is what converts a dilation into a decay in the channel index.  Substituting
`y = k t` in `∫_1^X f(k t) dt` gives `k⁻¹ ∫_k^{kX} f(y) dy`, and the estimate over `[k, kX]`
contributes a second factor `k⁻¹` through its left endpoint.  With the endpoint fixed at `2` only
one of the two factors is visible.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace RHTower

theorem integral_inv_sq_le_left {L X : ℝ} (hL : 0 < L) (hLX : L ≤ X) :
    (∫ x in L..X, (x ^ (2 : ℕ))⁻¹) ≤ 1 / L := by
  have hpos : ∀ x ∈ Set.uIcc L X, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    exact ne_of_gt (lt_of_lt_of_le hL hx.1)
  have hderiv : ∀ x ∈ Set.uIcc L X, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ (2 : ℕ))⁻¹) x := by
    intro x hx
    have h := (hasDerivAt_inv (hpos x hx)).neg
    rwa [neg_neg] at h
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ (2 : ℕ))⁻¹) volume L X := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuousOn_pow 2) fun x hx => ?_
    exact pow_ne_zero 2 (hpos x hx)
  have hftc : (∫ x in L..X, (x ^ (2 : ℕ))⁻¹) = -X⁻¹ - -L⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le hL hLX
  have hXinv : 0 < X⁻¹ := inv_pos.mpr hXpos
  rw [hftc, one_div]
  linarith

/-- **Nonstationary phase over `[L, X]`.** -/
theorem norm_integral_cexp_le_of_decay_left {L X K : ℝ} (hL : 0 < L) (hLX : L ≤ X) (hK : 0 ≤ K)
    {φ φ' : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ Set.uIcc L X, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ Set.uIcc L X, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (Set.uIcc L X))
    (hAc : ContinuousOn A (Set.uIcc L X))
    (hrel : ∀ x ∈ Set.uIcc L X, B x * (Complex.I * (φ' x : ℂ)) = A x)
    (hBdecay : ∀ x ∈ Set.uIcc L X, ‖B x‖ ≤ K / x)
    (hB'decay : ∀ x ∈ Set.uIcc L X, ‖B' x‖ ≤ K * (x ^ (2 : ℕ))⁻¹) :
    ‖∫ t in L..X, A t * Complex.exp (Complex.I * φ t)‖ ≤ 3 * K / L := by
  have hmain := norm_integral_cexp_le_of_antiderivative hLX hφ hB hB'c hAc hrel
  have hbX : ‖B X‖ ≤ K / L := by
    refine le_trans (hBdecay X Set.right_mem_uIcc) ?_
    exact div_le_div_of_nonneg_left hK hL hLX
  have hbL : ‖B L‖ ≤ K / L := hBdecay L Set.left_mem_uIcc
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖B' t‖) volume L X := hB'c.norm.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => K * (t ^ (2 : ℕ))⁻¹) volume L X := by
    refine (ContinuousOn.mul continuousOn_const ?_).intervalIntegrable
    refine ContinuousOn.inv₀ (continuousOn_pow 2) fun x hx => ?_
    rw [Set.uIcc_of_le hLX] at hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hL hx.1))
  have htail : (∫ t in L..X, ‖B' t‖) ≤ K / L := by
    have hmono : (∫ t in L..X, ‖B' t‖) ≤ ∫ t in L..X, K * (t ^ (2 : ℕ))⁻¹ := by
      refine intervalIntegral.integral_mono_on hLX hi1 hi2 fun t ht => ?_
      exact hB'decay t (Set.uIcc_of_le hLX ▸ ht)
    have hconst : (∫ t in L..X, K * (t ^ (2 : ℕ))⁻¹) = K * ∫ t in L..X, (t ^ (2 : ℕ))⁻¹ :=
      intervalIntegral.integral_const_mul K _
    have hbase := integral_inv_sq_le_left hL hLX
    have hstep : K * (∫ t in L..X, (t ^ (2 : ℕ))⁻¹) ≤ K * (1 / L) :=
      mul_le_mul_of_nonneg_left hbase hK
    rw [hconst] at hmono
    have hval : K * (1 / L) = K / L := by ring
    linarith [hmono, hstep, hval]
  have hsum : K / L + K / L + K / L = 3 * K / L := by ring
  linarith [hmain, hbX, hbL, htail, hsum]

/-- **The exterior primitive with a scaled phase over `[L, X]`.** -/
theorem norm_integral_cexp_le_of_profile_left {L X C c eps : ℝ} (hL : 0 < L) (hLX : L ≤ X)
    (hC : 0 ≤ C) (hc : 0 < c) (heps : |eps| = 1)
    {ξ ξ' : ℝ → ℝ} {A P P' : ℝ → ℂ}
    (hξ : ∀ x ∈ Set.uIcc L X, HasDerivAt ξ (ξ' x) x)
    (hP : ∀ x ∈ Set.uIcc L X, HasDerivAt P (P' x) x)
    (hP'c : ContinuousOn P' (Set.uIcc L X))
    (hAc : ContinuousOn A (Set.uIcc L X))
    (hrel : ∀ x ∈ Set.uIcc L X, P x * (ξ' x : ℂ) = A x)
    (hPd : ∀ x ∈ Set.uIcc L X, ‖P x‖ ≤ C / x)
    (hP'd : ∀ x ∈ Set.uIcc L X, ‖P' x‖ ≤ C * (x ^ (2 : ℕ))⁻¹) :
    ‖∫ t in L..X, A t * Complex.exp (Complex.I * ((eps * c * ξ t : ℝ) : ℂ))‖
      ≤ 3 * C / (L * c) := by
  have hepsne : eps ≠ 0 := by
    intro h
    rw [h, abs_zero] at heps
    exact absurd heps (by norm_num)
  have hscale : |eps * c| = c := by
    rw [abs_mul, heps, one_mul, abs_of_pos hc]
  have hnormden : ‖Complex.I * ((eps * c : ℝ) : ℂ)‖ = c := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hscale]
  set d : ℂ := Complex.I * ((eps * c : ℝ) : ℂ) with hd
  have hφ : ∀ x ∈ Set.uIcc L X,
      HasDerivAt (fun s : ℝ => eps * c * ξ s) (eps * c * ξ' x) x :=
    fun x hx => (hξ x hx).const_mul (eps * c)
  have hB : ∀ x ∈ Set.uIcc L X, HasDerivAt (fun s : ℝ => P s / d) (P' x / d) x :=
    fun x hx => (hP x hx).div_const d
  have hB'c : ContinuousOn (fun x : ℝ => P' x / d) (Set.uIcc L X) := hP'c.div_const d
  have hrel' : ∀ x ∈ Set.uIcc L X,
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
  have hxpos : ∀ x ∈ Set.uIcc L X, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    linarith [hx.1, hL]
  have hBd : ∀ x ∈ Set.uIcc L X, ‖P x / d‖ ≤ (C / c) / x := by
    intro x hx
    have hx0 := hxpos x hx
    rw [norm_div, hd, hnormden]
    calc ‖P x‖ / c ≤ (C / x) / c := by gcongr; exact hPd x hx
      _ = (C / c) / x := by ring
  have hB'd : ∀ x ∈ Set.uIcc L X, ‖P' x / d‖ ≤ (C / c) * (x ^ (2 : ℕ))⁻¹ := by
    intro x hx
    have hx0 := hxpos x hx
    rw [norm_div, hd, hnormden]
    calc ‖P' x‖ / c ≤ (C * (x ^ (2 : ℕ))⁻¹) / c := by gcongr; exact hP'd x hx
      _ = (C / c) * (x ^ (2 : ℕ))⁻¹ := by ring
  have hmain := norm_integral_cexp_le_of_decay_left (K := C / c) hL hLX hK hφ hB hB'c hAc
    hrel' hBd hB'd
  have hval : 3 * (C / c) / L = 3 * C / (L * c) := by
    field_simp
  rwa [hval] at hmain

/-- The pointwise derivative bound, valid from `x = 1` rather than `x = 2`.  The tail term
`Ca Cr/x³` is absorbed into `Ca Cr/x²` instead of into half of it, so the constant is
`3Ca/2 + Ca Cr` rather than `3Ca/2 + Ca Cr/2`. -/
theorem norm_deriv_exteriorProfile_left {x Ca Cr : ℝ} (hx1 : 1 ≤ x)
    (hCa : 0 ≤ Ca) (hCr : 0 ≤ Cr) {ξ' ρ : ℝ → ℝ} {a a' : ℝ → ℂ}
    (hξ : 1 ≤ ξ' x) (hρ : |ρ x| ≤ Cr / x ^ (2 : ℕ))
    (ha : ‖a x‖ ≤ Ca / Real.sqrt x) (ha' : ‖a' x‖ ≤ Ca / (x * Real.sqrt x)) :
    ‖a' x * (exteriorWeight ξ' x : ℂ)
        + a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ (3 * Ca / 2 + Ca * Cr) / x ^ (2 : ℕ) := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hw := abs_exteriorWeight_le hx hξ
  have hw' := abs_deriv_exteriorWeight_le hx hξ hρ
  have hterm1 : ‖a' x * (exteriorWeight ξ' x : ℂ)‖ ≤ Ca / x ^ (2 : ℕ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a' x‖ * |exteriorWeight ξ' x| ≤ (Ca / (x * Real.sqrt x)) * (Real.sqrt x)⁻¹ :=
          mul_le_mul ha' hw (abs_nonneg _) (le_trans (norm_nonneg _) ha')
      _ = Ca / x ^ (2 : ℕ) := by
          field_simp
          rw [Real.sq_sqrt hx.le]
  have hterm2 : ‖a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹
        + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ Ca / (2 * x ^ (2 : ℕ)) + Ca * Cr / x ^ (3 : ℕ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbase : ‖a x‖ * |(-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x)|
        ≤ (Ca / Real.sqrt x) * ((2 * x * Real.sqrt x)⁻¹ + (Real.sqrt x)⁻¹ * (Cr / x ^ (2 : ℕ))) :=
      mul_le_mul ha hw' (abs_nonneg _) (le_trans (norm_nonneg _) ha)
    refine le_trans hbase (le_of_eq ?_)
    field_simp
    rw [Real.sq_sqrt hx.le]
  have htail : Ca * Cr / x ^ (3 : ℕ) ≤ Ca * Cr / x ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hCa hCr) (sq_nonneg x), hx.le, hx1]
  have hsum : Ca / x ^ (2 : ℕ) + (Ca / (2 * x ^ (2 : ℕ)) + Ca * Cr / x ^ (2 : ℕ))
      = (3 * Ca / 2 + Ca * Cr) / x ^ (2 : ℕ) := by
    field_simp
    ring
  calc ‖a' x * (exteriorWeight ξ' x : ℂ)
        + a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ ‖a' x * (exteriorWeight ξ' x : ℂ)‖
        + ‖a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ (3 * Ca / 2 + Ca * Cr) / x ^ (2 : ℕ) := by linarith [hterm1, hterm2, htail, hsum]

/-- **The exterior estimate over `[L, X]` with `L ≥ 1`.** -/
theorem norm_integral_exterior_left {L X Ca Cr c eps : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X)
    (hCa : 0 ≤ Ca) (hCr : 0 ≤ Cr) (hc : 0 < c) (heps : |eps| = 1)
    {ξ ξ' ρ : ℝ → ℝ} {a a' : ℝ → ℂ}
    (hξ : ∀ x ∈ Set.uIcc L X, HasDerivAt ξ (ξ' x) x)
    (hρ : ∀ x ∈ Set.uIcc L X, HasDerivAt (fun s : ℝ => (ξ' s)⁻¹) (ρ x) x)
    (ha : ∀ x ∈ Set.uIcc L X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc L X))
    (ha'c : ContinuousOn a' (Set.uIcc L X))
    (hξ'c : ContinuousOn ξ' (Set.uIcc L X))
    (hρc : ContinuousOn ρ (Set.uIcc L X))
    (hspeed : ∀ x ∈ Set.uIcc L X, 1 ≤ ξ' x)
    (haB : ∀ x ∈ Set.uIcc L X, ‖a x‖ ≤ Ca / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc L X, ‖a' x‖ ≤ Ca / (x * Real.sqrt x))
    (hρB : ∀ x ∈ Set.uIcc L X, |ρ x| ≤ Cr / x ^ (2 : ℕ)) :
    ‖∫ t in L..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * c * ξ t : ℝ) : ℂ))‖
      ≤ 3 * (Ca * (3 / 2 + Cr)) / (L * c) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hxpos : ∀ x ∈ Set.uIcc L X, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    linarith [hx.1, hL0]
  have hx1 : ∀ x ∈ Set.uIcc L X, (1 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    linarith [hx.1, hL]
  have hξ'ne : ∀ x ∈ Set.uIcc L X, ξ' x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hspeed x hx))
  have hsqrtne : ∀ x ∈ Set.uIcc L X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (hxpos x hx))
  set C' : ℝ := Ca * (3 / 2 + Cr) with hC'def
  have hC'0 : 0 ≤ C' := mul_nonneg hCa (by linarith)
  set W' : ℝ → ℝ :=
    fun x => -(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x with hW'def
  have hPderiv : ∀ x ∈ Set.uIcc L X,
      HasDerivAt (fun s : ℝ => a s * ((exteriorWeight ξ' s : ℝ) : ℂ))
        (a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ)) x := by
    intro x hx
    exact (ha x hx).mul ((hasDerivAt_exteriorWeight (hxpos x hx) (hρ x hx)).ofReal_comp)
  have hsqc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.uIcc L X) :=
    (Real.continuous_sqrt.continuousOn).inv₀ hsqrtne
  have hWc : ContinuousOn (exteriorWeight ξ') (Set.uIcc L X) :=
    hsqc.mul (hξ'c.inv₀ hξ'ne)
  have hW'c : ContinuousOn W' (Set.uIcc L X) := by
    refine ContinuousOn.add ?_ (hsqc.mul hρc)
    refine ContinuousOn.mul (ContinuousOn.neg ?_) (hξ'c.inv₀ hξ'ne)
    refine ContinuousOn.inv₀ ((continuousOn_const.mul continuousOn_id).mul
      Real.continuous_sqrt.continuousOn) fun x hx => ?_
    have hp := hxpos x hx
    have hs := Real.sqrt_pos.mpr hp
    positivity
  have hP'c : ContinuousOn
      (fun x : ℝ => a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ))
      (Set.uIcc L X) :=
    (ha'c.mul (Complex.continuous_ofReal.comp_continuousOn hWc)).add
      (hac.mul (Complex.continuous_ofReal.comp_continuousOn hW'c))
  have hAc : ContinuousOn (fun t : ℝ => a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) (Set.uIcc L X) :=
    hac.mul (Complex.continuous_ofReal.comp_continuousOn hsqc)
  have hrel : ∀ x ∈ Set.uIcc L X,
      (a x * ((exteriorWeight ξ' x : ℝ) : ℂ)) * ((ξ' x : ℝ) : ℂ)
        = a x * (((Real.sqrt x)⁻¹ : ℝ) : ℂ) := by
    intro x hx
    have hne : ((ξ' x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ'ne x hx
    rw [exteriorWeight]
    push_cast
    field_simp
  have hPd : ∀ x ∈ Set.uIcc L X,
      ‖a x * ((exteriorWeight ξ' x : ℝ) : ℂ)‖ ≤ C' / x := by
    intro x hx
    refine le_trans (norm_exteriorProfile_le (hxpos x hx) (hspeed x hx) (haB x hx)) ?_
    have hx0 := hxpos x hx
    have hCC' : Ca ≤ C' := by
      rw [hC'def]
      nlinarith [hCa, hCr]
    gcongr
  have hP'd : ∀ x ∈ Set.uIcc L X,
      ‖a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ)‖
        ≤ C' * (x ^ (2 : ℕ))⁻¹ := by
    intro x hx
    have h := norm_deriv_exteriorProfile_left (hx1 x hx) hCa hCr (hspeed x hx)
      (hρB x hx) (haB x hx) (ha'B x hx)
    rw [hW'def]
    have hval : (3 * Ca / 2 + Ca * Cr) / x ^ (2 : ℕ) = C' * (x ^ (2 : ℕ))⁻¹ := by
      rw [hC'def, div_eq_mul_inv]
      ring
    rw [hval] at h
    exact h
  exact norm_integral_cexp_le_of_profile_left hL0 hLX hC'0 hc heps hξ hPderiv hP'c hAc hrel
    hPd hP'd


end RHTower
