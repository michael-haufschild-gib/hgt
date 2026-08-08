import GaloisForLFunctions.RHTower.OscillatoryDecayPrimitive

/-!
# The exterior profile of a Liouville–Green amplitude

An exterior Liouville–Green expansion supplies an amplitude `a` with `|a| ≤ C x^{-1/2}` and
`|a'| ≤ C x^{-3/2}`, and a phase whose speed satisfies `ξ' ≥ 1` with the reciprocal speed of
controlled variation, `|(1/ξ')'| ≤ C x^{-2}`.

The oscillatory primitive consumes not the amplitude but the *profile* `a/(√x · ξ')`, the amplitude
of the integrand divided by the phase speed.  This module differentiates that profile and shows it
decays like `1/x` with derivative decaying like `1/x²`, which is exactly the input of the exterior
primitive bound.

Nothing here is asymptotic: the estimates hold at every `x ≥ 2` with explicit constants.
-/

noncomputable section

open Set

namespace RHTower

/-- The derivative of the reciprocal square root. -/
theorem hasDerivAt_inv_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt y)⁻¹) (-(2 * x * Real.sqrt x)⁻¹) x := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have h := hs.inv hne
  have hval : -(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ 2 = -(2 * x * Real.sqrt x)⁻¹ := by
    rw [Real.sq_sqrt hx.le]
    field_simp
  rwa [hval] at h

/-- The exterior weight: reciprocal square root times reciprocal phase speed. -/
def exteriorWeight (ξ' : ℝ → ℝ) (x : ℝ) : ℝ := (Real.sqrt x)⁻¹ * (ξ' x)⁻¹

/-- Its derivative, expressed through the reciprocal-speed derivative. -/
theorem hasDerivAt_exteriorWeight {x : ℝ} (hx : 0 < x) {ξ' ρ : ℝ → ℝ}
    (hρ : HasDerivAt (fun s : ℝ => (ξ' s)⁻¹) (ρ x) x) :
    HasDerivAt (exteriorWeight ξ')
      (-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x) x :=
  (hasDerivAt_inv_sqrt hx).mul hρ

/-- The exterior weight is bounded by the reciprocal square root when the phase speed is at
least one. -/
theorem abs_exteriorWeight_le {x : ℝ} (hx : 0 < x) {ξ' : ℝ → ℝ} (hξ : 1 ≤ ξ' x) :
    |exteriorWeight ξ' x| ≤ (Real.sqrt x)⁻¹ := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hinv : |(ξ' x)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ξ' x)⁻¹)]
    exact inv_le_one_of_one_le₀ hξ
  rw [exteriorWeight, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt x)⁻¹)]
  calc (Real.sqrt x)⁻¹ * |(ξ' x)⁻¹| ≤ (Real.sqrt x)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (Real.sqrt x)⁻¹ := mul_one _

/-- The derivative of the exterior weight is bounded once the reciprocal speed has controlled
variation. -/
theorem abs_deriv_exteriorWeight_le {x C : ℝ} (hx : 0 < x) {ξ' ρ : ℝ → ℝ}
    (hξ : 1 ≤ ξ' x) (hρ : |ρ x| ≤ C / x ^ 2) :
    |(-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x)|
      ≤ (2 * x * Real.sqrt x)⁻¹ + (Real.sqrt x)⁻¹ * (C / x ^ 2) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hinv : |(ξ' x)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ξ' x)⁻¹)]
    exact inv_le_one_of_one_le₀ hξ
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |(-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹)| ≤ (2 * x * Real.sqrt x)⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * x * Real.sqrt x)⁻¹)]
    calc (2 * x * Real.sqrt x)⁻¹ * |(ξ' x)⁻¹| ≤ (2 * x * Real.sqrt x)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 * x * Real.sqrt x)⁻¹ := mul_one _
  have h2 : |(Real.sqrt x)⁻¹ * ρ x| ≤ (Real.sqrt x)⁻¹ * (C / x ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt x)⁻¹)]
    exact mul_le_mul_of_nonneg_left hρ (by positivity)
  linarith

/-- **The exterior profile decays like `1/x`.** -/
theorem norm_exteriorProfile_le {x C : ℝ} (hx : 0 < x) {ξ' : ℝ → ℝ} {a : ℝ → ℂ}
    (hξ : 1 ≤ ξ' x) (ha : ‖a x‖ ≤ C / Real.sqrt x) :
    ‖a x * (exteriorWeight ξ' x : ℂ)‖ ≤ C / x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hw := abs_exteriorWeight_le hx hξ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖a x‖ * |exteriorWeight ξ' x| ≤ (C / Real.sqrt x) * (Real.sqrt x)⁻¹ :=
        mul_le_mul ha hw (abs_nonneg _) (le_trans (norm_nonneg _) ha)
    _ = C / x := by
        field_simp
        rw [Real.sq_sqrt hx.le]

/-- **The derivative of the exterior profile decays like `1/x²`.** -/
theorem norm_deriv_exteriorProfile_le {x C : ℝ} (hx2 : 2 ≤ x) (hC : 0 ≤ C)
    {ξ' ρ : ℝ → ℝ} {a a' : ℝ → ℂ}
    (hξ : 1 ≤ ξ' x) (hρ : |ρ x| ≤ C / x ^ 2)
    (ha : ‖a x‖ ≤ C / Real.sqrt x) (ha' : ‖a' x‖ ≤ C / (x * Real.sqrt x)) :
    ‖a' x * (exteriorWeight ξ' x : ℂ)
        + a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ (3 * C / 2 + C ^ 2 / 2) / x ^ 2 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hw := abs_exteriorWeight_le hx hξ
  have hw' := abs_deriv_exteriorWeight_le hx hξ hρ
  have hterm1 : ‖a' x * (exteriorWeight ξ' x : ℂ)‖ ≤ C / x ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a' x‖ * |exteriorWeight ξ' x| ≤ (C / (x * Real.sqrt x)) * (Real.sqrt x)⁻¹ :=
          mul_le_mul ha' hw (abs_nonneg _) (le_trans (norm_nonneg _) ha')
      _ = C / x ^ 2 := by
          field_simp
          rw [Real.sq_sqrt hx.le]
  have hterm2 : ‖a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹
        + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ C / (2 * x ^ 2) + C ^ 2 / x ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbase : ‖a x‖ * |(-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x)|
        ≤ (C / Real.sqrt x) * ((2 * x * Real.sqrt x)⁻¹ + (Real.sqrt x)⁻¹ * (C / x ^ 2)) :=
      mul_le_mul ha hw' (abs_nonneg _) (le_trans (norm_nonneg _) ha)
    refine le_trans hbase (le_of_eq ?_)
    field_simp
    rw [Real.sq_sqrt hx.le]
  have htail : C ^ 2 / x ^ 3 ≤ C ^ 2 / (2 * x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg x)) (sub_nonneg.mpr hx2)]
  have hsum : C / x ^ 2 + (C / (2 * x ^ 2) + C ^ 2 / (2 * x ^ 2))
      = (3 * C / 2 + C ^ 2 / 2) / x ^ 2 := by
    field_simp
    ring
  calc ‖a' x * (exteriorWeight ξ' x : ℂ)
        + a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖
      ≤ ‖a' x * (exteriorWeight ξ' x : ℂ)‖
        + ‖a x * ((-(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ C / x ^ 2 + (C / (2 * x ^ 2) + C ^ 2 / (2 * x ^ 2)) := by
        linarith [hterm1, hterm2, htail]
    _ = (3 * C / 2 + C ^ 2 / 2) / x ^ 2 := hsum

/-- **The exterior primitive of a Liouville–Green branch.**  Given an amplitude with the decay of an
exterior expansion and a phase whose speed is at least one with reciprocal of controlled variation,
the oscillatory integral over `[2, X]` is bounded by a constant over the frequency, uniformly in the
endpoint. -/
theorem norm_integral_exterior_le
    {X C c eps : ℝ} (hX : 2 ≤ X) (hC : 0 ≤ C) (hc : 0 < c) (heps : |eps| = 1)
    {ξ ξ' ρ : ℝ → ℝ} {a a' : ℝ → ℂ}
    (hξ : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt ξ (ξ' x) x)
    (hρ : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt (fun s : ℝ => (ξ' s)⁻¹) (ρ x) x)
    (ha : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc (2 : ℝ) X))
    (ha'c : ContinuousOn a' (Set.uIcc (2 : ℝ) X))
    (hξ'c : ContinuousOn ξ' (Set.uIcc (2 : ℝ) X))
    (hρc : ContinuousOn ρ (Set.uIcc (2 : ℝ) X))
    (hspeed : ∀ x ∈ Set.uIcc (2 : ℝ) X, 1 ≤ ξ' x)
    (haB : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a x‖ ≤ C / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a' x‖ ≤ C / (x * Real.sqrt x))
    (hρB : ∀ x ∈ Set.uIcc (2 : ℝ) X, |ρ x| ≤ C / x ^ 2) :
    ‖∫ t in (2 : ℝ)..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * c * ξ t : ℝ) : ℂ))‖
      ≤ 3 * (3 * C / 2 + C ^ 2 / 2) / (2 * c) := by
  have hxpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    linarith [hx.1]
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hξ'ne : ∀ x ∈ Set.uIcc (2 : ℝ) X, ξ' x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hspeed x hx))
  have hsqrtne : ∀ x ∈ Set.uIcc (2 : ℝ) X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (hxpos x hx))
  set C' : ℝ := 3 * C / 2 + C ^ 2 / 2 with hC'def
  have hC'0 : 0 ≤ C' := by rw [hC'def]; positivity
  have hCC' : C ≤ C' := by rw [hC'def]; nlinarith [sq_nonneg C]
  -- the profile and its derivative
  set W' : ℝ → ℝ :=
    fun x => -(2 * x * Real.sqrt x)⁻¹ * (ξ' x)⁻¹ + (Real.sqrt x)⁻¹ * ρ x with hW'def
  have hPderiv : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      HasDerivAt (fun s : ℝ => a s * ((exteriorWeight ξ' s : ℝ) : ℂ))
        (a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ)) x := by
    intro x hx
    exact (ha x hx).mul ((hasDerivAt_exteriorWeight (hxpos x hx) (hρ x hx)).ofReal_comp)
  -- continuity of the data
  have hsqc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.uIcc (2 : ℝ) X) :=
    (Real.continuous_sqrt.continuousOn).inv₀ hsqrtne
  have hWc : ContinuousOn (exteriorWeight ξ') (Set.uIcc (2 : ℝ) X) :=
    hsqc.mul (hξ'c.inv₀ hξ'ne)
  have hW'c : ContinuousOn W' (Set.uIcc (2 : ℝ) X) := by
    refine ContinuousOn.add ?_ (hsqc.mul hρc)
    refine ContinuousOn.mul (ContinuousOn.neg ?_) (hξ'c.inv₀ hξ'ne)
    refine ContinuousOn.inv₀ ((continuousOn_const.mul continuousOn_id).mul
      Real.continuous_sqrt.continuousOn) fun x hx => ?_
    have := hxpos x hx
    have hs := Real.sqrt_pos.mpr this
    positivity
  have hP'c : ContinuousOn
      (fun x : ℝ => a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    (ha'c.mul (Complex.continuous_ofReal.comp_continuousOn hWc)).add
      (hac.mul (Complex.continuous_ofReal.comp_continuousOn hW'c))
  have hAc : ContinuousOn (fun t : ℝ => a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    hac.mul (Complex.continuous_ofReal.comp_continuousOn hsqc)
  -- the algebraic relation between profile and amplitude
  have hrel : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      (a x * ((exteriorWeight ξ' x : ℝ) : ℂ)) * ((ξ' x : ℝ) : ℂ)
        = a x * (((Real.sqrt x)⁻¹ : ℝ) : ℂ) := by
    intro x hx
    have hne : ((ξ' x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ'ne x hx
    rw [exteriorWeight]
    push_cast
    field_simp
  -- the two decay bounds
  have hPd : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      ‖a x * ((exteriorWeight ξ' x : ℝ) : ℂ)‖ ≤ C' / x := by
    intro x hx
    refine le_trans (norm_exteriorProfile_le (hxpos x hx) (hspeed x hx) (haB x hx)) ?_
    have hx0 := hxpos x hx
    gcongr
  have hP'd : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      ‖a' x * ((exteriorWeight ξ' x : ℝ) : ℂ) + a x * ((W' x : ℝ) : ℂ)‖ ≤ C' * (x ^ 2)⁻¹ := by
    intro x hx
    have h := norm_deriv_exteriorProfile_le (hx2 x hx) hC (hspeed x hx) (hρB x hx)
      (haB x hx) (ha'B x hx)
    rw [hW'def]
    rw [← hC'def] at h
    rw [div_eq_mul_inv] at h
    exact h
  exact norm_integral_cexp_le_of_profile hX hC'0 hc heps hξ hPderiv hP'c hAc hrel hPd hP'd


end RHTower
