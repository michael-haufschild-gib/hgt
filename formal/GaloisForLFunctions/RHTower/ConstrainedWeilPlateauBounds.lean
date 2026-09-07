import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauProfile

/-!
# Bounds for the plateau coefficients

One integration by parts on the edge gives the exact representations

`κ(c) = (1/c) ∫_0^{1/4} τ'(4s)·4 · e^{−cs} ds`,  `ρ(c) = −(1/c) ∫_0^{1/4} τ'(4u)·4 · e^{cu} du`

for `c ≠ 0`, where `τ'(4s)·4` is the derivative of the edge `s ↦ τ(4s)`.  Since the edge derivative is
bounded on `[0, 1/4]`, both coefficients satisfy `‖κ(c)‖, ‖ρ(c)‖ ≤ M e^{|Re c|/4} / ‖c‖` with a single
constant `M`.  For real positive `c = b` the coefficient `κ(b)` is real and at least `e^{−b/4}/b`.
-/

open MeasureTheory Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-! ## Derivatives of the edge -/

theorem plateauEdge_differentiable : Differentiable ℝ plateauEdge :=
  plateauEdge_contDiff.differentiable (by simp)

theorem plateauEdge_hasDerivAt (s : ℝ) :
    HasDerivAt plateauEdge (deriv plateauEdge s) s :=
  (plateauEdge_differentiable s).hasDerivAt

theorem plateauEdge_deriv_continuous : Continuous (deriv plateauEdge) :=
  plateauEdge_contDiff.continuous_deriv (by exact_mod_cast le_top)

theorem hasDerivAt_ofReal_plateauEdge (s : ℝ) :
    HasDerivAt (fun y : ℝ => ((plateauEdge y : ℝ) : ℂ)) ((deriv plateauEdge s : ℝ) : ℂ) s :=
  (plateauEdge_hasDerivAt s).ofReal_comp

theorem hasDerivAt_cexp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (s : ℂ)) * c) s := by
  have hz : HasDerivAt (fun z : ℂ => c * z) c (s : ℂ) := by
    simpa using (hasDerivAt_id (s : ℂ)).const_mul c
  exact ((Complex.hasDerivAt_exp _).comp (s : ℂ) hz).comp_ofReal

theorem hasDerivAt_cexp_neg_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(c * (y : ℂ))))
      (Complex.exp (-(c * (s : ℂ))) * (-c)) s := by
  have h := hasDerivAt_cexp_mul (-c) s
  simp only [neg_mul] at h
  exact h

/-! ## Integration by parts -/

/-- `λ₁(c) = −e^{−c/4}/c + (1/c) ∫_0^{1/4} (edge)'(s) e^{−cs} ds`. -/
theorem plateauLambda₁_eq {c : ℂ} (hc : c ≠ 0) :
    plateauLambda₁ c
      = -(Complex.exp (-(c / 4)) / c)
        + (1 / c) * ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
            ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ))) := by
  have hu : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => ((plateauEdge y : ℝ) : ℂ)) ((deriv plateauEdge s : ℝ) : ℂ) s :=
    fun s _ => hasDerivAt_ofReal_plateauEdge s
  have hv : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 / c) * Complex.exp (-(c * (y : ℂ))))
        (Complex.exp (-(c * (s : ℂ)))) s := by
    intro s _
    have h := (hasDerivAt_cexp_neg_mul c s).const_mul (-(1 / c))
    refine h.congr_deriv ?_
    field_simp
  have hu' : IntervalIntegrable (fun s : ℝ => ((deriv plateauEdge s : ℝ) : ℂ)) volume 0 (1 / 4) :=
    (Complex.continuous_ofReal.comp plateauEdge_deriv_continuous).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s : ℝ => Complex.exp (-(c * (s : ℂ)))) volume 0 (1 / 4) :=
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).intervalIntegrable
      _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hL : plateauLambda₁ c
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ))) := by
    unfold plateauLambda₁
    refine integral_congr fun s _ => ?_
    ring
  rw [hL, hibp, plateauEdge_eq_one (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4),
    plateauEdge_eq_zero (le_refl (0 : ℝ))]
  push_cast
  have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
      ((deriv plateauEdge s : ℝ) : ℂ) * (-(1 / c) * Complex.exp (-(c * (s : ℂ))))
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          -(1 / c) * (((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ)))) := by
    refine integral_congr fun s _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have e : Complex.exp (-(c * (1 / 4 : ℂ))) = Complex.exp (-(c / 4)) := by
    congr 1
    ring
  rw [e]
  ring

/-- `κ(c) = (1/c) ∫_0^{1/4} (edge)'(s) e^{−cs} ds`. -/
theorem plateauKappa_eq {c : ℂ} (hc : c ≠ 0) :
    plateauKappa c
      = (1 / c) * ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ))) := by
  unfold plateauKappa
  rw [plateauLambda₁_eq hc]
  ring

/-- `λ₀(c) = e^{c/4}/c − (1/c) ∫_0^{1/4} (edge)'(u) e^{cu} du`. -/
theorem plateauLambda₀_eq {c : ℂ} (hc : c ≠ 0) :
    plateauLambda₀ c
      = Complex.exp (c / 4) / c
        - (1 / c) * ∫ u in (0 : ℝ)..(1 / 4 : ℝ),
            ((deriv plateauEdge u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
  have hu : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => ((plateauEdge y : ℝ) : ℂ)) ((deriv plateauEdge s : ℝ) : ℂ) s :=
    fun s _ => hasDerivAt_ofReal_plateauEdge s
  have hv : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => (1 / c) * Complex.exp (c * (y : ℂ)))
        (Complex.exp (c * (s : ℂ))) s := by
    intro s _
    have h := (hasDerivAt_cexp_mul c s).const_mul (1 / c)
    refine h.congr_deriv ?_
    field_simp
  have hu' : IntervalIntegrable (fun s : ℝ => ((deriv plateauEdge s : ℝ) : ℂ)) volume 0 (1 / 4) :=
    (Complex.continuous_ofReal.comp plateauEdge_deriv_continuous).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s : ℝ => Complex.exp (c * (s : ℂ))) volume 0 (1 / 4) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable
      _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hL : plateauLambda₀ c
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ)) := by
    unfold plateauLambda₀
    refine integral_congr fun s _ => ?_
    ring
  rw [hL, hibp, plateauEdge_eq_one (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4),
    plateauEdge_eq_zero (le_refl (0 : ℝ))]
  push_cast
  have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
      ((deriv plateauEdge s : ℝ) : ℂ) * ((1 / c) * Complex.exp (c * (s : ℂ)))
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          (1 / c) * (((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))) := by
    refine integral_congr fun s _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have e : Complex.exp (c * (1 / 4 : ℂ)) = Complex.exp (c / 4) := by
    congr 1
    ring
  rw [e]
  ring

/-- `ρ(c) = −(1/c) ∫_0^{1/4} (edge)'(u) e^{cu} du`. -/
theorem plateauRho_eq {c : ℂ} (hc : c ≠ 0) :
    plateauRho c
      = -(1 / c) * ∫ u in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv plateauEdge u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
  unfold plateauRho
  rw [plateauLambda₀_eq hc]
  ring

/-! ## The coefficient bounds -/

theorem exists_plateauEdge_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) (1 / 4 : ℝ), |deriv plateauEdge s| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn
    plateauEdge_deriv_continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s hs => ?_⟩
  have := hM s hs
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem norm_cexp_mul_le_exp_abs_re {c : ℂ} {s : ℝ} (hs : |s| ≤ 1 / 4) :
    ‖Complex.exp (c * (s : ℂ))‖ ≤ Real.exp (|c.re| / 4) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc c.re * s ≤ |c.re * s| := le_abs_self _
    _ = |c.re| * |s| := abs_mul _ _
    _ ≤ |c.re| * (1 / 4) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = |c.re| / 4 := by ring

theorem norm_integral_edgeDeriv_cexp_le {M₀ : ℝ} (hM : ∀ s ∈ Icc (0 : ℝ) (1 / 4 : ℝ),
    |deriv plateauEdge s| ≤ M₀) (c : ℂ) :
    ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖
      ≤ M₀ * Real.exp (|c.re| / 4) / 4 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1 / 4) (C := M₀ * Real.exp (|c.re| / 4))
    (f := fun s : ℝ => ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))) ?_
  · have e : |(1 / 4 : ℝ) - 0| = 1 / 4 := by norm_num
    rw [e] at h
    linarith
  · intro s hs
    rw [uIoc_of_le (by norm_num), mem_Ioc] at hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |deriv plateauEdge s| ≤ M₀ := hM s ⟨hs.1.le, hs.2⟩
    have h2 : ‖Complex.exp (c * (s : ℂ))‖ ≤ Real.exp (|c.re| / 4) :=
      norm_cexp_mul_le_exp_abs_re (by rw [abs_of_pos hs.1]; exact hs.2)
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (abs_nonneg _) h1)

/-- **Coefficient bounds.**  There is `M ≥ 0` with `‖κ(c)‖, ‖ρ(c)‖ ≤ M e^{|Re c|/4} / ‖c‖` for all
`c ≠ 0`. -/
theorem exists_plateau_coeff_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c ≠ 0 →
      ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ := by
  obtain ⟨M₀, hM₀, hM⟩ := exists_plateauEdge_deriv_bound
  refine ⟨M₀ / 4, by positivity, fun c hc => ?_⟩
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  constructor
  · rw [plateauKappa_eq hc, norm_mul, norm_div, norm_one]
    have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
        ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ)))
        = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
            ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-c * (s : ℂ)) := by
      refine integral_congr fun s _ => ?_
      rw [neg_mul]
    rw [hcongr]
    have h := norm_integral_edgeDeriv_cexp_le hM (-c)
    rw [Complex.neg_re, abs_neg] at h
    calc 1 / ‖c‖ * ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-c * (s : ℂ))‖
        ≤ 1 / ‖c‖ * (M₀ * Real.exp (|c.re| / 4) / 4) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M₀ / 4 * Real.exp (|c.re| / 4) / ‖c‖ := by ring
  · rw [plateauRho_eq hc, norm_mul, norm_neg, norm_div, norm_one]
    have h := norm_integral_edgeDeriv_cexp_le hM c
    calc 1 / ‖c‖ * ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖
        ≤ 1 / ‖c‖ * (M₀ * Real.exp (|c.re| / 4) / 4) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M₀ / 4 * Real.exp (|c.re| / 4) / ‖c‖ := by ring

/-! ## Real positive frequency -/

/-- For real `b`, `κ(b)` is real and at least `e^{−b/4}/b`. -/
theorem plateauKappa_ofReal (b : ℝ) :
    (plateauKappa (b : ℂ)).im = 0 ∧ Real.exp (-b / 4) / b ≤ (plateauKappa (b : ℂ)).re := by
  have hL : plateauLambda₁ (b : ℂ)
      = ((∫ s in (0 : ℝ)..(1 / 4 : ℝ), Real.exp (-(b * s)) * plateauEdge s : ℝ) : ℂ) := by
    unfold plateauLambda₁
    rw [← intervalIntegral.integral_ofReal]
    refine integral_congr fun s _ => ?_
    push_cast
    ring_nf
  have hpos : 0 ≤ ∫ s in (0 : ℝ)..(1 / 4 : ℝ), Real.exp (-(b * s)) * plateauEdge s :=
    intervalIntegral.integral_nonneg (by norm_num)
      fun s _ => mul_nonneg (Real.exp_pos _).le (plateauEdge_nonneg s)
  have hκ : plateauKappa (b : ℂ)
      = (((∫ s in (0 : ℝ)..(1 / 4 : ℝ), Real.exp (-(b * s)) * plateauEdge s)
          + Real.exp (-b / 4) / b : ℝ) : ℂ) := by
    unfold plateauKappa
    rw [hL]
    push_cast
    ring_nf
  rw [hκ]
  constructor
  · exact Complex.ofReal_im _
  · rw [Complex.ofReal_re]
    linarith

end

end RHTower
