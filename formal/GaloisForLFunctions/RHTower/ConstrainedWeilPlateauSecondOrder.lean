import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauBounds

/-!
# Second-order bounds for the plateau coefficients and derivative bounds for the profile

The edge `s ↦ τ(4s)` is flat at both ends of `[0, 1/4]`: it attains its minimum `0` at `0` and its
maximum `1` at `1/4`, so its derivative vanishes there.  A second integration by parts therefore gives

`κ(c) = (1/c²) ∫_0^{1/4} (edge)''(s) e^{−cs} ds`,  `ρ(c) = (1/c²) ∫_0^{1/4} (edge)''(u) e^{cu} du`,

hence `‖κ(c)‖, ‖ρ(c)‖ ≤ M₂ e^{|Re c|/4}/‖c‖²`.  The edge derivative is bounded on the whole line, so
the plateau profile and its derivative are bounded uniformly in the aperture.
-/

open MeasureTheory Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-! ## The edge is flat at its ends -/

theorem deriv_plateauEdge_zero : deriv plateauEdge 0 = 0 := by
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [plateauEdge_eq_zero (le_refl 0)]
  exact plateauEdge_nonneg s

theorem deriv_plateauEdge_quarter : deriv plateauEdge (1 / 4) = 0 := by
  apply IsLocalMax.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s => ?_
  rw [plateauEdge_eq_one (le_refl _)]
  exact plateauEdge_le_one s

theorem plateauEdge_deriv_deriv_continuous : Continuous (deriv (deriv plateauEdge)) := by
  have := plateauEdge_contDiff.iterate_deriv 2
  simpa [Function.iterate_succ, Function.comp] using this.continuous

theorem plateauEdge_deriv_contDiff : ContDiff ℝ (⊤ : ℕ∞) (deriv plateauEdge) :=
  (contDiff_infty_iff_deriv.mp plateauEdge_contDiff).2

theorem hasDerivAt_deriv_plateauEdge (s : ℝ) :
    HasDerivAt (deriv plateauEdge) (deriv (deriv plateauEdge) s) s :=
  (plateauEdge_deriv_contDiff.differentiable (by simp) s).hasDerivAt

theorem hasDerivAt_ofReal_deriv_plateauEdge (s : ℝ) :
    HasDerivAt (fun y : ℝ => ((deriv plateauEdge y : ℝ) : ℂ))
      ((deriv (deriv plateauEdge) s : ℝ) : ℂ) s :=
  (hasDerivAt_deriv_plateauEdge s).ofReal_comp

/-! ## Second integration by parts -/

/-- `∫_0^{1/4} (edge)'(s) e^{−cs} ds = (1/c) ∫_0^{1/4} (edge)''(s) e^{−cs} ds` for `c ≠ 0`. -/
theorem integral_edgeDeriv_cexp_neg_eq {c : ℂ} (hc : c ≠ 0) :
    ∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ)))
      = (1 / c) * ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ))) := by
  have hu : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => ((deriv plateauEdge y : ℝ) : ℂ))
        ((deriv (deriv plateauEdge) s : ℝ) : ℂ) s :=
    fun s _ => hasDerivAt_ofReal_deriv_plateauEdge s
  have hv : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 / c) * Complex.exp (-(c * (y : ℂ))))
        (Complex.exp (-(c * (s : ℂ)))) s := by
    intro s _
    have h := (hasDerivAt_cexp_neg_mul c s).const_mul (-(1 / c))
    refine h.congr_deriv ?_
    field_simp
  have hu' : IntervalIntegrable (fun s : ℝ => ((deriv (deriv plateauEdge) s : ℝ) : ℂ)) volume 0
      (1 / 4) :=
    (Complex.continuous_ofReal.comp plateauEdge_deriv_deriv_continuous).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s : ℝ => Complex.exp (-(c * (s : ℂ)))) volume 0 (1 / 4) :=
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).intervalIntegrable
      _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [hibp, deriv_plateauEdge_quarter, deriv_plateauEdge_zero]
  push_cast
  have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
      ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * (-(1 / c) * Complex.exp (-(c * (s : ℂ))))
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          -(1 / c) * (((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ)))) := by
    refine integral_congr fun s _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  ring

/-- `∫_0^{1/4} (edge)'(u) e^{cu} du = −(1/c) ∫_0^{1/4} (edge)''(u) e^{cu} du` for `c ≠ 0`. -/
theorem integral_edgeDeriv_cexp_eq {c : ℂ} (hc : c ≠ 0) :
    ∫ u in (0 : ℝ)..(1 / 4 : ℝ), ((deriv plateauEdge u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ))
      = -(1 / c) * ∫ u in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
  have hu : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => ((deriv plateauEdge y : ℝ) : ℂ))
        ((deriv (deriv plateauEdge) s : ℝ) : ℂ) s :=
    fun s _ => hasDerivAt_ofReal_deriv_plateauEdge s
  have hv : ∀ s ∈ uIcc (0 : ℝ) (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => (1 / c) * Complex.exp (c * (y : ℂ)))
        (Complex.exp (c * (s : ℂ))) s := by
    intro s _
    have h := (hasDerivAt_cexp_mul c s).const_mul (1 / c)
    refine h.congr_deriv ?_
    field_simp
  have hu' : IntervalIntegrable (fun s : ℝ => ((deriv (deriv plateauEdge) s : ℝ) : ℂ)) volume 0
      (1 / 4) :=
    (Complex.continuous_ofReal.comp plateauEdge_deriv_deriv_continuous).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s : ℝ => Complex.exp (c * (s : ℂ))) volume 0 (1 / 4) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable
      _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [hibp, deriv_plateauEdge_quarter, deriv_plateauEdge_zero]
  push_cast
  have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
      ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * ((1 / c) * Complex.exp (c * (s : ℂ)))
      = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          (1 / c) * (((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))) := by
    refine integral_congr fun s _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  ring

/-- `κ(c) = (1/c²) ∫_0^{1/4} (edge)''(s) e^{−cs} ds`. -/
theorem plateauKappa_eq₂ {c : ℂ} (hc : c ≠ 0) :
    plateauKappa c
      = (1 / c ^ (2 : ℕ)) * ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ))) := by
  rw [plateauKappa_eq hc, integral_edgeDeriv_cexp_neg_eq hc]
  field_simp

/-- `ρ(c) = (1/c²) ∫_0^{1/4} (edge)''(u) e^{cu} du`. -/
theorem plateauRho_eq₂ {c : ℂ} (hc : c ≠ 0) :
    plateauRho c
      = (1 / c ^ (2 : ℕ)) * ∫ u in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) u : ℝ) : ℂ) * Complex.exp (c * (u : ℂ)) := by
  rw [plateauRho_eq hc, integral_edgeDeriv_cexp_eq hc]
  field_simp

/-! ## Second-order coefficient bounds -/

theorem exists_plateauEdge_deriv_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) (1 / 4 : ℝ), |deriv (deriv plateauEdge) s| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn
    plateauEdge_deriv_deriv_continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s hs => ?_⟩
  have := hM s hs
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem norm_integral_edgeDerivDeriv_cexp_le {M₀ : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) (1 / 4 : ℝ), |deriv (deriv plateauEdge) s| ≤ M₀) (c : ℂ) :
    ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ),
        ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖
      ≤ M₀ * Real.exp (|c.re| / 4) / 4 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1 / 4) (C := M₀ * Real.exp (|c.re| / 4))
    (f := fun s : ℝ => ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))) ?_
  · have e : |(1 / 4 : ℝ) - 0| = 1 / 4 := by norm_num
    rw [e] at h
    linarith
  · intro s hs
    rw [uIoc_of_le (by norm_num), mem_Ioc] at hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |deriv (deriv plateauEdge) s| ≤ M₀ := hM s ⟨hs.1.le, hs.2⟩
    have h2 : ‖Complex.exp (c * (s : ℂ))‖ ≤ Real.exp (|c.re| / 4) :=
      norm_cexp_mul_le_exp_abs_re (by rw [abs_of_pos hs.1]; exact hs.2)
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (abs_nonneg _) h1)

/-- **Second-order coefficient bounds.**  `‖κ(c)‖, ‖ρ(c)‖ ≤ M₂ e^{|Re c|/4} / ‖c‖²` for `c ≠ 0`. -/
theorem exists_plateau_coeff_bound₂ :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c ≠ 0 →
      ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ) := by
  obtain ⟨M₀, hM₀, hM⟩ := exists_plateauEdge_deriv_deriv_bound
  refine ⟨M₀ / 4, by positivity, fun c hc => ?_⟩
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  constructor
  · rw [plateauKappa_eq₂ hc, norm_mul, norm_div, norm_one, norm_pow]
    have hcongr : ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
        ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-(c * (s : ℂ)))
        = ∫ s in (0 : ℝ)..(1 / 4 : ℝ),
            ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-c * (s : ℂ)) := by
      refine integral_congr fun s _ => ?_
      rw [neg_mul]
    rw [hcongr]
    have h := norm_integral_edgeDerivDeriv_cexp_le hM (-c)
    rw [Complex.neg_re, abs_neg] at h
    calc 1 / ‖c‖ ^ (2 : ℕ) * ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (-c * (s : ℂ))‖
        ≤ 1 / ‖c‖ ^ (2 : ℕ) * (M₀ * Real.exp (|c.re| / 4) / 4) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M₀ / 4 * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ) := by ring
  · rw [plateauRho_eq₂ hc, norm_mul, norm_div, norm_one, norm_pow]
    have h := norm_integral_edgeDerivDeriv_cexp_le hM c
    calc 1 / ‖c‖ ^ (2 : ℕ) * ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ),
          ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖
        ≤ 1 / ‖c‖ ^ (2 : ℕ) * (M₀ * Real.exp (|c.re| / 4) / 4) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M₀ / 4 * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ) := by ring

/-! ## Global bound on the edge derivative -/

theorem deriv_plateauEdge_eq_zero_of_neg {s : ℝ} (hs : s < 0) : deriv plateauEdge s = 0 := by
  have hev : plateauEdge =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact plateauEdge_eq_zero (le_of_lt hy)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_plateauEdge_eq_zero_of_gt {s : ℝ} (hs : 1 / 4 < s) : deriv plateauEdge s = 0 := by
  have hev : plateauEdge =ᶠ[nhds s] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact plateauEdge_eq_one (le_of_lt hy)
  rw [hev.deriv_eq, deriv_const]

/-- The edge derivative is bounded on the whole line. -/
theorem exists_plateauEdge_deriv_global_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, |deriv plateauEdge s| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := exists_plateauEdge_deriv_bound
  refine ⟨K, hK0, fun s => ?_⟩
  rcases lt_or_ge s 0 with hs | hs
  · rw [deriv_plateauEdge_eq_zero_of_neg hs, abs_zero]; exact hK0
  rcases lt_or_ge (1 / 4 : ℝ) s with hs' | hs'
  · rw [deriv_plateauEdge_eq_zero_of_gt hs', abs_zero]; exact hK0
  · exact hK s ⟨hs, hs'⟩

/-! ## Derivatives of the bump and the profile -/

theorem hasDerivAt_plateauBump (a u : ℝ) :
    HasDerivAt (plateauBump a)
      (deriv plateauEdge u * plateauEdge (a - u) - plateauEdge u * deriv plateauEdge (a - u)) u := by
  have h1 := plateauEdge_hasDerivAt u
  have h2 : HasDerivAt (fun y : ℝ => plateauEdge (a - y)) (-(deriv plateauEdge (a - u))) u :=
    (plateauEdge_hasDerivAt (a - u)).comp_const_sub a u
  have := h1.mul h2
  refine this.congr_deriv ?_
  ring

theorem abs_deriv_plateauBump_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ s : ℝ, |deriv plateauEdge s| ≤ K)
    (a u : ℝ) :
    |deriv plateauEdge u * plateauEdge (a - u) - plateauEdge u * deriv plateauEdge (a - u)|
      ≤ 2 * K := by
  have h1 := hK u
  have h2 := hK (a - u)
  have e1 := plateauEdge_nonneg (a - u)
  have e1' := plateauEdge_le_one (a - u)
  have e2 := plateauEdge_nonneg u
  have e2' := plateauEdge_le_one u
  calc |deriv plateauEdge u * plateauEdge (a - u) - plateauEdge u * deriv plateauEdge (a - u)|
      ≤ |deriv plateauEdge u * plateauEdge (a - u)| + |plateauEdge u * deriv plateauEdge (a - u)| :=
        abs_sub _ _
    _ = |deriv plateauEdge u| * plateauEdge (a - u) + plateauEdge u * |deriv plateauEdge (a - u)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg e1, abs_of_nonneg e2]
    _ ≤ K * 1 + 1 * K := by
        gcongr
    _ = 2 * K := by ring

/-- The derivative of the profile. -/
def plateauProfileDeriv (a u : ℝ) : ℝ :=
  (deriv plateauEdge u * plateauEdge (a - u) - plateauEdge u * deriv plateauEdge (a - u))
    + (deriv plateauEdge (-u) * plateauEdge (a - -u) - plateauEdge (-u) * deriv plateauEdge (a - -u))

theorem hasDerivAt_plateauProfileFun (a u : ℝ) :
    HasDerivAt (plateauProfileFun a) (plateauProfileDeriv a u) u := by
  have h1 := hasDerivAt_plateauBump a u
  have h2 : HasDerivAt (fun y : ℝ => plateauBump a (-y))
      (-(deriv plateauEdge (-u) * plateauEdge (a - -u) - plateauEdge (-u) * deriv plateauEdge (a - -u)))
      u := by
    have := (hasDerivAt_plateauBump a (0 - u)).comp_const_sub 0 u
    simpa [zero_sub] using this
  have := h1.sub h2
  refine this.congr_deriv ?_
  unfold plateauProfileDeriv
  ring

theorem abs_plateauProfileDeriv_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ s : ℝ, |deriv plateauEdge s| ≤ K)
    (a u : ℝ) :
    |plateauProfileDeriv a u| ≤ 4 * K := by
  unfold plateauProfileDeriv
  have h1 := abs_deriv_plateauBump_le hK0 hK a u
  have h2 := abs_deriv_plateauBump_le hK0 hK a (-u)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * K + 2 * K := add_le_add h1 h2
    _ = 4 * K := by ring

end

end RHTower
