import GaloisForLFunctions.RHTower.ArchimedeanWeilApertureConstant

/-!
# The aperture certificate: a uniform deficit bound and the two-sided positivity window

Continuing `ArchimedeanWeilApertureConstant`.  Three sharpenings.

* **A uniform bound on the deficit correction.**  The linear bound `J S ≤ (3/2) S` is wasteful: the
  integrand satisfies `kernelDeficit u ≤ e^{-u/2}`, which integrates to `J S ≤ 4` for *every*
  aperture.  The proof is the one-line comparison `y⁵ ≤ y⁴` at `y = e^{-u/2}`.

* **Positivity of the aperture constant at large aperture.**  Since `-log (1 - e^{-2S}) ≥ 0` and
  `J S ≤ 4` while `8 sinh (S/2)` grows, the constant is again positive once `S ≥ 4`.  So the
  aperture constant is positive at both ends, and its only possible failure is a bounded middle
  window.

* **The certificate inequality.**  Past the kernel's sign change the Dirichlet term must be bounded,
  not merely signed.  For `g = f ⋆ f̃` the deficit obeys `D u = ‖f - T_u f‖²/2 ≤ 2 ‖f‖²`, so
  pointwise `D u · K u ≥ 2 ‖f‖² · min (K u) 0`.  This replaces the sign of `K` by a competition
  between the constant and the negative mass of the kernel, which is what decides how far the
  elementary route reaches.

All statements are unconditional.
-/

namespace RHTower.ArchimedeanKernel

/-! ## A uniform bound on the deficit correction -/

/-- The deficit integrand is dominated by `e^{-u/2}`.  In the variable `y = e^{-u/2} ∈ (0,1)` this is
`y - y⁴ ≤ y (1 - y⁴)`, i.e. `y⁵ ≤ y⁴`. -/
theorem kernelDeficit_le_exp {u : ℝ} (hu : 0 < u) :
    kernelDeficit u ≤ Real.exp (-u / 2) := by
  have hden := one_sub_exp_neg_two_mul_pos hu
  have hy : (0 : ℝ) < Real.exp (-u / 2) := Real.exp_pos _
  have hy1 : Real.exp (-u / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h4 := exp_neg_two_mul u
  rw [kernelDeficit, div_le_iff₀ hden, h4]
  have hy4 : 0 < Real.exp (-u / 2) * Real.exp (-u / 2) * Real.exp (-u / 2) *
      Real.exp (-u / 2) := by positivity
  nlinarith [hy4, hy1, hy]

theorem measurable_kernelDeficit : Measurable kernelDeficit := by
  unfold kernelDeficit
  fun_prop

theorem intervalIntegrable_kernelDeficit {S : ℝ} (hS : 0 ≤ S) :
    IntervalIntegrable kernelDeficit MeasureTheory.volume 0 S := by
  rw [intervalIntegrable_iff]
  have hfin : MeasureTheory.volume (Set.uIoc (0 : ℝ) S) < ⊤ := by
    rw [Set.uIoc_of_le hS]
    exact (measure_Ioc_lt_top)
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (3 : ℝ) / 4) ?_
    measurable_kernelDeficit.aestronglyMeasurable ?_
  · exact MeasureTheory.integrableOn_const hfin.ne
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Set.uIoc_of_le hS] at hx
    exact abs_kernelDeficit_le hx.1

theorem integral_exp_neg_half {S : ℝ} :
    (∫ u in (0 : ℝ)..S, Real.exp (-u / 2)) = 2 - 2 * Real.exp (-S / 2) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) S,
      HasDerivAt (fun t : ℝ => -2 * Real.exp (-t / 2)) (Real.exp (-u / 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) u := by
      simpa using ((hasDerivAt_id u).neg).div_const 2
    have h2 := (Real.hasDerivAt_exp (-u / 2)).comp u h1
    have h3 := h2.const_mul (-2 : ℝ)
    refine h3.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
  simp
  ring

/-- **The deficit correction is bounded by `4` at every aperture.** -/
theorem deficitIntegral_le_four {S : ℝ} (hS : 0 ≤ S) : deficitIntegral S ≤ 4 := by
  have hmono : (∫ u in (0 : ℝ)..S, kernelDeficit u) ≤ ∫ u in (0 : ℝ)..S, Real.exp (-u / 2) := by
    apply intervalIntegral.integral_mono_on hS (intervalIntegrable_kernelDeficit hS)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)
    intro u hu
    rcases lt_or_eq_of_le hu.1 with h | h
    · exact kernelDeficit_le_exp h
    · rw [← h, kernelDeficit]
      norm_num
  rw [integral_exp_neg_half] at hmono
  have hpos : (0 : ℝ) < Real.exp (-S / 2) := Real.exp_pos _
  rw [deficitIntegral]
  linarith

/-! ## Positivity of the aperture constant at large aperture -/

theorem log_pi_lt_two : Real.log Real.pi < 2 := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  have h4' : (4 : ℝ) < Real.exp 2 := by
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
      linarith
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  have hlt : Real.pi < Real.exp 2 := by
    have := Real.pi_le_four
    linarith
  have := Real.log_lt_log Real.pi_pos hlt
  rwa [Real.log_exp] at this

theorem neg_log_one_sub_exp_nonneg {S : ℝ} (hS : 0 < S) :
    0 ≤ -Real.log (1 - Real.exp (-2 * S)) := by
  have hden := one_sub_exp_neg_two_mul_pos hS
  have hle : 1 - Real.exp (-2 * S) ≤ 1 := by
    have := Real.exp_pos (-2 * S)
    linarith
  have := Real.log_nonpos hden.le hle
  linarith

/-- **The aperture constant is positive again at large aperture.**  Together with
`apertureConstant_pos` this confines any failure to a bounded middle window. -/
theorem apertureConstant_pos_of_four_le {S : ℝ} (hS : 4 ≤ S) : 0 < apertureConstant S := by
  have hSpos : (0 : ℝ) < S := by linarith
  have hJ : deficitIntegral S ≤ 4 := deficitIntegral_le_four hSpos.le
  have hlog : 0 ≤ -Real.log (1 - Real.exp (-2 * S)) := neg_log_one_sub_exp_nonneg hSpos
  have hgamma : Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hpi : Real.log Real.pi < 2 := log_pi_lt_two
  have hsinh2 : (15 : ℝ) / 8 ≤ Real.sinh 2 := by
    have he : (4 : ℝ) ≤ Real.exp 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith
    have hinv : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      linarith
    rw [Real.sinh_eq]
    linarith
  have hmono : Real.sinh 2 ≤ Real.sinh (S / 2) := Real.sinh_le_sinh.mpr (by linarith)
  rw [apertureConstant]
  linarith

/-! ## The certificate inequality -/

/-- Past the sign change the Dirichlet term must be bounded rather than merely signed.  For a
deficit `d` confined to `[0, 2 m]` and any weight `k`, the product is bounded below by
`2 m · min k 0`. -/
theorem deficit_mul_kernel_ge {d m k : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * m) :
    2 * m * min k 0 ≤ d * k := by
  rcases le_total 0 k with hk | hk
  · rw [min_eq_right hk]
    have : 0 ≤ d * k := mul_nonneg hd0 hk
    linarith
  · rw [min_eq_left hk]
    nlinarith

/-- The translation deficit of a unit-preserving translate is at most twice the squared norm:
`‖x - y‖² / 2 ≤ 2 ‖x‖²` whenever `‖y‖ = ‖x‖`.  This is the bound that makes
`deficit_mul_kernel_ge` applicable with `m = ‖x‖²`. -/
theorem half_norm_sub_sq_le {E : Type*} [NormedAddCommGroup E] {x y : E} (h : ‖y‖ = ‖x‖) :
    ‖x - y‖ ^ (2 : ℕ) / 2 ≤ 2 * ‖x‖ ^ (2 : ℕ) := by
  have htri : ‖x - y‖ ≤ 2 * ‖x‖ := by
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ = 2 * ‖x‖ := by rw [h]; ring
  have hnn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  nlinarith [norm_nonneg x]

end RHTower.ArchimedeanKernel
