import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.HTGeometry.FrequencyRank

/-!
# The Bohr coefficient of a derivative, and the spectrum of a trigonometric polynomial

Two computations that any differential-algebraic argument over the Bohr spectrum needs.

Differentiating multiplies each Bohr coefficient by `iλ`: integrating by parts against the character
`e^{-iλt}` moves the derivative onto the character and leaves a boundary term of size `O(1)`, which
the window average kills.  In particular the spectrum of `f'` is contained in that of `f`, and the
mean of a derivative vanishes.

Dually, the coefficients of a trigonometric polynomial are its own coefficients: its spectrum is
contained in its finite frequency set, so its frequency module is finitely generated.  This is the
concrete instance showing the finite-phase conclusion is attained.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-! ### Differentiation on the Bohr side -/

/-- **The Bohr coefficient of a derivative.**  `a_{f'}(λ) = iλ · a_f(λ)`. -/
theorem bohrCoefficient_deriv {f f' : ℝ → ℂ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hfc : Continuous f) (hf'c : Continuous f')
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hf'a : HTGeometry.IsBohrAlmostPeriodic f')
    (lam : ℝ) :
    bohrCoefficient f' lam = (lam : ℂ) * Complex.I * bohrCoefficient f lam := by
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic hfc hfa
  set c : ℂ := -(lam : ℂ) * Complex.I with hc
  have hchar : ∀ t : ℝ, bohrChar lam t = Complex.exp (c * (t : ℂ)) := by
    intro t
    simp only [bohrChar, hc]
    congr 1
    push_cast
    ring
  have hvderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ))) (c * Complex.exp (c * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
    simpa [mul_comm] using h1.cexp
  have hvc : Continuous fun u : ℝ => Complex.exp (c * (u : ℂ)) := by fun_prop
  have hIBP : ∀ T : ℝ,
      (∫ t in (0 : ℝ)..T, f' t * Complex.exp (c * (t : ℂ)))
        = (f T * Complex.exp (c * (T : ℂ)) - f 0 * Complex.exp (c * ((0 : ℝ) : ℂ)))
          - c * ∫ t in (0 : ℝ)..T, f t * Complex.exp (c * (t : ℂ)) := by
    intro T
    have h := intervalIntegral.integral_deriv_mul_eq_sub (a := (0 : ℝ)) (b := T)
      (u := f) (u' := f') (v := fun u : ℝ => Complex.exp (c * (u : ℂ)))
      (v' := fun u : ℝ => c * Complex.exp (c * (u : ℂ)))
      (fun x _ => hderiv x) (fun x _ => hvderiv x)
      (hf'c.intervalIntegrable _ _)
      ((continuous_const.mul hvc).intervalIntegrable _ _)
    have hsplit : (∫ t in (0 : ℝ)..T,
          (f' t * Complex.exp (c * (t : ℂ)) + f t * (c * Complex.exp (c * (t : ℂ)))))
        = (∫ t in (0 : ℝ)..T, f' t * Complex.exp (c * (t : ℂ)))
          + c * ∫ t in (0 : ℝ)..T, f t * Complex.exp (c * (t : ℂ)) := by
      rw [intervalIntegral.integral_add
        (f := fun t : ℝ => f' t * Complex.exp (c * (t : ℂ)))
        (g := fun t : ℝ => f t * (c * Complex.exp (c * (t : ℂ))))
        ((hf'c.mul hvc).intervalIntegrable _ _)
        ((hfc.mul (continuous_const.mul hvc)).intervalIntegrable _ _)]
      congr 1
      rw [show (fun t : ℝ => f t * (c * Complex.exp (c * (t : ℂ))))
          = fun t : ℝ => c * (f t * Complex.exp (c * (t : ℂ))) from funext fun t => by ring]
      exact intervalIntegral.integral_const_mul c _
    rw [hsplit] at h
    linear_combination h
  -- window averages
  have hbdry : Tendsto (fun T : ℝ =>
      (T : ℝ)⁻¹ • (f T * Complex.exp (c * (T : ℂ)) - f 0 * Complex.exp (c * ((0 : ℝ) : ℂ))))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun T : ℝ => (2 * C) / T)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hnormc : ∀ u : ℝ, ‖Complex.exp (c * (u : ℂ))‖ = 1 := by
        intro u
        rw [← hchar u]
        exact norm_bohrChar _ _
      have hb : ‖f T * Complex.exp (c * (T : ℂ)) - f 0 * Complex.exp (c * ((0 : ℝ) : ℂ))‖
          ≤ 2 * C := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, hnormc T, hnormc 0, mul_one, mul_one]
        have := hC T
        have := hC 0
        linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hT.le)]
      calc T⁻¹ * ‖f T * Complex.exp (c * (T : ℂ)) - f 0 * Complex.exp (c * ((0 : ℝ) : ℂ))‖
          ≤ T⁻¹ * (2 * C) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)
        _ = (2 * C) / T := by rw [inv_mul_eq_div]
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have hlimf' := tendsto_windowAverage_bohrCoefficient hf'c hf'a lam
  have hlimf := tendsto_windowAverage_bohrCoefficient hfc hfa lam
  have hmodel : Tendsto (fun T : ℝ =>
      windowAverage (fun t => f' t * bohrChar lam t) T) atTop
      (nhds (0 - c * bohrCoefficient f lam)) := by
    refine (hbdry.sub (hlimf.const_mul c)).congr (fun T => ?_)
    simp only [windowAverage]
    have hrw : ∀ t : ℝ, f' t * bohrChar lam t = f' t * Complex.exp (c * (t : ℂ)) := by
      intro t; rw [hchar]
    rw [show (fun t : ℝ => f' t * bohrChar lam t)
        = fun t : ℝ => f' t * Complex.exp (c * (t : ℂ)) from funext hrw, hIBP T]
    have hrw2 : (fun t : ℝ => f t * bohrChar lam t)
        = fun t : ℝ => f t * Complex.exp (c * (t : ℂ)) := funext fun t => by rw [hchar]
    rw [hrw2]
    simp only [Complex.real_smul]
    ring
  have huniq := tendsto_nhds_unique hlimf' hmodel
  rw [huniq, zero_sub, hc]
  ring

/-- The mean of a derivative vanishes. -/
theorem bohrMean_deriv_eq_zero {f f' : ℝ → ℂ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hfc : Continuous f) (hf'c : Continuous f')
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hf'a : HTGeometry.IsBohrAlmostPeriodic f') :
    bohrCoefficient f' 0 = 0 := by
  rw [bohrCoefficient_deriv hderiv hfc hf'c hfa hf'a 0]
  simp

/-- **The spectrum of the derivative is contained in the spectrum.** -/
theorem bohrSpectrum_deriv_subset {f f' : ℝ → ℂ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hfc : Continuous f) (hf'c : Continuous f')
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hf'a : HTGeometry.IsBohrAlmostPeriodic f') :
    bohrSpectrum f' ⊆ bohrSpectrum f := by
  intro lam hlam
  by_contra hnot
  apply hlam
  have hzero : bohrCoefficient f lam = 0 := by
    by_contra h
    exact hnot h
  rw [bohrCoefficient_deriv hderiv hfc hf'c hfa hf'a lam, hzero, mul_zero]

/-! ### The spectrum of a trigonometric polynomial -/

/-- The Bohr coefficients of a trigonometric polynomial are its own coefficients. -/
theorem bohrCoefficient_sum_expChar {ι : Type*} (s : Finset ι) (cf : ι → ℂ) (mu : ι → ℝ)
    (lam : ℝ) :
    bohrCoefficient (fun t => ∑ i ∈ s, cf i * expChar (mu i) t) lam
      = ∑ i ∈ s, if mu i = lam then cf i else 0 := by
  classical
  have hfun : (fun t : ℝ => (∑ i ∈ s, cf i * expChar (mu i) t) * bohrChar lam t)
      = fun t : ℝ => ∑ i ∈ s, cf i * expChar (mu i - lam) t := by
    funext t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hb : bohrChar lam t = expChar (-lam) t := by
      rw [expChar_eq_bohrChar]
      congr 1
      ring
    rw [hb, mul_assoc, expChar_add]
    congr 2
  rw [bohrCoefficient, hfun, bohrMean_sum_expChar s cf (fun i => mu i - lam)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : mu i = lam
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (fun hz => h (by linarith [sub_eq_zero.mp hz])), if_neg h]

/-- The spectrum of a trigonometric polynomial lies in its frequency set. -/
theorem bohrSpectrum_sum_expChar_subset {ι : Type*} [DecidableEq ι] (s : Finset ι) (cf : ι → ℂ)
    (mu : ι → ℝ) :
    bohrSpectrum (fun t => ∑ i ∈ s, cf i * expChar (mu i) t) ⊆ ((s.image mu : Finset ℝ) : Set ℝ) := by
  intro lam hlam
  by_contra hnot
  apply hlam
  rw [bohrCoefficient_sum_expChar]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [if_neg]
  intro h
  exact hnot (by simpa using Finset.mem_image.mpr ⟨i, hi, h⟩)

/-- **The frequency module of a trigonometric polynomial is finitely generated.**  It lies in the
`ℚ`-span of the finite frequency set, whose rank is bounded by the number of terms
(`frequencyRank_le_card`). -/
theorem bohrFrequencyModule_sum_expChar_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (cf : ι → ℂ)
    (mu : ι → ℝ) :
    bohrFrequencyModule (fun t => ∑ i ∈ s, cf i * expChar (mu i) t)
      ≤ Submodule.span ℚ ((s.image mu : Finset ℝ) : Set ℝ) :=
  Submodule.span_mono (bohrSpectrum_sum_expChar_subset s cf mu)

end

end GaloisForLFunctions
