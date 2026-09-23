import GaloisForLFunctions.RHTower.Sieve.CesaroKernelVertical

/-!
# Primitives for the Cesàro kernel

Two antiderivatives carry the Cesàro Perron formula.

Along the vertical line, `t ↦ i/(σ+it)` is a primitive of `t ↦ 1/(σ+it)²`, so the truncated line
integral of the pure second-order pole is a difference of two endpoint values and hence `O(1/T)`:

`∫_{-T}^{T} dt/(σ+it)² = i/(σ+iT) − i/(σ−iT)`,   `‖·‖ ≤ 2/T`.

Along the cutoff, `u ↦ u^s/s` is a primitive of `u ↦ u^{s−1}`, so

`∫_1^y u^{s−1} du = (y^s − 1)/s`.

The second identity is what turns the first-order kernel into the second-order one under the `du/u`
average: `(y^s − 1)/s² = ∫_1^y (u^s/s)(du/u)`.  So the Cesàro kernel is the logarithmic average of the
sharp-cutoff kernel, and its truncation error is the corresponding average — with no near-diagonal
analysis, because averaging `1/|log(u/n)|` in `u` is what the sharp kernel's error needed and the
Cesàro kernel's error avoids.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- A point of the line `Re s = σ` is nonzero when `σ > 0`. -/
theorem line_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
  intro h
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  linarith [hre]

/-- `t ↦ i/(σ+it)` is a primitive of `t ↦ 1/(σ+it)²`. -/
theorem hasDerivAt_inv_line {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => I / ((σ : ℂ) + (u : ℝ) * I))
      (1 / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ)) t := by
  have hne : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := line_ne_zero hσ t
  have hd : HasDerivAt (fun u : ℝ => ((σ : ℂ) + (u : ℝ) * I)) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (σ : ℂ)
  have h := (hasDerivAt_const t I).div hd hne
  have hsq : ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hne
  have hval : (0 * ((σ : ℂ) + (t : ℝ) * I) - I * I) / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ)
      = 1 / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ) := by
    rw [Complex.I_mul_I]
    ring
  rw [← hval]
  exact h

/-- The reciprocal square is continuous on the line. -/
theorem continuous_inv_sq_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => 1 / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ) := by
  refine continuous_const.div ?_ fun t => pow_ne_zero 2 (line_ne_zero hσ t)
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2

/-- **The truncated line integral of the pure second-order pole.**  A difference of endpoint values. -/
theorem integral_inv_sq_line_eq {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    (∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ))
      = I / ((σ : ℂ) + (T : ℝ) * I) - I / ((σ : ℂ) + ((-T : ℝ) : ℝ) * I) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_inv_line hσ t)
    ((continuous_inv_sq_line hσ).intervalIntegrable _ _)

/-- **The pure second-order pole contributes `O(1/T)`.** -/
theorem norm_integral_inv_sq_line_le {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    ‖∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ (2 : ℕ)‖ ≤ 2 / T := by
  have hbound : ∀ u : ℝ, u ^ (2 : ℕ) = T ^ (2 : ℕ) → ‖I / ((σ : ℂ) + (u : ℝ) * I)‖ ≤ 1 / T := by
    intro u hu
    rw [norm_div, Complex.norm_I, Complex.norm_add_mul_I]
    have hge : T ≤ Real.sqrt (σ ^ (2 : ℕ) + u ^ (2 : ℕ)) := by
      rw [show σ ^ (2 : ℕ) + u ^ (2 : ℕ) = σ ^ (2 : ℕ) + T ^ (2 : ℕ) by rw [hu]]
      have h1 : T = Real.sqrt (T ^ (2 : ℕ)) := by
        rw [Real.sqrt_sq hT.le]
      rw [h1]
      exact Real.sqrt_le_sqrt (by nlinarith)
    exact div_le_div_of_nonneg_left zero_le_one hT hge
  rw [integral_inv_sq_line_eq hσ T]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := hbound T rfl
  have h2 := hbound (-T) (by ring)
  have hval : (2 : ℝ) / T = 1 / T + 1 / T := by ring
  rw [hval]
  exact add_le_add h1 h2

/-- `u ↦ u^s/s` is a primitive of `u ↦ u^{s−1}` on the positive reals. -/
theorem hasDerivAt_cpow_div {s : ℂ} (hs : s ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => ((v : ℂ)) ^ s / s) (((u : ℂ)) ^ (s - 1)) u := by
  have hr : s - 1 ≠ -1 := fun h => hs (by linear_combination h)
  have h := hasDerivAt_ofReal_cpow_const' hu hr
  rw [sub_add_cancel] at h
  exact h

/-- **The cutoff primitive.**  `∫_1^y u^{s−1} du = (y^s − 1)/s`. -/
theorem integral_cpow_sub_one_eq {s : ℂ} (hs : s ≠ 0) {y : ℝ} (hy : 1 ≤ y) :
    (∫ u in (1 : ℝ)..y, ((u : ℂ)) ^ (s - 1)) = ((y : ℂ)) ^ s / s - 1 / s := by
  have hmem : ∀ u ∈ Set.uIcc (1 : ℝ) y, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hy, Set.mem_Icc] at hu
    linarith [hu.1]
  have hcont : ContinuousOn (fun u : ℝ => ((u : ℂ)) ^ (s - 1)) (Set.uIcc (1 : ℝ) y) := by
    intro u hu
    exact ((Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (by exact_mod_cast (hmem u hu).ne'))).continuousWithinAt)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => ((v : ℂ)) ^ s / s)
    (fun u hu => hasDerivAt_cpow_div hs (hmem u hu).ne')
    (hcont.intervalIntegrable)
  rw [h, Complex.ofReal_one, Complex.one_cpow]

end RHTower.Sieve
end
