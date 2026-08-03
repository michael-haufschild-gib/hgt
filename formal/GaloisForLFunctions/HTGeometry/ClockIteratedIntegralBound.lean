import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The double integration of a power-dominated integrand

The step of the analytic clock iteration integrates the operator twice, once along each
characteristic. What the Ovsyannikov recursion asks of that step is exactly this: an integrand
dominated by `c sᵐ tᵐ` on the rectangle integrates to at most `c x^{m+1} y^{m+1}/(m+1)²`.

Both factorials of the recursion come from here — one from each direction — and they are what
compensates the derivative loss.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

theorem integral_pow_zero_left (m : ℕ) (x : ℝ) :
    (∫ s in (0 : ℝ)..x, s ^ m) = x ^ (m + 1) / ((m : ℝ) + 1) := by
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun u : ℝ => u ^ (m + 1) / ((m : ℝ) + 1)) (s ^ m) s := by
    intro s _
    have h := hasDerivAt_pow (m + 1) s
    have h2 : HasDerivAt (fun u : ℝ => u ^ (m + 1) / ((m : ℝ) + 1))
        (((m + 1 : ℕ) : ℝ) * s ^ (m + 1 - 1) / ((m : ℝ) + 1)) s := h.div_const _
    have hval : ((m + 1 : ℕ) : ℝ) * s ^ (m + 1 - 1) / ((m : ℝ) + 1) = s ^ m := by
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    rwa [hval] at h2
  have hint : IntervalIntegrable (fun s : ℝ => s ^ m) volume 0 x :=
    (continuous_pow m).intervalIntegrable 0 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **A power-dominated integrand integrates to a power.** -/
theorem abs_integral_pow_bound {m : ℕ} {c y : ℝ} (hy : 0 ≤ y) {f : ℝ → ℝ}
    (hf : Continuous f) (hb : ∀ t ∈ Icc (0 : ℝ) y, |f t| ≤ c * t ^ m) :
    |∫ t in (0 : ℝ)..y, f t| ≤ c * y ^ (m + 1) / ((m : ℝ) + 1) := by
  have habs : |∫ t in (0 : ℝ)..y, f t| ≤ ∫ t in (0 : ℝ)..y, |f t| :=
    abs_integral_le_integral_abs hy
  have hmono : (∫ t in (0 : ℝ)..y, |f t|) ≤ ∫ t in (0 : ℝ)..y, c * t ^ m := by
    refine integral_mono_on hy (hf.abs.intervalIntegrable 0 y)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 y) ?_
    intro t ht
    exact hb t ht
  have hval : (∫ t in (0 : ℝ)..y, c * t ^ m) = c * y ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    ring
  linarith [habs, hmono, hval.le, hval.ge]

/-- **The double integration of a power-dominated integrand.** -/
theorem abs_iterated_integral_le {m : ℕ} {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {F : ℝ → ℝ → ℝ} (hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hFb : ∀ s ∈ Icc (0 : ℝ) x, ∀ t ∈ Icc (0 : ℝ) y, |F s t| ≤ c * s ^ m * t ^ m) :
    |∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t|
      ≤ c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ 2 := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hslice : ∀ s : ℝ, Continuous fun t => F s t :=
    fun s => hFc.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous fun s : ℝ => ∫ t in (0 : ℝ)..y, F s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have hbound : ∀ s ∈ Icc (0 : ℝ) x,
      |∫ t in (0 : ℝ)..y, F s t| ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := by
    intro s hs
    exact abs_integral_pow_bound hy (hslice s) fun t ht => hFb s hs t ht
  have habs : |∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t|
      ≤ ∫ s in (0 : ℝ)..x, |∫ t in (0 : ℝ)..y, F s t| :=
    abs_integral_le_integral_abs hx
  have hmono : (∫ s in (0 : ℝ)..x, |∫ t in (0 : ℝ)..y, F s t|)
      ≤ ∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by
    refine integral_mono_on hx (hinner.abs.intervalIntegrable 0 x)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 x) ?_
    intro s hs
    have h := hbound s hs
    calc |∫ t in (0 : ℝ)..y, F s t| ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := h
      _ = c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by ring
  have hval : (∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m)
      = c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    field_simp
  linarith [habs, hmono, hval.le, hval.ge]

/-! ## The vector-valued form

The iteration of the clock equation integrates a function with values in a space of holomorphic
functions, so the bound is needed for a Banach-valued integrand. Nothing changes: the norm of an
integral is at most the integral of the norm, and the comparison is then between real integrals.
-/

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_integral_pow_bound {m : ℕ} {c y : ℝ} (hy : 0 ≤ y) {f : ℝ → E}
    (hf : Continuous f) (hb : ∀ t ∈ Icc (0 : ℝ) y, ‖f t‖ ≤ c * t ^ m) :
    ‖∫ t in (0 : ℝ)..y, f t‖ ≤ c * y ^ (m + 1) / ((m : ℝ) + 1) := by
  have hnorm : ‖∫ t in (0 : ℝ)..y, f t‖ ≤ ∫ t in (0 : ℝ)..y, ‖f t‖ :=
    norm_integral_le_integral_norm hy
  have hmono : (∫ t in (0 : ℝ)..y, ‖f t‖) ≤ ∫ t in (0 : ℝ)..y, c * t ^ m := by
    refine integral_mono_on hy (hf.norm.intervalIntegrable 0 y)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 y) ?_
    intro t ht
    exact hb t ht
  have hval : (∫ t in (0 : ℝ)..y, c * t ^ m) = c * y ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    ring
  linarith [hnorm, hmono, hval.le, hval.ge]

/-- **The double integration of a power-dominated Banach-valued integrand.** -/
theorem norm_iterated_integral_le {m : ℕ} {c x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {F : ℝ → ℝ → E} (hFc : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hFb : ∀ s ∈ Icc (0 : ℝ) x, ∀ t ∈ Icc (0 : ℝ) y, ‖F s t‖ ≤ c * s ^ m * t ^ m) :
    ‖∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t‖
      ≤ c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ 2 := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hslice : ∀ s : ℝ, Continuous fun t => F s t :=
    fun s => hFc.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous fun s : ℝ => ∫ t in (0 : ℝ)..y, F s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have hbound : ∀ s ∈ Icc (0 : ℝ) x,
      ‖∫ t in (0 : ℝ)..y, F s t‖ ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := by
    intro s hs
    exact norm_integral_pow_bound hy (hslice s) fun t ht => hFb s hs t ht
  have hnorm : ‖∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..y, F s t‖
      ≤ ∫ s in (0 : ℝ)..x, ‖∫ t in (0 : ℝ)..y, F s t‖ :=
    norm_integral_le_integral_norm hx
  have hmono : (∫ s in (0 : ℝ)..x, ‖∫ t in (0 : ℝ)..y, F s t‖)
      ≤ ∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by
    refine integral_mono_on hx (hinner.norm.intervalIntegrable 0 x)
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 x) ?_
    intro s hs
    have h := hbound s hs
    calc ‖∫ t in (0 : ℝ)..y, F s t‖ ≤ c * s ^ m * y ^ (m + 1) / ((m : ℝ) + 1) := h
      _ = c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m := by ring
  have hval : (∫ s in (0 : ℝ)..x, c * y ^ (m + 1) / ((m : ℝ) + 1) * s ^ m)
      = c * (x ^ (m + 1) * y ^ (m + 1)) / ((m : ℝ) + 1) ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_pow_zero_left]
    field_simp
  linarith [hnorm, hmono, hval.le, hval.ge]

end Vector

end GaloisForLFunctions.HTGeometry
