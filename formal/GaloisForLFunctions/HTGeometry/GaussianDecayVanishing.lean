import GaloisForLFunctions.HTGeometry.HermitianRadicalPositivity

/-!
# Gaussian decay kills an entire function

An entire function bounded by `C exp (-a |t|^2)` with `a > 0` vanishes identically: the bound makes
it bounded, so Liouville makes it constant, and the bound then forces the constant to be zero.

Restricted to a complex line this is the mechanism behind semi-definiteness of the Hermitian form
of a line bundle with a nonzero section.  Along a direction on which the form is negative, the
periodicity-normalised modulus of a theta function acquires exactly a Gaussian factor, so the
section must vanish on that whole line.
-/

open Filter Topology Bornology Set

namespace GaloisForLFunctions.HTGeometry

/-- **An entire function of one variable with Gaussian decay is zero.** -/
theorem eq_zero_of_gaussian_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C a : ℝ} (ha : 0 < a)
    (hbound : ∀ t : ℂ, ‖f t‖ ≤ C * Real.exp (-a * ‖t‖ ^ 2)) (t : ℂ) :
    f t = 0 := by
  have hC : 0 ≤ C := by
    have h := hbound 0
    simp only [norm_zero] at h
    have hexp : Real.exp (-a * (0 : ℝ) ^ 2) = 1 := by norm_num
    rw [hexp, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hbdd : IsBounded (Set.range f) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hbound z
    have h2 : Real.exp (-a * ‖z‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg ‖z‖, ha.le]
    nlinarith [norm_nonneg (f z)]
  have hconst : ∀ z : ℂ, f z = f 0 := fun z => hf.apply_eq_apply_of_bounded hbdd z 0
  by_contra hne
  have hc : 0 < ‖f 0‖ := by
    rw [← hconst t]
    exact norm_pos_iff.mpr hne
  have htend : Tendsto (fun r : ℝ => C * Real.exp (-a * r ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => a * r ^ 2) atTop atTop :=
      Filter.Tendsto.const_mul_atTop ha (tendsto_pow_atTop two_ne_zero)
    have h2 : Tendsto (fun r : ℝ => -(a * r ^ 2)) atTop atBot := tendsto_neg_atTop_atBot.comp h1
    have h3 : Tendsto (fun r : ℝ => Real.exp (-(a * r ^ 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h2
    have h4 := h3.const_mul C
    rw [mul_zero] at h4
    refine h4.congr fun r => ?_
    ring_nf
  obtain ⟨r, hr⟩ := (htend.eventually (eventually_lt_nhds hc)).exists
  have hnormr : ‖((r : ℂ))‖ ^ 2 = r ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle := hbound ((r : ℂ))
  rw [hconst ((r : ℂ)), hnormr] at hle
  linarith

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Gaussian decay along a complex line kills the function on that line.** -/
theorem eq_zero_of_gaussian_decay_along_line {f : W → ℂ} (hf : Differentiable ℂ f) (v : W)
    {C a : ℝ} (ha : 0 < a)
    (hbound : ∀ t : ℂ, ‖f (t • v)‖ ≤ C * Real.exp (-a * ‖t‖ ^ 2)) (t : ℂ) :
    f (t • v) = 0 :=
  eq_zero_of_gaussian_decay (hf.comp (differentiable_id.smul_const v)) ha hbound t

/-- **A nonzero value on a line forbids Gaussian decay on it.**  Contrapositive form: this is the
step that turns the existence of a section into semi-definiteness of the Hermitian form. -/
theorem not_gaussian_decay_along_line_of_ne_zero {f : W → ℂ} (hf : Differentiable ℂ f) {v : W}
    {t₀ : ℂ} (hne : f (t₀ • v) ≠ 0) {C a : ℝ} (ha : 0 < a) :
    ¬ ∀ t : ℂ, ‖f (t • v)‖ ≤ C * Real.exp (-a * ‖t‖ ^ 2) := by
  intro hbound
  exact hne (eq_zero_of_gaussian_decay_along_line hf v ha hbound t₀)

end GaloisForLFunctions.HTGeometry
