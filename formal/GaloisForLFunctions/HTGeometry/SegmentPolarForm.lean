import Mathlib

/-!
# Continuous logarithm and polar form along a segment

A differentiable, nowhere-zero complex function of a real variable has a continuous logarithm on any
compact interval: integrate its logarithmic derivative from the left endpoint and check that
`f·exp(−L)` has vanishing derivative, hence equals its value `1` at the left endpoint.

The corollary is the polar form `Re f = ρ·cos ψ` with `ρ > 0` and `ψ` continuous — the shape
`PhaseSignChain.exists_sign_chain_of_phase_increase` consumes, and the missing link between an
argument-variation bound and a sign-change count.
-/

open Set MeasureTheory intervalIntegral


noncomputable section

namespace RHTower

/-- **A continuous logarithm along a segment.**  A differentiable, nowhere-zero complex function of
a real variable has a continuous logarithm on any compact interval: integrate its logarithmic
derivative from the left endpoint. -/
theorem exists_continuousOn_log_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℂ} (hf : ∀ τ ∈ Icc a b, HasDerivAt f (f' τ) τ)
    (hcontOn : ContinuousOn (fun τ => f' τ / f τ) (Icc a b))
    (hne : ∀ τ ∈ Icc a b, f τ ≠ 0) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Icc a b) ∧
      (∀ τ ∈ Icc a b, HasDerivAt L (f' τ / f τ) τ) ∧
      ∀ τ ∈ Icc a b, f τ = Complex.exp (L τ) := by
  set clamp : ℝ → ℝ := fun t => max a (min b t) with hclamp
  have hclampCont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclampMem : ∀ t, clamp t ∈ Icc a b := fun t =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hclampEq : ∀ t ∈ Icc a b, clamp t = t := by
    intro t ht
    rw [hclamp]
    simp only
    rw [min_eq_right ht.2, max_eq_right ht.1]
  set u : ℝ → ℂ := fun t => f' (clamp t) / f (clamp t) with hu
  have hcont : Continuous u := hcontOn.comp_continuous hclampCont hclampMem
  have hueq : ∀ t ∈ Icc a b, u t = f' t / f t := by
    intro t ht
    rw [hu]
    simp only
    rw [hclampEq t ht]
  set L : ℝ → ℂ := fun τ => Complex.log (f a) + ∫ t in a..τ, u t with hL
  have hLderiv : ∀ τ, HasDerivAt L (u τ) τ := by
    intro τ
    have hint : HasDerivAt (fun x => ∫ t in a..x, u t) (u τ) τ := by
      refine intervalIntegral.integral_hasDerivAt_right
        (hcont.intervalIntegrable a τ) ?_ hcont.continuousAt
      exact (hcont.stronglyMeasurableAtFilter _ _)
    simpa [hL] using hint.const_add (Complex.log (f a))
  have hLcont : ContinuousOn L (Icc a b) :=
    fun τ _ => (hLderiv τ).continuousAt.continuousWithinAt
  refine ⟨L, hLcont, fun τ hτ => by rw [← hueq τ hτ]; exact hLderiv τ, ?_⟩
  set g : ℝ → ℂ := fun τ => f τ * Complex.exp (-L τ) with hg
  have hgderiv : ∀ τ ∈ Icc a b, HasDerivAt g 0 τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun x => Complex.exp (-L x))
        (Complex.exp (-L τ) * (-(u τ))) τ := by
      have h := ((hLderiv τ).neg).cexp
      simpa [mul_comm] using h
    have h2 := (hf τ hτ).mul h1
    have hfne : f τ ≠ 0 := hne τ hτ
    refine h2.congr_deriv ?_
    rw [hueq τ hτ]
    field_simp
    ring
  have hgcont : ContinuousOn g (Icc a b) := by
    refine ContinuousOn.mul (fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt) ?_
    exact Complex.continuous_exp.comp_continuousOn hLcont.neg
  have hgconst : ∀ τ ∈ Icc a b, g τ = g a := by
    refine constant_of_has_deriv_right_zero hgcont ?_
    intro τ hτ
    exact ((hgderiv τ ⟨hτ.1, le_of_lt hτ.2⟩).hasDerivWithinAt)
  have hga : g a = 1 := by
    have hfa : f a ≠ 0 := hne a ⟨le_rfl, hab⟩
    have hLa : L a = Complex.log (f a) := by simp [hL]
    rw [hg]
    simp only [hLa]
    rw [Complex.exp_neg, Complex.exp_log hfa]
    field_simp
  intro τ hτ
  have h := hgconst τ hτ
  rw [hga, hg] at h
  simp only at h
  have hexp : Complex.exp (-L τ) ≠ 0 := Complex.exp_ne_zero _
  have hmul : f τ * Complex.exp (-L τ) * Complex.exp (L τ) = Complex.exp (L τ) := by
    rw [h, one_mul]
  rw [mul_assoc, ← Complex.exp_add] at hmul
  simpa using hmul

/-- **Continuous polar form along a segment.**  The real part of a differentiable, nowhere-zero
complex function of a real variable is `ρ·cos ψ` with `ρ > 0` and `ψ` continuous — the exact shape
`exists_sign_chain_of_phase_increase` consumes. -/
theorem exists_continuousOn_polar {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ}
    (hf : ∀ τ ∈ Icc a b, HasDerivAt f (f' τ) τ)
    (hcont : ContinuousOn (fun τ => f' τ / f τ) (Icc a b))
    (hne : ∀ τ ∈ Icc a b, f τ ≠ 0) :
    ∃ r ψ : ℝ → ℝ, ContinuousOn ψ (Icc a b) ∧ (∀ τ ∈ Icc a b, 0 < r τ) ∧
      (∀ τ ∈ Icc a b, HasDerivAt ψ ((f' τ / f τ).im) τ) ∧
      (∀ τ ∈ Icc a b, (f τ).re = r τ * Real.cos (ψ τ)) := by
  obtain ⟨L, hLcont, hLderiv, hLeq⟩ := exists_continuousOn_log_of_hasDerivAt hab hf hcont hne
  refine ⟨fun τ => Real.exp (L τ).re, fun τ => (L τ).im, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_im.comp_continuousOn hLcont
  · intro τ _
    exact Real.exp_pos _
  · intro τ hτ
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hLderiv τ hτ))
  · intro τ hτ
    rw [hLeq τ hτ, Complex.exp_re]

/-- **The phase advance is the integral of the imaginary part of the logarithmic derivative.**
Together with `exists_continuousOn_polar` this turns a bound on `∫ Im(f'/f)` into a bound on the
number of sign changes of `Re f`. -/
theorem exists_continuousOn_polar_advance {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ}
    (hf : ∀ τ ∈ Icc a b, HasDerivAt f (f' τ) τ)
    (hcont : ContinuousOn (fun τ => f' τ / f τ) (Icc a b))
    (hne : ∀ τ ∈ Icc a b, f τ ≠ 0) :
    ∃ r ψ : ℝ → ℝ, ContinuousOn ψ (Icc a b) ∧ (∀ τ ∈ Icc a b, 0 < r τ) ∧
      (∀ τ ∈ Icc a b, (f τ).re = r τ * Real.cos (ψ τ)) ∧
      ψ b - ψ a = ∫ τ in a..b, (f' τ / f τ).im := by
  obtain ⟨r, ψ, hψc, hrpos, hψd, hpolar⟩ := exists_continuousOn_polar hab hf hcont hne
  refine ⟨r, ψ, hψc, hrpos, hpolar, ?_⟩
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntervalIntegrable (fun τ => (f' τ / f τ).im) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact Complex.continuous_im.comp_continuousOn hcont
  have hd : ∀ x ∈ uIcc a b, HasDerivAt ψ ((f' x / f x).im) x := by
    rw [huIcc]; exact hψd
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint).symm

end RHTower

end
