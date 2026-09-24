import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity

/-!
# Two-ray decay forces infinitely many zeros below order two

A finite-zero subquadratic entire function is a finite divisor times one exponential
character.  On opposite real rays, the two exponential norms cancel, while the
finite divisor has norm at least one outside a fixed ball.  Thus a nonzero such
function cannot decay to zero on both rays.  This form is useful for Fourier
transforms of positive kernels with super-Gaussian decay.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower

theorem zeroSet_infinite_of_subquadratic_twoRayDecay
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a))
    (hplus : Tendsto (fun r : ℝ => ‖f (r : ℂ)‖) atTop (𝓝 0))
    (hminus : Tendsto (fun r : ℝ => ‖f ((-r : ℝ) : ℂ)‖) atTop (𝓝 0)) :
    {z : ℂ | f z = 0}.Infinite := by
  classical
  intro hfinite
  obtain ⟨t, m, c, B, hc, hform, _⟩ :=
    exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet
      hf ha0 ha2 hC hg hfinite
  let R : ℝ := 1 + ∑ w ∈ t, ‖w‖
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hcp : 0 < ‖c‖ ^ (2 : ℕ) := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hc)
  have hdecay : Tendsto
      (fun r : ℝ => ‖f (r : ℂ)‖ * ‖f ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) :=
    by simpa using hplus.mul hminus
  have hsmall : ∀ᶠ r : ℝ in atTop,
      ‖f (r : ℂ)‖ * ‖f ((-r : ℝ) : ℂ)‖ < ‖c‖ ^ (2 : ℕ) :=
    hdecay.eventually (gt_mem_nhds hcp)
  obtain ⟨r, hsmallr, hr⟩ :=
    Filter.Eventually.exists (hsmall.and (eventually_ge_atTop R))
  have hr0 : 0 ≤ r := hR0.trans hr
  have hpr : 1 ≤ ‖finiteDivisorFactor t m (r : ℂ)‖ := by
    apply one_le_norm_finiteDivisorFactor_of_far t m
    simpa only [R, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr
  have hpm : 1 ≤ ‖finiteDivisorFactor t m ((-r : ℝ) : ℂ)‖ := by
    apply one_le_norm_finiteDivisorFactor_of_far t m
    simpa only [R, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg hr0] using hr
  have hexp : ‖Complex.exp (B * (r : ℂ))‖ *
      ‖Complex.exp (B * ((-r : ℝ) : ℂ))‖ = 1 := by
    rw [← norm_mul, ← Complex.exp_add]
    have hzero : B * (r : ℂ) + B * ((-r : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [hzero, Complex.exp_zero, norm_one]
  have hprod :
      ‖f (r : ℂ)‖ * ‖f ((-r : ℝ) : ℂ)‖ =
        (‖finiteDivisorFactor t m (r : ℂ)‖ *
          ‖finiteDivisorFactor t m ((-r : ℝ) : ℂ)‖) * ‖c‖ ^ (2 : ℕ) := by
    calc
      _ = (‖finiteDivisorFactor t m (r : ℂ)‖ *
            ‖finiteDivisorFactor t m ((-r : ℝ) : ℂ)‖) * ‖c‖ ^ (2 : ℕ) *
            (‖Complex.exp (B * (r : ℂ))‖ *
              ‖Complex.exp (B * ((-r : ℝ) : ℂ))‖) := by
          rw [hform, hform]
          simp only [norm_mul]
          ring
      _ = _ := by rw [hexp, mul_one]
  have hmul : 1 ≤ ‖finiteDivisorFactor t m (r : ℂ)‖ *
      ‖finiteDivisorFactor t m ((-r : ℝ) : ℂ)‖ := by
    nlinarith
  rw [hprod] at hsmallr
  nlinarith

end RHTower
