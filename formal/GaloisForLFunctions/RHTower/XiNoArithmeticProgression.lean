import GaloisForLFunctions.RHTower.PutnamJumpBlowUp
import GaloisForLFunctions.RHTower.SamplingProgressionCriterion
import GaloisForLFunctions.RHTower.XiSamplingIdealizerCollapse

/-!
# The critical zeros contain no one-sided arithmetic progression

Putnam's periodisation turns a one-sided arithmetic progression of critical zeros into the vanishing
of every Fourier coefficient of nonnegative index of the periodised kernel, which is impossible
because the periodisation has a nonzero jump at the origin.  The real Xi divisor therefore contains
no infinite arithmetic progression, and the sampling idealizer of the prime-modulated Weyl algebra
collapses unconditionally.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- **Putnam's theorem.**  For every real phase `a` and every positive step `d` there is a
nonnegative integer `n` with `ζ(1/2 + i(a + dn)) ≠ 0`. -/
theorem exists_riemannZeta_critical_ne_zero {a d : ℝ} (hd : 0 < d) :
    ∃ n : ℕ, riemannZeta (1 / 2 + ((a + d * (n : ℕ) : ℝ) : ℂ) * I) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_fourierCoeff_ne_zero (a := a) hd
  refine ⟨n, fun hz => hn ?_⟩
  have h := integral_putnamPeriodization_fourier (a := a) hd (n : ℤ)
  have h2 : (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x)
      = -riemannZeta (1 / 2 + ((a + d * ((n : ℤ) : ℝ) : ℝ) : ℂ) * I)
          / (1 / 2 + ((a + d * ((n : ℤ) : ℝ) : ℝ) : ℂ) * I) := by
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => rfl)
  rw [h2, show ((a + d * ((n : ℤ) : ℝ) : ℝ) : ℂ) = ((a + d * (n : ℕ) : ℝ) : ℂ) by push_cast; ring,
    hz]
  simp

/-- **The real Xi divisor contains no infinite one-sided arithmetic progression.** -/
theorem xiRealDivisor_no_progression :
    ∀ b k : ℝ, 0 < k → ∃ n : ℕ, b + (n : ℝ) * k ∉ xiRealDivisor := by
  intro b k hk
  obtain ⟨n, hn⟩ := exists_riemannZeta_critical_ne_zero (a := b) hk
  refine ⟨n, fun hmem => hn ?_⟩
  rw [xiRealDivisor, Set.mem_setOf_eq, XiC] at hmem
  have hpt : ((b + (n : ℝ) * k : ℝ) : ℂ) = ((b + k * (n : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hpt] at hmem
  have hre : (0 : ℝ) < (1 / 2 + ((b + k * (n : ℕ) : ℝ) : ℂ) * I).re := by
    simp [Complex.add_re, Complex.mul_re]
  have hne1 : (1 / 2 + ((b + k * (n : ℕ) : ℝ) : ℂ) * I) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hr
  exact (xi_eq_zero_iff hre hne1).mp hmem

/-- **Equation (23) of the prime-modulated Weyl idealizer card, unconditionally.**  The sampling
idealizer of the prime-modulated Weyl algebra on the real Xi divisor collapses to the scalars. -/
theorem xiSamplingIdealizer_collapse_unconditional {m : ℕ} {F : Finset ℝ} {a : ℝ → ℕ → Polynomial ℂ}
    (h0 : (0 : ℝ) ∈ F) (hpres : PreservesSamplingIdeal m xiRealDivisor F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 :=
  xiSamplingIdealizer_collapse_of_no_progression xiRealDivisor_no_progression h0 hpres

/-- **The sampling quotient sees only polynomial multiplication.**  A finite shift--Weyl operator
that descends to the real Xi sampling quotient acts there as multiplication by its constant-shift
zeroth coefficient. -/
theorem xiSamplingIdealizer_eq_polynomial_multiplier_unconditional {m : ℕ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ} (h0 : (0 : ℝ) ∈ F)
    (hpres : PreservesSamplingIdeal m xiRealDivisor F a) (φ : ℝ → ℂ) (x : ℝ) :
    shiftWeylEval m F a φ x = (a 0 0).eval (x : ℂ) * φ x :=
  shiftWeylEval_eq_polynomial_multiplier h0 (xiSamplingIdealizer_collapse_unconditional h0 hpres) φ x

end RHTower

end
