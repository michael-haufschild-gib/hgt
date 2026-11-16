import GaloisForLFunctions.BlackHoleRingdown.ThePositiveEulerTwinsArePassive
import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses

/-!
# Positive Euler twins without real zeros

The reciprocal positive Euler multiplier is strictly positive on the real axis.
Its entire completion therefore retains Xi's real-axis positivity while adding
off-critical zeros. This persists beyond every finite prefix of zeta's ordinary
coefficients, with bounded positive multiplicative coefficients and passive
scattering. Real-axis nonvanishing does not supply an arithmetic separator for
these models; their logarithmic coefficients still fail nonnegativity.
-/

noncomputable section
open Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open SelbergClass.PositiveFiniteEuler BlackHoleRingdown.PositiveEulerHorizon

/-- The completed local factor is a positive real sum at every real argument. -/
theorem positiveEuler_completedFactor_ofReal (p : ℕ) (A x : ℝ) :
    completedFactor p A (x : ℂ) =
      (((p : ℝ) ^ x + A + (p : ℝ) ^ (1-x) : ℝ) : ℂ) := by
  have he (y : ℝ) : (p : ℂ) ^ (y : ℂ) = (((p : ℝ) ^ y : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (Nat.cast_nonneg (α := ℝ) p) y).symm
  rw [completedFactor, show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,
    he x, he (1-x)]
  simp only [Complex.ofReal_add]

/-- A positive ordinary Euler edit preserves strict positivity of Xi on the real axis. -/
theorem positiveEuler_completedXi_real_pos {p : ℕ} (hp : 0 < p) {A : ℝ}
    (hA : 0 ≤ A) (x : ℝ) : 0 < (completedXi p A (x : ℂ)).re := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [completedXi, positiveEuler_completedFactor_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos
    (add_pos (add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hpR x) hA)
      (Real.rpow_pos_of_pos hpR (1-x))) (_root_.RHTower.XiGlobalKummer.xi_real_pos x)

private theorem nonneg_middle_of_prime_coeff {p : ℕ} (hp : p.Prime) {A : ℝ}
    (hcoeff : 1 ≤ (arithmeticCoeffs p A p).re) : 0 ≤ A := by
  have hnot : ¬ p^2 ∣ p := by
    intro h
    have hle := Nat.le_of_dvd hp.pos h
    nlinarith only [hle, hp.two_le]
  simp only [arithmeticCoeffs_apply, Complex.ofReal_re, coeff,
    if_neg hp.ne_zero, if_pos (dvd_refl p), if_neg hnot, add_zero] at hcoeff
  linarith only [hcoeff]

/-- Real-axis positivity, a reflected entire completion, positive bounded ordinary
coefficients and passive scattering coexist with off-critical zeros after every finite prefix.
The same model fails the nonnegative logarithmic coefficient test. -/
theorem exists_positive_euler_twin_without_real_zeros (N : ℕ)
    (σ : Set.Ioo (1/2 : ℝ) 1) :
    ∃ (p : ℕ) (hp : p.Prime) (A : ℝ), N < p ∧ 0 ≤ A ∧
      (arithmeticCoeffs p A).IsMultiplicative ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (arithmeticCoeffs p A n).im = 0 ∧
        1 ≤ (arithmeticCoeffs p A n).re ∧ ‖arithmeticCoeffs p A n‖ ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n ≤ N → arithmeticCoeffs p A n = 1) ∧
      Differentiable ℂ (completedXi p A) ∧
      (∀ s : ℂ, completedXi p A (1-s) = completedXi p A s) ∧
      (∀ x : ℝ, 0 < (completedXi p A (x : ℂ)).re) ∧
      (∃ s : ℂ, s.re = σ ∧ completedXi p A s = 0 ∧ (extendedClass hp A) s = 0) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖reducedScattering p A w‖ ≤ 1) ∧
      (¬ ∃ b : ℕ → ℂ, (∀ n : ℕ, 0 ≤ (b n).re) ∧ ∃ B : ℝ,
        ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
          Complex.exp (LSeries b s) = localFactor p A s * riemannZeta s) := by
  obtain ⟨p,hp,A,hpN,_,hm,hcoeff,hprefix,_,hlog,hzero,hpass,_,_⟩ :=
    exists_positive_passive_twin N σ
  have hA : 0 ≤ A :=
    nonneg_middle_of_prime_coeff hp (hcoeff.choose_spec p hp.ne_zero).2.1
  exact ⟨p,hp,A,hpN,hA,hm,hcoeff,hprefix,
    differentiable_completedXi hp.ne_zero A,completedXi_one_sub p A,
    positiveEuler_completedXi_real_pos hp.pos hA,hzero,
    fun w hw => (hpass w hw).2.1,hlog⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
