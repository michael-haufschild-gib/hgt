import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCompletion
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerZeros
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerProduct
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Positive multiplicative twins beyond every prescribed prefix

A reciprocal quadratic at a prime beyond the prescribed prefix gives a
degree-one extended Selberg series with a zero at any prescribed real
part strictly between `1/2` and `1`.
Every coefficient is real, positive and uniformly bounded. Its Euler
logarithm converges on `Re s > 1` and obeys an `n^σ` bound. The strict
square-root bound excludes every full Selberg presentation.
-/

noncomputable section
open Complex
namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- Every finite zeta coefficient prefix extends to a positive multiplicative
degree-one series with a zero strictly to the right of the critical line. -/
theorem exists_positive_multiplicative_euler_twin_at (N : ℕ) (σ : ℝ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ F : RHTower.ExtendedSelbergClass, F.presentationDegree = 1 ∧
      F.coeff.IsMultiplicative ∧ F.coeff 1 = 1 ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (F.coeff n).im = 0 ∧ 1 ≤ (F.coeff n).re ∧ (F.coeff n).re ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n ≤ N → F.coeff n = 1) ∧
      (∃ s : ℂ, s.re = σ ∧ F s = 0) ∧
      (∃ b : ArithmeticFunction ℂ,
        (∀ n : ℕ, b n ≠ 0 → IsPrimePow n) ∧
        (∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ 3 * (n : ℝ) ^ σ) ∧
        ∀ s : ℂ, 1 < s.re →
          LSeriesSummable b s ∧ Complex.exp (LSeries b s) = F s) ∧
      ¬ ∃ G : RHTower.SelbergClass, G.coeff = F.coeff := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  let r : ℝ := Real.exp (σ * Real.log p)
  let q : ℝ := Real.exp ((1 - σ) * Real.log p)
  have hr : 0 < r := Real.exp_pos _
  have hq : 0 < q := Real.exp_pos _
  let A : ℝ := reciprocalParameter p r
  have hA : 0 ≤ A := add_nonneg hr.le (div_nonneg (Nat.cast_nonneg p) hr.le)
  let F := extendedClass hp A
  refine ⟨F, extendedClass_degree hp A, arithmeticCoeffs_isMultiplicative hp A, ?_,
    ⟨1 + A + p, ?_⟩, ?_, ?_, ?_, not_fullClass hp A⟩
  · change arithmeticCoeffs p A 1 = 1
    rw [arithmeticCoeffs_apply, coeff_one hp, Complex.ofReal_one]
  · intro n hn
    change ((coeff p A n : ℝ) : ℂ).im = 0 ∧
      1 ≤ ((coeff p A n : ℝ) : ℂ).re ∧
      ((coeff p A n : ℝ) : ℂ).re ≤ 1 + A + p
    exact ⟨Complex.ofReal_im _, coeff_bounds hA hn⟩
  · intro n hn hnN
    change arithmeticCoeffs p A n = 1
    rw [arithmeticCoeffs_apply, coeff_eq_one_of_lt hn (by omega), Complex.ofReal_one]
  · have hre : (factorZero p r).re = σ := by
      rw [factorZero_re, show Real.log r = σ * Real.log p from Real.log_exp _]
      exact mul_div_cancel_right₀ _ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    refine ⟨factorZero p r, hre, ?_⟩
    have hs : factorZero p r ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hre, Complex.one_re] at this
      exact hσ1.ne this
    change (continuation hp.ne_zero A).value (factorZero p r) = 0
    rw [continuation_eq hp.ne_zero A hs, localFactor_factorZero hp.one_lt hr, zero_mul]
  · have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hpR
    have hrq : r * q = (p : ℝ) := by
      dsimp only [r, q]
      rw [← Real.exp_add, show σ * Real.log p +
        (1 - σ) * Real.log p = Real.log p by ring, Real.exp_log (zero_lt_one.trans hpR)]
    have hpr : (p : ℝ) / r = q := (div_eq_iff hr.ne').mpr (by rw [mul_comm, hrq])
    have hqr : q ≤ r := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith only [hσ0]) hl.le)
    have hrp : r ≤ (p : ℝ) := by
      conv_rhs => rw [← Real.exp_log (zero_lt_one.trans hpR)]
      apply Real.exp_le_exp.mpr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ1.le hl.le
    have hrpow : r = (p : ℝ) ^ σ := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hpR)]
      change Real.exp (σ * Real.log p) = Real.exp (Real.log p * σ)
      congr 1
      ring
    let α : ℂ := -(r : ℂ)
    let β : ℂ := -(q : ℂ)
    have hα : ‖α‖ = r := by
      simp only [α, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hβ : ‖β‖ = q := by
      simp only [β, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    have hadd : α + β = -(A : ℂ) := by
      dsimp only [α, β, A, reciprocalParameter]
      rw [hpr]
      push_cast
      ring
    have hmul : α * β = p := by
      change -(r : ℂ) * -(q : ℂ) = p
      rw [neg_mul_neg, ← Complex.ofReal_mul, hrq, Complex.ofReal_natCast]
    have hαp : ‖α‖ ≤ p := hα.trans_le hrp
    have hβp : ‖β‖ ≤ p := hβ.trans_le (hqr.trans hrp)
    refine ⟨logarithmicCoeffs hp α β, fun n hn => eulerLogCoeff_primePower hp α β hn,
      fun n hn => eulerLogCoeff_bound hp (by linarith only [hσ0]) (hα.trans_le hrpow.le)
        (hβ.trans_le (hqr.trans hrpow.le)) hn, ?_⟩
    intro s hs
    refine ⟨logarithmicCoeffs_summable hp hαp hβp hs, ?_⟩
    change Complex.exp (LSeries (logarithmicCoeffs hp α β) s) =
      (continuation hp.ne_zero A).value s
    rw [logarithmicCoeffs_exp hp hadd hmul hαp hβp hs,
      continuation_eq hp.ne_zero A (by intro h; subst s; norm_num at hs)]

/-- Positive multiplicativity, Ramanujan bounds, the scalar functional equation
and an Euler product do not rule out a zero at real part `3/4`. -/
theorem exists_positive_multiplicative_twin (N : ℕ) :
    ∃ F : RHTower.ExtendedSelbergClass, F.presentationDegree = 1 ∧
      F.coeff.IsMultiplicative ∧ F.coeff 1 = 1 ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (F.coeff n).im = 0 ∧ 1 ≤ (F.coeff n).re ∧ (F.coeff n).re ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n ≤ N → F.coeff n = 1) ∧
      (∃ s : ℂ, s.re = 3 / 4 ∧ F s = 0) ∧
      (∃ b : ArithmeticFunction ℂ,
        (∀ n : ℕ, b n ≠ 0 → IsPrimePow n) ∧
        (∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ 3 * (n : ℝ) ^ (3 / 4 : ℝ)) ∧
        ∀ s : ℂ, 1 < s.re →
          LSeriesSummable b s ∧ Complex.exp (LSeries b s) = F s) ∧
      ¬ ∃ G : RHTower.SelbergClass, G.coeff = F.coeff :=
  exists_positive_multiplicative_euler_twin_at N (3 / 4) (by norm_num) (by norm_num)

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
