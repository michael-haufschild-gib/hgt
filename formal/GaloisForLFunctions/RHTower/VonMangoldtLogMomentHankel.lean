import GaloisForLFunctions.RHTower.VonMangoldtThreeFourOneSeries
import GaloisForLFunctions.HTGeometry.NonnegativeWeightMomentHankel

/-!
# The von Mangoldt log-moment array is unconditionally positive semidefinite

The 3-4-1 inequality forces a sign out of `Lambda(n) >= 0` for one fixed three-point configuration.
The structural upgrade is that the prime weights are a nonnegative measure on the points `log n`,
so **every** power-moment array they generate is positive semidefinite:

`0 <= sum_(j,k<N) a j a k * sum_n Lambda(n) n^(-sigma) (log n)^(j+k)`.

This is matrix positivity of the arithmetic side, valid for every finite configuration of weights,
which is what the 3-4-1 no-go asked for.  The moments are exactly the derivatives of the von
Mangoldt Dirichlet series `-zeta'/zeta` at a real point of the convergence half-plane, so this is
the arithmetic half of the resolvent ladder's entries.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A polynomial weight is dominated by an exponential: `x^n exp (-c x) <= n! / c^n`. -/
theorem pow_mul_exp_neg_le_factorial_div_pow' {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-(c * x)) ≤ (n.factorial : ℝ) / c ^ n := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hcpow : 0 < c ^ n := pow_pos hc n
  have hseries := Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx) n
  rw [div_le_iff₀ hfac] at hseries
  have hneg : 0 ≤ Real.exp (-(c * x)) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hseries hneg
  have hcancel : Real.exp (c * x) * Real.exp (-(c * x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  apply (le_div_iff₀ hcpow).2
  calc
    (x ^ n * Real.exp (-(c * x))) * c ^ n = (c * x) ^ n * Real.exp (-(c * x)) := by
      rw [mul_pow]; ring
    _ ≤ (Real.exp (c * x) * (n.factorial : ℝ)) * Real.exp (-(c * x)) := hmul
    _ = (n.factorial : ℝ) := by
      rw [mul_comm (Real.exp (c * x)) ((n.factorial : ℝ)), mul_assoc, hcancel, mul_one]

/-- The von Mangoldt weight is summable on every convergence line, in real form. -/
theorem summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hc := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by rw [hre]; exact hσ)
  refine ((Complex.hasSum_re hc.hasSum).summable).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact re_lseries_term_vonMangoldt_real hn σ

/-- Every logarithmic moment of the von Mangoldt weight converges on a convergence line. -/
theorem summable_vonMangoldt_logPow {σ : ℝ} (hσ : 1 < σ) (m : ℕ) :
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) * Real.log n ^ m) := by
  set σ' : ℝ := (1 + σ) / 2 with hσ'def
  have hσ'1 : 1 < σ' := by rw [hσ'def]; linarith
  have hgap : 0 < σ - σ' := by rw [hσ'def]; linarith
  refine Summable.of_nonneg_of_le ?_ ?_
    ((summable_vonMangoldt_rpow hσ'1).mul_left
      ((m.factorial : ℝ) / (σ - σ') ^ m))
  · intro n
    have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : 0 ≤ ((n : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h3 : 0 ≤ Real.log n ^ m := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact pow_nonneg (Real.log_natCast_nonneg n) m
    positivity
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlognn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hsplit : ((n : ℝ) ^ (-σ)) = ((n : ℝ) ^ (-σ')) * ((n : ℝ) ^ (-(σ - σ'))) := by
      rw [← Real.rpow_add hnpos]
      ring_nf
    have hexp : ((n : ℝ) ^ (-(σ - σ'))) = Real.exp (-((σ - σ') * Real.log n)) := by
      rw [Real.rpow_def_of_pos hnpos]
      ring_nf
    have hkey : Real.log n ^ m * ((n : ℝ) ^ (-(σ - σ'))) ≤
        (m.factorial : ℝ) / (σ - σ') ^ m := by
      rw [hexp]
      exact pow_mul_exp_neg_le_factorial_div_pow' hgap hlognn m
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hσ'pow : 0 < ((n : ℝ) ^ (-σ')) := Real.rpow_pos_of_pos hnpos _
    calc
      (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ (-σ)) * Real.log n ^ m
          = ((ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ (-σ'))) *
              (Real.log n ^ m * ((n : ℝ) ^ (-(σ - σ')))) := by
            rw [hsplit]; ring
      _ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ (-σ'))) *
              ((m.factorial : ℝ) / (σ - σ') ^ m) := by
            apply mul_le_mul_of_nonneg_left hkey
            positivity
      _ = (m.factorial : ℝ) / (σ - σ') ^ m *
              ((ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ (-σ'))) := by ring

/-- The `m`-th logarithmic moment of the von Mangoldt weight on a convergence line: up to sign,
the `m`-th derivative of the von Mangoldt Dirichlet series at `sigma`. -/
def vonMangoldtWeightLogMoment (m : ℕ) (σ : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.weightMoment
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
    (fun n : ℕ => Real.log n) m

/-- **The arithmetic side supplies matrix positivity.**  For every convergence line and every
finite configuration of real weights, the von Mangoldt logarithmic moment array is positive
semidefinite — the configuration-adaptive successor of the fixed `(3,4,1)` instance. -/
theorem vonMangoldtWeightLogMoment_hankel_nonneg {σ : ℝ} (hσ : 1 < σ) (N : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      a j * a k * vonMangoldtWeightLogMoment (j + k) σ := by
  refine GaloisForLFunctions.HTGeometry.weightMoment_hankel_nonneg ?_ ?_ N a
  · intro n
    have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : 0 ≤ ((n : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  · intro m
    exact summable_vonMangoldt_logPow hσ m

end

end RHTower
