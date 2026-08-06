import GaloisForLFunctions.RHTower.Sieve.ZetaThreeFourOne
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The three-four-one inequality for the logarithmic derivative

For `Re s > 1` the logarithmic derivative of `ζ` is the von Mangoldt Dirichlet series,
`-ζ'/ζ (s) = ∑ Λ(n) n^(-s)`, whose terms have real part `Λ(n) n^(-σ) cos(t log n)`.  Since
`Λ(n) ≥ 0` and

`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`,

the same combination that bounds `|ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)|` from below bounds the logarithmic
derivatives:

`0 ≤ 3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it))`.

This is the form de la Vallée Poussin's argument consumes; the modulus form loses the factor that
the derivative form keeps.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The three-four-one weight applied to a nonnegative amplitude. -/
theorem zero_le_three_four_one_scalar {a E θ : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E) :
    0 ≤ 3 * (a * (E * 1)) + 4 * (a * (E * Real.cos θ)) + a * (E * Real.cos (2 * θ)) := by
  have hkey : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
    rw [Real.cos_two_mul]; ring
  have hfactor : 3 * (a * (E * 1)) + 4 * (a * (E * Real.cos θ)) + a * (E * Real.cos (2 * θ))
      = a * E * (3 + 4 * Real.cos θ + Real.cos (2 * θ)) := by ring
  rw [hfactor, hkey]
  positivity

/-- The real part of a von Mangoldt Dirichlet term. -/
theorem re_lseries_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n).re
      = vonMangoldt n * (Real.exp (-(Real.log n) * s.re) * Real.cos (Real.log n * s.im)) := by
  have hne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hdiv : ((vonMangoldt n : ℝ) : ℂ) / ((n : ℕ) : ℂ) ^ s
      = ((vonMangoldt n : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (-s) := by
    rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [LSeries.term_def, if_neg hn, hdiv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [re_prime_cpow_neg (Nat.pos_of_ne_zero hn) s]

/-- The three-four-one combination of von Mangoldt terms is nonnegative. -/
theorem zero_le_three_four_one_vonMangoldt_term (n : ℕ) {σ t : ℝ} :
    0 ≤ 3 * (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) ((σ : ℂ)) n).re
      + 4 * (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
              ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
              ((σ : ℂ) + (2 * t : ℂ) * Complex.I) n).re := by
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp [LSeries.term]
  · have hre0 : ((σ : ℂ)).re = σ := by simp
    have him0 : ((σ : ℂ)).im = 0 := by simp
    have hre1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    have him1 : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have hre2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
    have him2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).im = 2 * t := by simp
    rw [re_lseries_term_vonMangoldt h, re_lseries_term_vonMangoldt h,
      re_lseries_term_vonMangoldt h, hre0, him0, hre1, him1, hre2, him2]
    have hzero : Real.log n * 0 = 0 := by ring
    have hdouble : Real.log n * (2 * t) = 2 * (Real.log n * t) := by ring
    rw [hzero, hdouble, Real.cos_zero]
    exact zero_le_three_four_one_scalar vonMangoldt_nonneg (Real.exp_nonneg _)

/-- The real parts of the von Mangoldt terms are summable. -/
theorem summable_re_lseries_term_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n).re :=
  (LSeriesSummable_vonMangoldt hs).map Complex.reAddGroupHom Complex.continuous_re

/-- The real part of the von Mangoldt `L`-series is the series of real parts. -/
theorem re_lseries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun m => ((vonMangoldt m : ℝ) : ℂ)) s).re
      = ∑' n : ℕ, (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n).re :=
  Complex.re_tsum (LSeriesSummable_vonMangoldt hs)

/-- **The three-four-one inequality for the logarithmic derivative.** -/
theorem zero_le_three_four_one_logDeriv {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)
              / riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)).re := by
  have hre0 : ((σ : ℂ)).re = σ := by simp
  have hre1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hre2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
  have h0 : (1 : ℝ) < ((σ : ℂ)).re := by rw [hre0]; exact hσ
  have h1 : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by rw [hre1]; exact hσ
  have h2 : (1 : ℝ) < ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re := by rw [hre2]; exact hσ
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h0,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div h2,
    re_lseries_vonMangoldt h0, re_lseries_vonMangoldt h1, re_lseries_vonMangoldt h2]
  have s0 := summable_re_lseries_term_vonMangoldt h0
  have s1 := summable_re_lseries_term_vonMangoldt h1
  have s2 := summable_re_lseries_term_vonMangoldt h2
  have hcomb : 3 * (∑' n : ℕ, (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) ((σ : ℂ)) n).re)
      + 4 * (∑' n : ℕ, (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
          ((σ : ℂ) + (t : ℂ) * Complex.I) n).re)
      + (∑' n : ℕ, (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
          ((σ : ℂ) + (2 * t : ℂ) * Complex.I) n).re)
      = ∑' n : ℕ,
          (3 * (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) ((σ : ℂ)) n).re
            + 4 * (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
                ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
            + (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
                ((σ : ℂ) + (2 * t : ℂ) * Complex.I) n).re) := by
    rw [((s0.mul_left 3).add (s1.mul_left 4)).tsum_add s2,
      (s0.mul_left 3).tsum_add (s1.mul_left 4), s0.tsum_mul_left, s1.tsum_mul_left]
  rw [hcomb]
  exact tsum_nonneg fun n => zero_le_three_four_one_vonMangoldt_term n

/-- **The usable form.**  Upper bounds at `σ` and at `σ + 2it` give an upper bound for
`-Re ζ'/ζ` at `σ + it`, with the factor `4` that the modulus form loses. -/
theorem re_logDeriv_shift_le {σ t A B : ℝ} (hσ : 1 < σ)
    (hA : (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re ≤ A)
    (hB : (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)
            / riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)).re ≤ B) :
    -(3 * A + B) / 4
      ≤ (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hbase := zero_le_three_four_one_logDeriv (σ := σ) (t := t) hσ
  linarith

end RHTower.Sieve
