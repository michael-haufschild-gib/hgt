import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound
import Mathlib.NumberTheory.LSeries.Dirichlet
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Combining the five inputs

The three-four-one inequality bounds `log‖ζ(σ+it)‖` from below in terms of the values at `σ` and at
`σ+2it`.  Feeding in the real-axis bound and a bound at `σ+2it` turns it into an explicit positive
lower bound for `‖ζ(σ+it)‖`; a hypothetical zero at `β+it` makes `‖ζ(σ+it)‖` at most `M(σ−β)`, and
the two together bound `σ − β` from below.

That is the shape of the classical zero-free region: the free parameters are the offset `σ − 1` and
the derivative bound `M`, and optimising them against the growth of `B₀` in `t` produces
`β ≤ 1 − c/log t`.
-/

namespace RHTower.Sieve

open Complex

/-- **The lower bound at the shifted point.** -/
theorem exp_le_norm_riemannZeta_shift {σ t B₀ : ℝ} (hσ : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀) :
    Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)
      ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hbase := three_four_one_log_zeta_const (σ := σ) (t := t) hσ
  have hA := log_norm_riemannZeta_real_le hσ
  have hBlog : Real.log ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ Real.log B₀ := by
    have hpos : 0 < ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ := by
      refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re ?_)
      have hre : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
      rw [hre]
      linarith
    exact Real.log_le_log hpos hB
  have hlow : (-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    linarith
  have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re ?_)
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    linarith
  calc Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)
      ≤ Real.exp (Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖) :=
        Real.exp_le_exp.2 hlow
    _ = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := Real.exp_log hzpos

/-- **The zero-free combination.**  A zero at `β + it` forces `σ − β` to be at least an explicit
positive quantity. -/
theorem le_mul_sub_of_riemannZeta_eq_zero {σ β t M B₀ : ℝ} (hσ : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀)
    (hzero : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (σ - β)) :
    Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) ≤ M * (σ - β) :=
  le_trans (exp_le_norm_riemannZeta_shift hσ hB) hzero

/-- **The reciprocal bound.**  The lower bound for `‖ζ‖` off the real axis inverts to an explicit
upper bound for `‖1/ζ‖`, which is the shape a Perron-type argument consumes. -/
theorem norm_inv_riemannZeta_le {σ t B₀ : ℝ} (hσ : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀) :
    ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
      ≤ Real.exp (-((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)) := by
  have hlow := exp_le_norm_riemannZeta_shift hσ hB
  have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re ?_)
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    linarith
  rw [norm_inv, Real.exp_neg]
  rw [inv_le_inv₀ hzpos (Real.exp_pos _)]
  exact hlow

/-- **The Möbius L-series is the reciprocal of zeta.**  From mathlib's product identity and the
nonvanishing on `re s > 1`. -/
theorem LSeries_moebius_eq_inv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hprod := LSeries_one_mul_Lseries_moebius hs
  have hone : LSeries 1 s = riemannZeta s := LSeries_one_eq_riemannZeta hs
  rw [hone] at hprod
  field_simp at hprod ⊢
  linear_combination hprod

/-- **A bound for the Möbius L-series.** -/
theorem norm_LSeries_moebius_le {σ t B₀ : ℝ} (hσ : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀) :
    ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (-((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)) := by
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [LSeries_moebius_eq_inv (by rw [hre]; exact hσ)]
  exact norm_inv_riemannZeta_le hσ hB

/-- **A uniform bound for the Möbius L-series.**  Using the trivial bound at the doubled frequency,
the estimate becomes independent of the height. -/
theorem norm_LSeries_moebius_le_uniform {σ t : ℝ} (hσ : 1 < σ) :
    ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1)) := by
  have hre2 : ((σ : ℂ) + (2 * t : ℂ) * Complex.I).re = σ := by simp
  have hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ 1 + 1 / (σ - 1) := by
    have h := norm_riemannZeta_le (s := (σ : ℂ) + (2 * t : ℂ) * Complex.I) (by rw [hre2]; exact hσ)
    rwa [hre2] at h
  have hbase := norm_LSeries_moebius_le hσ hB
  refine le_trans hbase (le_of_eq ?_)
  have hpos : (0 : ℝ) < 1 + 1 / (σ - 1) := by
    have : (0 : ℝ) < σ - 1 := by linarith
    positivity
  rw [show -((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log (1 + 1 / (σ - 1))) / 4)
      = 22 / 4 + Real.log (1 + 1 / (σ - 1)) by ring]
  rw [Real.exp_add, Real.exp_log hpos]

end RHTower.Sieve
