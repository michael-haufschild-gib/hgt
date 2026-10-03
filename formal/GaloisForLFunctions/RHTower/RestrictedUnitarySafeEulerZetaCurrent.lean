import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicRelativeIndex
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The safe Euler current is the logarithmic derivative of zeta

The literal safe current `J(t) = ∑_n Λ(n) n^{-(1+t)}` of the restricted-unitary Gamma clock is
`-ζ'(1+t)/ζ(1+t)` for every `t > 0`: it is the von Mangoldt `L`-series on the absolute-convergence
half-plane.
-/

noncomputable section

open Complex

namespace RHTower

theorem natCast_cpow_one_add (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ ((1 + t : ℝ) : ℂ) = ((n * Real.exp (Real.log n * t) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hn0.le,
    Real.rpow_add hn0, Real.rpow_one, Real.rpow_def_of_pos hn0]

/-- **(RUCRI.8)** `J(t) = -ζ'(1+t)/ζ(1+t)` for `t > 0`. -/
theorem restrictedUnitarySafeEulerCurrent_eq_logDeriv_zeta {t : ℝ} (ht : 0 < t) :
    (restrictedUnitarySafeEulerCurrent t : ℂ) =
      -deriv riemannZeta (1 + t) / riemannZeta (1 + t) := by
  have hs : 1 < ((1 + t : ℝ) : ℂ).re := by simp; linarith
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  push_cast at h
  rw [← h, LSeries, restrictedUnitarySafeEulerCurrent, ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [finiteVonMangoldtRealWeight]
  · rw [if_neg hn, show ((1 : ℂ) + t) = ((1 + t : ℝ) : ℂ) by push_cast; ring,
      natCast_cpow_one_add n hn t, finiteVonMangoldtRealWeight]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he : Real.exp (-(Real.log n * t)) = (Real.exp (Real.log n * t))⁻¹ := by
      rw [Real.exp_neg]
    rw [he]
    push_cast
    field_simp

end RHTower
