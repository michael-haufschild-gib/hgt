/-
# Deck translations of the covering half-plane `coverPlane c`

The covering half-plane `coverPlane c = exp⁻¹(escapeOpen c) = {Re t > log R}` is invariant under
translation by any purely-imaginary vector (`exp_add_im_mem`). This file packages that as an explicit
homeomorphism `coverPlaneShift`, and records the **deck-invariance** of the `ρ` tower under translation
by integer multiples of the level-`n` vertical period `2ⁿ·2πi` (`rho_period_int_mul`):

    ρ_n(t + k·2ⁿ·2πi) = ρ_n(t)   (as a homeomorphism composed with `ρ_n`).

These are the building blocks — the ones whose "algebra normalization" is the fiddly step — for
assembling evenly-covered neighborhoods of `ρ_n : coverPlane c → escapeLevel c n` (the covering datum
`hcov` consumed by the connected-case winding route in `ConnectedPi1`). The deck group acts by the
homeomorphisms `coverPlaneShift c (k·2ⁿ·2πi)` and `ρ_n` is constant on its orbits.
-/
import GaloisForLFunctions.Bottcher.PeriodDoubling

open Topology

namespace Bottcher

/-- **Translation of `coverPlane c` by a purely-imaginary vector is a homeomorphism.** For `P.re = 0`,
`t ↦ t + P` maps `coverPlane c = {Re t > log R}` to itself (the real part is unchanged), with inverse
`t ↦ t - P`. This is the ambient deck translation of the covering half-plane. -/
noncomputable def coverPlaneShift (c P : ℂ) (hP : P.re = 0) :
    {t : ℂ // t ∈ coverPlane c} ≃ₜ {t : ℂ // t ∈ coverPlane c} where
  toFun t := ⟨(t : ℂ) + P, exp_add_im_mem t.2 hP⟩
  invFun t := ⟨(t : ℂ) - P, by
    rw [sub_eq_add_neg]
    exact exp_add_im_mem t.2 (by rw [Complex.neg_re, hP, neg_zero])⟩
  left_inv t := by apply Subtype.ext; simp
  right_inv t := by apply Subtype.ext; simp
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  continuous_invFun := by apply Continuous.subtype_mk; fun_prop

@[simp] theorem coverPlaneShift_coe (c P : ℂ) (hP : P.re = 0)
    (t : {t : ℂ // t ∈ coverPlane c}) : (coverPlaneShift c P hP t : ℂ) = (t : ℂ) + P := rfl

/-- The level-`n` vertical period vector `2ⁿ·2πi`, whose integer multiples generate the deck group of
`ρ_n`. -/
noncomputable def dyadicPeriodVec (n : ℕ) : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

theorem dyadicPeriodVec_re (n : ℕ) : (dyadicPeriodVec n).re = 0 := vshift_re_zero n

theorem intMul_dyadicPeriodVec_re (n : ℕ) (k : ℤ) : ((k : ℂ) * dyadicPeriodVec n).re = 0 := by
  simp [Complex.mul_re, dyadicPeriodVec_re n]

/-- **Deck-invariance of `ρ_n` under integer vertical periods.** For every integer `k`, the deck
translation by `k·2ⁿ·2πi` is a homeomorphism of `coverPlane c` on whose orbit `ρ_n` is constant:
`ρ_n(shift t) = ρ_n(t)`. This is the regular-covering structure of the `ρ` tower (`rho_period_int_mul`
packaged with `coverPlaneShift`). -/
theorem rho_coverPlaneShift (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) (k : ℤ)
    (t : {t : ℂ // t ∈ coverPlane c}) :
    rho c n (coverPlaneShift c ((k : ℂ) * dyadicPeriodVec n) (intMul_dyadicPeriodVec_re n k) t : ℂ)
      = rho c n (t : ℂ) := by
  show rho c n ((t : ℂ) + (k : ℂ) * dyadicPeriodVec n) = rho c n (t : ℂ)
  exact rho_period_int_mul hc n k t.2

end Bottcher
