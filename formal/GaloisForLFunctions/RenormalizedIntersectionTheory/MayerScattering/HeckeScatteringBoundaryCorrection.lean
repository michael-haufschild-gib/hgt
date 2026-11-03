import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerKreinLaxPhillipsRealization

/-!
# The Hecke correction of the finite-energy scattering core

The complete period obeys the Lewis relation, but subtracting its scattering powers changes
its Hecke equation. Evaluation at `1` recovers the exact correction. At every upper resonance
this correction is nonzero, so the core used by the Krein realization is not a Hecke eigenvector
with the eigenvalue of the completed period.
-/

noncomputable section
open Complex Set
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerScatteringCore MayerQuadraticCone

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem half_power_product (w : ℂ) :
    (2 : ℂ) ^ (-w) * ((1 / 2 : ℝ) : ℂ) ^ (-w) = 1 := by
  change ((2 : ℝ) : ℂ) ^ (-w) * ((1 / 2 : ℝ) : ℂ) ^ (-w) = 1
  rw [← Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Complex.ofReal_mul]
  norm_num

private theorem power_one_sub (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (a : ℂ) ^ (1 - w) = (a : ℂ) * (a : ℂ) ^ (-w) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'),
    Complex.cpow_one]

/-- The exact Hecke error of the finite-energy core at the inversion-fixed point.
Both the zeta-axis term and the scattering-power term are retained. -/
theorem hecke_mayerPeriodCore_at_one {s : ℂ} (hs : 0 < s.re) (him : 0 < s.im) :
    lewisHeckeT2 s (mayerPeriodCore s) 1 -
        (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * mayerPeriodCore s 1 =
      -2 * (2 : ℂ) ^ (-(2 * s)) * riemannZeta (2 * s) +
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) *
          (1 - 4 * (2 : ℂ) ^ (-(2 * s))) := by
  have hw : 0 < (2 * s).re := by simp; linarith
  have hwi : 0 < (2 * s).im := by simp; linarith
  have hw2 : 2 * s ≠ 2 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcore (a : ℝ) (ha : a ∈ MayerScatteringPeriod.periodSegment) :
      mayerPeriodCore s a = MayerScatteringPeriod.periodValue (2 * s) a -
        riemannZeta (2 * s) * (1 + (a : ℂ) ^ (-(2 * s))) -
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * scatteringPowers (2 * s) a :=
    cauchyKernel_core_period hw hwi ha
  have hperiod := MayerScatteringPeriod.three_term hw hw2
    (a := 1) (by norm_num : (1 : ℝ) ∈ Icc 1 2)
  norm_num only [one_div, Complex.ofReal_ofNat] at hperiod
  have hqr := half_power_product (2 * s)
  have hpow2 : (2 : ℂ) ^ (1 - 2 * s) = 2 * (2 : ℂ) ^ (-(2 * s)) := by
    simpa only [Complex.ofReal_ofNat] using power_one_sub 2 (by norm_num) (2 * s)
  rw [lewisHeckeT2]
  norm_num only [mul_one, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Complex.ofReal_ofNat]
  rw [hcore 2 (by norm_num [MayerScatteringPeriod.periodSegment]),
    hcore (1 / 2) (by norm_num [MayerScatteringPeriod.periodSegment]),
    hcore 1 (by norm_num [MayerScatteringPeriod.periodSegment])]
  simp only [scatteringPowers, hpow2,
    power_one_sub (1 / 2) (by norm_num), Complex.ofReal_ofNat, Complex.ofReal_one,
    Complex.one_cpow, Complex.cpow_neg_one]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    one_div, inv_inv] at hqr hperiod ⊢
  linear_combination -hperiod -
    (riemannZeta (2 * s) + (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) / 2) * hqr

private theorem scattering_hecke_factor_ne_zero {s : ℂ} (hs : s.re < 1 / 2) :
    1 - 4 * (2 : ℂ) ^ (-(2 * s)) ≠ 0 := by
  have hn : ‖(2 : ℂ) ^ (-(2 * s))‖ = (2 : ℝ) ^ (-(2 * s.re)) := by
    change ‖((2 : ℝ) : ℂ) ^ (-(2 * s))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    congr 1
    simp
  have hlow : (1 / 2 : ℝ) < (2 : ℝ) ^ (-(2 * s.re)) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith : (-1 : ℝ) < -(2 * s.re))
    norm_num at h
    exact h
  intro hz
  have hnorm := congrArg norm ((sub_eq_zero.mp hz).symm)
  rw [norm_mul, hn] at hnorm
  norm_num at hnorm
  linarith

/-- Every upper resonance has a nonzero Hecke correction on its finite-energy period core.
Thus the completed period's eigenvalue cannot be assigned to this actual core function. -/
theorem hecke_mayerPeriodCore_at_one_ne {s : ℂ} (hs : s ∈ upperMayerResonances) :
    lewisHeckeT2 s (mayerPeriodCore s) 1 ≠
      (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * mayerPeriodCore s 1 := by
  obtain ⟨him, hres⟩ := hs
  have hzero : riemannZeta (2 * s) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero hres.1 hres.2.1).mp hres
  have hw0 : 0 < (2 * s).re := by simp; linarith [hres.1]
  have hw1 : (2 * s).re < 1 := by simp; linarith [hres.2.1]
  have hden : 2 * s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hres.2.1]
  have hc : 2 * riemannZeta (2 * s - 1) / (2 * s - 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num)
      (MayerScatteringMultiplicity.shifted_zeta_ne_zero hw0 hw1)) hden
  intro heq
  have h := hecke_mayerPeriodCore_at_one hres.1 him
  rw [heq, sub_self, hzero, mul_zero, zero_add] at h
  exact (mul_ne_zero hc (scattering_hecke_factor_ne_zero hres.2.1)) h.symm

#print axioms hecke_mayerPeriodCore_at_one
#print axioms hecke_mayerPeriodCore_at_one_ne

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
