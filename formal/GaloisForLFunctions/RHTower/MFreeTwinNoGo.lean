import GaloisForLFunctions.RHTower.MFreeTower
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The m-free dilation telescope is one-channel on the right half-plane

For the dyadic telescope, put

`F_k(s) = ζ(2^k s) / ζ(2^(k+1) s)`.

On `Re s > 1/2`, every rung `k >= 1` is nonzero because both scaled arguments lie in
`Re > 1`.  The base rung vanishes exactly where `ζ(s)` vanishes.  Consequently every finite
subproduct avoiding rung zero is zero-free, while every subproduct containing rung zero carries
the entire zeta divisor.

Thus splitting the m-free telescope by even/odd depth, mixed radix, or any finite partition cannot
produce equal-divisor arithmetic twins.  The positive structural conclusion is that every viable
twin or projective channel must contain unscaled prime data; dilation depth alone is maximally
one-channel.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `k`-th scalar quotient in the dyadic m-free zeta telescope. -/
def dyadicMFreeZetaRung (k : ℕ) (s : ℂ) : ℂ :=
  riemannZeta (((2 ^ k : ℕ) : ℂ) * s) /
    riemannZeta (((2 ^ (k + 1) : ℕ) : ℂ) * s)

private theorem natCast_mul_re (n : ℕ) (s : ℂ) :
    ((n : ℂ) * s).re = (n : ℝ) * s.re := by
  simp [Complex.mul_re]

private theorem one_lt_dyadic_mul_re {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    1 < ((((2 ^ k : ℕ) : ℂ) * s).re) := by
  rw [natCast_mul_re]
  have hpowN : 2 ≤ 2 ^ k := by
    simpa using (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hk)
  have hpowR : (2 : ℝ) ≤ (2 ^ k : ℕ) := by
    exact_mod_cast hpowN
  nlinarith

/-- Every positive-depth dyadic m-free rung is zero-free on `Re s > 1/2`. -/
theorem dyadicMFreeZetaRung_ne_zero {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    dyadicMFreeZetaRung k s ≠ 0 := by
  apply div_ne_zero
  · exact riemannZeta_ne_zero_of_one_lt_re (one_lt_dyadic_mul_re hk hs)
  · exact riemannZeta_ne_zero_of_one_lt_re
      (one_lt_dyadic_mul_re (show 1 ≤ k + 1 by omega) hs)

/-- The base rung carries exactly the unscaled zeta zeros on `Re s > 1/2`. -/
theorem dyadicMFreeZetaRung_zero_iff_base {s : ℂ} (hs : 1 / 2 < s.re) :
    dyadicMFreeZetaRung 0 s = 0 ↔ riemannZeta s = 0 := by
  have hden : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.mul_re]
      norm_num
      linarith : 1 < ((2 : ℂ) * s).re)
  have hrung : dyadicMFreeZetaRung 0 s = riemannZeta s / riemannZeta (2 * s) := by
    simp [dyadicMFreeZetaRung]
  rw [hrung]
  exact div_eq_zero_iff.trans (or_iff_left hden)

/-- Every finite depth-subproduct avoiding rung zero is zero-free on the right half-plane. -/
theorem dyadicMFreeZetaSubproduct_ne_zero {K : Finset ℕ} (hzero : 0 ∉ K) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    ∏ k ∈ K, dyadicMFreeZetaRung k s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact dyadicMFreeZetaRung_ne_zero
    (Nat.one_le_iff_ne_zero.mpr fun hk0 => hzero (hk0 ▸ hk)) hs

/-- Every finite depth-subproduct containing rung zero carries every right-half zeta zero. -/
theorem dyadicMFreeZetaSubproduct_eq_zero {K : Finset ℕ} (hzero : 0 ∈ K) {s : ℂ}
    (hs : 1 / 2 < s.re) (hzeta : riemannZeta s = 0) :
    ∏ k ∈ K, dyadicMFreeZetaRung k s = 0 := by
  apply Finset.prod_eq_zero hzero
  exact (dyadicMFreeZetaRung_zero_iff_base hs).mpr hzeta

/-- **Divisor localization.** At a right-half zeta zero, rung zero vanishes and every positive
depth rung is nonzero.  The dilation telescope cannot distribute that divisor among channels. -/
theorem dyadicMFreeZetaTower_divisor_localizes {s : ℂ}
    (hs : 1 / 2 < s.re) (hzeta : riemannZeta s = 0) :
    dyadicMFreeZetaRung 0 s = 0 ∧
      ∀ k : ℕ, 1 ≤ k → dyadicMFreeZetaRung k s ≠ 0 := by
  exact ⟨(dyadicMFreeZetaRung_zero_iff_base hs).mpr hzeta,
    fun k hk => dyadicMFreeZetaRung_ne_zero hk hs⟩

end

end RHTower
