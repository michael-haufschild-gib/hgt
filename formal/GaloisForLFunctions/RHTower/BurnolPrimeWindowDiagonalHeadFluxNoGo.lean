import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux

/-!
# Positive ordinary-prime diagonal head flux in the right half-strip

For the source window `[1/p,1]`, the two retained reciprocal-head sizes are `p-1` and `log p`.
This module proves that their diagonal current is strictly positive at every point of the open
right half of the critical strip, for every ordinary prime.  Hence no nonzero finite combination
with nonnegative prime-diagonal weights can supply the missing pre-polar nonpositive current.

The obstruction is unconditional and precedes Xi landing: cancellation must use a signed
off-diagonal or singular/domain-sensitive source law.
-/

open Complex Real
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Prime-`p` source-window diagonal current, with retained head sizes `p-1` and `log p`. -/
def burnolPrimeWindowDiagonalHeadFlux (p : ℕ) (rho : ℂ) : ℝ :=
  ((p : ℝ) - 1) ^ (2 : ℕ) * ‖((1 : ℂ) - rho)⁻¹‖ ^ (2 : ℕ) -
    (Real.log p) ^ (2 : ℕ) * ‖rho⁻¹‖ ^ (2 : ℕ)

/-- Every ordinary-prime diagonal channel has the wrong strict sign in the open right half-strip. -/
theorem burnolPrimeWindowDiagonalHeadFlux_pos
    {p : ℕ} (hp : Nat.Prime p) {rho : ℂ}
    (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    0 < burnolPrimeWindowDiagonalHeadFlux p rho := by
  have hrho : rho ≠ 0 := by
    intro hz
    rw [hz] at hright
    norm_num at hright
  have hrhoOne : rho ≠ 1 := by
    intro hz
    rw [hz] at hlt
    norm_num at hlt
  let x : ℝ := ‖rho‖
  let y : ℝ := ‖(1 : ℂ) - rho‖
  let P : ℝ := (p : ℝ) - 1
  let L : ℝ := Real.log p
  have hx : 0 < x := norm_pos_iff.mpr hrho
  have hy : 0 < y := norm_pos_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  have hxy : y < x := by
    have hgain := one_lt_norm_burnolCartierForwardHeadGain hright hlt
    unfold burnolCartierForwardHeadGain at hgain
    rw [norm_div, norm_conj, one_lt_div hy] at hgain
    exact hgain
  have hpReal : (1 : ℝ) < p := by
    exact_mod_cast hp.two_le
  have hP : 0 < P := by
    dsimp [P]
    linarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hpReal
  have hLP : L < P := by
    dsimp [L, P]
    exact Real.log_lt_sub_one_of_pos (by positivity) (ne_of_gt hpReal)
  have hinv : x⁻¹ < y⁻¹ := (inv_lt_inv₀ hx hy).2 hxy
  have hfirst : L * x⁻¹ < L * y⁻¹ := mul_lt_mul_of_pos_left hinv hL
  have hsecond : L * y⁻¹ < P * y⁻¹ := mul_lt_mul_of_pos_right hLP (inv_pos.mpr hy)
  have hstrict : L * x⁻¹ < P * y⁻¹ := hfirst.trans hsecond
  have hleftNonneg : 0 ≤ L * x⁻¹ := mul_nonneg hL.le (inv_pos.mpr hx).le
  have hrightNonneg : 0 ≤ P * y⁻¹ := mul_nonneg hP.le (inv_pos.mpr hy).le
  unfold burnolPrimeWindowDiagonalHeadFlux
  rw [norm_inv, norm_inv]
  change 0 < P ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) - L ^ (2 : ℕ) * x⁻¹ ^ (2 : ℕ)
  nlinarith [sq_nonneg (P * y⁻¹), sq_nonneg (L * x⁻¹)]

/-- Any nonempty finite nonnegative diagonal prime combination remains strictly positive. -/
theorem burnolPrimeWindowDiagonalHeadFlux_finset_sum_pos
    {S : Finset Nat.Primes} (hS : S.Nonempty) (w : Nat.Primes → ℝ)
    (hw : ∀ p ∈ S, 0 < w p) {rho : ℂ}
    (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    0 < ∑ p ∈ S, w p * burnolPrimeWindowDiagonalHeadFlux p rho := by
  apply Finset.sum_pos
  · intro p hpS
    exact mul_pos (hw p hpS)
      (burnolPrimeWindowDiagonalHeadFlux_pos p.prop hright hlt)
  · simpa using hS

/-- Xi-support specialization: every ordinary-prime diagonal port is strictly positive at a
hypothetical right-half divisor. -/
theorem xiDivisor_burnolPrimeWindowDiagonalHeadFlux_pos
    (p : Nat.Primes) (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    0 < burnolPrimeWindowDiagonalHeadFlux p (rho : ℂ) :=
  burnolPrimeWindowDiagonalHeadFlux_pos p.prop hright
    (xiDivisor_re_lt_one_of_half_lt rho hright)

end RHTower
