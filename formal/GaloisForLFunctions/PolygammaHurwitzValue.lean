/-
The classical value bridge between positive-order polygamma functions and the Hurwitz zeta in its
complex shift variable.

The project already contains both sides independently: the all-order polygamma recurrence and
far-field decay in `GammaProjectiveBoundary`, and the convergent complex-shift Hurwitz series in
`HurwitzZeta`.  This module identifies their values on the open right half-plane.
-/
import GaloisForLFunctions.GammaProjectiveBoundary
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import GaloisForLFunctions.PolygammaMultiplication
import GaloisForLFunctions.RHTower.PolygammaReflection
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace GaloisForLFunctions

open Complex Filter

/-- **Hurwitz shift recurrence.**  In the convergence half-plane,
`ζ(s,a+1)=ζ(s,a)-a^(-s)`. -/
theorem hzeta_add_one {s : ℂ} (hs : 1 < s.re) (a : ℂ) :
    HurwitzZetaShift.hzeta s (a + 1) =
      HurwitzZetaShift.hzeta s a - a ^ (-s) := by
  have hsum := HurwitzZetaShift.summable_hurwitzSeries hs a
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simp only [HurwitzZetaShift.hzeta]
  have heq : (∑' n : ℕ, ((↑(n + 1) : ℂ) + a) ^ (-s)) =
      ∑' n : ℕ, ((n : ℂ) + (a + 1)) ^ (-s) := by
    apply tsum_congr
    intro n
    congr 1
    push_cast
    ring
  rw [heq] at hsplit
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero] at hsplit
  linear_combination hsplit

/-- **The project Hurwitz base value is the Riemann zeta.**  For `Re s>1`,
`hzeta(s,0)=riemannZeta(s)`. -/
theorem hzeta_zero_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HurwitzZetaShift.hzeta s 0 = riemannZeta s := by
  rw [HurwitzZetaShift.hzeta, zeta_eq_tsum_one_div_nat_cpow hs]
  apply tsum_congr
  intro n
  simp [Complex.cpow_neg, one_div]

/-- The unit-shift Hurwitz value also equals the Riemann zeta on `Re s>1`. -/
theorem hzeta_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HurwitzZetaShift.hzeta s 1 = riemannZeta s := by
  have h := hzeta_add_one hs (0 : ℂ)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    norm_num at hs
  rw [zero_add, Complex.zero_cpow (neg_ne_zero.mpr hs0), sub_zero,
    hzeta_zero_eq_riemannZeta hs] at h
  exact h

/-- **Negative-integer Hurwitz values with their base constant identified.**  This strengthens the
banked tail formula by replacing the formerly internal `hzeta(s,0)` constant with the actual
Riemann zeta value. -/
theorem hzeta_neg_nat_eq_riemannZeta_add {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    HurwitzZetaShift.hzeta s (-(n : ℂ)) = riemannZeta s
      + Complex.exp (-((Real.pi : ℂ) * Complex.I * s))
        * ∑ l ∈ Finset.range n, ((l : ℂ) + 1) ^ (-s) := by
  rw [HurwitzZetaShift.hzeta_neg_nat hs n, hzeta_zero_eq_riemannZeta hs]

/-- **Polygamma as an integer-exponent Hurwitz-zeta value.**  For every `m ≥ 0` and
`Re z > 0`,

`ψ⁽ᵐ⁺¹⁾(z) = (-1)^(m+2) (m+1)! ζ(m+2,z)`.

Here `ζ(s,z)` is `HurwitzZetaShift.hzeta`, the project's complex-shift Hurwitz series. -/
theorem polygamma_eq_hzeta (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv (m + 1) Complex.digamma z =
      (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
        HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) z := by
  let q : ℕ := m + 1
  let C : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
  have hsummable := HurwitzZetaShift.summable_hurwitzSeries
    (s := ((q + 1 : ℕ) : ℂ)) (by simp [q]; positivity) z
  have hterm : (fun n : ℕ => ((n : ℂ) + z) ^ (-((q + 1 : ℕ) : ℂ))) =
      (fun n : ℕ => ((z + (n : ℂ)) ^ (q + 1))⁻¹) := by
    funext n
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    congr 2
    ring
  have hsum : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (q + 1))⁻¹)
      atTop (nhds (HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) z)) := by
    rw [HurwitzZetaShift.hzeta, hterm]
    rw [hterm] at hsummable
    exact hsummable.hasSum.tendsto_sum_nat
  have hscaled := hsum.const_mul C
  have hfar := iteratedDeriv_digamma_add_nat_tendsto m z
  have hrec : ∀ N : ℕ,
      C * ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (q + 1))⁻¹ =
        iteratedDeriv q Complex.digamma (z + (N : ℂ)) -
          iteratedDeriv q Complex.digamma z := by
    intro N
    have h := polygamma_apply_add_nat q N hz
    change iteratedDeriv q Complex.digamma (z + (N : ℂ)) =
      iteratedDeriv q Complex.digamma z +
        C * ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (q + 1))⁻¹ at h
    rw [h]
    ring
  have hright : Tendsto
      (fun N : ℕ => iteratedDeriv q Complex.digamma (z + (N : ℂ)) -
        iteratedDeriv q Complex.digamma z)
      atTop (nhds (0 - iteratedDeriv q Complex.digamma z)) := by
    simpa [q] using hfar.sub tendsto_const_nhds
  have heq : C * HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) z =
      0 - iteratedDeriv q Complex.digamma z := by
    apply tendsto_nhds_unique hscaled
    exact hright.congr (fun N => (hrec N).symm)
  have hvalue : iteratedDeriv q Complex.digamma z =
      -(C * HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) z) := by
    calc
      iteratedDeriv q Complex.digamma z =
          -(0 - iteratedDeriv q Complex.digamma z) := by ring
      _ = -(C * HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) z) := by rw [heq]
  rw [hvalue]
  have hsign : -((-1 : ℂ) ^ (m + 1)) = (-1 : ℂ) ^ (m + 2) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    ring
  dsimp [q, C]
  calc
    -((-1 : ℂ) ^ (m + 1) * ((m + 1).factorial : ℂ) *
        HurwitzZetaShift.hzeta ((m + 1 + 1 : ℕ) : ℂ) z) =
        (-((-1 : ℂ) ^ (m + 1))) * ((m + 1).factorial : ℂ) *
          HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) z := by
            rw [show m + 1 + 1 = m + 2 by omega]
            ring
    _ = _ := by rw [hsign]

/-- **All positive-order polygamma values at one are zeta values.**

`ψ⁽ᵐ⁺¹⁾(1)=(-1)^(m+2)(m+1)!·ζ(m+2)`. -/
theorem polygamma_one_eq_riemannZeta (m : ℕ) :
    iteratedDeriv (m + 1) Complex.digamma 1 =
      (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
        riemannZeta ((m + 2 : ℕ) : ℂ) := by
  have h := polygamma_eq_hzeta m (z := (1 : ℂ)) (by norm_num)
  rw [hzeta_one_eq_riemannZeta (by
    rw [Complex.natCast_re]
    exact_mod_cast (show 1 < m + 2 by omega))] at h
  exact h

/-- **All positive-order polygamma values at one half are zeta values.**

`ψ⁽ᵐ⁺¹⁾(1/2)=(2^(m+2)-1)(-1)^(m+2)(m+1)!·ζ(m+2)`. -/
theorem polygamma_one_half_eq_riemannZeta (m : ℕ) :
    iteratedDeriv (m + 1) Complex.digamma (1 / 2 : ℂ) =
      ((2 : ℂ) ^ (m + 2) - 1) *
        ((-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
          riemannZeta ((m + 2 : ℕ) : ℂ)) := by
  rw [polygamma_one_half_eq_mul_one, polygamma_one_eq_riemannZeta]

/-- **Integer-exponent Hurwitz values at one half.**  For every `m ≥ 0`,
`ζ(m+2,1/2)=(2^(m+2)-1)ζ(m+2)`. -/
theorem hzeta_nat_one_half_eq_mul_riemannZeta (m : ℕ) :
    HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) (1 / 2 : ℂ) =
      ((2 : ℂ) ^ (m + 2) - 1) * riemannZeta ((m + 2 : ℕ) : ℂ) := by
  have hhalf := polygamma_eq_hzeta m (z := (1 / 2 : ℂ)) (by norm_num)
  have hvalue := polygamma_one_half_eq_riemannZeta m
  rw [hhalf] at hvalue
  let C : ℂ := (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ)
  have hC : C ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (m + 1))
  apply mul_left_cancel₀ hC
  dsimp [C]
  linear_combination hvalue

/-- The trigamma/Hurwitz-zeta bridge: `ψ'(z)=ζ(2,z)` on `Re z>0`. -/
theorem trigamma_eq_hzeta_two {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.digamma z = HurwitzZetaShift.hzeta 2 z := by
  have h := polygamma_eq_hzeta 0 hz
  simpa [iteratedDeriv_succ] using h

/-- Exact custom-Hurwitz value `ζ(2,1)=π²/6`. -/
theorem hzeta_two_one :
    HurwitzZetaShift.hzeta 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [← trigamma_eq_hzeta_two (z := (1 : ℂ)) (by norm_num)]
  exact RHTower.trigamma_one

/-- Exact custom-Hurwitz half-shift value `ζ(2,1/2)=π²/2`. -/
theorem hzeta_two_one_half :
    HurwitzZetaShift.hzeta 2 (1 / 2 : ℂ) = (Real.pi : ℂ) ^ 2 / 2 := by
  have hhalf := hzeta_nat_one_half_eq_mul_riemannZeta 0
  rw [show ((0 + 2 : ℕ) : ℂ) = 2 by norm_num] at hhalf
  rw [hhalf, ← hzeta_one_eq_riemannZeta (s := (2 : ℂ)) (by norm_num), hzeta_two_one]
  ring

end GaloisForLFunctions
