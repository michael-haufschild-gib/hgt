/-
The classical value bridge between positive-order polygamma functions and the Hurwitz zeta in its
complex shift variable.

The project already contains both sides independently: the all-order polygamma recurrence and
far-field decay in `GammaProjectiveBoundary`, and the convergent complex-shift Hurwitz series in
`HurwitzZeta`.  This module identifies their values on the open right half-plane.
-/
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import GaloisForLFunctions.HTGeometry.PolygammaMultiplication
import GaloisForLFunctions.HTGeometry.PolygammaReflection
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

private theorem posReal_mul_cpow {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  by_cases hz : z = 0
  · subst z
    by_cases hw : w = 0
    · simp [hw]
    · simp only [mul_zero]
      rw [Complex.zero_cpow hw, mul_zero]
  · have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz),
      Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hz,
      Complex.log_ofReal_mul hr hz, ← Complex.ofReal_log hr.le, ← Complex.exp_add]
    congr 1
    ring

/-- **Hurwitz zeta at one half.**  In the convergence half-plane,
`ζ(s,1/2)=(2^s-1)ζ(s)`. -/
theorem hzeta_one_half_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HurwitzZetaShift.hzeta s (1 / 2 : ℂ) =
      ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s)
  have hf : Summable f := by
    simpa [f] using HurwitzZetaShift.summable_hurwitzSeries hs (1 : ℂ)
  have heinj : Function.Injective (fun k : ℕ => (2 * k : ℕ)) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hoinj : Function.Injective (fun k : ℕ => (2 * k + 1 : ℕ)) := by
    intro a b h
    apply heinj
    exact Nat.add_right_cancel h
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective heinj
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective hoinj
  have hsplit := tsum_even_add_odd he ho
  have htotal : (∑' k : ℕ, f k) = HurwitzZetaShift.hzeta s 1 := by
    simp [f, HurwitzZetaShift.hzeta]
  have heven : (∑' k : ℕ, f (2 * k + 1)) =
      (2 : ℂ) ^ (-s) * HurwitzZetaShift.hzeta s 1 := by
    rw [HurwitzZetaShift.hzeta, ← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [f]
    have hmul := Complex.mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) (-s)
    push_cast at hmul
    rw [show ((2 * k + 1 : ℕ) : ℂ) + 1 = (2 : ℂ) * ((k : ℂ) + 1) by
      push_cast
      ring]
    exact hmul
  have hhalf : HurwitzZetaShift.hzeta s (1 / 2 : ℂ) =
      (2 : ℂ) ^ s * ∑' k : ℕ, f (2 * k) := by
    rw [HurwitzZetaShift.hzeta, ← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [f]
    have hmul := Complex.mul_cpow_ofReal_nonneg
      (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
      (show (0 : ℝ) ≤ 2 * (k : ℝ) + 1 by positivity) (-s)
    push_cast at hmul
    have hmul' : ((1 / 2 : ℂ) * (((2 * k + 1 : ℕ) : ℂ))) ^ (-s) =
        (1 / 2 : ℂ) ^ (-s) * (((2 * k + 1 : ℕ) : ℂ)) ^ (-s) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hmul
    rw [show ((k : ℂ) + (1 / 2 : ℂ)) =
      (1 / 2 : ℂ) * (((2 * k + 1 : ℕ) : ℂ)) by
        push_cast
        ring, hmul']
    have htwo : ((1 / 2 : ℂ) ^ (-s)) = (2 : ℂ) ^ s := by
      have harg : (2 : ℂ).arg ≠ Real.pi := by
        change Complex.arg ((2 : ℝ) : ℂ) ≠ Real.pi
        rw [Complex.arg_ofReal_of_nonneg (by norm_num)]
        exact ne_of_lt Real.pi_pos
      rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,
        Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
    rw [htwo]
    congr 2
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [hhalf]
  rw [heven, htotal, hzeta_one_eq_riemannZeta hs] at hsplit
  have hpow : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) (by norm_num : (2 : ℂ) ≠ 0)]
    simp
  have hodd : (∑' k : ℕ, f (2 * k)) =
      riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    linear_combination hsplit
  rw [hodd]
  calc
    (2 : ℂ) ^ s * (riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s) =
        (2 : ℂ) ^ s * riemannZeta s -
          ((2 : ℂ) ^ s * (2 : ℂ) ^ (-s)) * riemannZeta s := by ring
    _ = ((2 : ℂ) ^ s - 1) * riemannZeta s := by rw [hpow]; ring

/-- **Hurwitz distribution relation.**  For `Re s > 1` and every positive integer `n`, the values
on a complete rational fiber sum to one scaled base value:

`∑_{k<n} ζ(s,(a+k)/n)=n^s ζ(s,a)`. -/
theorem hzeta_distribution {s : ℂ} (hs : 1 < s.re) {n : ℕ} (hn : 0 < n) (a : ℂ) :
    (∑ k ∈ Finset.range n,
      HurwitzZetaShift.hzeta s ((a + (k : ℕ)) / (n : ℕ))) =
        (n : ℂ) ^ s * HurwitzZetaShift.hzeta s a := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let g : ℕ → ℂ := fun r => ((r : ℂ) + a) ^ (-s)
  have hg : Summable g := by
    simpa [g] using HurwitzZetaShift.summable_hurwitzSeries hs a
  have hprod : Summable (fun p : ℕ × Fin n => g (p.1 * n + (p.2 : ℕ))) := by
    have heq : (fun p : ℕ × Fin n => g (p.1 * n + (p.2 : ℕ))) =
        g ∘ (Nat.divModEquiv n).symm := by
      funext p
      simp only [Function.comp_apply, Nat.divModEquiv_symm_apply]
    rw [heq]
    exact (Nat.divModEquiv n).symm.summable_iff.mpr hg
  have hreindex : (∑ k : Fin n, ∑' m : ℕ, g (m * n + (k : ℕ))) = ∑' r : ℕ, g r := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (Fin n))]
    calc
      (∑' k : Fin n, ∑' m : ℕ, g (m * n + (k : ℕ))) =
          ∑' m : ℕ, ∑' k : Fin n, g (m * n + (k : ℕ)) := hprod.tsum_comm
      _ = ∑' p : ℕ × Fin n, g (p.1 * n + (p.2 : ℕ)) := hprod.tsum_prod.symm
      _ = ∑' r : ℕ, g r := by
        simpa [Nat.divModEquiv_symm_apply] using
          ((Nat.divModEquiv n).symm.tsum_eq g)
  have hnarg : (n : ℂ).arg ≠ Real.pi := by
    change Complex.arg ((n : ℝ) : ℂ) ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact ne_of_lt Real.pi_pos
  have hscale : ((1 / (n : ℂ)) ^ (-s)) = (n : ℂ) ^ s := by
    rw [show (1 / (n : ℂ)) = (n : ℂ)⁻¹ by ring,
      Complex.inv_cpow _ _ hnarg, Complex.cpow_neg, inv_inv]
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    HurwitzZetaShift.hzeta s ((a + (k : ℕ)) / (n : ℕ)))]
  calc
    (∑ k : Fin n, HurwitzZetaShift.hzeta s ((a + (k : ℕ)) / (n : ℕ))) =
        ∑ k : Fin n, (n : ℂ) ^ s * ∑' m : ℕ, g (m * n + (k : ℕ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [HurwitzZetaShift.hzeta, ← tsum_mul_left]
          apply tsum_congr
          intro m
          dsimp [g]
          rw [← hscale]
          have hbase : ((m : ℂ) + (a + (k : ℕ)) / (n : ℕ)) =
              (1 / (n : ℂ)) * (((m * n + (k : ℕ) : ℕ) : ℂ) + a) := by
            field_simp [Nat.ne_of_gt hn]
            push_cast
            ring
          rw [hbase]
          have hmul := posReal_mul_cpow (r := (1 / (n : ℝ))) (by positivity)
            ((((m * n + (k : ℕ) : ℕ) : ℂ) + a)) (-s)
          simpa using hmul
    _ = (n : ℂ) ^ s * ∑ k : Fin n, ∑' m : ℕ, g (m * n + (k : ℕ)) := by
      rw [Finset.mul_sum]
    _ = (n : ℂ) ^ s * ∑' r : ℕ, g r := by rw [hreindex]
    _ = (n : ℂ) ^ s * HurwitzZetaShift.hzeta s a := by rfl

/-- **Integer-exponent Hurwitz values at one half.**  For every `m ≥ 0`,
`ζ(m+2,1/2)=(2^(m+2)-1)ζ(m+2)`. -/
theorem hzeta_nat_one_half_eq_mul_riemannZeta (m : ℕ) :
    HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) (1 / 2 : ℂ) =
      ((2 : ℂ) ^ (m + 2) - 1) * riemannZeta ((m + 2 : ℕ) : ℂ) := by
  have hs : 1 < (((m + 2 : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (show 1 < m + 2 by omega)
  have h := hzeta_one_half_eq_mul_riemannZeta (s := ((m + 2 : ℕ) : ℂ)) hs
  rw [Complex.cpow_natCast] at h
  exact h

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
