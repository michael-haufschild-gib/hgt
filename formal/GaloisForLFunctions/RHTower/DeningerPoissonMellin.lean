import GaloisForLFunctions.RHTower.DeningerPoissonOperator
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Mellin symbol of the Poisson operator is the zeta function

Each term of the Poisson sum is a dilation, and the Mellin transform turns a dilation by `n` into
multiplication by `n^{-s}`.  For `Re s > 1` the family of dilated Mellin integrals is absolutely
summable, so the sum may be taken out of the integral, and the resulting scalar factor is the
Dirichlet series of the zeta function:

`M(Zf)(s) = ζ(s)·M(f)(s)`.

This is the reason the cokernel of the Poisson operator is a zeta object: on the Mellin side `Z` is
multiplication by `ζ`, so the obstruction to surjectivity is exactly the zero divisor of `ζ`.

* `mellinConvergent_schwartz` : the Mellin transform of a Schwartz function converges for
  `Re s > 0`.
* `integral_mellinNorm_comp_mul` : the scaling law for the absolute Mellin integral.
* `mellin_deningerPoissonValue` : **`M(Zf)(s) = ζ(s)M(f)(s)` for `Re s > 1`.**
-/

open scoped Real SchwartzMap FourierTransform Topology
open Complex MeasureTheory Set Filter Asymptotics GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## Convergence of the Mellin transform of a Schwartz function -/

theorem schwartz_isBigO_atTop (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (f : ℝ → ℂ) =O[atTop] fun x : ℝ => x ^ (-a) := by
  have hcocompact := f.isBigO_cocompact_rpow (-a)
  have hle : (atTop : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  have h := hcocompact.mono hle
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]

theorem schwartz_isBigO_zero (f : 𝓢(ℝ, ℂ)) :
    (f : ℝ → ℂ) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(0 : ℝ)) := by
  refine Asymptotics.isBigO_of_le' (𝓝[>] (0 : ℝ)) (c := SchwartzMap.seminorm ℂ 0 0 f) ?_
  intro x
  have hbound : ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f x
  have hnorm : ‖x ^ (-(0 : ℝ))‖ = 1 := by
    rw [neg_zero, Real.rpow_zero, norm_one]
  rw [hnorm, mul_one]
  exact hbound

theorem mellinConvergent_schwartz (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (f : ℝ → ℂ) s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0) ?_ ?_ (by linarith) ?_ hs
  · exact (f.continuous.locallyIntegrable).locallyIntegrableOn _
  · exact schwartz_isBigO_atTop f (s.re + 1)
  · exact schwartz_isBigO_zero f

theorem integrableOn_mellinNorm_schwartz (f : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * ‖f x‖) (Ioi 0) := by
  have hconv : MellinConvergent (f : ℝ → ℂ) (σ : ℂ) := by
    refine mellinConvergent_schwartz f ?_
    rwa [Complex.ofReal_re]
  rw [MellinConvergent,
    mellin_convergent_iff_norm (T := Ioi 0) Subset.rfl measurableSet_Ioi
      f.continuous.aestronglyMeasurable] at hconv
  simpa using hconv

/-! ## The scaling law of the absolute Mellin integral -/

theorem integral_mellinNorm_comp_mul (f : 𝓢(ℝ, ℂ)) {σ : ℝ} (_hσ : 0 < σ) {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * ‖f (c * x)‖)
      = c ^ (-σ) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * ‖f x‖ := by
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => x ^ (σ - 1) * ‖f x‖) 0 hc
  rw [mul_zero] at hsub
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      x ^ (σ - 1) * ‖f (c * x)‖
        = c ^ (1 - σ) * ((c * x) ^ (σ - 1) * ‖f (c * x)‖) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    rw [Real.mul_rpow hc.le hx'.le]
    rw [show (1 : ℝ) - σ = -(σ - 1) by ring, Real.rpow_neg hc.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul, hsub, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [show (1 : ℝ) - σ = -(σ - 1) by ring, Real.rpow_neg hc.le, Real.rpow_neg hc.le,
    Real.rpow_sub hc]
  field_simp
  rw [Real.rpow_one]

/-! ## The zeta factorization -/

theorem tsum_one_add_cpow_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (((n : ℂ) + 1)) ^ (-s)) = riemannZeta s := by
  have hzeta := zeta_eq_tsum_one_div_nat_cpow hs
  have hzero : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero]
  have hshift : (∑' n : ℕ, 1 / ((n : ℂ)) ^ s) = ∑' n : ℕ, 1 / (((n : ℕ) + 1 : ℕ) : ℂ) ^ s := by
    have hsummable : Summable fun n : ℕ => 1 / ((n : ℂ)) ^ s := by
      have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
      exact h
    rw [hsummable.tsum_eq_zero_add, hzero, zero_add]
  rw [hzeta, hshift]
  refine tsum_congr fun n => ?_
  have hcast : ((((n + 1 : ℕ)) : ℂ)) = ((n : ℂ) + 1) := by
    push_cast
    ring
  rw [hcast, Complex.cpow_neg, one_div]

/-- **The Mellin symbol of the Poisson operator is the zeta function.** -/
theorem mellin_deningerPoissonValue (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 1 < s.re) :
    mellin (deningerPoissonValue f) s = riemannZeta s * mellin (f : ℝ → ℂ) s := by
  have hσ : (0 : ℝ) < s.re := by linarith
  set F : ℕ → ℝ → ℂ := fun n x => (x : ℂ) ^ (s - 1) • f (((n : ℝ) + 1) * x) with hF
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hconv : MellinConvergent (fun x : ℝ => f (((n : ℝ) + 1) * x)) s :=
      (MellinConvergent.comp_mul_left hpos).mpr (mellinConvergent_schwartz f hσ)
    exact hconv
  have hnorm : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), ‖F n x‖)
      = ((n : ℝ) + 1) ^ (-s.re) * ∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖f x‖ := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpoint : ∀ x ∈ Ioi (0 : ℝ),
        ‖F n x‖ = x ^ (s.re - 1) * ‖f (((n : ℝ) + 1) * x)‖ := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      rw [hF, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx']
      congr 1
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_mellinNorm_comp_mul f hσ hpos]
  have hsummable : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    have hbase : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re) := by
      have h : Summable fun n : ℕ => ((n : ℝ)) ^ (-s.re) := by
        rw [Real.summable_nat_rpow]
        linarith
      have h1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
        (summable_nat_add_iff 1).mpr h
      refine h1.congr fun n => ?_
      push_cast
      ring_nf
    have hfun : (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖)
        = fun n : ℕ => (∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖f x‖)
          * (((n : ℝ) + 1) ^ (-s.re)) := by
      funext n
      rw [hnorm n]
      ring
    rw [hfun]
    exact hbase.mul_left _
  have hswap : (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), F n x)
      = ∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x :=
    integral_tsum_of_summable_integral_norm hint hsummable
  have hterm : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), F n x)
      = ((n : ℂ) + 1) ^ (-s) * mellin (f : ℝ → ℂ) s := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := mellin_comp_mul_left (f : ℝ → ℂ) s hpos
    have hcast : ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) := by
      push_cast
      ring
    show mellin (fun x : ℝ => f (((n : ℝ) + 1) * x)) s = _
    rw [h, smul_eq_mul, hcast]
  have hvalue : (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x) = mellin (deningerPoissonValue f) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    have hsum : Summable fun n : ℕ => f (x * ((n : ℝ) + 1)) :=
      summable_deningerPoissonTerm f hx'.ne'
    rw [deningerPoissonValue, ← hsum.tsum_const_smul]
    refine tsum_congr fun n => ?_
    show (x : ℂ) ^ (s - 1) • f (((n : ℝ) + 1) * x) = (x : ℂ) ^ (s - 1) • f (x * ((n : ℝ) + 1))
    rw [mul_comm ((n : ℝ) + 1) x]
  rw [← hvalue, ← hswap, tsum_congr hterm, tsum_mul_right, tsum_one_add_cpow_eq_zeta hs]

end RHTower

end
