import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Polynomial factors are invisible to the root growth functional

A sequence squeezed between two polynomial envelopes has `k`-th roots tending to
one: both a positive constant and a power of `k` become trivial after taking a
`k`-th root.  Consequently the Cauchy--Hadamard growth functional of such a
sequence is one, and a geometric factor times such a sequence has growth
functional exactly the modulus of that factor.

This is the mechanism of the independent cusp-constant computation: after the
functional equation the shifted `L`-value is a geometric factor `(2π)^{-k}` times
a ratio of Gamma values and an `L`-value tending to one, and only the geometric
factor survives the `k`-th root.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

section RootLimits

/-- A positive constant has `k`-th roots tending to one. -/
theorem tendsto_const_rpow_inv_nat {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ => C ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun k : ℕ => Real.log C * (1 / (k : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_mul (Real.log C)
  have hexp := (Real.continuous_exp.tendsto 0).comp hzero
  rw [Real.exp_zero] at hexp
  refine hexp.congr fun k => ?_
  rw [Function.comp_apply, ← Real.rpow_def_of_pos hC]

/-- A power of the index has `k`-th roots tending to one. -/
theorem tendsto_nat_rpow_div_self (B : ℝ) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ (B * (1 / (k : ℝ)))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    hlog.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun k : ℕ => Real.log (k : ℝ) * (B * (1 / (k : ℝ))))
      atTop (𝓝 0) := by
    have := hnat.const_mul B
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    ring
  have hexp := (Real.continuous_exp.tendsto 0).comp hzero
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [Function.comp_apply, ← Real.rpow_def_of_pos hkR]

/-- **Polynomial envelopes are invisible to the `k`-th root.** -/
theorem tendsto_rpow_inv_of_polynomial_bounds {u : ℕ → ℝ} {C₁ C₂ B : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hlb : ∀ᶠ k : ℕ in atTop, C₁ * (k : ℝ) ^ (-B) ≤ u k)
    (hub : ∀ᶠ k : ℕ in atTop, u k ≤ C₂ * (k : ℝ) ^ B) :
    Tendsto (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have hlow : Tendsto
      (fun k : ℕ => (C₁ * (k : ℝ) ^ (-B)) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hmul := (tendsto_const_rpow_inv_nat hC₁).mul (tendsto_nat_rpow_div_self (-B))
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [Real.mul_rpow hC₁.le (Real.rpow_nonneg hkR.le _), ← Real.rpow_mul hkR.le]
  have hhigh : Tendsto
      (fun k : ℕ => (C₂ * (k : ℝ) ^ B) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hmul := (tendsto_const_rpow_inv_nat hC₂).mul (tendsto_nat_rpow_div_self B)
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [Real.mul_rpow hC₂.le (Real.rpow_nonneg hkR.le _), ← Real.rpow_mul hkR.le]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [hlb, eventually_gt_atTop 0] with k h hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hpos : (0 : ℝ) < C₁ * (k : ℝ) ^ (-B) := by positivity
    exact Real.rpow_le_rpow hpos.le h (by positivity)
  · filter_upwards [hub, eventually_gt_atTop 0, hlb] with k h hk hl
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hpos : (0 : ℝ) < C₁ * (k : ℝ) ^ (-B) := by positivity
    exact Real.rpow_le_rpow (le_trans hpos.le hl) h (by positivity)

/-- **Ratio-to-root, unit case.**  A strictly positive sequence whose consecutive
ratios tend to one has `k`-th roots tending to one.  Telescoping turns the
logarithms of the ratios into `log (a k) - log (a 0)`, and the Cesàro average of
a null sequence is null. -/
theorem tendsto_rpow_inv_one_of_ratio_one {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) :
    Tendsto (fun k : ℕ => (a k) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n => Real.log (a (n + 1) / a n)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    rwa [Real.log_one] at this
  have havg : Tendsto
      (fun n : ℕ => ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
        Real.log (a (i + 1) / a i)) atTop (𝓝 0) := hlog.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, Real.log (a (i + 1) / a i)
      = Real.log (a n) - Real.log (a 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, Real.log_div (ha (n + 1)).ne' (ha n).ne']
        ring
  have hconst : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log (a 0)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (Real.log (a 0))
  have hlogroot : Tendsto
      (fun n : ℕ => Real.log (a n) * (1 / (n : ℝ))) atTop (𝓝 0) := by
    have hsum := havg.add hconst
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [htel n]
    ring
  have hexp := (Real.continuous_exp.tendsto 0).comp hlogroot
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards with n
  rw [Function.comp_apply, ← Real.rpow_def_of_pos (ha n)]

end RootLimits

section GammaRatio

theorem norm_one_add_natCast_inv_le (k : ℕ) :
    ‖((1 : ℂ) + (k : ℂ))⁻¹‖ ≤ 1 / ((k : ℝ) + 1) := by
  have hre : ((1 : ℂ) + (k : ℂ)).re = (k : ℝ) + 1 := by simp [add_comm]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hge : (k : ℝ) + 1 ≤ ‖(1 : ℂ) + (k : ℂ)‖ := by
    rw [← hre]
    exact Complex.re_le_norm _
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hge

theorem tendsto_one_add_natCast_inv_zero :
    Tendsto (fun k : ℕ => ((1 : ℂ) + (k : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) norm_one_add_natCast_inv_le
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The consecutive ratio of the Gamma quotient tends to one. -/
theorem tendsto_gammaRatioFactor (w : ℂ) :
    Tendsto (fun k : ℕ => (w + (k : ℂ)) / (1 + (k : ℂ))) atTop (𝓝 1) := by
  have hne : ∀ k : ℕ, (1 : ℂ) + (k : ℂ) ≠ 0 := by
    intro k hcon
    have hre : ((1 : ℂ) + (k : ℂ)).re = 0 := by rw [hcon]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have heq : ∀ k : ℕ, (w + (k : ℂ)) / (1 + (k : ℂ))
      = 1 + (w - 1) * ((1 : ℂ) + (k : ℂ))⁻¹ := by
    intro k
    field_simp [hne k]
    ring
  refine Tendsto.congr (fun k => (heq k).symm) ?_
  have hmul := tendsto_one_add_natCast_inv_zero.const_mul (w - 1)
  rw [mul_zero] at hmul
  simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))).add hmul

/-- **The Gamma ratio is invisible to the `k`-th root.**  Consecutive ratios of
`Γ(w+k)/Γ(1+k)` are `(w+k)/(1+k)`, which tends to one. -/
theorem tendsto_norm_gammaRatio_rpow_inv {w : ℂ}
    (hne : ∀ k : ℕ, Complex.Gamma (w + (k : ℂ)) ≠ 0)
    (hw0 : ∀ k : ℕ, w + (k : ℂ) ≠ 0) :
    Tendsto (fun k : ℕ =>
        ‖Complex.Gamma (w + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖ ^ (1 / (k : ℝ)))
      atTop (𝓝 1) := by
  have hden : ∀ k : ℕ, Complex.Gamma (1 + (k : ℂ)) ≠ 0 := by
    intro k
    have hfac : Complex.Gamma ((k : ℂ) + 1) = (Nat.factorial k : ℂ) :=
      Complex.Gamma_nat_eq_factorial k
    rw [add_comm, hfac]
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ∀ k : ℕ, (1 : ℂ) + (k : ℂ) ≠ 0 := by
    intro k hcon
    have hre : ((1 : ℂ) + (k : ℂ)).re = 0 := by rw [hcon]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos : ∀ k : ℕ,
      0 < ‖Complex.Gamma (w + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖ := by
    intro k
    rw [norm_pos_iff]
    exact div_ne_zero (hne k) (hden k)
  refine tendsto_rpow_inv_one_of_ratio_one hpos ?_
  have hstep : ∀ k : ℕ,
      ‖Complex.Gamma (w + ((k + 1 : ℕ) : ℂ)) / Complex.Gamma (1 + ((k + 1 : ℕ) : ℂ))‖
        / ‖Complex.Gamma (w + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖
        = ‖(w + (k : ℂ)) / (1 + (k : ℂ))‖ := by
    intro k
    have h1 : Complex.Gamma (w + ((k + 1 : ℕ) : ℂ))
        = (w + (k : ℂ)) * Complex.Gamma (w + (k : ℂ)) := by
      have hg := Complex.Gamma_add_one (w + (k : ℂ)) (hw0 k)
      rw [← hg]
      congr 1
      push_cast
      ring
    have h2 : Complex.Gamma (1 + ((k + 1 : ℕ) : ℂ))
        = (1 + (k : ℂ)) * Complex.Gamma (1 + (k : ℂ)) := by
      have hg := Complex.Gamma_add_one (1 + (k : ℂ)) (hk1 k)
      rw [← hg]
      congr 1
      push_cast
      ring
    have hn1 : ‖Complex.Gamma (w + (k : ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr (hne k)
    have hn2 : ‖Complex.Gamma (1 + (k : ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr (hden k)
    rw [h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_div]
    field_simp
  refine Tendsto.congr (fun k => (hstep k).symm) ?_
  simpa using (tendsto_gammaRatioFactor w).norm

end GammaRatio

section Hadamard

/-- **A polynomially bounded family has growth functional one.** -/
theorem hadamardLimsup_eq_one_of_tendsto {c : ℕ → ℂ}
    (h : Tendsto (fun k : ℕ => ‖c k‖ ^ (1 / (k : ℝ))) atTop (𝓝 1)) :
    hadamardLimsup c = 1 := by
  have hcoe : Tendsto
      (fun k : ℕ => ((‖c k‖₊ ^ (1 / (k : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 1) := by
    have hnn : Tendsto (fun k : ℕ => (‖c k‖₊ ^ (1 / (k : ℝ)) : ℝ≥0)) atTop (𝓝 1) := by
      rw [← NNReal.tendsto_coe]
      refine h.congr fun k => ?_
      rw [NNReal.coe_rpow, coe_nnnorm]
    exact (ENNReal.continuous_coe.tendsto 1).comp hnn
  rw [hadamardLimsup]
  simpa using hcoe.limsup_eq

/-- **Only the geometric factor survives.**  A geometric factor times a
polynomially bounded family has growth functional the modulus of that factor. -/
theorem hadamardLimsup_geometric_of_tendsto_one {A : ℂ} {c : ℕ → ℂ}
    (h : Tendsto (fun k : ℕ => ‖c k‖ ^ (1 / (k : ℝ))) atTop (𝓝 1)) :
    hadamardLimsup (fun k => A ^ k * c k) = ((‖A‖₊ : ℝ≥0∞)) := by
  rw [hadamardLimsup_geometric, hadamardLimsup_eq_one_of_tendsto h, mul_one]

end Hadamard

end GaloisForLFunctions.HTGeometry
