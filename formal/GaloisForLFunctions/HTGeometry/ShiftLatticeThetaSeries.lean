import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.PSeries

/-!
# The shift-lattice theta series and its standard twists

The degree-`d` theta series of a coefficient family is
`Θ(w, z) = ∑_{n ≥ 1} a(n) n^{-w} e(z n^{1/d})`.  On the upper half plane the
exponential factor decays like `exp(-2π (Im z) n^{1/d})`, which beats every
polynomial, so the series converges absolutely for every complex `w` as soon as
the coefficients are polynomially bounded.  At `z` real the same series is the
Kaczorowski--Perelli standard twist, and there convergence is the ordinary
Dirichlet abscissa question.

This file builds the convergence layer: the super-polynomial decay estimate, the
exact norm of a term, and absolute summability on the open upper half plane,
uniformly in the spectral variable.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Decay

/-- Any positive power of the argument inside the exponential beats every
polynomial: the mixed family is summable over the naturals. -/
theorem summable_rpow_mul_exp_neg_rpow {A c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    Summable fun n : ℕ => (n : ℝ) ^ A * Real.exp (-(c * (n : ℝ) ^ e)) := by
  have hbase : Summable fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
    simp
  have hcomp : Tendsto
      (fun x : ℝ => x ^ (A + 2) * Real.exp (-(c * x ^ e))) atTop (𝓝 0) := by
    have hg : Tendsto (fun x : ℝ => x ^ e) atTop atTop := tendsto_rpow_atTop he
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((A + 2) / e) c hc
    refine (hh.comp hg).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : (0 : ℝ) ≤ x := hx.le
    have hexp : e * ((A + 2) / e) = A + 2 := by field_simp
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hx0, hexp, neg_mul]
  have hzero : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (A + 2) * Real.exp (-(c * (n : ℝ) ^ e))) atTop (𝓝 0) :=
    hcomp.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ A * Real.exp (-(c * (n : ℝ) ^ e)) ≤ ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
    have h1 := hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h1, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hsplit : (n : ℝ) ^ (A + 2) = (n : ℝ) ^ A * (n : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hnR]
    have hpos2 : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hnR _
    rw [hsplit] at hn
    rw [inv_eq_one_div, le_div_iff₀ hpos2]
    nlinarith [hn]
  refine summable_of_isBigO_nat hbase (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [hev, eventually_gt_atTop 0] with n hle hn0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ A * Real.exp (-(c * (n : ℝ) ^ e))),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ) ^ (2 : ℝ))⁻¹)]
  exact hle

end Decay

section ThetaSeries

/-- One term of the degree-`d` shift-lattice theta series. -/
noncomputable def thetaTerm (a : ℕ → ℂ) (d : ℝ) (w z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else a n * (n : ℂ) ^ (-w) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * (((n : ℝ) ^ (1 / d) : ℝ) : ℂ))

/-- The degree-`d` shift-lattice theta series.  At `z` in the upper half plane it
is the theta function of the coefficient family; at real `z = -α` it is the
Kaczorowski--Perelli standard twist. -/
noncomputable def thetaSeries (a : ℕ → ℂ) (d : ℝ) (w z : ℂ) : ℂ :=
  ∑' n : ℕ, thetaTerm a d w z n

@[simp] theorem thetaTerm_zero (a : ℕ → ℂ) (d : ℝ) (w z : ℂ) :
    thetaTerm a d w z 0 = 0 := by
  rw [thetaTerm, if_pos rfl]

/-- The exact modulus of one term: the coefficient, the polynomial factor, and
the exponential decay produced by the height of `z`. -/
theorem norm_thetaTerm (a : ℕ → ℂ) (d : ℝ) (w z : ℂ) {n : ℕ} (hn : 0 < n) :
    ‖thetaTerm a d w z n‖
      = ‖a n‖ * (n : ℝ) ^ (-w.re)
        * Real.exp (-(2 * Real.pi * z.im * ((n : ℝ) ^ (1 / d)))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [thetaTerm, if_neg hn.ne', norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hn, Complex.norm_exp]
  rw [Complex.neg_re]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The coefficient bound is nonnegative. -/
theorem const_nonneg_of_bound {a : ℕ → ℂ} {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) : 0 ≤ C := by
  have h := ha 1
  rw [Nat.cast_one, Real.one_rpow, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- **Absolute convergence on the upper half plane.**  Above the real axis the
exponential decay beats every polynomial, so the theta series converges for every
spectral parameter. -/
theorem summable_norm_thetaTerm_of_im_pos {a : ℕ → ℂ} {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) {d : ℝ} (hd : 0 < d) (w z : ℂ)
    (hz : 0 < z.im) : Summable fun n : ℕ => ‖thetaTerm a d w z n‖ := by
  have hC : 0 ≤ C := const_nonneg_of_bound ha
  have hc : 0 < 2 * Real.pi * z.im := by
    have := Real.pi_pos
    positivity
  have he : 0 < 1 / d := by positivity
  have hsum : Summable fun n : ℕ =>
      C * ((n : ℝ) ^ (B - w.re)
        * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d)))) :=
    (summable_rpow_mul_exp_neg_rpow hc he).mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, norm_zero]
    have h0 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (B - w.re) := Real.rpow_nonneg (by norm_num) _
    have h1 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * z.im * ((0 : ℕ) : ℝ) ^ (1 / d))) :=
      (Real.exp_pos _).le
    exact mul_nonneg hC (mul_nonneg h0 h1)
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_thetaTerm a d w z hn]
    have hsplit : (n : ℝ) ^ (B - w.re) = (n : ℝ) ^ B * (n : ℝ) ^ (-w.re) := by
      rw [← Real.rpow_add hnR, sub_eq_add_neg]
    rw [hsplit]
    have hexp : (0 : ℝ) < Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d))) :=
      Real.exp_pos _
    have hpow : (0 : ℝ) < (n : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hnR _
    calc ‖a n‖ * (n : ℝ) ^ (-w.re)
          * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d)))
        ≤ (C * (n : ℝ) ^ B) * (n : ℝ) ^ (-w.re)
            * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ha n) hpow.le) hexp.le
      _ = C * ((n : ℝ) ^ B * (n : ℝ) ^ (-w.re)
            * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d)))) := by ring

/-- **Absolute convergence on the upper half plane**, unnormed form. -/
theorem summable_thetaTerm_of_im_pos {a : ℕ → ℂ} {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) {d : ℝ} (hd : 0 < d) (w z : ℂ)
    (hz : 0 < z.im) : Summable fun n : ℕ => thetaTerm a d w z n :=
  (summable_norm_thetaTerm_of_im_pos ha hd w z hz).of_norm

/-- **Absolute convergence of the standard twist.**  On the closed upper half
plane the theta series converges absolutely to the right of the abscissa fixed by
the coefficient bound; this includes the real boundary, where it is the standard
twist. -/
theorem summable_thetaTerm_of_re {a : ℕ → ℂ} {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) {d : ℝ} (w z : ℂ)
    (hz : 0 ≤ z.im) (hw : B + 1 < w.re) :
    Summable fun n : ℕ => thetaTerm a d w z n := by
  have hC : 0 ≤ C := const_nonneg_of_bound ha
  have hsum : Summable fun n : ℕ => C * (((n : ℝ) ^ (w.re - B))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left C
  refine Summable.of_norm_bounded hsum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, norm_zero]
    have h0 : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) ^ (w.re - B))⁻¹ := by positivity
    exact mul_nonneg hC h0
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_thetaTerm a d w z hn]
    have hinv : (((n : ℝ)) ^ (w.re - B))⁻¹ = (n : ℝ) ^ B * (n : ℝ) ^ (-w.re) := by
      rw [← Real.rpow_neg hnR.le, ← Real.rpow_add hnR]
      congr 1
      ring
    rw [hinv]
    have hexp : Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (1 / d) := Real.rpow_nonneg hnR.le _
      have hprod : (0 : ℝ) ≤ 2 * Real.pi * z.im * (n : ℝ) ^ (1 / d) :=
        mul_nonneg (mul_nonneg (by positivity) hz) hnp
      linarith
    have hexp0 : (0 : ℝ) < Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d))) :=
      Real.exp_pos _
    have hpow : (0 : ℝ) < (n : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hnR _
    have hCB : (0 : ℝ) ≤ C * (n : ℝ) ^ B * (n : ℝ) ^ (-w.re) := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ B := Real.rpow_nonneg hnR.le _
      positivity
    calc ‖a n‖ * (n : ℝ) ^ (-w.re)
          * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d)))
        ≤ (C * (n : ℝ) ^ B) * (n : ℝ) ^ (-w.re)
            * Real.exp (-(2 * Real.pi * z.im * (n : ℝ) ^ (1 / d))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ha n) hpow.le) hexp0.le
      _ ≤ (C * (n : ℝ) ^ B) * (n : ℝ) ^ (-w.re) * 1 :=
          mul_le_mul_of_nonneg_left hexp hCB
      _ = C * ((n : ℝ) ^ B * (n : ℝ) ^ (-w.re)) := by ring

end ThetaSeries

end GaloisForLFunctions.HTGeometry
