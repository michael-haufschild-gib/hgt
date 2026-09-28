import GaloisForLFunctions.HTGeometry.BinetLogGamma
import GaloisForLFunctions.RHTower.XiSliceCircleDecay
import GaloisForLFunctions.RHTower.XiHorizontalRatioSelection
import GaloisForLFunctions.RHTower.WeightedEulerPaleyWienerVanishing
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# The theta threshold for `ξ`-divisible transforms

For `F : ℝ → ℂ` write `M_F(s) = ∫ F(x) e^{(s−½)x} dx`. Riemann's kernel `Φ` has `M_Φ = ξ`, so its
transform vanishes on the whole zero divisor of `ζ`, and `|Φ(x)| ≍ e^{9|x|/2} exp(−π e^{2|x|})`.
This file proves that the theta rate `π` is exactly the threshold
(`theta_threshold_xi_divisible`):

* if `|F(x)| ≤ C exp(−c e^{2|x|})` with `c > π` and `M_F = ξ · h` with `h` entire, then `F = 0`
  almost everywhere (`ae_eq_zero_of_centredLaplace_xi_dvd`);
* for every `0 ≤ c < π`, `Φ` has rate `c`, `M_Φ = ξ` and `Φ ≠ 0`
  (`riemannPhiKernel_decay_below_theta`).

So no function decaying faster than Riemann's kernel has a transform divisible by `ξ`: the zero
divisor of `ζ` is a uniqueness set for the rate-`c` class exactly when `c > π`.

**Proof.**
* *Gamma floor.* Gauss' product shows that `|Γ(x+iy)|/Γ(x)` increases in `x`. The reflection
  formula gives `|Γ(1+iy)|² = πy/sinh(πy) ≥ e^{−π|y|}`. So `|Γ(x+iy)| ≥ Γ(x) e^{−π|y|/2}` for
  `x ≥ 1` (`Gamma_mul_exp_le_norm_Gamma`).
* *`ξ` floor.* With `|ζ| ≥ 1/3` on `Re s ≥ 2`, this gives
  `|ξ(σ+it)| ≥ (1/3) π^{−σ/2} Γ(σ/2) e^{−π|t|/4}` for `σ ≥ 2` (`xi_floor`).
* *Legendre growth.* `e^u ≥ 1+u` gives `yx − c e^{2x} ≤ (y/2)(log(y/2c) − 1)`. So `M_F` grows at
  most like `exp((y/2)(log(y/2c') − 1))` with `y = |σ − ½|` and any `c' < c`
  (`norm_centredLaplace_le`).
* *Quotient on the half-planes.* Against Binet's lower bound for `Γ(σ/2)`, the quotient
  `h = M_F/ξ` is `O(e^{Aσ + π|t|/4})` on `Re s ≥ 2`, and it decays like `e^{−(σ/4) log(c'/π)}`
  on the real axis when `c' > π`. The functional equation `ξ(s) = ξ(1−s)` and
  `M_F(1−s) = M_{F(−·)}(s)` transfer both bounds to `Re s ≤ −1`.
* *Strip.* At Burnol's good heights `|ξ(σ ± iT)| ≥ T^{−M}|ξ(2 ± iT)|` for `σ ∈ [−1,2]`. The maximum
  principle on the rectangles `[−1,2] × [−T,T]` then bounds `h` in the strip.
* *Conclusion.* `h` has exponential type and decays exponentially along both real rays, so `h = 0`
  (two-ray Paley–Wiener). Hence `M_F = 0` and `F = 0` by Fourier uniqueness.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-! ## The Gamma floor on vertical lines -/

/-- `|Γ(1+iy)|² = πy / sinh(πy)` from the reflection formula. -/
theorem norm_Gamma_one_add_mul_I_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (1 + y * I)‖ ^ 2 = π * y / Real.sinh (π * y) := by
  set z : ℂ := y * I with hz
  have hz0 : z ≠ 0 := by
    rw [hz]; exact mul_ne_zero (by exact_mod_cast hy) I_ne_zero
  have hconj : (starRingEnd ℂ) (1 + z) = 1 - z := by
    rw [hz]; simp [map_add, map_mul, conj_ofReal, conj_I]; ring
  have hmul : Complex.Gamma (1 + z) * (starRingEnd ℂ) (Complex.Gamma (1 + z)) =
      z * (π / Complex.sin (π * z)) := by
    rw [← Complex.Gamma_conj, hconj, add_comm, Complex.Gamma_add_one z hz0, mul_assoc,
      Complex.Gamma_mul_Gamma_one_sub]
  have hsin : Complex.sin (π * z) = Complex.sinh (π * y) * I := by
    rw [hz, ← mul_assoc, Complex.sin_mul_I]
  have hsinh_ne : Real.sinh (π * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hy
  rw [Complex.mul_conj, hsin, ← Complex.ofReal_mul, ← Complex.ofReal_sinh] at hmul
  have hR : z * (π / (((Real.sinh (π * y) : ℝ) : ℂ) * I)) =
      ((π * y / Real.sinh (π * y) : ℝ) : ℂ) := by
    have hs : ((Real.sinh (π * y) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsinh_ne
    rw [hz]
    push_cast
    field_simp
  rw [hR, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] at hmul
  exact hmul

/-- `u / sinh u ≥ e^{-u}` for `u > 0`. -/
theorem exp_neg_le_div_sinh {u : ℝ} (hu : 0 < u) : Real.exp (-u) ≤ u / Real.sinh u := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  rw [le_div_iff₀ hs, Real.sinh_eq]
  have h1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (-u) * Real.exp (-u) = Real.exp (-(2 * u)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - 2 * u ≤ Real.exp (-(2 * u)) := by
    have := Real.add_one_le_exp (-(2 * u)); linarith
  nlinarith

/-- `|Γ(1+iy)| ≥ e^{-π|y|/2}`. -/
theorem exp_neg_le_norm_Gamma_one_add_mul_I (y : ℝ) :
    Real.exp (-(π * |y| / 2)) ≤ ‖Complex.Gamma (1 + y * I)‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hsq := norm_Gamma_one_add_mul_I_sq hy
  have hpos : 0 < π * |y| := mul_pos Real.pi_pos (abs_pos.mpr hy)
  have hsym : π * y / Real.sinh (π * y) = π * |y| / Real.sinh (π * |y|) := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.sinh_neg, div_neg, neg_div, neg_neg]
  have hlow := exp_neg_le_div_sinh hpos
  rw [← hsym, ← hsq] at hlow
  have he : Real.exp (-(π * |y| / 2)) ^ 2 = Real.exp (-(π * |y|)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← he] at hlow
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).mp hlow

/-- The Gauss-product ratio `|GammaSeq(x+iy) n| = GammaSeq x n · ∏ (x+j)/|x+j+iy|`. -/
theorem norm_GammaSeq_ofReal_add_mul_I {x : ℝ} (hx : 0 < x) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq (x + y * I) n‖ = Real.GammaSeq x n *
      ∏ j ∈ Finset.range (n + 1), ((x + j) / ‖((x + j : ℝ) : ℂ) + y * I‖) := by
  unfold Complex.GammaSeq Real.GammaSeq
  have hprod_pos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) :=
    Finset.prod_pos fun j _ => by positivity
  have hnorm_ne : ∀ j ∈ Finset.range (n + 1), ‖((x + j : ℝ) : ℂ) + y * I‖ ≠ 0 := by
    intro j _
    rw [norm_ne_zero_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hn, norm_prod, Complex.norm_natCast]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  rw [Finset.prod_div_distrib]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖(x : ℂ) + y * I + (j : ℂ)‖ = ‖((x + j : ℝ) : ℂ) + y * I‖ := by
    intro j _; congr 1; push_cast; ring
  rw [Finset.prod_congr rfl hterm]
  have hden_pos : 0 < ∏ j ∈ Finset.range (n + 1), ‖((x + j : ℝ) : ℂ) + y * I‖ :=
    Finset.prod_pos fun j hj => lt_of_le_of_ne (norm_nonneg _) (hnorm_ne j hj).symm
  field_simp

/-- Each Gauss factor `t/|t+iy|` is increasing in `t > 0`. -/
theorem div_norm_add_mul_I_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (y : ℝ) :
    s / ‖((s : ℝ) : ℂ) + y * I‖ ≤ t / ‖((t : ℝ) : ℂ) + y * I‖ := by
  have hnorm : ∀ u : ℝ, ‖((u : ℝ) : ℂ) + y * I‖ = Real.sqrt (u ^ 2 + y ^ 2) := by
    intro u
    rw [Complex.norm_add_mul_I]
  rw [hnorm, hnorm]
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hsq : 0 < Real.sqrt (s ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have htq : 0 < Real.sqrt (t ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hsq htq]
  -- `s² (t² + y²) ≤ t² (s² + y²)` and both sides are nonnegative
  have key : (s * Real.sqrt (t ^ 2 + y ^ 2)) ^ 2 ≤ (t * Real.sqrt (s ^ 2 + y ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs.le hst 2
    nlinarith [sq_nonneg y]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key

/-- **Gamma floor.** For `x ≥ 1`, `|Γ(x+iy)| ≥ Γ(x)|Γ(1+iy)|`: the Gauss factors
`(x+j)/|x+j+iy|` increase with `x`. -/
theorem Gamma_mul_norm_Gamma_one_le {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    Real.Gamma x * ‖Complex.Gamma (1 + y * I)‖ ≤ ‖Complex.Gamma (x + y * I)‖ := by
  have hx0 : 0 < x := by linarith
  have hlimx := (Complex.GammaSeq_tendsto_Gamma (x + y * I)).norm
  have hlim1 := (Complex.GammaSeq_tendsto_Gamma (1 + y * I)).norm
  have hlimr := Real.GammaSeq_tendsto_Gamma x
  have hlimr1 := Real.GammaSeq_tendsto_Gamma 1
  rw [Real.Gamma_one] at hlimr1
  -- `‖GS(x+iy)‖ · GS(1) ≥ GS(x) · ‖GS(1+iy)‖` for every `n ≥ 1`
  have hineq : ∀ᶠ n : ℕ in atTop,
      Real.GammaSeq x n * ‖Complex.GammaSeq (1 + y * I) n‖ ≤
        ‖Complex.GammaSeq (x + y * I) n‖ * Real.GammaSeq 1 n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have e1 := norm_GammaSeq_ofReal_add_mul_I one_pos y hn
    have ex := norm_GammaSeq_ofReal_add_mul_I hx0 y hn
    rw [Complex.ofReal_one] at e1
    rw [e1, ex]
    have hGx : 0 ≤ Real.GammaSeq x n := by
      unfold Real.GammaSeq
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (Finset.prod_nonneg fun j _ => by positivity)
    have hG1 : 0 ≤ Real.GammaSeq 1 n := by
      unfold Real.GammaSeq
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (Finset.prod_nonneg fun j _ => by positivity)
    have hprod : ∏ j ∈ Finset.range (n + 1), ((1 + (j : ℝ)) / ‖((1 + j : ℝ) : ℂ) + y * I‖) ≤
        ∏ j ∈ Finset.range (n + 1), ((x + j) / ‖((x + j : ℝ) : ℂ) + y * I‖) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j _
        exact div_norm_add_mul_I_mono (by positivity) (by linarith) y
    have hm := mul_le_mul_of_nonneg_left hprod (mul_nonneg hGx hG1)
    generalize ∏ j ∈ Finset.range (n + 1), ((1 + (j : ℝ)) / ‖((1 + j : ℝ) : ℂ) + y * I‖) = P1
      at hm ⊢
    generalize ∏ j ∈ Finset.range (n + 1), ((x + j) / ‖((x + j : ℝ) : ℂ) + y * I‖) = Px at hm ⊢
    generalize Real.GammaSeq x n = A at hm ⊢
    generalize Real.GammaSeq 1 n = B at hm ⊢
    linarith [hm, show A * (B * P1) = A * B * P1 by ring, show A * Px * B = A * B * Px by ring]
  have h := le_of_tendsto_of_tendsto (hlimr.mul hlim1) (hlimx.mul hlimr1) hineq
  simpa using h

/-- `|Γ(x+iy)| ≥ Γ(x) e^{-π|y|/2}` for `x ≥ 1`. -/
theorem Gamma_mul_exp_le_norm_Gamma {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    Real.Gamma x * Real.exp (-(π * |y| / 2)) ≤ ‖Complex.Gamma (x + y * I)‖ :=
  (mul_le_mul_of_nonneg_left (exp_neg_le_norm_Gamma_one_add_mul_I y)
    (Real.Gamma_pos_of_pos (by linarith)).le).trans (Gamma_mul_norm_Gamma_one_le hx y)

/-! ## The `ζ`, `Γ` and `ξ` floors on `Re s ≥ 2` -/

/-- `‖ζ(s) − 1‖ ≤ π²/6 − 1` on `Re s ≥ 2`. -/
theorem norm_riemannZeta_sub_one_le_zeta_two {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ π ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  have hsum0 : Summable fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s :=
    Complex.summable_one_div_nat_cpow.mpr hs1
  have hsum : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    have hshift : Summable fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s :=
      (summable_nat_add_iff 1).mpr hsum0
    refine hshift.congr fun n => ?_
    norm_num
  have hsplit : riemannZeta s - 1 = ∑' k : ℕ, (1 : ℂ) / ((k : ℂ) + 2) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1, hsum.tsum_eq_zero_add]
    have hterm : ∀ k : ℕ, (1 : ℂ) / (((k + 1 : ℕ) : ℂ) + 1) ^ s = 1 / ((k : ℂ) + 2) ^ s := by
      intro k
      norm_num
      ring_nf
    rw [tsum_congr hterm]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one]
    ring
  have hw : HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at h
    norm_num at h
    refine h.congr_fun fun k => ?_
    ring_nf
  have hbound : ∀ k : ℕ, ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖ ≤ (1 : ℝ) / ((k : ℝ) + 2) ^ 2 := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hcast : (((k : ℝ) + 2 : ℝ) : ℂ) = (k : ℂ) + 2 := by push_cast; ring
    rw [norm_div, norm_one, ← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hk]
    apply one_div_le_one_div_of_le (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k])
      (by norm_num; linarith)
  have hsn : Summable fun k : ℕ => ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖ :=
    hw.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [hsplit]
  exact (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hbound hw.summable).trans_eq hw.tsum_eq)

/-- `‖ζ(s)‖ ≥ 1/3` on `Re s ≥ 2`. -/
theorem one_third_le_norm_riemannZeta {s : ℂ} (hs : 2 ≤ s.re) : 1 / 3 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le_zeta_two hs
  have hpi : π ^ 2 / 6 - 1 ≤ 2 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h4 := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  simp only [norm_one, sub_sub_cancel] at h4
  rw [norm_sub_rev] at h
  linarith

/-- Binet's formula with its nonpositive kernel: `log Γ(a) ≥ (a − ½) log a − a + ½ log 2π`. -/
theorem stirling_le_log_Gamma {a : ℝ} (ha : 0 < a) :
    (a - 1 / 2) * Real.log a - a + Real.log (2 * π) / 2 ≤ Real.log (Real.Gamma a) := by
  rw [GaloisForLFunctions.HTGeometry.log_Gamma_eq_binet ha]
  have hK : GaloisForLFunctions.HTGeometry.binetKernel a ≤ 0 := by
    unfold GaloisForLFunctions.HTGeometry.binetKernel
    refine setIntegral_nonpos measurableSet_Ioi fun x _ => ?_
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    unfold GaloisForLFunctions.HTGeometry.bernoulliHalfPer
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    nlinarith
  linarith

/-- **`ξ` floor.** For `σ ≥ 2`, `|ξ(σ+it)| ≥ (1/3) π^{-σ/2} Γ(σ/2) e^{-π|t|/4}`. -/
theorem xi_floor {σ t : ℝ} (hσ : 2 ≤ σ) :
    1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * Real.exp (-(π * |t| / 4)) ≤
      ‖xi ((σ : ℂ) + (t : ℂ) * I)‖ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  rw [norm_xi_eq_factors (by rw [hsre]; linarith) hs1, hsre]
  have hpoly : 1 ≤ ‖s * (s - 1) / 2‖ := by
    rw [norm_mul_sub_one_div_two]
    have h1 : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_of_pos (by linarith)] at this
      simpa using this
    have h2 : σ - 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re, abs_of_pos (by linarith)] at this
      simpa using this
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hG : Real.Gamma (σ / 2) * Real.exp (-(π * |t / 2| / 2)) ≤ ‖Complex.Gamma (s / 2)‖ := by
    have := Gamma_mul_exp_le_norm_Gamma (x := σ / 2) (by linarith) (t / 2)
    convert this using 2
    rw [hs]; push_cast; ring_nf
  have ht : π * |t / 2| / 2 = π * |t| / 4 := by rw [abs_div, abs_two]; ring
  rw [ht] at hG
  have hZ := one_third_le_norm_riemannZeta (s := s) (by rw [hsre]; exact hσ)
  have hpi : 0 < Real.pi ^ (-(σ / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have he : 0 < Real.exp (-(π * |t| / 4)) := Real.exp_pos _
  calc 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * Real.exp (-(π * |t| / 4))
      = (Real.pi ^ (-(σ / 2)) * (Real.Gamma (σ / 2) * Real.exp (-(π * |t| / 4)))) * (1 / 3) := by
        ring
    _ ≤ (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) * ‖riemannZeta s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hG hpi.le) hZ (by norm_num) (by positivity)
    _ ≤ ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖) *
          ‖riemannZeta s‖ := by
        have : 0 ≤ Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
          positivity
        nlinarith

/-! ## Growth of the centred Laplace transform -/

/-- The centred two-sided Laplace transform `M_F(s) = ∫ F(x) e^{(s−½)x} dx`. -/
def centredLaplace (F : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, cexp ((s - 1 / 2) * x) * F x

/-- The Legendre majorant `max(0, (y/2)(log(y/2c) − 1))` of `x ↦ yx − c e^{2x}`. -/
def legendreMajorant (c y : ℝ) : ℝ := max 0 (y / 2 * (Real.log (y / (2 * c)) - 1))

theorem le_legendreMajorant {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (x : ℝ) :
    y * x - c * Real.exp (2 * x) ≤ legendreMajorant c y := by
  unfold legendreMajorant
  rcases hy.lt_or_eq with hy | rfl
  · refine le_max_of_le_right ?_
    set u := 2 * x - Real.log (y / (2 * c)) with hu
    have hq : 0 < y / (2 * c) := by positivity
    have hexp : c * Real.exp (2 * x) = y / 2 * Real.exp u := by
      rw [hu, Real.exp_sub, Real.exp_log hq]
      field_simp
    have h1 := Real.add_one_le_exp u
    rw [hexp]
    have : y / 2 * (u + 1) ≤ y / 2 * Real.exp u := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hu] at this
    nlinarith
  · refine le_max_of_le_left ?_
    have := Real.exp_pos (2 * x)
    nlinarith

theorem legendreMajorant_nonneg (c y : ℝ) : 0 ≤ legendreMajorant c y := le_max_left _ _

/-- The Gaussian integral constant `√(π/(2δ))`. -/
theorem norm_centredLaplace_le {F : ℝ → ℂ} {C c δ : ℝ} (hδ : 0 < δ) (hcδ : δ < c)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|)))) (s : ℂ) :
    ‖centredLaplace F s‖ ≤
      C * Real.exp (legendreMajorant (c - δ) |s.re - 1 / 2|) * Real.sqrt (π / (2 * δ)) := by
  have hC : 0 ≤ C := by
    have := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (-(c * Real.exp (2 * |(0 : ℝ)|)))
    by_contra hneg
    push Not at hneg
    nlinarith
  set G := legendreMajorant (c - δ) |s.re - 1 / 2| with hG
  have hpt : ∀ x : ℝ, ‖cexp ((s - 1 / 2) * x) * F x‖ ≤
      C * Real.exp G * Real.exp (-(2 * δ) * x ^ 2) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    have hre : ((s - 1 / 2) * (x : ℂ)).re = (s.re - 1 / 2) * x := by simp
    rw [hre]
    have hlin : (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
      calc (s.re - 1 / 2) * x ≤ |(s.re - 1 / 2) * x| := le_abs_self _
        _ = |s.re - 1 / 2| * |x| := abs_mul _ _
    have hleg := le_legendreMajorant (c := c - δ) (by linarith) (abs_nonneg (s.re - 1 / 2)) |x|
    have hq : 2 * x ^ 2 ≤ Real.exp (2 * |x|) := by
      have := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |x|)
      have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [abs_nonneg x]
    have hexp : (s.re - 1 / 2) * x + -(c * Real.exp (2 * |x|)) ≤ G + -(2 * δ) * x ^ 2 := by
      rw [hG]; nlinarith
    calc Real.exp ((s.re - 1 / 2) * x) * ‖F x‖
        ≤ Real.exp ((s.re - 1 / 2) * x) * (C * Real.exp (-(c * Real.exp (2 * |x|)))) :=
          mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
      _ = C * Real.exp ((s.re - 1 / 2) * x + -(c * Real.exp (2 * |x|))) := by
          rw [Real.exp_add]; ring
      _ ≤ C * Real.exp (G + -(2 * δ) * x ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = C * Real.exp G * Real.exp (-(2 * δ) * x ^ 2) := by rw [Real.exp_add]; ring
  have hint : Integrable fun x : ℝ => C * Real.exp G * Real.exp (-(2 * δ) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (by linarith)).const_mul _
  unfold centredLaplace
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul, integral_gaussian]


/-! ## The quotient on the right half-plane `Re s ≥ 2` -/

theorem legendreMajorant_mono {c y₁ y₂ : ℝ} (hc : 0 < c) (hy₁ : 0 ≤ y₁) (h12 : y₁ ≤ y₂) :
    legendreMajorant c y₁ ≤ legendreMajorant c y₂ := by
  unfold legendreMajorant
  refine max_le (le_max_left _ _) ?_
  by_cases hf : y₁ / 2 * (Real.log (y₁ / (2 * c)) - 1) ≤ 0
  · exact hf.trans (le_max_left _ _)
  · push Not at hf
    have hy₁pos : 0 < y₁ := by
      rcases hy₁.lt_or_eq with h | h
      · exact h
      · rw [← h] at hf; simp at hf
    have hlog : 1 < Real.log (y₁ / (2 * c)) := by
      by_contra hcon; push Not at hcon
      have : y₁ / 2 * (Real.log (y₁ / (2 * c)) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith
    have hlog2 : Real.log (y₁ / (2 * c)) ≤ Real.log (y₂ / (2 * c)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right h12 (by positivity))
    refine le_max_of_le_right ?_
    have := mul_le_mul (div_le_div_of_nonneg_right h12 (by norm_num : (0 : ℝ) ≤ 2))
      (by linarith : Real.log (y₁ / (2 * c)) - 1 ≤ Real.log (y₂ / (2 * c)) - 1)
      (by linarith) (by linarith)
    linarith

/-- Crude bound: `legendreMajorant c y ≤ (σ/2)(log σ + |log 2c|)` for `0 ≤ y ≤ σ`, `σ ≥ 2`. -/
theorem legendreMajorant_le_crude {c y σ : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hyσ : y ≤ σ)
    (hσ : 2 ≤ σ) :
    legendreMajorant c y ≤ σ / 2 * (Real.log σ + |Real.log (2 * c)|) := by
  have hσl : 0 < Real.log σ := Real.log_pos (by linarith)
  have hR : 0 ≤ σ / 2 * (Real.log σ + |Real.log (2 * c)|) := by positivity
  unfold legendreMajorant
  refine max_le hR ?_
  rcases hy.lt_or_eq with hy0 | rfl
  · have hl : Real.log (y / (2 * c)) = Real.log y - Real.log (2 * c) :=
      Real.log_div hy0.ne' (by positivity)
    have hly : Real.log y ≤ Real.log σ := Real.log_le_log hy0 hyσ
    have hab := neg_abs_le (Real.log (2 * c))
    by_cases hX : Real.log (y / (2 * c)) - 1 ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hX).trans hR
    · push Not at hX
      calc y / 2 * (Real.log (y / (2 * c)) - 1)
          ≤ σ / 2 * (Real.log (y / (2 * c)) - 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hX.le
        _ ≤ σ / 2 * (Real.log σ + |Real.log (2 * c)|) :=
            mul_le_mul_of_nonneg_left (by rw [hl]; linarith) (by positivity)
  · simpa using hR

/-- The exponential-type factor on the right half-plane:
`e^{G} π^{σ/2} / Γ(σ/2) ≤ e^{(|log 2c|/2 + 3) σ}` for `σ ≥ 2`, `G = legendreMajorant c (σ − ½)`. -/
theorem legendre_div_Gamma_le_exp {c σ : ℝ} (hc : 0 < c) (hσ : 2 ≤ σ) :
    Real.exp (legendreMajorant c (σ - 1 / 2)) * Real.pi ^ (σ / 2) / Real.Gamma (σ / 2) ≤
      Real.exp ((|Real.log (2 * c)| / 2 + 3) * σ) := by
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hst := stirling_le_log_Gamma (a := σ / 2) (by linarith)
  have hG := legendreMajorant_le_crude hc (y := σ - 1 / 2) (σ := σ) (by linarith) (by linarith) hσ
  have hlog2 : Real.log σ = Real.log 2 + Real.log (σ / 2) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]; ring_nf
  have hl2 : Real.log (σ / 2) ≤ σ / 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < σ / 2 by linarith); linarith
  have hl2' : 0 ≤ Real.log (σ / 2) := Real.log_nonneg (by linarith)
  have hlpi : Real.log π ≤ π - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 : π < 3.15 := Real.pi_lt_d2
  have hl2v : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hl2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hexpo : legendreMajorant c (σ - 1 / 2) + σ / 2 * Real.log π - Real.log (Real.Gamma (σ / 2))
      ≤ (|Real.log (2 * c)| / 2 + 3) * σ := by
    nlinarith [abs_nonneg (Real.log (2 * c))]
  rw [div_le_iff₀ hΓ, ← Real.exp_log hΓ, ← Real.exp_add]
  have hpi : Real.pi ^ (σ / 2) = Real.exp (σ / 2 * Real.log π) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; ring_nf
  rw [hpi, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The decay factor on the real axis: for `c > π` and `σ ≥ 2e c + ½` (and `σ ≥ 2`),
`e^{G} π^{σ/2} / Γ(σ/2) ≤ e^{-(1+log κ)/2} e^{-κσ/4}` with `κ = log(c/π) > 0`. -/
theorem legendre_div_Gamma_le_decay {c σ : ℝ} (hc : π < c) (hσ : 2 ≤ σ)
    (hσ1 : 2 * Real.exp 1 * c + 1 / 2 ≤ σ) :
    Real.exp (legendreMajorant c (σ - 1 / 2)) * Real.pi ^ (σ / 2) / Real.Gamma (σ / 2) ≤
      Real.exp (-(1 + Real.log (Real.log (c / π))) / 2) *
        Real.exp (-(Real.log (c / π) / 4 * σ)) := by
  have hc0 : 0 < c := lt_trans Real.pi_pos hc
  set κ := Real.log (c / π) with hκ
  have hκpos : 0 < κ := Real.log_pos (by rw [lt_div_iff₀ Real.pi_pos]; linarith)
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hst := stirling_le_log_Gamma (a := σ / 2) (by linarith)
  set y := σ - 1 / 2 with hy
  have hypos : 0 < y := by linarith
  have hy1 : 1 ≤ Real.log (y / (2 * c)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith
  have hG : legendreMajorant c y = y / 2 * (Real.log (y / (2 * c)) - 1) := by
    unfold legendreMajorant
    exact max_eq_right (mul_nonneg (by positivity) (by linarith))
  have hlogσ : Real.log (y / (2 * c)) ≤ Real.log (σ / (2 * c)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hGσ : legendreMajorant c y ≤ σ / 2 * (Real.log (σ / (2 * c)) - 1) := by
    rw [hG]
    have := mul_le_mul (div_le_div_of_nonneg_right (show y ≤ σ by linarith)
      (by norm_num : (0 : ℝ) ≤ 2)) (by linarith : Real.log (y / (2 * c)) - 1 ≤
        Real.log (σ / (2 * c)) - 1) (by linarith) (by linarith)
    linarith
  have hsplit : Real.log (σ / (2 * c)) = Real.log (σ / 2) - Real.log c := by
    rw [show σ / (2 * c) = (σ / 2) / c by ring, Real.log_div (by linarith) hc0.ne']
  have hκe : κ = Real.log c - Real.log π := by
    rw [hκ, Real.log_div hc0.ne' Real.pi_pos.ne']
  have hlogκ : Real.log (σ / 2) ≤ κ / 2 * σ - 1 - Real.log κ := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < κ / 2 * σ by positivity)
    have h2 : Real.log (κ / 2 * σ) = Real.log κ + Real.log (σ / 2) := by
      rw [← Real.log_mul hκpos.ne' (by linarith)]; ring_nf
    linarith
  have hl2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hexpo : legendreMajorant c y + σ / 2 * Real.log π - Real.log (Real.Gamma (σ / 2))
      ≤ -(1 + Real.log κ) / 2 + -(κ / 4 * σ) := by
    have e1 : σ / 2 * (Real.log (σ / (2 * c)) - 1) + σ / 2 * Real.log π
        - ((σ / 2 - 1 / 2) * Real.log (σ / 2) - σ / 2 + Real.log (2 * π) / 2)
        = -(κ / 2) * σ + Real.log (σ / 2) / 2 - Real.log (2 * π) / 2 := by
      rw [hsplit, hκe]; ring
    nlinarith
  rw [div_le_iff₀ hΓ, ← Real.exp_log hΓ, ← Real.exp_add, ← Real.exp_add]
  have hpi : Real.pi ^ (σ / 2) = Real.exp (σ / 2 * Real.log π) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; ring_nf
  rw [hpi, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Quotient bound on `Re s ≥ 2`.** If `M_F = ξ · H` there and `‖M_F(s)‖ ≤ K e^{G(|σ−½|)}`,
then `‖H(σ+it)‖ ≤ 3K · e^{G(σ−½)} π^{σ/2}/Γ(σ/2) · e^{π|t|/4}`. -/
theorem norm_quotient_le_right {F H : ℂ → ℂ} {K c σ t : ℝ} (hσ : 2 ≤ σ)
    (hdiv : F ((σ : ℂ) + (t : ℂ) * I) = xi ((σ : ℂ) + (t : ℂ) * I) * H ((σ : ℂ) + (t : ℂ) * I))
    (hM : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * Real.exp (legendreMajorant c (σ - 1 / 2))) :
    ‖H ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      3 * K * (Real.exp (legendreMajorant c (σ - 1 / 2)) * Real.pi ^ (σ / 2) /
        Real.Gamma (σ / 2)) * Real.exp (π * |t| / 4) := by
  have hfl := xi_floor (t := t) hσ
  have hΓ : 0 < Real.Gamma (σ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpiσ : 0 < Real.pi ^ (-(σ / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  set f := 1 / 3 * (Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2)) * Real.exp (-(π * |t| / 4)) with hf
  have hfpos : 0 < f := by positivity
  have hnorm : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ =
      ‖xi ((σ : ℂ) + (t : ℂ) * I)‖ * ‖H ((σ : ℂ) + (t : ℂ) * I)‖ := by
    rw [hdiv, norm_mul]
  have h1 : f * ‖H ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * Real.exp (legendreMajorant c (σ - 1 / 2)) := by
    calc f * ‖H ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖xi ((σ : ℂ) + (t : ℂ) * I)‖ * ‖H ((σ : ℂ) + (t : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
      _ ≤ _ := hnorm ▸ hM
  have hinv : 1 / f = 3 * (Real.pi ^ (σ / 2) / Real.Gamma (σ / 2)) * Real.exp (π * |t| / 4) := by
    rw [hf, Real.rpow_neg Real.pi_pos.le, Real.exp_neg]
    field_simp
  rw [← le_div_iff₀' hfpos] at h1
  calc ‖H ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * Real.exp (legendreMajorant c (σ - 1 / 2)) / f := h1
    _ = K * Real.exp (legendreMajorant c (σ - 1 / 2)) * (1 / f) := by ring
    _ = _ := by rw [hinv]; ring


/-! ## Reflection and the two half-planes -/

theorem decay_const_nonneg {F : ℝ → ℂ} {C c : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|)))) : 0 ≤ C := by
  have h1 := hF 0
  have h2 := norm_nonneg (F 0)
  have h3 := Real.exp_pos (-(c * Real.exp (2 * |(0 : ℝ)|)))
  by_contra hneg
  push Not at hneg
  nlinarith

/-- `M_F(1 − s) = M_{F(−·)}(s)`. -/
theorem centredLaplace_one_sub (F : ℝ → ℂ) (s : ℂ) :
    centredLaplace F (1 - s) = centredLaplace (fun x => F (-x)) s := by
  unfold centredLaplace
  rw [← integral_neg_eq_self (fun x : ℝ => cexp ((s - 1 / 2) * x) * F (-x))]
  congr 1; funext x
  simp only [neg_neg]
  congr 1; push_cast; ring_nf

/-- The right half-plane bound for the quotient `h = M_F/ξ`. -/
theorem norm_quotient_le_exp_right {F : ℝ → ℂ} {h : ℂ → ℂ} {C c δ : ℝ} (hδ : 0 < δ)
    (hcδ : δ < c) (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))))
    (hdiv : ∀ s : ℂ, 2 ≤ s.re → centredLaplace F s = xi s * h s) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖h s‖ ≤ 3 * (C * Real.sqrt (π / (2 * δ))) *
      Real.exp ((|Real.log (2 * (c - δ))| / 2 + 3) * s.re) * Real.exp (π * |s.im| / 4) := by
  have hC := decay_const_nonneg hF
  set σ := s.re; set t := s.im
  have hs' : s = (σ : ℂ) + (t : ℂ) * I := (Complex.re_add_im s).symm
  have hMb := norm_centredLaplace_le hδ hcδ hF s
  have habs : |s.re - 1 / 2| = σ - 1 / 2 := abs_of_pos (by linarith)
  rw [habs] at hMb
  have hdiv' := hdiv s hs
  rw [hs'] at hMb hdiv'
  rw [hs']
  have hq := norm_quotient_le_right (F := centredLaplace F) (H := h)
    (K := C * Real.sqrt (π / (2 * δ))) (c := c - δ) hs hdiv'
    (by rw [show C * Real.sqrt (π / (2 * δ)) * Real.exp (legendreMajorant (c - δ) (σ - 1 / 2))
        = C * Real.exp (legendreMajorant (c - δ) (σ - 1 / 2)) * Real.sqrt (π / (2 * δ)) by ring]
        exact hMb)
  have hl := legendre_div_Gamma_le_exp (c := c - δ) (by linarith) hs
  have hK : 0 ≤ 3 * (C * Real.sqrt (π / (2 * δ))) := by positivity
  calc ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤ _ := hq
    _ ≤ 3 * (C * Real.sqrt (π / (2 * δ))) *
          Real.exp ((|Real.log (2 * (c - δ))| / 2 + 3) * σ) * Real.exp (π * |t| / 4) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hK) (Real.exp_pos _).le
    _ = _ := by simp

/-- The real-axis decay of the quotient for `c − δ > π`. -/
theorem norm_quotient_le_decay {F : ℝ → ℂ} {h : ℂ → ℂ} {C c δ : ℝ} (hδ : 0 < δ)
    (hπ : π < c - δ) (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))))
    (hdiv : ∀ s : ℂ, 2 ≤ s.re → centredLaplace F s = xi s * h s) {σ : ℝ} (hσ : 2 ≤ σ)
    (hσ1 : 2 * Real.exp 1 * (c - δ) + 1 / 2 ≤ σ) :
    ‖h σ‖ ≤ 3 * (C * Real.sqrt (π / (2 * δ))) *
      (Real.exp (-(1 + Real.log (Real.log ((c - δ) / π))) / 2) *
        Real.exp (-(Real.log ((c - δ) / π) / 4 * σ))) := by
  have hC := decay_const_nonneg hF
  have hcδ : δ < c := by linarith [Real.pi_pos]
  have hMb := norm_centredLaplace_le hδ hcδ hF (σ : ℂ)
  have habs : |(σ : ℂ).re - 1 / 2| = σ - 1 / 2 := by
    rw [Complex.ofReal_re]; exact abs_of_pos (by linarith)
  rw [habs] at hMb
  have hσc : (σ : ℂ) = (σ : ℂ) + ((0 : ℝ) : ℂ) * I := by simp
  have hq := norm_quotient_le_right (F := centredLaplace F) (H := h)
    (K := C * Real.sqrt (π / (2 * δ))) (c := c - δ) (t := 0) hσ
    (by rw [← hσc]; exact hdiv _ (by simpa using hσ))
    (by rw [← hσc, show C * Real.sqrt (π / (2 * δ)) * Real.exp (legendreMajorant (c - δ) (σ - 1 / 2))
        = C * Real.exp (legendreMajorant (c - δ) (σ - 1 / 2)) * Real.sqrt (π / (2 * δ)) by ring]
        exact hMb)
  rw [← hσc] at hq
  simp only [abs_zero, mul_zero, zero_div, Real.exp_zero, mul_one] at hq
  have hl := legendre_div_Gamma_le_decay hπ hσ hσ1
  have hK : 0 ≤ 3 * (C * Real.sqrt (π / (2 * δ))) := by positivity
  exact hq.trans (mul_le_mul_of_nonneg_left hl hK)


/-! ## Maximum principle on rectangles -/

/-- The maximum modulus principle on the closed rectangle `[x₀,x₁] × [y₀,y₁]`. -/
theorem norm_le_of_rectangle_frontier_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) {C : ℝ}
    (hC : ∀ u : ℂ, x₀ ≤ u.re → u.re ≤ x₁ → y₀ ≤ u.im → u.im ≤ y₁ →
      (u.re = x₀ ∨ u.re = x₁ ∨ u.im = y₀ ∨ u.im = y₁) → ‖f u‖ ≤ C)
    {z : ℂ} (h1 : x₀ ≤ z.re) (h2 : z.re ≤ x₁) (h3 : y₀ ≤ z.im) (h4 : z.im ≤ y₁) :
    ‖f z‖ ≤ C := by
  have hb : Bornology.IsBounded (Set.Ioo x₀ x₁ ×ℂ Set.Ioo y₀ y₁) :=
    (Metric.isBounded_Ioo x₀ x₁).reProdIm (Metric.isBounded_Ioo y₀ y₁)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hb hf.diffContOnCl (fun u hu => ?_) ?_
  · rw [Complex.frontier_reProdIm, closure_Ioo hx.ne, closure_Ioo hy.ne, frontier_Ioo hx,
      frontier_Ioo hy] at hu
    rcases hu with ⟨hre, him⟩ | ⟨hre, him⟩
    · have hre' : u.re ∈ Set.Icc x₀ x₁ := hre
      have him' : u.im ∈ ({y₀, y₁} : Set ℝ) := him
      rcases him' with h | h
      · exact hC u hre'.1 hre'.2 (le_of_eq h.symm) (by rw [h]; exact hy.le)
          (Or.inr (Or.inr (Or.inl h)))
      · exact hC u hre'.1 hre'.2 (by rw [h]; exact hy.le) (le_of_eq h)
          (Or.inr (Or.inr (Or.inr h)))
    · have hre' : u.re ∈ ({x₀, x₁} : Set ℝ) := hre
      have him' : u.im ∈ Set.Icc y₀ y₁ := him
      rcases hre' with h | h
      · exact hC u (le_of_eq h.symm) (by rw [h]; exact hx.le) him'.1 him'.2 (Or.inl h)
      · exact hC u (by rw [h]; exact hx.le) (le_of_eq h) him'.1 him'.2 (Or.inr (Or.inl h))
  · rw [Complex.closure_reProdIm, closure_Ioo hx.ne, closure_Ioo hy.ne]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-! ## Exponential type of the quotient -/

/-- The reflected function inherits the double-exponential decay. -/
theorem decay_reflect {F : ℝ → ℂ} {C c : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|)))) :
    ∀ x, ‖(fun y => F (-y)) x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))) := by
  intro x; simpa [abs_neg] using hF (-x)

/-- The reflected quotient `w ↦ h(1 − w)` divides the reflected transform. -/
theorem centredLaplace_reflect_eq {F : ℝ → ℂ} {h : ℂ → ℂ}
    (hdiv : ∀ s, centredLaplace F s = xi s * h s) (w : ℂ) :
    centredLaplace (fun x => F (-x)) w = xi w * h (1 - w) := by
  rw [← centredLaplace_one_sub, hdiv, xi_one_sub]

/-- The `ξ` floor at abscissa `2`: `|ξ(2+it)| ≥ e^{-π|t|/4}/(3π)`. -/
theorem xi_floor_two (t : ℝ) :
    Real.exp (-(π * |t| / 4)) / (3 * π) ≤ ‖xi ((2 : ℂ) + (t : ℂ) * I)‖ := by
  have := xi_floor (σ := 2) (t := t) le_rfl
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.Gamma_one, Real.rpow_neg_one] at this
  have e : ((2 : ℝ) : ℂ) = 2 := by norm_num
  rw [e] at this
  calc Real.exp (-(π * |t| / 4)) / (3 * π) = 1 / 3 * (π⁻¹ * 1) * Real.exp (-(π * |t| / 4)) := by
        field_simp
    _ ≤ _ := this

/-- **Horizontal side of a good rectangle.** At a good height `T` the quotient is at most
`3π K e^{G₀} T^M e^{πT/4}` along `Im u = ±T`, `−1 ≤ Re u ≤ 2`. -/
theorem norm_quotient_le_horizontal {F : ℝ → ℂ} {h : ℂ → ℂ} {K G₀ T : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hdiv : ∀ s, centredLaplace F s = xi s * h s)
    (hMstrip : ∀ u : ℂ, -1 ≤ u.re → u.re ≤ 2 → ‖centredLaplace F u‖ ≤ K * Real.exp G₀)
    (hgood : ∀ σ τ : ℝ, -1 ≤ σ → σ ≤ 2 → -1 ≤ τ → τ ≤ 2 →
        ‖xi ((σ : ℂ) + (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) + (T : ℂ) * I)‖ ∧
          ‖xi ((σ : ℂ) - (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) - (T : ℂ) * I)‖)
    {u : ℂ} (hu1 : -1 ≤ u.re) (hu2 : u.re ≤ 2) (hsign : |u.im| = T) :
    ‖h u‖ ≤ 3 * π * K * Real.exp G₀ * T ^ M * Real.exp (π * T / 4) := by
  have hu : u = (u.re : ℂ) + (u.im : ℂ) * I := (Complex.re_add_im u).symm
  have hxi : Real.exp (-(π * T / 4)) / (3 * π) ≤ T ^ M * ‖xi u‖ := by
    rcases le_or_gt 0 u.im with hpos | hneg
    · have him' : u.im = T := by rw [← hsign, abs_of_nonneg hpos]
      have hr := (hgood 2 u.re (by norm_num) (by norm_num) hu1 hu2).1
      have hf := xi_floor_two T
      rw [abs_of_pos (by linarith : (0 : ℝ) < T)] at hf
      have e3 : ((2 : ℝ) : ℂ) = 2 := by norm_num
      rw [e3] at hr
      rw [hu, him']
      linarith
    · have him' : u.im = -T := by rw [abs_of_neg hneg] at hsign; linarith
      have hr := (hgood 2 u.re (by norm_num) (by norm_num) hu1 hu2).2
      have hf := xi_floor_two (-T)
      rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < T)] at hf
      have e2 : (2 : ℂ) + ((-T : ℝ) : ℂ) * I = (2 : ℂ) - (T : ℂ) * I := by push_cast; ring
      rw [e2] at hf
      have e3 : ((2 : ℝ) : ℂ) = 2 := by norm_num
      rw [e3] at hr
      have e4 : (u.re : ℂ) + ((-T : ℝ) : ℂ) * I = (u.re : ℂ) - (T : ℂ) * I := by push_cast; ring
      rw [hu, him', e4]
      linarith
  have hTpos : 0 < T := by linarith
  have hpi : 0 < 3 * π := by positivity
  have hxipos : 0 < ‖xi u‖ := by
    by_contra hz
    have h0 : ‖xi u‖ = 0 := le_antisymm (not_lt.mp hz) (norm_nonneg _)
    rw [h0, mul_zero] at hxi
    have : 0 < Real.exp (-(π * T / 4)) / (3 * π) := by positivity
    linarith
  have hq : ‖h u‖ ≤ K * Real.exp G₀ / ‖xi u‖ := by
    rw [le_div_iff₀ hxipos, mul_comm]
    have := hMstrip u hu1 hu2
    rw [hdiv, norm_mul] at this
    exact this
  have hinv : 1 / ‖xi u‖ ≤ 3 * π * T ^ M * Real.exp (π * T / 4) := by
    rw [div_le_iff₀ hxipos]
    rw [div_le_iff₀ hpi] at hxi
    have he : Real.exp (-(π * T / 4)) * Real.exp (π * T / 4) = 1 := by
      rw [← Real.exp_add]; simp
    have hep := Real.exp_pos (π * T / 4)
    calc (1 : ℝ) = Real.exp (-(π * T / 4)) * Real.exp (π * T / 4) := he.symm
      _ ≤ T ^ M * ‖xi u‖ * (3 * π) * Real.exp (π * T / 4) :=
          mul_le_mul_of_nonneg_right hxi hep.le
      _ = 3 * π * T ^ M * Real.exp (π * T / 4) * ‖xi u‖ := by ring
  have hKG : 0 ≤ K * Real.exp G₀ := by
    have := (norm_nonneg _).trans (hMstrip u hu1 hu2); exact this
  calc ‖h u‖ ≤ K * Real.exp G₀ / ‖xi u‖ := hq
    _ = K * Real.exp G₀ * (1 / ‖xi u‖) := by ring
    _ ≤ K * Real.exp G₀ * (3 * π * T ^ M * Real.exp (π * T / 4)) :=
        mul_le_mul_of_nonneg_left hinv hKG
    _ = 3 * π * K * Real.exp G₀ * T ^ M * Real.exp (π * T / 4) := by ring

/-- **Good rectangle.** With the half-plane bounds on the vertical sides and the horizontal-side
bound, the maximum principle bounds the quotient on `[−1,2] × [−T,T]`. -/
theorem norm_quotient_le_rectangle {F : ℝ → ℂ} {h : ℂ → ℂ} {K A₁ G₀ T : ℝ} {M : ℕ}
    (hK : 0 ≤ K) (hT : 1 ≤ T) (hh : Differentiable ℂ h)
    (hdiv : ∀ s, centredLaplace F s = xi s * h s)
    (hR : ∀ s : ℂ, 2 ≤ s.re → ‖h s‖ ≤ 3 * K * Real.exp (A₁ * s.re) * Real.exp (π * |s.im| / 4))
    (hL : ∀ s : ℂ, s.re ≤ -1 →
      ‖h s‖ ≤ 3 * K * Real.exp (A₁ * (1 - s.re)) * Real.exp (π * |s.im| / 4))
    (hMstrip : ∀ u : ℂ, -1 ≤ u.re → u.re ≤ 2 → ‖centredLaplace F u‖ ≤ K * Real.exp G₀)
    (hgood : ∀ σ τ : ℝ, -1 ≤ σ → σ ≤ 2 → -1 ≤ τ → τ ≤ 2 →
        ‖xi ((σ : ℂ) + (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) + (T : ℂ) * I)‖ ∧
          ‖xi ((σ : ℂ) - (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) - (T : ℂ) * I)‖)
    {z : ℂ} (hz1 : -1 ≤ z.re) (hz2 : z.re ≤ 2) (hz3 : -T ≤ z.im) (hz4 : z.im ≤ T) :
    ‖h z‖ ≤ (3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀) * T ^ M *
      Real.exp (π * T / 4) := by
  have hTM : 1 ≤ T ^ M := one_le_pow₀ hT
  set B₀ := 3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀ with hB₀
  have hB₀nn : 0 ≤ B₀ := by positivity
  have hside : 3 * K * Real.exp (2 * A₁) * Real.exp (π * T / 4) ≤
      B₀ * T ^ M * Real.exp (π * T / 4) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc 3 * K * Real.exp (2 * A₁) ≤ B₀ := by
          rw [hB₀]; have : 0 ≤ 3 * π * K * Real.exp G₀ := by positivity
          linarith
      _ = B₀ * 1 := (mul_one _).symm
      _ ≤ B₀ * T ^ M := mul_le_mul_of_nonneg_left hTM hB₀nn
  refine norm_le_of_rectangle_frontier_bound hh (by norm_num : (-1 : ℝ) < 2)
    (by linarith : -T < T) (fun u hu1 hu2 hu3 hu4 hs => ?_) hz1 hz2 hz3 hz4
  have himT : |u.im| ≤ T := abs_le.mpr ⟨hu3, hu4⟩
  have hexpT : Real.exp (π * |u.im| / 4) ≤ Real.exp (π * T / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  rcases hs with hre | hre | him | him
  · have := hL u (by rw [hre])
    rw [hre, show A₁ * ((1 : ℝ) - -1) = 2 * A₁ by ring] at this
    refine this.trans (le_trans ?_ hside)
    exact mul_le_mul_of_nonneg_left hexpT (by positivity)
  · have := hR u (by rw [hre])
    rw [hre, show A₁ * 2 = 2 * A₁ by ring] at this
    refine this.trans (le_trans ?_ hside)
    exact mul_le_mul_of_nonneg_left hexpT (by positivity)
  · have := norm_quotient_le_horizontal (M := M) hT hdiv hMstrip hgood hu1 hu2
      (by rw [him, abs_neg, abs_of_pos (by linarith)])
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hB₀]; have : 0 ≤ 3 * K * Real.exp (2 * A₁) := by positivity
    linarith
  · have := norm_quotient_le_horizontal (M := M) hT hdiv hMstrip hgood hu1 hu2
      (by rw [him, abs_of_pos (by linarith)])
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hB₀]; have : 0 ≤ 3 * K * Real.exp (2 * A₁) := by positivity
    linarith

/-- The strip bound: for `−1 ≤ Re s ≤ 2`, `‖h s‖ ≤ B₀ e^{(M+π/4)(N+|Im s|)}`. -/
theorem norm_quotient_le_strip {F : ℝ → ℂ} {h : ℂ → ℂ} {K A₁ G₀ n0 : ℝ} {M : ℕ}
    (hK : 0 ≤ K) (hh : Differentiable ℂ h)
    (hdiv : ∀ s, centredLaplace F s = xi s * h s)
    (hR : ∀ s : ℂ, 2 ≤ s.re → ‖h s‖ ≤ 3 * K * Real.exp (A₁ * s.re) * Real.exp (π * |s.im| / 4))
    (hL : ∀ s : ℂ, s.re ≤ -1 →
      ‖h s‖ ≤ 3 * K * Real.exp (A₁ * (1 - s.re)) * Real.exp (π * |s.im| / 4))
    (hMstrip : ∀ u : ℂ, -1 ≤ u.re → u.re ≤ 2 → ‖centredLaplace F u‖ ≤ K * Real.exp G₀)
    (hsel : ∀ n : ℝ, n0 ≤ n → ∃ T : ℝ, n ≤ T ∧ T ≤ n + 1 ∧
      ∀ σ τ : ℝ, -1 ≤ σ → σ ≤ 2 → -1 ≤ τ → τ ≤ 2 →
        ‖xi ((σ : ℂ) + (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) + (T : ℂ) * I)‖ ∧
          ‖xi ((σ : ℂ) - (T : ℂ) * I)‖ ≤ T ^ M * ‖xi ((τ : ℂ) - (T : ℂ) * I)‖)
    {s : ℂ} (hs1 : -1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖h s‖ ≤ (3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀) *
      Real.exp (((M : ℝ) + π / 4) * (|s.im| + (|n0| + 2))) := by
  obtain ⟨T, hnT, hTn, hgood⟩ := hsel (max |s.im| (max n0 1)) (le_trans (le_max_left _ _)
    (le_max_right _ _))
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnT
  have hTim : |s.im| ≤ T := le_trans (le_max_left _ _) hnT
  have hbound := norm_quotient_le_rectangle (M := M) hK hT1 hh hdiv hR hL hMstrip hgood hs1 hs2
    (by linarith [neg_abs_le s.im]) (by linarith [le_abs_self s.im])
  have hTN : T ≤ |s.im| + (|n0| + 2) := by
    have h1 := le_abs_self n0
    have h2 := abs_nonneg s.im
    have h3 := abs_nonneg n0
    have : max |s.im| (max n0 1) ≤ |s.im| + |n0| + 1 :=
      max_le (by linarith) (max_le (by linarith) (by linarith))
    linarith
  have hTM : T ^ M ≤ Real.exp (M * T) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have := Real.log_le_sub_one_of_pos (show 0 < T by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hB : 0 ≤ 3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀ := by positivity
  calc ‖h s‖ ≤ _ := hbound
    _ ≤ (3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀) * Real.exp (M * T) *
          Real.exp (π * T / 4) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hTM hB
    _ = (3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀) *
          Real.exp (((M : ℝ) + π / 4) * T) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hTN (by positivity)

/-- **The quotient `h = M_F/ξ` has exponential type.** On `Re s ≥ 2` and `Re s ≤ −1` this is the
Stirling floor for `ξ`; in the strip it is Burnol's good heights plus the maximum principle on
rectangles. -/
theorem exists_quotient_exponential_type {F : ℝ → ℂ} {h : ℂ → ℂ} {C c δ : ℝ} (hδ : 0 < δ)
    (hcδ : δ < c) (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))))
    (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    ∃ A τ : ℝ, 0 ≤ A ∧ 0 ≤ τ ∧ ∀ s : ℂ, ‖h s‖ ≤ A * Real.exp (τ * ‖s‖) := by
  have hC := decay_const_nonneg hF
  obtain ⟨K, hKdef⟩ : ∃ K, K = C * Real.sqrt (π / (2 * δ)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁, A₁ = |Real.log (2 * (c - δ))| / 2 + 3 := ⟨_, rfl⟩
  have hA₁ : 0 ≤ A₁ := by rw [hA₁def]; positivity
  have hR : ∀ s : ℂ, 2 ≤ s.re →
      ‖h s‖ ≤ 3 * K * Real.exp (A₁ * s.re) * Real.exp (π * |s.im| / 4) := by
    intro s hs
    rw [hKdef, hA₁def]
    exact norm_quotient_le_exp_right hδ hcδ hF (fun s _ => hdiv s) hs
  have hL : ∀ s : ℂ, s.re ≤ -1 →
      ‖h s‖ ≤ 3 * K * Real.exp (A₁ * (1 - s.re)) * Real.exp (π * |s.im| / 4) := by
    intro s hs
    have h1 := norm_quotient_le_exp_right (h := fun w => h (1 - w)) hδ hcδ (decay_reflect hF)
      (fun w _ => centredLaplace_reflect_eq hdiv w) (s := 1 - s) (by simp; linarith)
    simp only [sub_sub_cancel, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg] at h1
    rw [hKdef, hA₁def]
    exact h1
  obtain ⟨M, n0, hsel⟩ := exists_xi_horizontal_ratio_nat_bound
  obtain ⟨G₀, hG₀⟩ : ∃ G₀, G₀ = legendreMajorant (c - δ) (3 / 2) := ⟨_, rfl⟩
  have hMstrip : ∀ u : ℂ, -1 ≤ u.re → u.re ≤ 2 → ‖centredLaplace F u‖ ≤ K * Real.exp G₀ := by
    intro u h1 h2
    have hb := norm_centredLaplace_le hδ hcδ hF u
    have hmono : legendreMajorant (c - δ) |u.re - 1 / 2| ≤ G₀ := by
      rw [hG₀]
      exact legendreMajorant_mono (by linarith) (abs_nonneg _)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hs : 0 ≤ Real.sqrt (π / (2 * δ)) := Real.sqrt_nonneg _
    calc ‖centredLaplace F u‖ ≤ _ := hb
      _ ≤ C * Real.exp G₀ * Real.sqrt (π / (2 * δ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono) hC) hs
      _ = K * Real.exp G₀ := by rw [hKdef]; ring
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 3 * K * Real.exp (2 * A₁) + 3 * π * K * Real.exp G₀ := ⟨_, rfl⟩
  have hB₀nn : 0 ≤ B₀ := by rw [hB₀]; positivity
  obtain ⟨N, hN⟩ : ∃ N, N = |n0| + 2 := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = A₁ + π / 4 + (M : ℝ) := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  refine ⟨3 * K * Real.exp A₁ + B₀ * Real.exp (τ * N), τ, by positivity, hτ0, fun s => ?_⟩
  have hre := Complex.re_le_norm s
  have hre' : -s.re ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s; linarith [neg_abs_le s.re]
  have him := Complex.abs_im_le_norm s
  have hsn := norm_nonneg s
  have hMn := Nat.cast_nonneg (α := ℝ) M
  have hA1pos : 0 ≤ 3 * K * Real.exp A₁ := by positivity
  have hBpos : 0 ≤ B₀ * Real.exp (τ * N) := by positivity
  have hexpτ : 0 < Real.exp (τ * ‖s‖) := Real.exp_pos _
  rcases le_or_gt 2 s.re with hs2 | hs2
  · have hb := hR s hs2
    have hexp : A₁ * s.re + π * |s.im| / 4 ≤ A₁ + τ * ‖s‖ := by
      rw [hτ]; nlinarith [Real.pi_pos]
    have : ‖h s‖ ≤ 3 * K * Real.exp A₁ * Real.exp (τ * ‖s‖) := by
      calc ‖h s‖ ≤ _ := hb
        _ = 3 * K * Real.exp (A₁ * s.re + π * |s.im| / 4) := by rw [Real.exp_add]; ring
        _ ≤ 3 * K * Real.exp (A₁ + τ * ‖s‖) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = _ := by rw [Real.exp_add]; ring
    nlinarith
  rcases le_or_gt s.re (-1) with hs1 | hs1
  · have hb := hL s hs1
    have hexp : A₁ * (1 - s.re) + π * |s.im| / 4 ≤ A₁ + τ * ‖s‖ := by
      rw [hτ]; nlinarith [Real.pi_pos]
    have : ‖h s‖ ≤ 3 * K * Real.exp A₁ * Real.exp (τ * ‖s‖) := by
      calc ‖h s‖ ≤ _ := hb
        _ = 3 * K * Real.exp (A₁ * (1 - s.re) + π * |s.im| / 4) := by rw [Real.exp_add]; ring
        _ ≤ 3 * K * Real.exp (A₁ + τ * ‖s‖) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = _ := by rw [Real.exp_add]; ring
    nlinarith
  have hb := norm_quotient_le_strip (M := M) (n0 := n0) hK0 hh hdiv hR hL hMstrip hsel hs1.le
    hs2.le
  rw [← hB₀, ← hN] at hb
  have hexp : ((M : ℝ) + π / 4) * (|s.im| + N) ≤ τ * N + τ * ‖s‖ := by
    rw [hτ]; nlinarith [Real.pi_pos]
  have : ‖h s‖ ≤ B₀ * Real.exp (τ * N) * Real.exp (τ * ‖s‖) := by
    calc ‖h s‖ ≤ _ := hb
      _ ≤ B₀ * Real.exp (τ * N + τ * ‖s‖) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB₀nn
      _ = _ := by rw [Real.exp_add]; ring
  nlinarith

/-! ## The theta threshold -/

/-- **Theta threshold, uniqueness side.** If `|F(x)| ≤ C exp(−c e^{2|x|})` with `c > π` and the
centred Laplace transform `M_F(s) = ∫ F(x) e^{(s−½)x} dx` is divisible by `ξ` among entire
functions, then `F = 0` almost everywhere.

The quotient `h = M_F/ξ` has exponential type (`exists_quotient_exponential_type`). Along both real
rays it decays like `e^{−(σ/2) log(c/π)}`: the Legendre transform of the decay rate `c` loses to
Stirling's growth of `Γ(σ/2)`, which is the Legendre transform of the theta rate `π`. The two-ray
Paley–Wiener theorem gives `h = 0`, and Fourier uniqueness gives `F = 0`. -/
theorem ae_eq_zero_of_centredLaplace_xi_dvd {F : ℝ → ℂ} (hFm : AEStronglyMeasurable F)
    {C c : ℝ} (hc : π < c) (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))))
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    F =ᵐ[volume] 0 := by
  have hC := decay_const_nonneg hF
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (c - π) / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hcδ : δ < c := by rw [hδdef]; linarith [Real.pi_pos]
  have hπ : π < c - δ := by rw [hδdef]; linarith
  obtain ⟨A, τ, hA, hτ, hgrow⟩ := exists_quotient_exponential_type hδ hcδ hF hh hdiv
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Real.log ((c - δ) / π) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]; exact Real.log_pos (by rw [lt_div_iff₀ Real.pi_pos]; linarith)
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁, σ₁ = max 2 (2 * Real.exp 1 * (c - δ) + 1 / 2) := ⟨_, rfl⟩
  have hσ₁2 : 2 ≤ σ₁ := by rw [hσ₁]; exact le_max_left _ _
  have hσ₁e : 2 * Real.exp 1 * (c - δ) + 1 / 2 ≤ σ₁ := by rw [hσ₁]; exact le_max_right _ _
  obtain ⟨D, hD⟩ : ∃ D, D = 3 * (C * Real.sqrt (π / (2 * δ))) *
      Real.exp (-(1 + Real.log κ) / 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hdecR : ∀ x : ℝ, σ₁ ≤ x → ‖h x‖ ≤ D * Real.exp (-(κ / 4 * x)) := by
    intro x hx
    have := norm_quotient_le_decay (h := h) hδ hπ hF (fun s _ => hdiv s) (σ := x) (by linarith)
      (by linarith)
    rw [← hκdef] at this
    rw [hD]; linarith
  have hdecL : ∀ x : ℝ, σ₁ ≤ 1 - x → ‖h x‖ ≤ D * Real.exp (-(κ / 4 * (1 - x))) := by
    intro x hx
    have := norm_quotient_le_decay (h := fun w => h (1 - w)) hδ hπ (decay_reflect hF)
      (fun w _ => centredLaplace_reflect_eq hdiv w) (σ := 1 - x) (by linarith) (by linarith)
    rw [← hκdef] at this
    have e : (1 : ℂ) - ((1 - x : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
    simp only [e] at this
    rw [hD]; linarith
  obtain ⟨Cst, hCst⟩ : ∃ Cst, Cst = D + A * Real.exp ((τ + κ / 4) * σ₁) := ⟨_, rfl⟩
  have hAe : 0 ≤ A * Real.exp ((τ + κ / 4) * σ₁) := by positivity
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖h (x : ℂ)‖ ≤ Cst * Real.exp (-(κ / 4 * x)) := by
    intro x hx
    rcases le_or_gt σ₁ x with h1 | h1
    · have := hdecR x h1
      have he := Real.exp_pos (-(κ / 4 * x))
      rw [hCst]; nlinarith
    · have hg := hgrow x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at hg
      have hle : τ * x ≤ (τ + κ / 4) * σ₁ + -(κ / 4 * x) := by nlinarith
      have : A * Real.exp (τ * x) ≤ A * Real.exp ((τ + κ / 4) * σ₁) * Real.exp (-(κ / 4 * x)) := by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hA
      have he := Real.exp_pos (-(κ / 4 * x))
      rw [hCst]; nlinarith
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖h (x : ℂ)‖ ≤ Cst * Real.exp (κ / 4 * x) := by
    intro x hx
    rcases le_or_gt σ₁ (1 - x) with h1 | h1
    · have := hdecL x h1
      have hle : Real.exp (-(κ / 4 * (1 - x))) ≤ Real.exp (κ / 4 * x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have he := Real.exp_pos (κ / 4 * x)
      rw [hCst]; nlinarith
    · have hg := hgrow x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx] at hg
      have hle : τ * -x ≤ (τ + κ / 4) * σ₁ + κ / 4 * x := by nlinarith
      have : A * Real.exp (τ * -x) ≤ A * Real.exp ((τ + κ / 4) * σ₁) * Real.exp (κ / 4 * x) := by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hA
      have he := Real.exp_pos (κ / 4 * x)
      rw [hCst]; nlinarith
  have hzero : h = 0 := eq_zero_of_two_ray_exponential_decay hh hA hτ (by positivity) hgrow
    hplus hminus
  -- `F` is integrable and its Fourier transform vanishes
  have hc0 : 0 < c := lt_trans Real.pi_pos hc
  have hFint : Integrable F := by
    refine ((integrable_exp_neg_mul_sq (b := 2 * c) (by positivity)).const_mul C).mono' hFm
      (Eventually.of_forall fun x => (hF x).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |x|)
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]
  refine HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hFint fun w => ?_
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hM := hdiv (1 / 2 + ((-2 * π * w : ℝ) : ℂ) * I)
  rw [hzero, Pi.zero_apply, mul_zero] at hM
  unfold centredLaplace at hM
  rw [← hM]
  congr 1; funext v
  rw [smul_eq_mul]
  congr 2
  push_cast; ring

open Bottcher Zeta23 in
/-- **Theta threshold, sharpness side.** Riemann's kernel `Φ` decays at every rate `c < π`:
`|Φ(x)| ≤ C_c exp(−c e^{2|x|})`. Its transform is `ξ` itself, and it is not zero. -/
theorem riemannPhiKernel_decay_below_theta {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π) :
    ∃ C : ℝ, ∀ x : ℝ, ‖riemannPhiKernel x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_riemannPhiKernel_le_exp (B := 0) le_rfl
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  set d := π - c with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  refine ⟨C₀ * Real.exp (3 * c) + 120 * jacobiThetaTailConstant * Real.exp π / d ^ 3, fun x => ?_⟩
  have hsym : ‖riemannPhiKernel x‖ = ‖riemannPhiKernel |x|‖ := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, riemannPhiKernel_neg]
  set u := Real.exp (2 * |x|) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have hexpc : 0 < Real.exp (-(c * u)) := Real.exp_pos _
  have hpos2 : 0 ≤ 120 * jacobiThetaTailConstant * Real.exp π / d ^ 3 := by positivity
  rcases lt_or_ge u 3 with hu3 | hu3
  · -- compact range: `‖Φ‖ ≤ C₀ ≤ C₀ e^{3c} e^{−cu}`
    have h1 := hb x
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
    have h2 : C₀ ≤ C₀ * Real.exp (3 * c) * Real.exp (-(c * u)) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ 3 * c + -(c * u) := by nlinarith
      have := Real.one_le_exp this
      nlinarith
    calc ‖riemannPhiKernel x‖ ≤ C₀ := h1
      _ ≤ C₀ * Real.exp (3 * c) * Real.exp (-(c * u)) := h2
      _ ≤ _ := by nlinarith
  · -- far range: `‖Φ‖ ≤ 4Mθ e^π e^{|x|/2}(3u + 2u²) e^{−πu}`
    have h1 := norm_riemannPhiKernel_le (x := |x|) hu3
    rw [← hsym] at h1
    have hx2 : Real.exp (|x| / 2) ≤ u := Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
    have hpoly : Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) ≤ 5 * u ^ 3 := by
      have : 3 * u + 2 * u ^ 2 ≤ 5 * u ^ 2 := by nlinarith
      calc Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) ≤ u * (5 * u ^ 2) :=
            mul_le_mul hx2 this (by positivity) (by linarith)
        _ = 5 * u ^ 3 := by ring
    -- `u³ e^{−du} ≤ 6/d³`
    have hcube : u ^ 3 * Real.exp (-(d * u)) ≤ 6 / d ^ 3 := by
      have h3 := Real.pow_div_factorial_le_exp (x := d * u) (by positivity) 3
      norm_num [Nat.factorial] at h3
      rw [le_div_iff₀ (by positivity)]
      have he : Real.exp (-(d * u)) * Real.exp (d * u) = 1 := by rw [← Real.exp_add]; simp
      have hep := Real.exp_pos (-(d * u))
      nlinarith [mul_pow d u 3]
    have hsplit : Real.exp (-π * u) = Real.exp (-(d * u)) * Real.exp (-(c * u)) := by
      rw [← Real.exp_add]; congr 1; rw [hd]; ring
    calc ‖riemannPhiKernel x‖
        ≤ 4 * jacobiThetaTailConstant * Real.exp π * Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2) *
            Real.exp (-π * u) := h1
      _ = 4 * jacobiThetaTailConstant * Real.exp π * (Real.exp (|x| / 2) * (3 * u + 2 * u ^ 2)) *
            Real.exp (-(d * u)) * Real.exp (-(c * u)) := by rw [hsplit]; ring
      _ ≤ 4 * jacobiThetaTailConstant * Real.exp π * (5 * u ^ 3) * Real.exp (-(d * u)) *
            Real.exp (-(c * u)) := by gcongr
      _ = 20 * jacobiThetaTailConstant * Real.exp π * (u ^ 3 * Real.exp (-(d * u))) *
            Real.exp (-(c * u)) := by ring
      _ ≤ 20 * jacobiThetaTailConstant * Real.exp π * (6 / d ^ 3) * Real.exp (-(c * u)) := by
          gcongr
      _ = 120 * jacobiThetaTailConstant * Real.exp π / d ^ 3 * Real.exp (-(c * u)) := by ring
      _ ≤ _ := by
          have : 0 ≤ C₀ * Real.exp (3 * c) := by positivity
          nlinarith

/-- Riemann's kernel lies in the `ξ`-divisible class with quotient `1`. -/
theorem centredLaplace_riemannPhiKernel (s : ℂ) :
    centredLaplace riemannPhiKernel s = xi s * 1 := by
  rw [mul_one, ← riemannPhiTransform_eq_xi]; rfl

theorem riemannPhiKernel_not_ae_zero : ¬ riemannPhiKernel =ᵐ[volume] 0 := by
  intro h0
  have hae : (fun x : ℝ => cexp ((2 - 1 / 2) * (x : ℂ)) * riemannPhiKernel x) =ᵐ[volume]
      fun _ => (0 : ℂ) := h0.mono fun x hx => by simp [hx]
  have h2 : centredLaplace riemannPhiKernel 2 = 0 := by
    unfold centredLaplace
    rw [integral_congr_ae hae, integral_zero]
  rw [centredLaplace_riemannPhiKernel, mul_one] at h2
  have := factorial_mul_rpow_le_norm_xi 0
  norm_num at this
  rw [h2, norm_zero] at this
  linarith [Real.rpow_pos_of_pos Real.pi_pos (-1 : ℝ)]

/-- **Theta threshold for `ξ`-divisible transforms.** The zero divisor of `ζ` is a uniqueness set
for the decay class `{|F(x)| ≤ C e^{−c e^{2|x|}}}` exactly above the theta rate:
* for every `c > π`, a measurable `F` of rate `c` whose transform `M_F` is divisible by `ξ`
  vanishes almost everywhere;
* for every `0 ≤ c < π`, Riemann's kernel `Φ` has rate `c`, `M_Φ = ξ`, and `Φ ≠ 0`. -/
theorem theta_threshold_xi_divisible :
    (∀ c : ℝ, π < c → ∀ F : ℝ → ℂ, AEStronglyMeasurable F → ∀ C : ℝ,
      (∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|)))) →
      ∀ h : ℂ → ℂ, Differentiable ℂ h → (∀ s, centredLaplace F s = xi s * h s) →
      F =ᵐ[volume] 0) ∧
    (∀ c : ℝ, 0 ≤ c → c < π → ∃ F : ℝ → ℂ, ∃ C : ℝ,
      (∀ x, ‖F x‖ ≤ C * Real.exp (-(c * Real.exp (2 * |x|)))) ∧
      (∀ s, centredLaplace F s = xi s * 1) ∧ ¬ F =ᵐ[volume] 0) := by
  refine ⟨fun c hc F hFm C hF h hh hdiv =>
    ae_eq_zero_of_centredLaplace_xi_dvd hFm hc hF hh hdiv, fun c hc0 hc => ?_⟩
  obtain ⟨C, hC⟩ := riemannPhiKernel_decay_below_theta hc0 hc
  exact ⟨riemannPhiKernel, C, hC, centredLaplace_riemannPhiKernel, riemannPhiKernel_not_ae_zero⟩


end

end RHTower
