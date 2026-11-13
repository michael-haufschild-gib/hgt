import GaloisForLFunctions.RHTower.KiKimLeeWeylHorizon
import GaloisForLFunctions.RHTower.DQPTZetaDerivBound

/-!
# The explicit height of the Weyl heat horizon

**Theorem** (`riemannHeat_zeros_real_simple_weyl_explicit`). For `0 < ε ≤ 1` and `0 < t ≤ 1/8`, every
zero `z` of the de Bruijn–Newman deformation `H_t` with

`|Re z| ≥ exp(10²⁰/ε⁴)` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}`

is real and simple. For `ε > 1` the height is `exp(10²⁰)`
(`riemannHeat_zeros_real_simple_weyl_explicit_of_pos`).

The horizon `riemannHeat_zeros_real_simple_weyl` has the same statement with an unspecified height
`X₀(ε)`. Its proof has three non-explicit constants, and each is made explicit here.

* **The segment constant.** The Phragmén–Lindelöf constant of the interpolated Weyl bound uses a
  bound for `(s − 1)ζ(s)` on `s = ½ + iy`, `|y| ≤ 8`. The eta series gives `‖ζ(s)‖ ≤ 5‖s‖` on the
  critical line, hence the bound `362` (`norm_zetaEntire_half_segment_le`) and
  `‖ζ(σ + it)‖ ≤ (16800 e^{1/4}/η) t^{ρ(1+η−σ)}` (`norm_riemannZeta_le_subconvex_explicit`).
* **The Euler anchor.** `‖ζ(s)‖ ≥ 1/3` on `Re s ≥ 3/2`, from `1/ζ = Σ μ(n) n^{−s}` and
  `Σ n^{−3/2} ≤ 3` (`one_third_le_norm_riemannZeta_of_three_halves_le_re`).
* **The error threshold.** With `A = 1/η + 3`, the two Gaussian error sums of the window argument
  are small for every slope `α ≥ max(50000 A² e⁸, 3600πK/(m/80)³)` (`weyl_errors_small`). The
  bounds are `e^{−x} ≤ 1/(1+x)` and `e^{−x} ≤ 6/x³`.

With `η = ε/36` and `m = 2ε/3` the strip constant is `K ≤ 2·10⁹/ε` and the threshold is at most
`4·10¹⁹/ε⁴`; the height is `2π e^{2α₀}`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ## The constants of the strip comparison -/

/-- `‖(s − 1)ζ(s)‖ ≤ 362` on the segment `s = ½ + iy`, `|y| ≤ 8`. The eta series gives
`‖(1 − 2^{1−s})ζ(s)‖ ≤ 2‖s‖` on the critical line, and `‖1 − 2^{1−s}‖ ≥ √2 − 1 ≥ 2/5`. -/
theorem norm_zetaEntire_half_segment_le {y : ℝ} (hy : |y| ≤ 8) :
    ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 362 := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I := ⟨_, rfl⟩
  rw [← hz]
  have hzre : z.re = 1 / 2 := by rw [hz]; simp
  have hzim : z.im = y := by rw [hz]; simp
  have hz1 : z ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; norm_num at this
  have hnz : ‖z‖ ≤ 17 / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [hzre, hzim, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hnz1 : ‖z - 1‖ ≤ 17 / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, hzre, hzim, Complex.one_re, Complex.one_im, sub_zero,
      show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  -- the eta multiplier
  have hmult : 2 / 5 ≤ ‖1 - (2 : ℂ) ^ (1 - z)‖ := by
    refine le_trans ?_ (DQPT.dqpt_two_rpow_sub_one_le_norm (s := z) (by rw [hzre]; norm_num))
    have h1 : ((7 / 5 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)] at h1
    rw [hzre, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    linarith
  have heta : ‖etaPair z‖ ≤ 2 * ‖z‖ := by
    have h := DQPT.dqpt_norm_etaPair_le (s := z) (by rw [hzre]; norm_num)
    rw [hzre] at h
    linarith
  have hζ : ‖riemannZeta z‖ ≤ 5 * ‖z‖ := by
    have h1 : ‖1 - (2 : ℂ) ^ (1 - z)‖ * ‖riemannZeta z‖ ≤ 2 * ‖z‖ := by
      rw [← norm_mul, ← etaPair_eq z (by rw [hzre]; norm_num) hz1]
      exact heta
    have h2 := mul_le_mul_of_nonneg_right hmult (norm_nonneg (riemannZeta z))
    linarith
  rw [zetaEntire_eq hz1, norm_mul]
  calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ 17 / 2 * (5 * (17 / 2)) :=
        mul_le_mul hnz1 (hζ.trans (by linarith)) (norm_nonneg _) (by norm_num)
    _ ≤ 362 := by norm_num

/-- **The Euler anchor.** `‖ζ(s)‖ ≥ 1/3` on `Re s ≥ 3/2`, since `ζ(s) · Σ μ(n) n^{−s} = 1` and
`Σ n^{−3/2} ≤ 3`. -/
theorem one_third_le_norm_riemannZeta_of_three_halves_le_re {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hfsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.2 (by norm_num)
  have hB : (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 :=
    (Sieve.tsum_nat_rpow_neg_le (σ := 3 / 2) (by norm_num)).trans (by norm_num)
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at hprod
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero, Nat.cast_zero, Real.zero_rpow (by norm_num)]
    · rw [LSeries.norm_term_eq, if_neg hn]
      have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← one_div]
      calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ / (n : ℝ) ^ s.re
          ≤ 1 / (n : ℝ) ^ s.re := div_le_div_of_nonneg_right hμ (by positivity)
        _ ≤ 1 / (n : ℝ) ^ ((3 : ℝ) / 2) := one_div_le_one_div_of_le (by positivity) hpow
  have hL : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ 3 := by
    unfold LSeries
    have hs' := hfsum.of_nonneg_of_le (fun n => norm_nonneg _) hterm
    exact ((norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hterm hfsum)).trans hB
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_one] at hnorm
  have := mul_le_mul_of_nonneg_left hL (norm_nonneg (riemannZeta s))
  linarith

/-- `e² ≤ 9`. -/
private theorem exp_two_le : Real.exp 2 ≤ 9 := by
  have he1 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]
  nlinarith [Real.exp_pos 1]

/-- **Weyl's bound across the strip, with its constant.** For `0 < η ≤ ½`, `½ ≤ σ ≤ 1 + η` and
`t ≥ 8`: `‖ζ(σ + it)‖ ≤ (16800 e^{1/4}/η) t^{(1/6+η)(1+η−σ)/(1/2+η)}`. -/
theorem norm_riemannZeta_le_subconvex_explicit {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) {σ t : ℝ}
    (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 + η) (ht : 8 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ 16800 / η * Real.exp (1 / 4) * t ^ ((1 / 6 + η) * (1 + η - σ) / (1 / 2 + η)) := by
  refine (norm_riemannZeta_le_subconvex_of_segment hη hη2 (by norm_num : (0 : ℝ) ≤ 362)
    (fun y hy => norm_zetaEntire_half_segment_le hy) hσ1 hσ2 ht).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _)
  have hu : 2 ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
  have he14 := Real.exp_pos (1 / 4)
  refine max_le ?_ (max_le (le_of_eq (by ring)) ?_)
  · -- the segment
    have : (362 : ℝ) ≤ 16800 / η := by rw [div_eq_mul_one_div (16800 : ℝ) η]; linarith
    exact mul_le_mul_of_nonneg_right this he14.le
  · -- the right edge: `4(1 + 1/η)e^{9/4} ≤ 72 e^{1/4}/η`
    have he : Real.exp (9 / 4) = Real.exp 2 * Real.exp (1 / 4) := by
      rw [← Real.exp_add]; norm_num
    have h1 : (1 + 1 / η) * Real.exp 2 ≤ 2 * (1 / η) * 9 :=
      mul_le_mul (by linarith) exp_two_le (Real.exp_pos 2).le (by linarith)
    have h2 : 4 * ((1 + 1 / η) * Real.exp 2) ≤ 16800 / η := by
      rw [div_eq_mul_one_div (16800 : ℝ) η]; linarith
    calc 4 * (1 + 1 / η) * Real.exp (9 / 4)
        = 4 * ((1 + 1 / η) * Real.exp 2) * Real.exp (1 / 4) := by rw [he]; ring
      _ ≤ 16800 / η * Real.exp (1 / 4) := mul_le_mul_of_nonneg_right h2 he14.le

/-- The constant of the Weyl strip comparison: `K(η) = 100800 e⁶ e^{1/4}/η`. -/
def weylStripConstant (η : ℝ) : ℝ := 2 * Real.exp 6 * (16800 / η * Real.exp (1 / 4)) / (1 / 3)

theorem weylStripConstant_nonneg {η : ℝ} (hη : 0 < η) : 0 ≤ weylStripConstant η := by
  unfold weylStripConstant; positivity

/-- **Strip comparison, Weyl form, explicit.** For `0 < η ≤ ½`, `X ≥ 16`, `0 ≤ w ≤ ½ + η` and
`1 ≤ u ≤ X`: `‖F(w)‖ ≤ K(η) X^{ρ(½+η−w)} (X/2π)^{(w−u)/2} ‖F(u)‖`, `F(w) = ξ(½ + w + iX)`. -/
theorem norm_xiLine_le_strip_weyl_explicit {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        weylStripConstant η * X ^ (weylRate η * (1 / 2 + η - w)) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖ := by
  intro X w u hX hw0 hwη hu1 huX
  unfold weylStripConstant
  exact norm_xiLine_le_strip_weyl_of_bounds hη hη2 (by positivity) (by norm_num)
    (fun σ t h1 h2 h3 => norm_riemannZeta_le_subconvex_explicit hη hη2 h1 h2 h3)
    (fun s hs => one_third_le_norm_riemannZeta_of_three_halves_le_re hs) hX hw0 hwη hu1 huX

/-! ## The error threshold -/

/-- `e^E ≤ 1/N` once `E ≤ 1 − N`. -/
private theorem exp_le_one_div_of_add_le {E N : ℝ} (hN : 0 < N) (h : E + N ≤ 1) :
    Real.exp E ≤ 1 / N := by
  have h1 : N ≤ (Real.exp E)⁻¹ := by
    rw [← Real.exp_neg]
    linarith [Real.add_one_le_exp (-E)]
  have hpos := Real.exp_pos E
  rw [le_div_iff₀ hN]
  calc Real.exp E * N ≤ Real.exp E * (Real.exp E)⁻¹ := mul_le_mul_of_nonneg_left h1 hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

/-- The model error: `2A√(20/α)e⁴ ≤ 1/25` once `α ≥ 50000 A² e⁸`. -/
private theorem model_error_le {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (h3 : 50000 * A ^ 2 * Real.exp 8 ≤ α) :
    2 * A * Real.sqrt (20 / α) * Real.exp 4 ≤ 1 / 25 := by
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  have he8 : Real.exp 4 ^ 2 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hsq : Real.sqrt (20 / α) ≤ 1 / (50 * A * Real.exp 4) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, one_pow, mul_pow, mul_pow, he8, div_le_div_iff₀ hα (by positivity)]
    linarith only [h3]
  calc 2 * A * Real.sqrt (20 / α) * Real.exp 4
      ≤ 2 * A * (1 / (50 * A * Real.exp 4)) * Real.exp 4 := by gcongr
    _ = 1 / 25 := by field_simp; norm_num

/-- The strip error: `24πKα²e^{−qα} ≤ 1/25` once `α ≥ 3600πK/q³`, from `e^{−x} ≤ 6/x³`. -/
private theorem strip_error_le {q K α : ℝ} (hq : 0 < q) (hK : 0 ≤ K) (hα : 0 < α)
    (h4 : 3600 * Real.pi * K / q ^ 3 ≤ α) :
    24 * Real.pi * K * α ^ 2 * Real.exp (-q * α) ≤ 1 / 25 := by
  have hx0 : 0 < q * α := by positivity
  have hexp : (q * α) ^ 3 / 6 ≤ Real.exp (q * α) := by
    have := Real.pow_div_factorial_le_exp (q * α) hx0.le 3
    norm_num [Nat.factorial] at this
    exact this
  have hinv : Real.exp (-q * α) ≤ 6 / (q * α) ^ 3 := by
    rw [show -q * α = -(q * α) by ring, Real.exp_neg, inv_eq_one_div,
      div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith only [hexp]
  have h4' : 3600 * Real.pi * K ≤ α * q ^ 3 := by
    rwa [div_le_iff₀ (by positivity)] at h4
  have hπK : 0 ≤ 24 * Real.pi * K * α ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hK) (by positivity)
  calc 24 * Real.pi * K * α ^ 2 * Real.exp (-q * α)
      ≤ 24 * Real.pi * K * α ^ 2 * (6 / (q * α) ^ 3) := mul_le_mul_of_nonneg_left hinv hπK
    _ = 144 * Real.pi * K / (q ^ 3 * α) := by field_simp; ring
    _ ≤ 1 / 25 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith only [h4']

/-- The far-region error. -/
private theorem far_error_le {A α : ℝ} (hαA : 150000 * A ≤ α) (hα : 450000 ≤ α) :
    Real.exp (9 / 2 * A) *
      (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 25 := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = -(15 / 8) * α ^ 2 + 20 * α + 164 := ⟨_, rfl⟩
  rw [← hP]
  have hα2 : 450000 * α ≤ α ^ 2 := by nlinarith only [hα]
  have hαexp : α ≤ Real.exp α := by linarith only [Real.add_one_le_exp α]
  have h300 : Real.exp (9 / 2 * A + 1 + α + P) ≤ 1 / 300 :=
    exp_le_one_div_of_add_le (by norm_num) (by rw [hP]; linarith only [hαA, hα, hα2])
  calc Real.exp (9 / 2 * A) * (12 * Real.exp 1 * α * Real.exp P)
      ≤ Real.exp (9 / 2 * A) * (12 * Real.exp 1 * Real.exp α * Real.exp P) := by gcongr
    _ = 12 * Real.exp (9 / 2 * A + 1 + α + P) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    _ ≤ 12 * (1 / 300) := by gcongr
    _ = 1 / 25 := by norm_num

/-- The quintic Gaussian exponent of the boundary value is at most `−α² − α` for `α ≥ 100`. -/
private theorem boundary_exponent_le {α : ℝ} (hα : 100 ≤ α) :
    -((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α + α ≤ -α ^ 2 := by
  have hα0 : 0 ≤ α := by linarith only [hα]
  have ha2 : α ^ 2 / 2 ≤ α ^ 2 - 1 / 2 := by nlinarith only [hα]
  have hsq : (α ^ 2 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) ha2 2
  have h5 : α ^ 5 / 320 ≤ (α ^ 2 - 1 / 2) ^ 2 * α / 80 := by
    have := mul_le_mul_of_nonneg_right hsq hα0
    nlinarith only [this]
  have h3 : (α ^ 2 + 1 / 2) * (α + 1 / 8) ≤ 4 * α ^ 3 := by nlinarith only [hα]
  have h6 : 4 * α ^ 3 + 21 * α + α ^ 2 ≤ α ^ 5 / 320 := by
    have hα2 : 10000 ≤ α ^ 2 := by nlinarith only [hα]
    have hα3 : 0 ≤ α ^ 3 := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hα2 hα3, hα, hα2]
  linarith only [h5, h3, h6]

/-- The boundary error. -/
private theorem boundary_error_le {A α : ℝ} (hαA : 150000 * A ≤ α) (hα : 450000 ≤ α) :
    Real.exp (9 / 2 * A) * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) ≤ 1 / 25 := by
  have hpoly := boundary_exponent_le (α := α) (by linarith only [hα])
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = -((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
    (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α := ⟨_, rfl⟩
  rw [← hQ] at hpoly ⊢
  have hα2 : 450000 * α ≤ α ^ 2 := by nlinarith only [hα]
  have hαexp : α ≤ Real.exp α := by linarith only [Real.add_one_le_exp α]
  have h50 : Real.exp (9 / 2 * A + α + Q) ≤ 1 / 50 :=
    exp_le_one_div_of_add_le (by norm_num) (by linarith only [hαA, hα, hα2, hpoly])
  calc Real.exp (9 / 2 * A) * (2 * α * Real.exp Q)
      ≤ Real.exp (9 / 2 * A) * (2 * Real.exp α * Real.exp Q) := by gcongr
    _ = 2 * Real.exp (9 / 2 * A + α + Q) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 2 * (1 / 50) := by gcongr
    _ = 1 / 25 := by norm_num

/-- **The Gaussian error sums above an explicit slope.** With `A = 1/η + 3`, both error sums of
the Weyl window argument are small for every `α ≥ max(50000 A² e⁸, 3600πK/(m/80)³)`: each of the
six decaying terms is at most `1/25`. -/
theorem weyl_errors_small {c₀ η m K α : ℝ} (hη : 0 < η) (hm : 0 < m) (hK : 0 ≤ K)
    (hδ : 1 / 8 ≤ 3 / 4 * c₀ - 1 - η)
    (h3 : 50000 * (1 / η + 3) ^ 2 * Real.exp 8 ≤ α)
    (h4 : 3600 * Real.pi * K / (m / 80) ^ 3 ≤ α) :
    160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 / η + 3 := ⟨_, rfl⟩
  rw [← hA] at h3 ⊢
  have hA3 : 3 ≤ A := by
    have : 0 < 1 / η := by positivity
    rw [hA]; linarith only [this]
  have hA0 : 0 < A := by linarith only [hA3]
  -- sizes of `α`
  have hαA2 : 50000 * A ^ 2 ≤ α :=
    (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by norm_num))).trans h3
  have hαA : 150000 * A ≤ α := by nlinarith only [hαA2, hA3]
  have hα450 : 450000 ≤ α := by linarith only [hαA, hA3]
  have hα0 : 0 < α := by linarith only [hα450]
  -- the six terms
  have T1 : Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) ≤ 1 / 25 := by
    refine exp_le_one_div_of_add_le (by norm_num) ?_
    have h := mul_le_mul (show (225000 : ℝ) ≤ α / 2 by linarith only [hα450]) hδ
      (by norm_num) (by linarith only [hα0])
    linarith only [h]
  have T2 : Real.exp (-α ^ 2 + 1) ≤ 1 / 25 :=
    exp_le_one_div_of_add_le (by norm_num) (by nlinarith only [hα450])
  have T3 := model_error_le hA0 hα0 h3
  have T4 := strip_error_le (q := m / 80) (by positivity) hK hα0 h4
  have T5 := far_error_le hαA hα450
  have T6 := boundary_error_le hαA hα450
  refine ⟨by linarith only [hα450], by linarith only [hαA2, sq_nonneg A],
    by linarith only [T1, T2, T3, T4, T5],
    ?_⟩
  have h3' : A * (1 + 2 * A * Real.sqrt (20 / α) * Real.exp 4) ≤ A * (1 + 1 / 25) :=
    mul_le_mul_of_nonneg_left (by linarith only [T3]) hA0.le
  rw [mul_add (Real.exp (9 / 2 * A))]
  linarith only [T4, T5, T6, h3', hαA, hα450]

/-! ## The height -/

private theorem exp_six_le : Real.exp 6 ≤ 405 := by
  have he1 : Real.exp 1 ≤ 2.72 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 6 ≤ (2.72 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 6
    _ ≤ 405 := by norm_num

private theorem exp_eight_le : Real.exp 8 ≤ 3000 := by
  have he1 : Real.exp 1 ≤ 2.72 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 8 ≤ (2.72 : ℝ) ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 8
    _ ≤ 3000 := by norm_num

private theorem exp_quarter_le : Real.exp (1 / 4) ≤ 13 / 10 := by
  have he1 : Real.exp 1 ≤ 2.72 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have h : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  refine (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 4 ≠ 0)).1 ?_
  rw [h]
  exact he1.trans (by norm_num)

/-- **The Weyl heat horizon with an explicit height.** For `0 < ε ≤ 1` and `0 < t ≤ 1/8`, every
zero `z` of `H_t` with `|Re z| ≥ exp(10²⁰/ε⁴)` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}` is real and
simple. -/
theorem riemannHeat_zeros_real_simple_weyl_explicit {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {t : ℝ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) {z : ℂ} (hz : riemannHeat t z = 0)
    (hX₀ : Real.exp (10 ^ 20 / ε ^ 4) ≤ |z.re|)
    (hXc : 2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re|) :
    z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  -- parameters: strip half-width `η = ε/36`, Gaussian margin `m = 2ε/3`, slope `α₀ = 4·10¹⁹/ε⁴`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 36 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = 2 * ε / 3 := ⟨_, rfl⟩
  obtain ⟨α₀, hα₀def⟩ : ∃ α₀ : ℝ, α₀ = 4 * 10 ^ 19 / ε ^ 4 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hη36 : η ≤ 1 / 36 := by rw [hηdef]; linarith
  have hm : 0 < m := by rw [hmdef]; positivity
  have hK0 := weylStripConstant_nonneg hη
  -- the Gaussian margin: `(2 − 2ρ)c − 2(1 + η) ≥ 2ε/3` and `2ρc ≥ 1` for `c ≥ 3/2 + ε`
  have hρ3 : 1 / 3 ≤ weylRate η := by
    unfold weylRate; rw [le_div_iff₀ (by linarith)]; linarith
  have hρle : 2 * weylRate η ≤ 2 / 3 + 4 * η := by
    have h : weylRate η ≤ (1 / 6 + η) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have e : (1 / 6 + η) / (1 / 2) = 1 / 3 + 2 * η := by ring
    linarith
  have hmc : ∀ c : ℝ, 3 / 2 + ε ≤ c → m ≤ c ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * c * (2 * weylRate η) * (1 + η) := by
    intro c hc
    have hbase : 2 * ε / 3 ≤ (4 / 3 - 4 * η) * (3 / 2 + ε) - 2 * (1 + η) := by
      rw [hηdef]; nlinarith [mul_nonneg hε.le (sub_nonneg.2 hε1)]
    have h1 : (4 / 3 - 4 * η) * (3 / 2 + ε) ≤ (2 - 2 * weylRate η) * (3 / 2 + ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (2 - 2 * weylRate η) * (3 / 2 + ε) ≤ (2 - 2 * weylRate η) * c :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    have hmarg : 2 * ε / 3 ≤ (2 - 2 * weylRate η) * c - 2 * (1 + η) := by linarith
    have hc1 : 1 ≤ c * (2 * weylRate η) := by nlinarith
    have e : c ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) - 2 * c * (2 * weylRate η) * (1 + η) =
        c * (2 * weylRate η) * ((2 - 2 * weylRate η) * c - 2 * (1 + η)) := by ring
    rw [e, hmdef]
    calc 2 * ε / 3 = 1 * (2 * ε / 3) := (one_mul _).symm
      _ ≤ c * (2 * weylRate η) * (2 * ε / 3) := mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ ≤ c * (2 * weylRate η) * ((2 - 2 * weylRate η) * c - 2 * (1 + η)) :=
          mul_le_mul_of_nonneg_left hmarg (by linarith)
  have hδ : 1 / 8 ≤ 3 / 4 * (3 / 2 + ε) - 1 - η := by rw [hηdef]; linarith
  -- the strip constant: `K ≤ 2·10⁹/ε`
  have hKle : weylStripConstant η ≤ 2 * 10 ^ 9 / ε := by
    have hE : Real.exp 6 * Real.exp (1 / 4) ≤ 405 * (13 / 10) :=
      mul_le_mul exp_six_le exp_quarter_le (Real.exp_pos _).le (by norm_num)
    have e : weylStripConstant η = 3628800 * (Real.exp 6 * Real.exp (1 / 4)) / ε := by
      unfold weylStripConstant; rw [hηdef]; field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  -- the two slope conditions
  have hε4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε.le hε1
  have hε4pos : 0 < ε ^ 4 := by positivity
  have h3 : 50000 * (1 / η + 3) ^ 2 * Real.exp 8 ≤ α₀ := by
    have hA : 1 / η + 3 ≤ 39 / ε := by
      rw [hηdef, show 1 / (ε / 36) = 36 / ε by field_simp, show (39 : ℝ) / ε = 36 / ε + 3 / ε by ring]
      have : 3 ≤ 3 / ε := by rw [le_div_iff₀ hε]; linarith
      linarith
    have hA0 : 0 ≤ 1 / η + 3 := by positivity
    have hA2 : (1 / η + 3) ^ 2 ≤ 1521 / ε ^ 4 := by
      calc (1 / η + 3) ^ 2 ≤ (39 / ε) ^ 2 := pow_le_pow_left₀ hA0 hA 2
        _ = 1521 / ε ^ 2 := by rw [div_pow]; norm_num
        _ ≤ 1521 / ε ^ 4 :=
            div_le_div_of_nonneg_left (by norm_num) hε4pos
              (pow_le_pow_of_le_one hε.le hε1 (by norm_num))
    calc 50000 * (1 / η + 3) ^ 2 * Real.exp 8
        ≤ 50000 * (1521 / ε ^ 4) * 3000 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA2 (by norm_num)) exp_eight_le
            (Real.exp_pos _).le (by positivity)
      _ = 228150000000 / ε ^ 4 := by ring
      _ ≤ 4 * 10 ^ 19 / ε ^ 4 := div_le_div_of_nonneg_right (by norm_num) hε4pos.le
      _ = α₀ := hα₀def.symm
  have h4 : 3600 * Real.pi * weylStripConstant η / (m / 80) ^ 3 ≤ α₀ := by
    rw [div_le_iff₀ (by positivity)]
    have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    calc 3600 * Real.pi * weylStripConstant η
        ≤ 3600 * 3.15 * (2 * 10 ^ 9 / ε) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hπ (by norm_num)) hKle hK0 (by norm_num)
      _ = 22680000000000 / ε := by ring
      _ ≤ (4 * 10 ^ 19 / 1728000) / ε := div_le_div_of_nonneg_right (by norm_num) hε.le
      _ = α₀ * (m / 80) ^ 3 := by rw [hα₀def, hmdef]; field_simp; ring
  -- the height: `2π e^{2α₀} ≤ exp(10²⁰/ε⁴)`
  have hα₀160 : 160 ≤ α₀ := by
    rw [hα₀def, le_div_iff₀ hε4pos]; linarith
  have hheight : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ |z.re| := by
    refine le_trans ?_ hX₀
    rw [max_eq_left hα₀160]
    have h2π : 2 * Real.pi ≤ Real.exp 7 := by
      have := Real.add_one_le_exp 7
      linarith [Real.pi_lt_d2]
    calc 2 * Real.pi * Real.exp (2 * α₀) ≤ Real.exp 7 * Real.exp (2 * α₀) :=
          mul_le_mul_of_nonneg_right h2π (Real.exp_pos _).le
      _ = Real.exp (7 + 2 * α₀) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (10 ^ 20 / ε ^ 4) := by
          apply Real.exp_le_exp.mpr
          have h1 : (1 : ℝ) ≤ 1 / ε ^ 4 := by rw [le_div_iff₀ hε4pos]; linarith
          rw [hα₀def, div_eq_mul_one_div (4 * 10 ^ 19) (ε ^ 4),
            div_eq_mul_one_div (10 ^ 20) (ε ^ 4)]
          linarith
  exact riemannHeat_zeros_real_simple_weyl_of_params (c₀ := 3 / 2 + ε) hη (by linarith)
    (by linarith) hm hmc (by linarith) (norm_xiLine_le_strip_weyl_explicit hη (by linarith)) hK0
    (fun α hα => weyl_errors_small hη hm hK0 hδ (h3.trans hα) (h4.trans hα)) ht ht8 hz hheight hXc

/-- **The explicit height for every `ε > 0`.** For `0 < t ≤ 1/8`, every zero `z` of `H_t` with
`|Re z| ≥ exp(10²⁰/min(ε,1)⁴)` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}` is real and simple. -/
theorem riemannHeat_zeros_real_simple_weyl_explicit_of_pos {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) {z : ℂ} (hz : riemannHeat t z = 0)
    (hX₀ : Real.exp (10 ^ 20 / (min ε 1) ^ 4) ≤ |z.re|)
    (hXc : 2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re|) :
    z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 :=
  riemannHeat_zeros_real_simple_weyl_explicit (lt_min hε one_pos) (min_le_right _ _) ht ht8 hz hX₀
    (le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (div_le_div_of_nonneg_right
      (by linarith only [min_le_left ε 1]) ht.le)) (by positivity)) hXc)

end

end GaloisForLFunctions.ZeroConfigurationGeometry
