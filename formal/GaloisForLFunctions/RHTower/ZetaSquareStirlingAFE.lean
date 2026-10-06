import GaloisForLFunctions.RHTower.ZetaSquareStirlingCarrier
import GaloisForLFunctions.RHTower.ZetaNotchTwistedOffDiagonal
import GaloisForLFunctions.RHTower.ZetaNearOneLineBound

/-!
# The symmetric approximate functional equation for `|ζ(½+it)|²`

With `V` the Gaussian cutoff, for large `t`

`|ζ(½+it)|² = Σ_{m,n} (mn)^{−1/2} V(2πmn/t) ((n/m)^{it} + (m/n)^{it}) + O(t^{−1/2} log t)`
(`exists_norm_zetaSq_sub_symmetricAFE_le`).

**Proof.**  The exact critical-pair formula at scale `L = t/2π` (`zetaSq_eq_afe`) has the direct
cutoff `V(mn/L)` and the dual weight `W_t(mnL)`.  On a vertical line `Re w = a`,
`W_t(Y) − V(Y/L²) = (1/2π) ∫ (G_t(−w) − L^{2w}) Y^{−w} e^{w²}/w dv`
and Stirling for the carrier (`norm_critCarrier_neg_sub_conductorPow_le`) bounds it by
`C L^{2a} Y^{−a}/t` (`norm_dualLine_sub_le`).  Take `a = −1/4` when `mn ≤ L` (both weights are then
`1 +` their line integrals) and `a = 1` when `mn > L`; the lattice sums
`Σ_{mn ≤ L} (mn)^{−1/2} ≪ √L log L` and `Σ_{mn > L} (mn)^{−3/2} ≪ L^{−1/2} log L` finish it.  The two
shifted residues carry `e^{−t²}`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex Set Filter Topology MeasureTheory RHTower

/-! ## Conductor powers -/

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

/-- `(Y/L²)^{−w} = L^{2w} Y^{−w}`. -/
theorem div_sq_cpow_neg {Y L : ℝ} (hY : 0 < Y) (hL : 0 < L) (w : ℂ) :
    ((Y / L ^ 2 : ℝ) : ℂ) ^ (-w) = ((L : ℝ) : ℂ) ^ (2 * w) * ((Y : ℝ) : ℂ) ^ (-w) := by
  rw [ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp hL, ofReal_cpow_eq_exp hY,
    ← Complex.exp_add, Real.log_div hY.ne' (by positivity), Real.log_pow]
  congr 1
  push_cast
  ring

theorem smoothAFEMellinIntegrand_div_sq {Y L : ℝ} (hY : 0 < Y) (hL : 0 < L) (w : ℂ) :
    smoothAFEMellinIntegrand (Y / L ^ 2) w =
      ((L : ℝ) : ℂ) ^ (2 * w) * smoothAFEMellinIntegrand Y w := by
  unfold smoothAFEMellinIntegrand
  rw [div_sq_cpow_neg hY hL]
  ring

/-! ## One vertical line -/

/-- `(1+t)² t³ e^{−t/2}` is bounded. -/
theorem exists_poly_mul_exp_neg_half_le : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
    (1 + t) ^ 2 * t ^ 3 * Real.exp (-(t / 2)) ≤ B := by
  refine ⟨2 * (2 ^ 3 * Nat.factorial 3) + 2 * (2 ^ 5 * Nat.factorial 5), fun t ht => ?_⟩
  have hpow : ∀ N : ℕ, t ^ N * Real.exp (-(t / 2)) ≤ 2 ^ N * N.factorial := by
    intro N
    have h := Real.pow_div_factorial_le_exp (t / 2) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hf] at h
    have h2 : t ^ N = 2 ^ N * (t / 2) ^ N := by rw [← mul_pow]; ring
    have he : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-(t / 2))
    rw [h2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ t / 2 by positivity) N]
  have e := Real.exp_pos (-(t / 2))
  have h3 := hpow 3
  have h5 := hpow 5
  have hpoly : (1 + t) ^ 2 * t ^ 3 ≤ 2 * t ^ 3 + 2 * t ^ 5 := by
    nlinarith [pow_nonneg ht 3, sq_nonneg (1 - t), pow_nonneg ht 5]
  calc (1 + t) ^ 2 * t ^ 3 * Real.exp (-(t / 2)) ≤ (2 * t ^ 3 + 2 * t ^ 5) * Real.exp (-(t / 2)) :=
        mul_le_mul_of_nonneg_right hpoly e.le
    _ = 2 * (t ^ 3 * Real.exp (-(t / 2))) + 2 * (t ^ 5 * Real.exp (-(t / 2))) := by ring
    _ ≤ _ := by linarith

theorem integrable_one_add_abs_sq_mul_exp_neg_half_sq :
    Integrable (fun v : ℝ => (1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) := by
  have h := integrable_one_add_abs_sq_mul_exp_neg_sq
  have hs : Integrable (fun v : ℝ => (1 + |v / Real.sqrt 2|) ^ 2 * Real.exp (-((v / Real.sqrt 2) ^ 2))) :=
    h.comp_div (by positivity)
  refine (hs.const_mul 2).mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  have hsq : (v / Real.sqrt 2) ^ 2 = v ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hab : 1 + |v| ≤ Real.sqrt 2 * (1 + |v / Real.sqrt 2|) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2), mul_add,
      mul_div_cancel₀ _ (by positivity : Real.sqrt 2 ≠ 0)]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsq, neg_div]
  calc (1 + |v|) ^ 2 * Real.exp (-(v ^ 2 / 2))
      ≤ (Real.sqrt 2 * (1 + |v / Real.sqrt 2|)) ^ 2 * Real.exp (-(v ^ 2 / 2)) := by
        gcongr
    _ = 2 * ((1 + |v / Real.sqrt 2|) ^ 2 * Real.exp (-(v ^ 2 / 2))) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring

/-- Stirling range `|v| ≤ √t`: `‖G_t(−w) − L^{2w}‖ ≤ 24 e^{96} L^{2a} (1+|v|)²/t`. -/
theorem norm_critCarrier_sub_conductorPow_stirling_le {a t v : ℝ} (ha1 : |a| ≤ 1) (ht : 16 ≤ t)
    (hv : |v| ≤ Real.sqrt t) :
    ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
        ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ ≤
      24 * Real.exp 96 * ((t / (2 * Real.pi)) ^ (2 * a) * (1 + |v|) ^ 2 / t) := by
  have ht0 : 0 < t := by linarith
  have hs4 : 4 ≤ Real.sqrt t := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  have hst := Real.mul_self_sqrt ht0.le
  have hsqrt : Real.sqrt t ≤ t / 2 := by nlinarith
  have hre : |((a : ℂ) + (v : ℂ) * I).re| ≤ 1 := by simpa using ha1
  have him : 2 * |((a : ℂ) + (v : ℂ) * I).im| ≤ t := by simp; linarith
  have hS := norm_critCarrier_neg_sub_conductorPow_le (by linarith) hre him
  have hwre : ((a : ℂ) + (v : ℂ) * I).re = a := by simp
  rw [hwre] at hS
  have hwnorm : ‖(a : ℂ) + (v : ℂ) * I‖ ≤ 1 + |v| := by
    calc ‖(a : ℂ) + (v : ℂ) * I‖ ≤ ‖(a : ℂ)‖ + ‖(v : ℂ) * I‖ := norm_add_le _ _
      _ = |a| + |v| := by simp
      _ ≤ 1 + |v| := by linarith
  set x : ℝ := ‖(a : ℂ) + (v : ℂ) * I‖ * (20 * ‖(a : ℂ) + (v : ℂ) * I‖ / t + 52 / t ^ 2) with hx
  have hε : x ≤ 24 * (1 + |v|) ^ 2 / t := by
    have h52 : 52 / t ^ 2 ≤ 4 / t := by
      rw [div_le_div_iff₀ (pow_pos ht0 2) ht0]; nlinarith
    have hw0 := norm_nonneg ((a : ℂ) + (v : ℂ) * I)
    calc x ≤ (1 + |v|) * (20 * (1 + |v|) / t + 4 / t) := by
          rw [hx]; gcongr
      _ = (1 + |v|) * (20 * (1 + |v|) + 4) / t := by ring
      _ ≤ 24 * (1 + |v|) ^ 2 / t := by
          rw [div_le_div_iff_of_pos_right ht0]; nlinarith [abs_nonneg v]
  have hε96 : 24 * (1 + |v|) ^ 2 / t ≤ 96 := by
    rw [div_le_iff₀ ht0]
    have h1 : 1 + |v| ≤ 2 * Real.sqrt t := by linarith
    have : (1 + |v|) ^ 2 ≤ 4 * t := by
      calc (1 + |v|) ^ 2 ≤ (2 * Real.sqrt t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = 4 * t := by rw [mul_pow, Real.sq_sqrt ht0.le]; ring
    linarith
  have hx0 : 0 ≤ x := le_trans (le_of_eq rfl) (by rw [hx]; positivity)
  have hxe : Real.exp x - 1 ≤ x * Real.exp x := by
    have h1 := Real.add_one_le_exp (-x)
    have he := Real.exp_pos x
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hexp : Real.exp x - 1 ≤ 24 * Real.exp 96 * ((1 + |v|) ^ 2 / t) := by
    calc Real.exp x - 1 ≤ x * Real.exp x := hxe
      _ ≤ x * Real.exp 96 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hε.trans hε96)) hx0
      _ ≤ (24 * (1 + |v|) ^ 2 / t) * Real.exp 96 :=
          mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le
      _ = _ := by ring
  have hL : 0 ≤ (t / (2 * Real.pi)) ^ (2 * a) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ (t / (2 * Real.pi)) ^ (2 * a) * (Real.exp x - 1) := hS
    _ ≤ (t / (2 * Real.pi)) ^ (2 * a) * (24 * Real.exp 96 * ((1 + |v|) ^ 2 / t)) :=
        mul_le_mul_of_nonneg_left hexp hL
    _ = _ := by ring

/-- Gaussian range `|v| > √t`: with a polynomial envelope `K(1+t)²(1+|v|)²` of the carrier,
`‖G_t(−w) − L^{2w}‖ e^{−v²} ≤ (KB/(2π)² + 1) L^{2a}/t (1+|v|)² e^{−v²/2}`. -/
theorem norm_critCarrier_sub_conductorPow_gauss_le {a t v K B : ℝ} (ha1 : |a| ≤ 1) (ht : 16 ≤ t)
    (hv : Real.sqrt t < |v|) (hK : 0 ≤ K)
    (hB : (1 + t) ^ 2 * t ^ 3 * Real.exp (-(t / 2)) ≤ B)
    (hcrude : ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I))‖ ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2) :
    ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
        ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ * Real.exp (-(v ^ 2)) ≤
      (K * B / (2 * Real.pi) ^ 2 + 1) * ((t / (2 * Real.pi)) ^ (2 * a) / t) *
        ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) := by
  have ht0 : 0 < t := by linarith
  set L : ℝ := t / (2 * Real.pi) with hLdef
  have hL0 : 0 < L := by positivity
  have hL1 : 1 ≤ L := by
    rw [hLdef, le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
  have hLa0 : 0 ≤ L ^ (2 * a) := Real.rpow_nonneg hL0.le _
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hvt : t < v ^ 2 := by
    have h' : Real.sqrt t ^ 2 < |v| ^ 2 := pow_lt_pow_left₀ hv (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt ht0.le, sq_abs] at h'
  have hLpow : ‖((L : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ = L ^ (2 * a) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hL0]; simp
  have hsub : ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
      ((L : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ ≤
      K * (1 + t) ^ 2 * (1 + |v|) ^ 2 + L ^ (2 * a) := by
    refine (norm_sub_le _ _).trans ?_
    rw [hLpow]
    exact add_le_add hcrude le_rfl
  have hsplit : Real.exp (-(v ^ 2)) ≤ Real.exp (-(t / 2)) * Real.exp (-(v ^ 2) / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have hLlow : (2 * Real.pi) ^ 2 / t ^ 2 ≤ L ^ (2 * a) := by
    have h1 : L ^ (-(2 : ℝ)) ≤ L ^ (2 * a) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by have := abs_le.mp ha1; linarith)
    have h2 : L ^ (-(2 : ℝ)) = (2 * Real.pi) ^ 2 / t ^ 2 := by
      rw [Real.rpow_neg hL0.le, Real.rpow_two, hLdef, div_pow, inv_div]
    linarith
  have hKB : K * (1 + t) ^ 2 * Real.exp (-(t / 2)) ≤
      K * B / (2 * Real.pi) ^ 2 * (L ^ (2 * a) / t) := by
    have h1 : (1 + t) ^ 2 * Real.exp (-(t / 2)) ≤ B / t ^ 3 := by
      rw [le_div_iff₀ (pow_pos ht0 3)]; nlinarith [hB]
    have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have h3 : 1 / t ^ 2 ≤ L ^ (2 * a) / (2 * Real.pi) ^ 2 := by
      rw [le_div_iff₀ hpi]
      calc 1 / t ^ 2 * (2 * Real.pi) ^ 2 = (2 * Real.pi) ^ 2 / t ^ 2 := by ring
        _ ≤ L ^ (2 * a) := hLlow
    have h2 : B / t ^ 3 ≤ B / (2 * Real.pi) ^ 2 * (L ^ (2 * a) / t) := by
      calc B / t ^ 3 = B * (1 / t ^ 2) / t := by field_simp
        _ ≤ B * (L ^ (2 * a) / (2 * Real.pi) ^ 2) / t := by
            gcongr
        _ = B / (2 * Real.pi) ^ 2 * (L ^ (2 * a) / t) := by ring
    calc K * (1 + t) ^ 2 * Real.exp (-(t / 2)) = K * ((1 + t) ^ 2 * Real.exp (-(t / 2))) := by
          ring
      _ ≤ K * (B / (2 * Real.pi) ^ 2 * (L ^ (2 * a) / t)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hK
      _ = _ := by ring
  have hLt : L ^ (2 * a) * Real.exp (-(t / 2)) ≤ L ^ (2 * a) / t := by
    rw [le_div_iff₀ ht0, mul_assoc]
    refine mul_le_of_le_one_right hLa0 ?_
    have h2 := Real.pow_div_factorial_le_exp (t / 2) (by positivity) 2
    have hpos := Real.exp_pos (t / 2)
    norm_num at h2
    rw [Real.exp_neg]
    rw [inv_mul_le_iff₀ hpos]
    nlinarith
  have hv1 : 1 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v]
  have hc : L ^ (2 * a) * Real.exp (-(t / 2)) ≤ L ^ (2 * a) / t * (1 + |v|) ^ 2 :=
    hLt.trans (le_mul_of_one_le_right (div_nonneg hLa0 ht0.le) hv1)
  have hsub0 : 0 ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2 + L ^ (2 * a) :=
    add_nonneg (mul_nonneg (mul_nonneg hK (sq_nonneg _)) (sq_nonneg _)) hLa0
  calc _ ≤ (K * (1 + t) ^ 2 * (1 + |v|) ^ 2 + L ^ (2 * a)) *
        (Real.exp (-(t / 2)) * Real.exp (-(v ^ 2) / 2)) :=
        mul_le_mul hsub hsplit (Real.exp_pos _).le hsub0
    _ = ((K * (1 + t) ^ 2 * Real.exp (-(t / 2))) * (1 + |v|) ^ 2 +
          L ^ (2 * a) * Real.exp (-(t / 2))) * Real.exp (-(v ^ 2) / 2) := by ring
    _ ≤ ((K * B / (2 * Real.pi) ^ 2 * (L ^ (2 * a) / t)) * (1 + |v|) ^ 2 +
          L ^ (2 * a) / t * (1 + |v|) ^ 2) * Real.exp (-(v ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_right hKB (sq_nonneg _)) hc) (Real.exp_pos _).le
    _ = _ := by ring

/-- **The dual weight minus the cutoff on one vertical line.**  For `0 < |a| ≤ 1` and a polynomial
envelope of the carrier on `Re w = a`, the integrand `(G_t(−w) − L^{2w}) Y^{−w} e^{w²}/w`
(`L = t/2π`) is at most `C L^{2a} Y^{−a}/t · (1+|v|)² e^{−v²/2}` for `t ≥ 16`. -/
theorem exists_norm_dualLine_sub_le {a : ℝ} (ha : a ≠ 0) (ha1 : |a| ≤ 1) {K : ℝ}
    (hK : 0 ≤ K) (hcrude : ∀ t v : ℝ, 4 ≤ t →
      ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I))‖ ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t Y : ℝ}, 16 ≤ t → 0 < Y →
      ∀ v : ℝ, ‖(critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
          ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))) *
          smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * ((t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) := by
  obtain ⟨B, hB⟩ := exists_poly_mul_exp_neg_half_le
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0 le_rfl)
  have hE0 : 0 ≤ Real.exp (a ^ 2) / |a| := by positivity
  refine ⟨(24 * Real.exp 96 + (K * B / (2 * Real.pi) ^ 2 + 1)) * (Real.exp (a ^ 2) / |a|),
    mul_nonneg (add_nonneg (by positivity) (add_nonneg (div_nonneg (mul_nonneg hK hB0)
      (by positivity)) zero_le_one)) hE0, fun {t Y} ht hY v => ?_⟩
  have ht0 : 0 < t := by linarith
  have hM := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY ha v
  have hLa0 : 0 ≤ (t / (2 * Real.pi)) ^ (2 * a) := Real.rpow_nonneg (by positivity) _
  have hYa0 : 0 ≤ Y ^ (-a) := Real.rpow_nonneg hY.le _
  have hG0 : 0 ≤ (1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hP0 : 0 ≤ (t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t :=
    div_nonneg (mul_nonneg hLa0 hYa0) ht0.le
  rw [norm_mul]
  rcases le_or_gt |v| (Real.sqrt t) with hv | hv
  · have hS := norm_critCarrier_sub_conductorPow_stirling_le ha1 ht hv
    have hev : Real.exp (-(v ^ 2)) ≤ Real.exp (-(v ^ 2) / 2) := by
      rw [Real.exp_le_exp]; nlinarith [sq_nonneg v]
    calc _ ≤ (24 * Real.exp 96 * ((t / (2 * Real.pi)) ^ (2 * a) * (1 + |v|) ^ 2 / t)) *
          (Y ^ (-a) * (Real.exp (a ^ 2) / |a|) * Real.exp (-(v ^ 2) / 2)) :=
          mul_le_mul hS (hM.trans (mul_le_mul_of_nonneg_left hev (mul_nonneg hYa0 hE0)))
            (norm_nonneg _) (by positivity)
      _ = (24 * Real.exp 96 * (Real.exp (a ^ 2) / |a|)) *
            ((t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t) *
            ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP0) hG0
          refine mul_le_mul_of_nonneg_right ?_ hE0
          have : 0 ≤ K * B / (2 * Real.pi) ^ 2 + 1 :=
            add_nonneg (div_nonneg (mul_nonneg hK hB0) (by positivity)) zero_le_one
          linarith
  · have hG := norm_critCarrier_sub_conductorPow_gauss_le ha1 ht hv hK (hB t ht0.le)
      (hcrude t v (by linarith))
    calc _ ≤ ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
          ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ (-a) * (Real.exp (a ^ 2) / |a|) * Real.exp (-(v ^ 2))) :=
          mul_le_mul_of_nonneg_left hM (norm_nonneg _)
      _ = (Y ^ (-a) * (Real.exp (a ^ 2) / |a|)) *
          (‖critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
            ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))‖ *
            Real.exp (-(v ^ 2))) := by ring
      _ ≤ (Y ^ (-a) * (Real.exp (a ^ 2) / |a|)) *
          ((K * B / (2 * Real.pi) ^ 2 + 1) * ((t / (2 * Real.pi)) ^ (2 * a) / t) *
            ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2))) :=
          mul_le_mul_of_nonneg_left hG (mul_nonneg hYa0 hE0)
      _ = ((K * B / (2 * Real.pi) ^ 2 + 1) * (Real.exp (a ^ 2) / |a|)) *
            ((t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t) *
            ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP0) hG0
          refine mul_le_mul_of_nonneg_right ?_ hE0
          have : 0 ≤ 24 * Real.exp 96 := by positivity
          linarith

/-! ## The dual weight against the direct cutoff -/

theorem integrable_one_add_abs_sq_mul_exp_neg_half_sq' :
    Integrable (fun v : ℝ => (1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2)) :=
  integrable_one_add_abs_sq_mul_exp_neg_half_sq

theorem integrable_smoothAFEMellinIntegrand_line {a Y : ℝ} (ha : a ≠ 0) (hY : 0 < Y) :
    Integrable (fun v : ℝ => smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)) := by
  refine ((integrable_exp_neg_mul_sq one_pos).const_mul
    (Y ^ (-a) * (Real.exp (a ^ 2) / |a|))).mono'
    (continuous_smoothAFEMellinIntegrand_line ha hY).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have h := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY ha v
  simpa using h

/-- On any line, `W_t^{(a)}(Y) − V^{(a)}(Y/L²) = (1/2π) ∫ (G_t(−w) − L^{2w}) Y^{−w} e^{w²}/w dv`. -/
theorem critDualWeightAt_sub_cutoffAt_eq {a t Y : ℝ} (ha : a ≠ 0) (ht : 0 < t) (hY : 0 < Y)
    (hint : Integrable (fun v : ℝ => critCarrier t (-((a : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I))) :
    critDualWeightAt a t Y - smoothAFECutoffAt a (Y / (t / (2 * Real.pi)) ^ 2) =
      (1 / (2 * Real.pi)) • ∫ v : ℝ, (critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
          ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))) *
        smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I) := by
  have hL : 0 < t / (2 * Real.pi) := by positivity
  have hcut : smoothAFECutoffAt a (Y / (t / (2 * Real.pi)) ^ 2) =
      (1 / (2 * Real.pi)) • ∫ v : ℝ, ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFECutoffAt mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [← smoothAFEMellinIntegrand_div_sq hY hL]
    rfl
  have hint2 : Integrable (fun v : ℝ =>
      ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)) := by
    refine (integrable_smoothAFEMellinIntegrand_line ha
      (show 0 < Y / (t / (2 * Real.pi)) ^ 2 by positivity)).congr
      (Eventually.of_forall fun v => ?_)
    exact smoothAFEMellinIntegrand_div_sq hY hL _
  rw [hcut]
  unfold critDualWeightAt
  rw [← smul_sub, ← integral_sub hint hint2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  ring

/-- `L¹` bound for the line difference. -/
theorem norm_critDualWeightAt_sub_cutoffAt_le {a : ℝ} (ha : a ≠ 0) (ha1 : |a| ≤ 1) {K : ℝ}
    (hK : 0 ≤ K) (hcrude : ∀ t v : ℝ, 4 ≤ t →
      ‖critCarrier t (-((a : ℂ) + (v : ℂ) * I))‖ ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t Y : ℝ}, 16 ≤ t → 0 < Y →
      Integrable (fun v : ℝ => critCarrier t (-((a : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)) →
      ‖critDualWeightAt a t Y - smoothAFECutoffAt a (Y / (t / (2 * Real.pi)) ^ 2)‖ ≤
        C * ((t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualLine_sub_le ha ha1 hK hcrude
  set I₀ : ℝ := ∫ v : ℝ, (1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2) with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun v => by positivity
  refine ⟨(1 / (2 * Real.pi)) * C * I₀, by positivity, fun {t Y} ht hY hint => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [critDualWeightAt_sub_cutoffAt_eq ha ht0 hY hint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  set P : ℝ := (t / (2 * Real.pi)) ^ (2 * a) * Y ^ (-a) / t with hP
  have hmaj : Integrable (fun v : ℝ => C * P * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2) / 2))) :=
    integrable_one_add_abs_sq_mul_exp_neg_half_sq.const_mul _
  have hb := norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun v => hC ht hY v)
  rw [integral_const_mul] at hb
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, (critCarrier t (-((a : ℂ) + (v : ℂ) * I)) -
          ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * ((a : ℂ) + (v : ℂ) * I))) *
        smoothAFEMellinIntegrand Y ((a : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * (C * P * I₀) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (2 * Real.pi) * C * I₀ * P := by ring

/-- **Right line `Re w = 1`:** `‖W_t(Y) − V(Y/L²)‖ ≤ C L²/(Y t)`. -/
theorem exists_norm_critDualWeight_sub_cutoff_le_right :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t Y : ℝ}, 16 ≤ t → 0 < Y →
      ‖critDualWeight t Y - smoothAFECutoff (Y / (t / (2 * Real.pi)) ^ 2)‖ ≤
        C * ((t / (2 * Real.pi)) ^ 2 / Y / t) := by
  have hcrude : ∀ t v : ℝ, 4 ≤ t →
      ‖critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ 1 * (1 + t) ^ 2 * (1 + |v|) ^ 2 := by
    intro t v ht
    have h := norm_critCarrier_dual_le t v
    rw [abs_of_nonneg (by linarith)] at h
    simpa using h
  obtain ⟨C, hC0, hC⟩ := norm_critDualWeightAt_sub_cutoffAt_le (a := 1) one_ne_zero
    (by norm_num) zero_le_one hcrude
  refine ⟨C, hC0, fun {t Y} ht hY => ?_⟩
  have h := hC ht hY (critDualWeightAt_one_integrable hY t)
  rw [← critDualWeight_eq_at_one] at h
  have hcut : smoothAFECutoffAt 1 (Y / (t / (2 * Real.pi)) ^ 2) =
      smoothAFECutoff (Y / (t / (2 * Real.pi)) ^ 2) := rfl
  rw [hcut] at h
  refine h.trans (le_of_eq ?_)
  have hL : 0 < t / (2 * Real.pi) := by
    have : (0 : ℝ) < t := by linarith
    positivity
  rw [show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_neg_one]
  ring

/-- **Left line `Re w = −1/4`:** `‖W_t(Y) − V(Y/L²)‖ ≤ C (Y/L²)^{1/4}/t`. -/
theorem exists_norm_critDualWeight_sub_cutoff_le_left :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t Y : ℝ}, 16 ≤ t → 0 < Y →
      ‖critDualWeight t Y - smoothAFECutoff (Y / (t / (2 * Real.pi)) ^ 2)‖ ≤
        C * ((t / (2 * Real.pi)) ^ (2 * (-(1 / 4) : ℝ)) * Y ^ (1 / 4 : ℝ) / t) := by
  obtain ⟨K, hK, hcar⟩ := exists_norm_critCarrier_right_le (δ := 1 / 4) (by norm_num) (by norm_num)
  have hcrude : ∀ t v : ℝ, 4 ≤ t →
      ‖critCarrier t (-(((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2 := by
    intro t v ht
    have h := hcar t v
    have harg : -(((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) = (((1 / 4 : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [harg]
    have hden : 1 ≤ (max 1 |t - v|) ^ (1 / 4 : ℝ) * (max 1 |-t - v|) ^ (1 / 4 : ℝ) := by
      have h1 : 1 ≤ (max 1 |t - v|) ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow (le_max_left _ _) (by norm_num)
      have h2 : 1 ≤ (max 1 |-t - v|) ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow (le_max_left _ _) (by norm_num)
      nlinarith
    calc _ ≤ K / ((max 1 |t - v|) ^ (1 / 4 : ℝ) * (max 1 |-t - v|) ^ (1 / 4 : ℝ)) := h
      _ ≤ K := div_le_self hK hden
      _ ≤ K * (1 + t) ^ 2 * (1 + |v|) ^ 2 := by
          have h1 : 1 ≤ (1 + t) ^ 2 := by nlinarith
          have h2 : 1 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v]
          have : 1 ≤ (1 + t) ^ 2 * (1 + |v|) ^ 2 := by nlinarith
          nlinarith
  obtain ⟨C, hC0, hC⟩ := norm_critDualWeightAt_sub_cutoffAt_le (a := -(1 / 4)) (by norm_num)
    (by norm_num [abs_of_neg]) hK hcrude
  refine ⟨C, hC0, fun {t Y} ht hY => ?_⟩
  have hint := critDualWeightAt_neg_integrable (δ := 1 / 4) (by norm_num) (by norm_num) hY t
  have h := hC ht hY (by simpa using hint)
  rw [critDualWeight_eq_one_add_at_neg (δ := 1 / 4) (by norm_num) (by norm_num) hY t]
  have hx : 0 < Y / (t / (2 * Real.pi)) ^ 2 := by
    have : (0 : ℝ) < t := by linarith
    positivity
  have hcut := smoothAFECutoffAt_eq_smoothAFECutoff_sub_one hx (show (-(1 / 4) : ℝ) < 0 by norm_num)
  have hrw : 1 + critDualWeightAt (-(1 / 4)) t Y - smoothAFECutoff (Y / (t / (2 * Real.pi)) ^ 2) =
      critDualWeightAt (-(1 / 4)) t Y - smoothAFECutoffAt (-(1 / 4)) (Y / (t / (2 * Real.pi)) ^ 2) := by
    rw [hcut]; ring
  rw [hrw]
  simpa using h

/-! ## Lattice sums -/

/-- `Σ_{N ≤ n < K} (n+1)^{−3/2} ≤ 2/√N` for `N ≥ 1`. -/
theorem sum_Ico_three_halves_le {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    ∑ n ∈ Finset.Ico N K, (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤
      2 * (Real.sqrt N)⁻¹ := by
  have hstep : ∀ n : ℕ, 1 ≤ n → (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤
      2 * ((Real.sqrt n)⁻¹ - (Real.sqrt ((n : ℝ) + 1))⁻¹) := by
    intro n hn
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set a := Real.sqrt (n : ℝ) with ha_def
    set b := Real.sqrt ((n : ℝ) + 1) with hb_def
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
    have hsa : a ^ 2 = n := Real.sq_sqrt (by linarith)
    have hsb : b ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have hn1 : (n : ℝ) + 1 = b ^ 2 := hsb.symm
    rw [hn1]
    rw [show 2 * (a⁻¹ - b⁻¹) = 2 * (b - a) / (a * b) by field_simp]
    rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hba : (b - a) * (b + a) = 1 := by nlinarith
    have hsq : 0 ≤ (b - a) ^ 2 * b * (2 * b + a) := by
      have := sub_nonneg.mpr hab
      positivity
    nlinarith [hba, hsq]
  induction K with
  | zero => simp
  | succ K ih =>
    rcases lt_or_ge K N with hK | hK
    · rw [Finset.Ico_eq_empty (by omega)]; simp
    · rw [Finset.sum_Ico_succ_top hK]
      have hstepK := hstep K (by omega)
      -- telescoping strengthening
      have htel : ∀ M : ℕ, N ≤ M → ∑ n ∈ Finset.Ico N M, (((n : ℝ) + 1) *
          Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 2 * ((Real.sqrt N)⁻¹ - (Real.sqrt M)⁻¹) := by
        intro M hM
        induction M with
        | zero => omega
        | succ M ihM =>
          rcases eq_or_lt_of_le hM with h | h
          · rw [← h]; simp
          · rw [Finset.sum_Ico_succ_top (by omega)]
            have := ihM (by omega)
            have hs := hstep M (by omega)
            push_cast at hs ⊢
            linarith
      have := htel (K + 1) (by omega)
      have hpos : 0 ≤ (Real.sqrt ((K + 1 : ℕ) : ℝ))⁻¹ := by positivity
      rw [Finset.sum_Ico_succ_top hK] at this
      linarith

/-- The one-dimensional weight `Σ_n n^{−1/2} min(1, X/n)`: at most `5√X` for `X ≥ 1` and `3X`
for every `X > 0`. -/
theorem tsum_inv_sqrt_mul_min_le {X : ℝ} (hX : 0 < X) :
    ∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤ 3 * X ∧
      (1 ≤ X → ∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤
        5 * Real.sqrt X) := by
  have hf0 : ∀ n : ℕ, 0 ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) :=
    fun n => mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
  have hle1 : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤
      (Real.sqrt ((n : ℝ) + 1))⁻¹ :=
    fun n => mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have hle2 : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤
      X * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
    intro n
    calc _ ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ * (X / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = X * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
          rw [mul_inv]; ring
  constructor
  · refine Real.tsum_le_of_sum_range_le hf0 fun K => ?_
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp; positivity
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hK]
    norm_num
    have h0 : min 1 X ≤ X := min_le_right _ _
    have hrest : ∑ n ∈ Finset.Ico 1 K, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤
        X * (2 * (Real.sqrt (1 : ℕ))⁻¹) := by
      calc _ ≤ ∑ n ∈ Finset.Ico 1 K, X * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ :=
            Finset.sum_le_sum fun n _ => hle2 n
        _ = X * ∑ n ∈ Finset.Ico 1 K, (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
            rw [Finset.mul_sum]
        _ ≤ X * (2 * (Real.sqrt (1 : ℕ))⁻¹) :=
            mul_le_mul_of_nonneg_left (sum_Ico_three_halves_le le_rfl K) hX.le
    norm_num at hrest
    linarith
  · intro hX1
    refine Real.tsum_le_of_sum_range_le hf0 fun K => ?_
    set N := ⌊X⌋₊ with hNdef
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
      rw [hNdef]; exact (Nat.floor_pos.mpr hX1).ne')
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hX.le
    have hXN : X < N + 1 := Nat.lt_floor_add_one X
    have hNhalf : X / 2 ≤ N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      linarith
    have hsplit : ∑ n ∈ Finset.range K, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 (X / ((n : ℝ) + 1)) ≤
        ∑ n ∈ Finset.range N, (Real.sqrt ((n : ℝ) + 1))⁻¹ +
          ∑ n ∈ Finset.Ico N K, X * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
      rcases le_or_gt K N with hKN | hKN
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
        calc _ ≤ ∑ n ∈ Finset.range K, (Real.sqrt ((n : ℝ) + 1))⁻¹ :=
              Finset.sum_le_sum fun n _ => hle1 n
          _ ≤ ∑ n ∈ Finset.range N, (Real.sqrt ((n : ℝ) + 1))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKN)
                (fun n _ _ => by positivity)
      · rw [← Finset.sum_range_add_sum_Ico _ hKN.le]
        exact add_le_add (Finset.sum_le_sum fun n _ => hle1 n)
          (Finset.sum_le_sum fun n _ => hle2 n)
    have h1 := sum_range_inv_sqrt_le N
    have h2 : ∑ n ∈ Finset.Ico N K, X * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤
        X * (2 * (Real.sqrt N)⁻¹) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ico_three_halves_le hN1 K) hX.le
    have hsN : Real.sqrt (X / 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt hNhalf
    have hsX := Real.sqrt_le_sqrt hNX
    have hpos : 0 < Real.sqrt (X / 2) := Real.sqrt_pos.mpr (by positivity)
    have hXX : X * (2 * (Real.sqrt N)⁻¹) ≤ 3 * Real.sqrt X := by
      have hx2 : Real.sqrt (X / 2) = Real.sqrt X / Real.sqrt 2 := Real.sqrt_div' X (by norm_num)
      have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hsxx := Real.mul_self_sqrt hX.le
      have hsX0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
      have hs20 : 0 < Real.sqrt 2 := by positivity
      calc X * (2 * (Real.sqrt N)⁻¹) ≤ X * (2 * (Real.sqrt (X / 2))⁻¹) := by
            gcongr
        _ = 2 * Real.sqrt 2 * Real.sqrt X := by
            rw [hx2]; field_simp; nlinarith
        _ ≤ 3 * Real.sqrt X := by nlinarith
    linarith

/-- **The pair-weight sum**: `Σ_{m,n} (mn)^{−1/2} min(1, L/(mn)) ≤ √L (5(1 + log L) + 9)` for
`L ≥ 1`. -/
theorem tsum_pairWeight_le_sqrt_log {L : ℝ} (hL : 1 ≤ L) :
    ∑' p, pairWeight L p ≤ Real.sqrt L * (5 * (1 + Real.log L) + 9) := by
  have hL0 : 0 < L := by linarith
  rw [(summable_pairWeight hL0.le).tsum_prod]
  set h : ℕ → ℝ := fun m => ∑' n : ℕ, pairWeight L (m, n) with hh
  have hrow : ∀ m : ℕ, h m = (Real.sqrt ((m : ℝ) + 1))⁻¹ *
      ∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ * min 1 ((L / ((m : ℝ) + 1)) / ((n : ℝ) + 1)) := by
    intro m
    rw [hh, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [pairWeight]
    rw [Real.sqrt_mul (by positivity), mul_inv, div_div]
    ring
  have hh0 : ∀ m, 0 ≤ h m := fun m => tsum_nonneg fun n => pairWeight_nonneg hL0.le _
  refine Real.tsum_le_of_sum_range_le hh0 fun K => ?_
  set N := ⌊L⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    rw [hNdef]; exact (Nat.floor_pos.mpr hL).ne')
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hL0.le
  have hLN : L < N + 1 := Nat.lt_floor_add_one L
  have hsmall : ∀ m : ℕ, m < N → h m ≤ 5 * Real.sqrt L * ((m : ℝ) + 1)⁻¹ := by
    intro m hm
    have hm1 : ((m : ℝ) + 1) ≤ L := by
      have : (m : ℝ) + 1 ≤ N := by exact_mod_cast hm
      linarith
    have hX : 1 ≤ L / ((m : ℝ) + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hb := (tsum_inv_sqrt_mul_min_le (show 0 < L / ((m : ℝ) + 1) by positivity)).2 hX
    rw [hrow]
    calc _ ≤ (Real.sqrt ((m : ℝ) + 1))⁻¹ * (5 * Real.sqrt (L / ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 5 * Real.sqrt L * ((m : ℝ) + 1)⁻¹ := by
          rw [Real.sqrt_div' L (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
          have hpos : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
          field_simp
          rw [Real.sq_sqrt (by positivity)]
  have hlarge : ∀ m : ℕ, h m ≤ 3 * L * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
    intro m
    have hb := (tsum_inv_sqrt_mul_min_le (show 0 < L / ((m : ℝ) + 1) by positivity)).1
    rw [hrow]
    calc _ ≤ (Real.sqrt ((m : ℝ) + 1))⁻¹ * (3 * (L / ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 3 * L * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
          rw [mul_inv]; ring
  have hsplit : ∑ m ∈ Finset.range K, h m ≤
      ∑ m ∈ Finset.range N, 5 * Real.sqrt L * ((m : ℝ) + 1)⁻¹ +
        ∑ m ∈ Finset.Ico N K, 3 * L * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
    rcases le_or_gt K N with hKN | hKN
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
      calc _ ≤ ∑ m ∈ Finset.range K, 5 * Real.sqrt L * ((m : ℝ) + 1)⁻¹ :=
            Finset.sum_le_sum fun m hm => hsmall m (by
              have := Finset.mem_range.mp hm; omega)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKN)
              (fun m _ _ => by positivity)
    · rw [← Finset.sum_range_add_sum_Ico _ hKN.le]
      exact add_le_add (Finset.sum_le_sum fun m hm => hsmall m (Finset.mem_range.mp hm))
        (Finset.sum_le_sum fun m _ => hlarge m)
  have hharm : ∑ m ∈ Finset.range N, ((m : ℝ) + 1)⁻¹ ≤ 1 + Real.log L := by
    have h1 := harmonic_le_one_add_log N
    have h2 : ∑ m ∈ Finset.range N, ((m : ℝ) + 1)⁻¹ = (harmonic N : ℝ) := by
      unfold harmonic
      push_cast
      rfl
    have h3 : Real.log N ≤ Real.log L :=
      Real.log_le_log (by exact_mod_cast hN1) hNL
    linarith
  have htail := sum_Ico_three_halves_le hN1 K
  have hsq : Real.sqrt (L / 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith)
  have hLpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hL2 : 3 * L * (2 * (Real.sqrt N)⁻¹) ≤ 9 * Real.sqrt L := by
    have hx2 : Real.sqrt (L / 2) = Real.sqrt L / Real.sqrt 2 := Real.sqrt_div' L (by norm_num)
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hsll := Real.mul_self_sqrt hL0.le
    have hpos2 : 0 < Real.sqrt (L / 2) := Real.sqrt_pos.mpr (by positivity)
    calc 3 * L * (2 * (Real.sqrt N)⁻¹) ≤ 3 * L * (2 * (Real.sqrt (L / 2))⁻¹) := by
          gcongr
      _ = 6 * Real.sqrt 2 * Real.sqrt L := by
          rw [hx2]; field_simp; nlinarith
      _ ≤ 9 * Real.sqrt L := by nlinarith
  calc ∑ m ∈ Finset.range K, h m
      ≤ ∑ m ∈ Finset.range N, 5 * Real.sqrt L * ((m : ℝ) + 1)⁻¹ +
        ∑ m ∈ Finset.Ico N K, 3 * L * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := hsplit
    _ = 5 * Real.sqrt L * ∑ m ∈ Finset.range N, ((m : ℝ) + 1)⁻¹ +
        3 * L * ∑ m ∈ Finset.Ico N K, (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 5 * Real.sqrt L * (1 + Real.log L) + 3 * L * (2 * (Real.sqrt N)⁻¹) := by
        gcongr
    _ ≤ Real.sqrt L * (5 * (1 + Real.log L) + 9) := by nlinarith

/-! ## The shifted residues -/

theorem norm_productAFEShiftedResidue_critical_le {t : ℝ} (ht : 16 ≤ t) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {x : ℝ} (hx : 0 < x) :
    ‖productAFEShiftedResidue (linePt (σ * t)) (linePt (-(σ * t))) x‖ ≤
      Real.sqrt x * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) / t := by
  have ht0 : 0 < t := by linarith
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  unfold productAFEShiftedResidue
  have h1 : (1 : ℂ) - linePt (σ * t) = (1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I := by
    unfold linePt; push_cast; ring
  have h2 : linePt (-(σ * t)) + (1 - linePt (σ * t)) =
      ((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I := by
    unfold linePt; push_cast; ring
  rw [h2, h1, norm_div, norm_mul, norm_mul, Complex.norm_exp]
  have hxpow : ‖((x : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I)‖ = Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [Real.sqrt_eq_rpow]
  have hre : ((1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I) ^ 2 = ((1 / 4 - (σ * t) ^ 2 : ℝ) : ℂ) +
      ((-(σ * t)) : ℝ) * I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hexp : (((1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I) ^ 2).re = 1 / 4 - t ^ 2 := by
    rw [hre, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero, mul_pow, hσ2, one_mul]
  have hzeta : ‖riemannZeta (((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I)‖ ≤ 16 * t + 39 := by
    have him : (((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I).im = -(2 * σ * t) := by simp
    have hre1 : (((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I).re = 1 := by simp
    have habs : |(((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I).im| = 2 * t := by
      rw [him, abs_neg, abs_mul, abs_mul, hσabs, abs_of_pos ht0]; norm_num
    have hb := norm_riemannZeta_le_log_near_one (s := ((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I)
      (by rw [hre1, habs]
          have : 0 < Real.log (2 * t) := Real.log_pos (by linarith)
          have : 0 < 1 / Real.log (2 * t) := by positivity
          linarith)
      (by rw [hre1]; norm_num) (by rw [habs]; linarith)
    rw [habs] at hb
    have hlog : Real.log (2 * t) ≤ 2 * t := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * t by positivity)
      linarith
    linarith
  have hden : t ≤ ‖(1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I)
    have him : ((1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I).im = -(σ * t) := by simp
    rw [him, abs_neg, abs_mul, hσabs, abs_of_pos ht0, one_mul] at this
    exact this
  rw [hxpow, hexp]
  rw [div_le_div_iff₀ (by linarith) ht0]
  have hA : 0 ≤ Real.sqrt x * Real.exp (1 / 4 - t ^ 2) := by positivity
  calc Real.sqrt x * Real.exp (1 / 4 - t ^ 2) *
        ‖riemannZeta (((1 : ℝ) : ℂ) + ((-(2 * σ * t)) : ℝ) * I)‖ * t
      ≤ Real.sqrt x * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) * t := by gcongr
    _ ≤ Real.sqrt x * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) *
          ‖(1 / 2 : ℂ) - ((σ * t : ℝ) : ℂ) * I‖ := by gcongr

/-- **The symmetric approximate functional equation for `|ζ(½+it)|²`.** -/
theorem exists_norm_zetaSq_sub_symmetricAFE_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t →
      ‖zetaSq t - ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
          smoothAFECutoff (pairProd p / (t / (2 * Real.pi))) *
          (Complex.exp ((t * pairFreq p : ℝ) * I) + Complex.exp ((t * (-pairFreq p) : ℝ) * I))‖ ≤
        C * (1 + Real.log t) / Real.sqrt t := by
  obtain ⟨CR, hCR0, hCR⟩ := exists_norm_critDualWeight_sub_cutoff_le_right
  obtain ⟨CL, hCL0, hCL⟩ := exists_norm_critDualWeight_sub_cutoff_le_left
  set Cm : ℝ := max CR CL with hCm
  have hCm0 : 0 ≤ Cm := le_max_of_le_left hCR0
  refine ⟨14 * Cm + 2 * Real.exp (1 / 4) * 55, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set L : ℝ := t / (2 * Real.pi) with hLdef
  have hL0 : 0 < L := by positivity
  have hL1 : 1 ≤ L := by
    rw [hLdef, le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
  -- the dual weight against the cutoff, pairwise
  have hWV : ∀ p : ℕ × ℕ, ‖critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)‖ ≤
      Cm / t * min 1 (L / pairProd p) := by
    intro p
    have hP := pairProd_pos p
    have hY : 0 < pairProd p * L := by positivity
    have harg : pairProd p * L / L ^ 2 = pairProd p / L := by field_simp
    rcases le_or_gt (pairProd p) L with hpl | hpl
    · have h := hCL ht hY
      rw [← hLdef, harg] at h
      rw [min_eq_left (by rw [le_div_iff₀ hP]; linarith)]
      refine h.trans ?_
      have hfac : L ^ (2 * (-(1 / 4) : ℝ)) * (pairProd p * L) ^ (1 / 4 : ℝ) =
          (pairProd p / L) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow hP.le hL0.le, Real.div_rpow hP.le hL0.le,
          show (2 * (-(1 / 4) : ℝ)) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hL0.le]
        have : L ^ (1 / 2 : ℝ) = L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hL0]; norm_num
        rw [this]
        have hq : 0 < L ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL0 _
        field_simp
      have hle1 : (pairProd p / L) ^ (1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one (by positivity) (by rw [div_le_one hL0]; exact hpl) (by norm_num)
      rw [hfac]
      calc CL * ((pairProd p / L) ^ (1 / 4 : ℝ) / t) ≤ CL * (1 / t) := by
            gcongr
        _ ≤ Cm / t * 1 := by
            rw [mul_one, mul_one_div]
            exact div_le_div_of_nonneg_right (le_max_right _ _) ht0.le
    · have h := hCR ht hY
      rw [← hLdef, harg] at h
      rw [min_eq_right (by rw [div_le_one hP]; exact hpl.le)]
      have e : CR * (L ^ 2 / (pairProd p * L) / t) = CR / t * (L / pairProd p) := by
        field_simp
      rw [e] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (le_max_left _ _) ht0.le) (by positivity))
  -- summability
  have hsumD : Summable (fun p : ℕ × ℕ => (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
      Complex.exp ((t * pairFreq p : ℝ) * I)) := by
    refine Summable.of_norm_bounded (summable_direct_envelope hL0) fun p => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos p),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsumD' : Summable (fun p : ℕ × ℕ => (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
      Complex.exp ((t * (-pairFreq p) : ℝ) * I)) := by
    refine Summable.of_norm_bounded (summable_direct_envelope hL0) fun p => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos p),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsumE : Summable (fun p : ℕ × ℕ => (pairAmp p : ℂ) *
      (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
      Complex.exp ((t * (-pairFreq p) : ℝ) * I)) := by
    refine Summable.of_norm_bounded ((summable_pairWeight hL0.le).mul_left (Cm / t)) fun p => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos p),
      Complex.norm_exp_ofReal_mul_I, mul_one, pairWeight_eq]
    calc pairAmp p * ‖critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)‖
        ≤ pairAmp p * (Cm / t * min 1 (L / pairProd p)) :=
          mul_le_mul_of_nonneg_left (hWV p) (pairAmp_pos p).le
      _ = Cm / t * (pairAmp p * min 1 (L / pairProd p)) := by ring
  -- the identity
  have hafe := zetaSq_eq_afe hL0 ht0.ne'
  have hdir : (∑' p, directTerm L t p) = ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
      smoothAFECutoff (pairProd p / L) * Complex.exp ((t * pairFreq p : ℝ) * I) :=
    tsum_congr fun p => directTerm_eq L t p
  have hdual : (∑' p, dualTerm L t p) = (∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
      (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
      Complex.exp ((t * (-pairFreq p) : ℝ) * I)) + ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        smoothAFECutoff (pairProd p / L) * Complex.exp ((t * (-pairFreq p) : ℝ) * I) := by
    rw [← hsumE.tsum_add hsumD']
    refine tsum_congr fun p => ?_
    rw [dualTerm_eq]
    ring
  have hsym : (∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
      (Complex.exp ((t * pairFreq p : ℝ) * I) + Complex.exp ((t * (-pairFreq p) : ℝ) * I))) =
      (∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
        Complex.exp ((t * pairFreq p : ℝ) * I)) + ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        smoothAFECutoff (pairProd p / L) * Complex.exp ((t * (-pairFreq p) : ℝ) * I) := by
    rw [← hsumD.tsum_add hsumD']
    refine tsum_congr fun p => ?_
    ring
  rw [hafe, hdir, hdual, hsym]
  have hkey : (∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
        Complex.exp ((t * pairFreq p : ℝ) * I)) +
      ((∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
        Complex.exp ((t * (-pairFreq p) : ℝ) * I)) + ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
          smoothAFECutoff (pairProd p / L) * Complex.exp ((t * (-pairFreq p) : ℝ) * I)) -
      residueTerm L t -
      ((∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
        Complex.exp ((t * pairFreq p : ℝ) * I)) + ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        smoothAFECutoff (pairProd p / L) * Complex.exp ((t * (-pairFreq p) : ℝ) * I)) =
      (∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
        Complex.exp ((t * (-pairFreq p) : ℝ) * I)) - residueTerm L t := by ring
  rw [hkey]
  -- the error sum
  have hE : ‖∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
      (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
      Complex.exp ((t * (-pairFreq p) : ℝ) * I)‖ ≤ Cm / t * (Real.sqrt L * (5 * (1 + Real.log L) + 9)) := by
    refine (norm_tsum_le_tsum_norm hsumE.norm).trans ?_
    have hb : ∀ p : ℕ × ℕ, ‖(pairAmp p : ℂ) *
        (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
        Complex.exp ((t * (-pairFreq p) : ℝ) * I)‖ ≤ Cm / t * pairWeight L p := by
      intro p
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos p),
        Complex.norm_exp_ofReal_mul_I, mul_one, pairWeight_eq]
      calc pairAmp p * ‖critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)‖
          ≤ pairAmp p * (Cm / t * min 1 (L / pairProd p)) :=
            mul_le_mul_of_nonneg_left (hWV p) (pairAmp_pos p).le
        _ = Cm / t * (pairAmp p * min 1 (L / pairProd p)) := by ring
    calc _ ≤ ∑' p, Cm / t * pairWeight L p :=
          hsumE.norm.tsum_le_tsum hb ((summable_pairWeight hL0.le).mul_left _)
      _ = Cm / t * ∑' p, pairWeight L p := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_pairWeight_le_sqrt_log hL1) (by positivity)
  have hR : ‖residueTerm L t‖ ≤ 2 * (Real.sqrt L * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) / t) := by
    unfold residueTerm
    have h1 := norm_productAFEShiftedResidue_critical_le ht 1 (Or.inl rfl) hL0
    have h2 := norm_productAFEShiftedResidue_critical_le ht (-1) (Or.inr rfl) hL0
    simp only [one_mul, neg_mul, neg_neg] at h1 h2
    refine (norm_add_le _ _).trans ?_
    linarith
  -- final comparison
  have hsL : Real.sqrt L ≤ Real.sqrt t := Real.sqrt_le_sqrt (by
    rw [hLdef, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three])
  have hlogL : Real.log L ≤ Real.log t := Real.log_le_log hL0 (by
    rw [hLdef, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three])
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsqt := Real.mul_self_sqrt ht0.le
  have hE' : Cm / t * (Real.sqrt L * (5 * (1 + Real.log L) + 9)) ≤
      14 * Cm * (1 + Real.log t) / Real.sqrt t := by
    have h1 : Real.sqrt L * (5 * (1 + Real.log L) + 9) ≤ Real.sqrt t * (14 * (1 + Real.log t)) := by
      have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
      calc Real.sqrt L * (5 * (1 + Real.log L) + 9) ≤ Real.sqrt t * (5 * (1 + Real.log t) + 9) := by
            gcongr
        _ ≤ Real.sqrt t * (14 * (1 + Real.log t)) := by
            gcongr; linarith
    calc Cm / t * (Real.sqrt L * (5 * (1 + Real.log L) + 9))
        ≤ Cm / t * (Real.sqrt t * (14 * (1 + Real.log t))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 14 * Cm * (1 + Real.log t) / Real.sqrt t := by
          rw [div_mul_eq_mul_div, div_eq_div_iff ht0.ne' hst.ne']
          linear_combination (14 * Cm * (1 + Real.log t)) * hsqt
  have hR' : 2 * (Real.sqrt L * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) / t) ≤
      2 * Real.exp (1 / 4) * 55 * (1 + Real.log t) / Real.sqrt t := by
    have hexp : Real.exp (1 / 4 - t ^ 2) ≤ Real.exp (1 / 4) / t ^ 2 := by
      rw [Real.exp_sub, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      have := Real.add_one_le_exp (t ^ 2)
      have hpos := Real.exp_pos (1 / 4)
      nlinarith
    have h1 : Real.sqrt L * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) / t ≤
        Real.sqrt t * (Real.exp (1 / 4) / t ^ 2) * (55 * t) / t := by
      gcongr
      linarith
    have h2 : Real.sqrt t * (Real.exp (1 / 4) / t ^ 2) * (55 * t) / t =
        Real.exp (1 / 4) * 55 * (Real.sqrt t / t ^ 2) := by
      field_simp
    have h3 : Real.sqrt t / t ^ 2 ≤ 1 / Real.sqrt t := by
      rw [div_le_div_iff₀ (by positivity) hst]
      nlinarith
    calc 2 * (Real.sqrt L * Real.exp (1 / 4 - t ^ 2) * (16 * t + 39) / t)
        ≤ 2 * (Real.exp (1 / 4) * 55 * (1 / Real.sqrt t)) := by
          rw [h2] at h1
          have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ Real.exp (1 / 4) * 55)
          linarith
      _ ≤ 2 * Real.exp (1 / 4) * 55 * (1 + Real.log t) / Real.sqrt t := by
          rw [show 2 * (Real.exp (1 / 4) * 55 * (1 / Real.sqrt t)) =
            (2 * Real.exp (1 / 4) * 55) / Real.sqrt t by ring]
          refine div_le_div_of_nonneg_right ?_ hst.le
          nlinarith [Real.exp_pos (1 / 4)]
  calc _ ≤ ‖∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        (critDualWeight t (pairProd p * L) - smoothAFECutoff (pairProd p / L)) *
        Complex.exp ((t * (-pairFreq p) : ℝ) * I)‖ + ‖residueTerm L t‖ := norm_sub_le _ _
    _ ≤ 14 * Cm * (1 + Real.log t) / Real.sqrt t +
          2 * Real.exp (1 / 4) * 55 * (1 + Real.log t) / Real.sqrt t :=
        add_le_add (hE.trans hE') (hR.trans hR')
    _ = (14 * Cm + 2 * Real.exp (1 / 4) * 55) * (1 + Real.log t) / Real.sqrt t := by ring

end RHTower.ZetaNotch
