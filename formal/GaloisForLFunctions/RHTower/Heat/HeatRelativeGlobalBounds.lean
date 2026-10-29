import GaloisForLFunctions.RHTower.Heat.HeatLocalGrowth
import GaloisForLFunctions.RHTower.Heat.HeatReverseGaussian

/-!+# Global relative bounds for the Riemann heat flow

An Euler-region anchor controls the heat flow throughout a horizontal
strip. Nearby heights use the logarithmic derivative of `ξ`; distant
heights use the fixed strip integral of the actual heated kernel.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

private theorem hasDerivAt_xiLine_height (x : ℝ) :
    HasDerivAt (fun v : ℝ => xiLine v 16) (I * xiLineDeriv x 16) x := by
  have hin : HasDerivAt (fun v : ℂ => (1 / 2 : ℂ) + 16 + I * v) I (x : ℂ) := by
    have h := ((hasDerivAt_id' (x : ℂ)).const_mul I).const_add ((1 / 2 : ℂ) + 16)
    simpa only [mul_one] using h
  have h := (xi_differentiable ((1 / 2 : ℂ) + 16 + I * x)).hasDerivAt.comp (x : ℂ) hin
  simpa only [xiLine, xiLineDeriv, Complex.ofReal_ofNat, Function.comp_def, mul_comm I]
    using h.comp_ofReal

private theorem log_height_le {X x : ℝ} (hx : 0 < x) (hxhi : x ≤ X ^ 2) :
    Real.log x ≤ 2 * Real.log X := by
  have h := Real.log_le_log hx hxhi
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- Euler values compare exponentially in height distance, with logarithmic slope. -/
theorem norm_xiLine_sixteen_height_le {X x : ℝ} (hX : 4096 ≤ X)
    (hL : 20 ≤ Real.log X) (hxlo : 2048 ≤ x) (hxhi : x ≤ X ^ 2) :
    ‖xiLine x 16‖ ≤ ‖xiLine X 16‖ * Real.exp ((2 * Real.log X) * |x - X|) := by
  have hL0 : 0 < 2 * Real.log X := by linarith
  have hsub : uIcc X x ⊆ Icc 2048 (X ^ 2) :=
    uIcc_subset_Icc ⟨by linarith, by nlinarith only [hX]⟩ ⟨hxlo, hxhi⟩
  have hb : ∀ s ∈ uIcc X x, ‖I * xiLineDeriv s 16 - (0 : ℂ) * xiLine s 16‖ ≤
      (2 * Real.log X) * ‖xiLine s 16‖ := by
    intro s hs
    obtain ⟨hslo, hshi⟩ := hsub hs
    have hs0 : 0 < s := by linarith
    have hlog := log_height_le hs0 hshi
    have hratio : Real.log (s / (2 * Real.pi)) ≤ Real.log s :=
      Real.log_le_log (by positivity)
        (div_le_self hs0.le (by nlinarith only [Real.pi_gt_three]))
    have hfrac : (16 + 1 / 2 : ℝ) / (2 * s) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 2 * s)]
      linarith only [hslo]
    rw [zero_mul, sub_zero, norm_mul, norm_I, one_mul]
    refine (norm_xiLineDeriv_le (by linarith : 200 ≤ s)
      (by norm_num : (9 / 2 : ℝ) ≤ 16)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith only [hlog, hratio, hfrac, hL]
  have hm := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := (0 : ℂ)) hL0
    (u := X) (w := x) (fun s _ => hasDerivAt_xiLine_height s) hb
  simp only [mul_zero, Complex.exp_zero, mul_one, Complex.zero_re, Real.exp_zero] at hm
  nlinarith only [hm, norm_sub_norm_le (xiLine x 16) (xiLine X 16)]

/-- The quadratic Gaussian envelope also includes zero heat. -/
theorem norm_riemannHeat_le_sixteen_exp_of_nonneg {t X : ℝ}
    (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (hX : 16 ≤ X) (y : ℝ) :
    ‖riemannHeat t ((X : ℂ) + I * y)‖ ≤ 4 * ‖xiLine X 16‖ *
      Real.exp (((Real.log X + xiSliceGlobalConstant) / 2) * |y| + y ^ 2 +
        2 * t * ((Real.log X + xiSliceGlobalConstant) / 2) ^ 2) := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    have hpt : riemannHeat 0 ((X : ℂ) + I * y) = xiLine X (-y) := by
      rw [riemannHeat_zero, xiLine]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hpt]
    have h := norm_xiLine_le_sixteen_exp hX (-y)
    simp only [abs_neg, neg_sq] at h
    refine h.trans (mul_le_mul ?_ (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (by positivity))
    · nlinarith only [norm_nonneg (xiLine X 16)]
    · nlinarith only [sq_nonneg y]
  · exact norm_riemannHeat_le_sixteen_exp hpos ht8 hX y

/-- The actual heated kernel gives one bound on the unit horizontal strip. -/
theorem exists_riemannHeat_unit_strip_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 →
      ∀ z : ℂ, |z.im| ≤ 1 → ‖riemannHeat t z‖ ≤ M := by
  let J := ∫ u : ℝ, riemannKernelReal u * Real.exp ((1 / 8 : ℝ) * u ^ 2) * Real.exp |u|
  have hJ : 0 ≤ J := integral_nonneg fun u => by
    exact mul_nonneg (mul_nonneg (riemannKernelReal_pos u).le (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hi : Integrable (fun u : ℝ =>
      riemannKernelReal u * Real.exp ((1 / 8 : ℝ) * u ^ 2) * Real.exp |u|) := by
    simpa only [one_mul] using
      (riemannKernel_superExp.mul_exp_sq (by norm_num : (0 : ℝ) ≤ 1 / 8)).integrable_mul_exp 1
  refine ⟨1 + J, by linarith, ?_⟩
  intro t ht ht8 z hz
  refine (norm_riemannHeat_le_strip_integral ht z).trans ((show
    (∫ u : ℝ, riemannKernelReal u * Real.exp (t * u ^ 2) * Real.exp (|z.im| * |u|)) ≤ J
    from ?_).trans (by linarith))
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun u =>
      mul_nonneg (mul_nonneg (riemannKernelReal_pos u).le (Real.exp_pos _).le)
        (Real.exp_pos _).le) hi
  filter_upwards [] with u
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right ht8 (sq_nonneg u))) (riemannKernelReal_pos u).le)
    (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (mul_nonneg (riemannKernelReal_pos u).le (Real.exp_pos _).le)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hz (abs_nonneg u)

private theorem norm_riemannHeat_near_half_height_le {t X x y : ℝ}
    (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X)
    (htL : t * Real.log X ≤ 1) (hx : |x - X| ≤ X / 2) (hy : |y| ≤ 1) :
    ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      ‖xiLine X 16‖ * Real.exp (15 * Real.log X + 2 * Real.log X * |x - X|) := by
  have hxlo : 2048 ≤ x := by linarith only [(abs_le.mp hx).1, hX]
  have hxhi : x ≤ X ^ 2 := by nlinarith only [(abs_le.mp hx).2, hX]
  have hlog := log_height_le (show 0 < x by linarith) hxhi
  set B := (Real.log x + xiSliceGlobalConstant) / 2
  have hB0 : 0 ≤ B := by
    have hl := Real.log_nonneg (show 1 ≤ x by linarith)
    dsimp [B]
    linarith only [hl, xiSliceGlobalConstant_pos]
  have hBhi : B ≤ 2 * Real.log X := by
    dsimp [B]
    linarith only [hlog, xiSliceGlobalConstant_le_sixteen, hL]
  have hL0 : 0 ≤ Real.log X := by linarith
  have hBsq : B ^ 2 ≤ 4 * (Real.log X) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hBhi)
      (add_nonneg hB0 (show 0 ≤ 2 * Real.log X by positivity))]
  have hheat : 2 * t * B ^ 2 ≤ 8 * Real.log X := by
    have h1 := mul_le_mul_of_nonneg_left hBsq (show 0 ≤ 2 * t by positivity)
    have h2 := mul_le_mul_of_nonneg_right htL hL0
    nlinarith only [h1, h2]
  have hlin : B * |y| ≤ 2 * Real.log X :=
    (mul_le_mul_of_nonneg_left hy hB0).trans (by simpa only [mul_one] using hBhi)
  have hysq : y ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ 1 + |y| by positivity), sq_abs y]
  have he : B * |y| + y ^ 2 + 2 * t * B ^ 2 ≤ 1 + 10 * Real.log X := by
    linarith only [hheat, hlin, hysq]
  have hv := norm_xiLine_sixteen_height_le hX hL hxlo hxhi
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * ‖xiLine x 16‖ * Real.exp (B * |y| + y ^ 2 + 2 * t * B ^ 2) :=
      norm_riemannHeat_le_sixteen_exp_of_nonneg ht ht8 (by linarith) y
    _ ≤ Real.exp 4 * (‖xiLine X 16‖ * Real.exp (2 * Real.log X * |x - X|)) *
        Real.exp (1 + 10 * Real.log X) :=
      mul_le_mul (mul_le_mul hfour hv (norm_nonneg _) (Real.exp_pos _).le)
        (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ = ‖xiLine X 16‖ * Real.exp (5 + 10 * Real.log X + 2 * Real.log X * |x - X|) := by
      rw [show Real.exp 4 * (‖xiLine X 16‖ * Real.exp (2 * Real.log X * |x - X|)) *
          Real.exp (1 + 10 * Real.log X) = ‖xiLine X 16‖ *
          (Real.exp 4 * Real.exp (2 * Real.log X * |x - X|) *
            Real.exp (1 + 10 * Real.log X)) by ring]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by linarith only [hL])) (norm_nonneg _)

/-- A global height envelope relative to the Euler anchor, uniform at small heat. -/
theorem exists_riemannHeat_global_relative_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ∀ x y : ℝ, |y| ≤ 1 → ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
          ‖xiLine X 16‖ * Real.exp (C * Real.log X * (1 + |x - X|)) := by
  obtain ⟨M, hM, hstrip⟩ := exists_riemannHeat_unit_strip_bound
  let N := ‖xiLine 2048 16‖
  have hN : 0 < N := by
    apply norm_pos_iff.mpr
    apply xi_ne_zero_of_one_lt_re
    norm_num [xiLine]
  let Q := M / N
  have hQ : 0 < Q := div_pos hM hN
  have hMQ : M ≤ N * Real.exp Q := by
    have hq : Q ≤ Real.exp Q := by linarith only [Real.add_one_le_exp Q]
    have h := (div_le_iff₀ hN).mp hq
    simpa only [mul_comm N] using h
  refine ⟨Q + 20, by positivity, 4096 + Real.exp 20,
    by linarith only [Real.exp_pos 20], ?_⟩
  intro X hX₀ t ht ht8 htL x y hy
  have hX : 4096 ≤ X := by linarith only [hX₀, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20) (show Real.exp 20 ≤ X by linarith)
    simpa only [Real.log_exp] using h
  have hL0 : 0 ≤ Real.log X := by linarith
  have hΔ : 0 ≤ |x - X| := abs_nonneg _
  by_cases hnear : |x - X| ≤ X / 2
  · refine (norm_riemannHeat_near_half_height_le ht ht8 hX hL htL hnear hy).trans ?_
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right (show (15 : ℝ) ≤ Q + 20 by linarith) hL0
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ Q + 20 by linarith) hL0) hΔ
    nlinarith only [h1, h2]
  · have hfar : X ≤ 2 * |x - X| := by linarith only [lt_of_not_ge hnear]
    have hanchor : N ≤ ‖xiLine X 16‖ * Real.exp (2 * Real.log X * X) := by
      have h := norm_xiLine_sixteen_height_le hX hL (by norm_num : (2048 : ℝ) ≤ 2048)
        (by nlinarith only [hX] : (2048 : ℝ) ≤ X ^ 2)
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
      rw [abs_of_nonpos (by linarith : (2048 : ℝ) - X ≤ 0)]
      nlinarith only [hL0]
    have hbound := hstrip t ht ht8 ((x : ℂ) + I * y) (by simpa using hy)
    calc
      _ ≤ M := hbound
      _ ≤ N * Real.exp Q := hMQ
      _ ≤ (‖xiLine X 16‖ * Real.exp (2 * Real.log X * X)) * Real.exp Q :=
        mul_le_mul_of_nonneg_right hanchor (Real.exp_pos _).le
      _ = ‖xiLine X 16‖ * Real.exp (2 * Real.log X * X + Q) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        have h1 := mul_le_mul_of_nonneg_left hfar (show 0 ≤ 2 * Real.log X by positivity)
        have h2 : Q ≤ Q * Real.log X := by nlinarith only [hQ, hL]
        have h3 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ Q + 20 by linarith) hL0) hΔ
        nlinarith only [h1, h2, h3, hL0]

end

end RHTower.DeBruijn
