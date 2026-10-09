import GaloisForLFunctions.RHTower.ChronologicalBoseDilateCompleteness
import Mathlib.Algebra.Group.ForwardDiff

/-!
# How far CTF rows are pinned to Möbius: dilation differences are invisible

Bounded chronological rows with small residual are pointwise Möbius on a prefix
(`ChronologicalBoundedRowMobiusRigidity`).  This file proves the complementary statement:
beyond the height window that the Γ weight resolves, the dilation index carries no rigidity.

* `norm_fwdDiff_iter_cpowNeg_le`: the `k`-th forward difference of `y ↦ y^{-s}` (`Re s ≥ 0`)
  satisfies `‖Δ^k y^{-s}|_x‖ ≤ ∏_{i<k}(‖s‖+i) · x^{-Re s - k}`.  Induction on `k` with the
  mean value inequality, since `∂_y Δ^k y^{-s} = -s Δ^k y^{-(s+1)}`.
* `halfLineMellinUnitary_boseDilateDiff`: the Mellin image of the dilation difference
  `Σ_j (−1)^{k−j} C(k,j) β_{n+1+j}` is `−Γ(s)ζ(s) · Δ^k y^{-s}|_{n+1}` on the critical line.
* `norm_boseDilateDiff_le`, `exists_norm_boseDilateDiff_le`: its `L²((0,∞))` norm is at most
  `C_k (n+1)^{-k-1/2}`, with `C_k = ‖G_k‖_{L²}` finite because `|Γζ(1/2+it)|` decays like
  `e^{-π|t|/2}` while `G_k` grows polynomially.

Reading.  Adding `δ Σ_j (−1)^{k−j}C(k,j) e_{n+1+j}` to a row changes its residual by at most
`|δ| C_k (n+1)^{-k-1/2}`.  Coefficients at indices `n ≫ (C_k/ε)^{1/(k+1/2)}` can therefore be
moved by `O(1)` at cost `ε`, for every `k`.  With the explicit constant
`C_k ≤ √(8π A_k)`, `A_k = (18√(2π))²(2k+2)! e^{1+k}` (`toReal_eLpNorm_boseDiffWeight_le`), one gets
`‖Δ^k‖ ≤ B e^{-k}` once `n + 1 ≥ e³(2k+2)` (`norm_boseDilateDiff_le_exp`).  Choosing
`k = ⌈log(B/ε)⌉` (`exists_log_scale_dilation_freedom`): every index `n` with
`n + 1 ≥ e³(2 log(B/ε) + 4)` is unpinned at accuracy `ε`.  The Möbius prefix forced at accuracy
`ε` is therefore `O(log(1/ε))` long, matching the residue bound of the rigidity theorem.
-/

open Complex Finset MeasureTheory Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The power function `y ↦ y^{-s}` on the real line. -/
noncomputable def cpowNeg (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (-s)


theorem hasDerivAt_cpowNeg_shift (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cpowNeg s) (-s * cpowNeg (s + 1) y) y := by
  have hslit : ((y : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hy
  have h := (Complex.hasStrictDerivAt_cpow_const (c := -s) hslit).hasDerivAt.comp_ofReal
  have he : (-s - 1) = -(s + 1) := by ring
  rw [he] at h
  exact h

theorem fwdDiff_iter_cpowNeg_eq (k : ℕ) (s : ℂ) (y : ℝ) :
    (fwdDiff (1 : ℝ))^[k] (cpowNeg s) y =
      ∑ j ∈ range (k + 1), (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) * cpowNeg s (y + j) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun j _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem hasDerivAt_fwdDiff_iter_cpowNeg (k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt ((fwdDiff (1 : ℝ))^[k] (cpowNeg s))
      (-s * (fwdDiff (1 : ℝ))^[k] (cpowNeg (s + 1)) y) y := by
  have hf : (fwdDiff (1 : ℝ))^[k] (cpowNeg s) = fun z =>
      ∑ j ∈ range (k + 1), (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) * cpowNeg s (z + j) := by
    funext z; exact fwdDiff_iter_cpowNeg_eq k s z
  rw [hf, fwdDiff_iter_cpowNeg_eq, mul_sum]
  refine HasDerivAt.fun_sum fun j _ => ?_
  have hyj : 0 < y + j := by positivity
  have h2 := ((hasDerivAt_cpowNeg_shift s hyj).comp_add_const).const_mul
    (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ)
  exact h2.congr_deriv (by ring)

/-- `‖Δ^k y^{-s}‖ ≤ ∏_{i<k} (‖s‖ + i) · x^{-Re s - k}` for `Re s ≥ 0`, `x > 0`. -/
theorem norm_fwdDiff_iter_cpowNeg_le (k : ℕ) :
    ∀ (s : ℂ), 0 ≤ s.re → ∀ x : ℝ, 0 < x →
      ‖(fwdDiff (1 : ℝ))^[k] (cpowNeg s) x‖ ≤
        (∏ i ∈ range k, (‖s‖ + i)) * x ^ (-s.re - k) := by
  induction k with
  | zero =>
    intro s hs x hx
    simp [cpowNeg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  | succ k ih =>
    intro s hs x hx
    rw [Function.iterate_succ_apply']
    set g := (fwdDiff (1 : ℝ))^[k] (cpowNeg s) with hg
    have hstep : fwdDiff (1 : ℝ) g x = g (x + 1) - g x := rfl
    rw [hstep]
    set C : ℝ := ‖s‖ * ((∏ i ∈ range k, (‖s + 1‖ + i)) * x ^ (-(s + 1).re - k)) with hC
    have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun u => g (x + u))
          (-s * (fwdDiff (1 : ℝ))^[k] (cpowNeg (s + 1)) (x + u)) (Set.Icc 0 1) u := by
      intro u hu
      have hxu : 0 < x + u := by linarith [hu.1]
      exact ((hasDerivAt_fwdDiff_iter_cpowNeg k s hxu).comp_const_add x u).hasDerivWithinAt
    have hbound : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        ‖-s * (fwdDiff (1 : ℝ))^[k] (cpowNeg (s + 1)) (x + u)‖ ≤ C := by
      intro u hu
      have hxu : 0 < x + u := by linarith [hu.1]
      have hre : 0 ≤ (s + 1).re := by simp; linarith
      have hih := ih (s + 1) hre (x + u) hxu
      rw [norm_mul, norm_neg, hC]
      refine mul_le_mul_of_nonneg_left (hih.trans ?_) (norm_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _ => by positivity)
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [hu.1])
        (by simp; linarith)
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
    simp only [add_zero] at hmvt
    refine hmvt.trans ?_
    rw [hC, prod_range_succ', Nat.cast_zero, add_zero]
    have hprod : ∏ i ∈ range k, (‖s + 1‖ + (i : ℝ)) ≤ ∏ i ∈ range k, (‖s‖ + ((i + 1 : ℕ) : ℝ)) := by
      refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
      have := norm_add_le s 1
      rw [norm_one] at this
      push_cast
      linarith
    have hexp : -(s + 1).re - (k : ℝ) = -s.re - ((k + 1 : ℕ) : ℝ) := by
      simp; ring
    rw [hexp]
    have hx0 : 0 ≤ x ^ (-s.re - ((k + 1 : ℕ) : ℝ)) := by positivity
    calc ‖s‖ * ((∏ i ∈ range k, (‖s + 1‖ + i)) * x ^ (-s.re - ((k + 1 : ℕ) : ℝ)))
        ≤ ‖s‖ * ((∏ i ∈ range k, (‖s‖ + ((i + 1 : ℕ) : ℝ))) * x ^ (-s.re - ((k + 1 : ℕ) : ℝ))) := by
          gcongr
      _ = (∏ i ∈ range k, (‖s‖ + ((i + 1 : ℕ) : ℝ))) * ‖s‖ * x ^ (-s.re - ((k + 1 : ℕ) : ℝ)) := by
          ring

/-- `Σ_j (−1)^{k−j} C(k,j) β_{n+1+j}`, the `k`-th difference of the Bose dilates in the dilation
index, as a vector of `L²((0,∞))`. -/
noncomputable def boseDilateDiff (k n : ℕ) : HalfLineL2 :=
  ∑ j ∈ range (k + 1), (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) • boseDilateL2 (n + j)

private theorem halfLineL2_coeFn_finset_sum {ι : Type*} (u : Finset ι) (f : ι → Lp ℂ 2 (volume : Measure ℝ)) :
    ((∑ i ∈ u, f i : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ i ∈ u, (f i : ℝ → ℂ) x := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    simp
  | insert i u hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ u, f j), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx', Finset.sum_insert hi]

/-- On the critical line the Mellin image of the dilation difference is
`−Γ(s)ζ(s) · Δ^k y^{-s}|_{y = n+1}`. -/
theorem halfLineMellinUnitary_boseDilateDiff (k n : ℕ) :
    (halfLineMellinUnitary (boseDilateDiff k n) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) *
        (fwdDiff (1 : ℝ))^[k] (cpowNeg (mellinLinePoint ξ)) ((n : ℝ) + 1) := by
  have hmap : halfLineMellinUnitary (boseDilateDiff k n) =
      ∑ j ∈ range (k + 1), (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) •
        halfLineMellinUnitary (boseDilateL2 (n + j)) := by
    rw [boseDilateDiff, map_sum]
    simp only [LinearIsometryEquiv.map_smul]
  have hall : ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ j ∈ range (k + 1),
      (halfLineMellinUnitary (boseDilateL2 (n + j)) : ℝ → ℂ) ξ =
        -((((n + j + 1 : ℕ)) : ℂ) ^ (-mellinLinePoint ξ) *
          Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) :=
    (Filter.eventually_all_finset _).mpr fun j _ => halfLineMellinUnitary_boseDilateL2 (n + j)
  have hsmul : ∀ j ∈ range (k + 1),
      (((((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) •
        halfLineMellinUnitary (boseDilateL2 (n + j)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) •
          (halfLineMellinUnitary (boseDilateL2 (n + j)) : ℝ → ℂ) :=
    fun j _ => Lp.coeFn_smul _ _
  have hsmul' := (Filter.eventually_all_finset _).mpr hsmul
  rw [hmap]
  filter_upwards [halfLineL2_coeFn_finset_sum (range (k + 1)) (fun j =>
      (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) : ℂ) • halfLineMellinUnitary (boseDilateL2 (n + j))),
    hall, hsmul'] with ξ hsum hj hs
  rw [hsum, fwdDiff_iter_cpowNeg_eq, mul_sum]
  refine sum_congr rfl fun j hjmem => ?_
  rw [hs j hjmem, Pi.smul_apply, smul_eq_mul, hj j hjmem, cpowNeg]
  have hc : (((n + j + 1 : ℕ)) : ℂ) = ((((n : ℝ) + 1 + j : ℝ)) : ℂ) := by push_cast; ring
  rw [hc]
  ring

/-- `‖s(ξ)‖ ≤ 1 + 2π|ξ|` on the Mellin line. -/
private theorem norm_mellinLinePoint_le (ξ : ℝ) : ‖mellinLinePoint ξ‖ ≤ 1 + 2 * Real.pi * |ξ| := by
  rw [mellinLinePoint]
  calc ‖(1 / 2 : ℂ) - 2 * Real.pi * ξ * Complex.I‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖2 * Real.pi * ξ * Complex.I‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 2 * Real.pi * |ξ| := by
        have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        have h2 : ‖(2 * Real.pi * ξ * Complex.I : ℂ)‖ = 2 * Real.pi * |ξ| := by
          rw [norm_mul, Complex.norm_I, mul_one]
          have : ((2 * Real.pi * ξ : ℝ) : ℂ) = 2 * Real.pi * ξ := by push_cast; ring
          rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
        rw [h1, h2]; linarith

/-- The weight `G_k(ξ) = ‖Γ(s)ζ(s)‖ ∏_{i<k} (‖s‖ + i)` at `s = s(ξ)` on the Mellin line. -/
noncomputable def boseDiffWeight (k : ℕ) (ξ : ℝ) : ℝ :=
  ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
    ∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i)

theorem continuous_boseDiffWeight (k : ℕ) : Continuous (boseDiffWeight k) := by
  unfold boseDiffWeight
  refine continuous_Gamma_mul_zeta_mellinLinePoint.norm.mul ?_
  exact continuous_finsetProd _ fun i _ =>
    (continuous_norm.comp continuous_mellinLinePoint).add continuous_const

private theorem integrable_exp_neg_half_abs_scale :
    Integrable fun x : ℝ => Real.exp (-(1 / 2 * |x|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
    8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

/-- `G_k(ξ)² ≤ A_k e^{-|ξ|/2}`. -/
theorem boseDiffWeight_sq_le (k : ℕ) (ξ : ℝ) :
    boseDiffWeight k ξ ^ 2 ≤
      (18 * Real.sqrt (2 * Real.pi)) ^ 2 * ((2 * k + 2).factorial * Real.exp (1 + k)) *
        Real.exp (-(1 / 2 * |ξ|)) := by
  set K := 18 * Real.sqrt (2 * Real.pi) with hK
  set t : ℝ := 2 * Real.pi * |ξ| with ht
  have ht0 : 0 ≤ t := by positivity
  have hG : ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ≤
      K * (1 + t) * Real.exp (-(Real.pi / 2 * t)) := by
    have h := norm_Gamma_mul_zeta_half_le (-(2 * Real.pi * ξ))
    rw [← mellinLinePoint_eq] at h
    have habs : |-(2 * Real.pi * ξ)| = t := by
      rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rwa [habs] at h
  have hs : ‖mellinLinePoint ξ‖ ≤ 1 + t := norm_mellinLinePoint_le ξ
  have hprod : ∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i) ≤ (1 + t + k) ^ k := by
    calc ∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i) ≤ ∏ _i ∈ range k, (1 + t + k) := by
          refine prod_le_prod (fun i _ => by positivity) fun i hi => ?_
          have : (i : ℝ) ≤ k := by exact_mod_cast (mem_range.mp hi).le
          linarith
      _ = (1 + t + k) ^ k := by rw [prod_const, card_range]
  have hW : boseDiffWeight k ξ ≤ K * (1 + t + k) ^ (k + 1) * Real.exp (-(Real.pi / 2 * t)) := by
    unfold boseDiffWeight
    have h1 : (1 + t) ≤ 1 + t + k := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
          ∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i)
        ≤ (K * (1 + t) * Real.exp (-(Real.pi / 2 * t))) * (1 + t + k) ^ k :=
          mul_le_mul hG hprod (prod_nonneg fun i _ => by positivity) (by positivity)
      _ ≤ (K * (1 + t + k) * Real.exp (-(Real.pi / 2 * t))) * (1 + t + k) ^ k := by
          gcongr
      _ = K * (1 + t + k) ^ (k + 1) * Real.exp (-(Real.pi / 2 * t)) := by ring
  have hW0 : 0 ≤ boseDiffWeight k ξ := by unfold boseDiffWeight; positivity
  have hfact : (1 + t + k) ^ (2 * k + 2) ≤ (2 * k + 2).factorial * Real.exp (1 + t + k) := by
    have h := Real.pow_div_factorial_le_exp (1 + t + k) (by positivity) (2 * k + 2)
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hexp : Real.exp (1 + t + k) * Real.exp (-(Real.pi / 2 * t)) ^ 2 ≤
      Real.exp (1 + k) * Real.exp (-(1 / 2 * |ξ|)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hpi : (1 : ℝ) / 2 ≤ (Real.pi - 1) * (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
    have : 1 / 2 * |ξ| ≤ (Real.pi - 1) * t := by
      rw [ht]; nlinarith [abs_nonneg ξ, Real.pi_gt_three]
    push_cast
    nlinarith
  calc boseDiffWeight k ξ ^ 2
      ≤ (K * (1 + t + k) ^ (k + 1) * Real.exp (-(Real.pi / 2 * t))) ^ 2 :=
        pow_le_pow_left₀ hW0 hW 2
    _ = K ^ 2 * ((1 + t + k) ^ (2 * k + 2) * Real.exp (-(Real.pi / 2 * t)) ^ 2) := by ring
    _ ≤ K ^ 2 * (((2 * k + 2).factorial * Real.exp (1 + t + k)) *
          Real.exp (-(Real.pi / 2 * t)) ^ 2) := by gcongr
    _ = K ^ 2 * ((2 * k + 2).factorial *
          (Real.exp (1 + t + k) * Real.exp (-(Real.pi / 2 * t)) ^ 2)) := by ring
    _ ≤ K ^ 2 * ((2 * k + 2).factorial * (Real.exp (1 + k) * Real.exp (-(1 / 2 * |ξ|)))) := by
        gcongr
    _ = K ^ 2 * ((2 * k + 2).factorial * Real.exp (1 + k)) * Real.exp (-(1 / 2 * |ξ|)) := by
        ring

theorem memLp_boseDiffWeight (k : ℕ) : MemLp (boseDiffWeight k) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_boseDiffWeight k).aestronglyMeasurable]
  refine (integrable_exp_neg_half_abs_scale.const_mul
      ((18 * Real.sqrt (2 * Real.pi)) ^ 2 * ((2 * k + 2).factorial * Real.exp (1 + k)))).mono'
    ((continuous_boseDiffWeight k).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
  exact boseDiffWeight_sq_le k ξ

/-- **Dilation differences of Bose dilates are small.**
`‖Σ_j (−1)^{k−j} C(k,j) β_{n+1+j}‖ ≤ C_k (n+1)^{-k-1/2}`, with `C_k = ‖G_k‖_{L²}`. -/
theorem norm_boseDilateDiff_le (k n : ℕ) :
    ‖boseDilateDiff k n‖ ≤
      (eLpNorm (boseDiffWeight k) 2 volume).toReal * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k) := by
  set c : ℝ := ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k) with hc
  have hc0 : 0 ≤ c := by positivity
  rw [← (halfLineMellinUnitary).norm_map, Lp.norm_def]
  have hbound : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ‖(halfLineMellinUnitary (boseDilateDiff k n) : ℝ → ℂ) ξ‖ ≤ ‖(c • boseDiffWeight k) ξ‖ := by
    filter_upwards [halfLineMellinUnitary_boseDilateDiff k n] with ξ hξ
    rw [hξ, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc0 (by unfold boseDiffWeight; positivity)), norm_mul, norm_neg]
    have hre : 0 ≤ (mellinLinePoint ξ).re := by rw [mellinLinePoint_re]; norm_num
    have hd := norm_fwdDiff_iter_cpowNeg_le k (mellinLinePoint ξ) hre ((n : ℝ) + 1) (by positivity)
    rw [mellinLinePoint_re] at hd
    unfold boseDiffWeight
    calc ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
          ‖(fwdDiff (1 : ℝ))^[k] (cpowNeg (mellinLinePoint ξ)) ((n : ℝ) + 1)‖
        ≤ ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
          ((∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i)) * c) :=
          mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = c * (‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
          ∏ i ∈ range k, (‖mellinLinePoint ξ‖ + i)) := by ring
  have hle := eLpNorm_mono_ae (p := 2) hbound
  rw [eLpNorm_const_smul] at hle
  have hfin : ‖c‖ₑ * eLpNorm (boseDiffWeight k) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (memLp_boseDiffWeight k).eLpNorm_ne_top
  calc (eLpNorm (halfLineMellinUnitary (boseDilateDiff k n) : ℝ → ℂ) 2 volume).toReal
      ≤ (‖c‖ₑ * eLpNorm (boseDiffWeight k) 2 volume).toReal := ENNReal.toReal_mono hfin hle
    _ = (eLpNorm (boseDiffWeight k) 2 volume).toReal * c := by
        rw [ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs,
          abs_of_nonneg hc0, mul_comm]

/-- **No Möbius rigidity beyond the resolved window.** For every `k` there is `C_k` with
`‖Σ_j (−1)^{k−j} C(k,j) β_{n+1+j}‖ ≤ C_k (n+1)^{-k-1/2}` for all `n`. -/
theorem exists_norm_boseDilateDiff_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖boseDilateDiff k n‖ ≤ C * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k) :=
  ⟨_, ENNReal.toReal_nonneg, norm_boseDilateDiff_le k⟩

/-! ## The explicit constant and the logarithmic scale law -/

private theorem exp_neg_half_abs_le_inv_one_add_sq (x : ℝ) :
    Real.exp (-(1 / 2 * |x|)) ≤ 8 * (1 + x ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
    8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

private theorem integral_exp_neg_half_abs_le :
    ∫ x : ℝ, Real.exp (-(1 / 2 * |x|)) ≤ 8 * Real.pi := by
  calc ∫ x : ℝ, Real.exp (-(1 / 2 * |x|)) ≤ ∫ x : ℝ, 8 * (1 + x ^ 2)⁻¹ :=
        integral_mono integrable_exp_neg_half_abs_scale (integrable_inv_one_add_sq.const_mul 8)
          exp_neg_half_abs_le_inv_one_add_sq
    _ = 8 * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- The constant `A_k = (18√(2π))² (2k+2)! e^{1+k}` of `G_k² ≤ A_k e^{-|ξ|/2}`. -/
noncomputable def boseDiffConst (k : ℕ) : ℝ :=
  (18 * Real.sqrt (2 * Real.pi)) ^ 2 * ((2 * k + 2).factorial * Real.exp (1 + k))

theorem boseDiffConst_nonneg (k : ℕ) : 0 ≤ boseDiffConst k := by
  unfold boseDiffConst; positivity

/-- `C_k = ‖G_k‖_{L²} ≤ √(8π A_k)`. -/
theorem toReal_eLpNorm_boseDiffWeight_le (k : ℕ) :
    (eLpNorm (boseDiffWeight k) 2 volume).toReal ≤ Real.sqrt (8 * Real.pi * boseDiffConst k) := by
  rw [(memLp_boseDiffWeight k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  have hsq : ∀ a : ℝ, ‖boseDiffWeight k a‖ ^ (2 : ℝ) = boseDiffWeight k a ^ 2 := by
    intro a
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp only [hsq]
  calc ∫ a : ℝ, boseDiffWeight k a ^ 2
      ≤ ∫ a : ℝ, boseDiffConst k * Real.exp (-(1 / 2 * |a|)) :=
        integral_mono ((memLp_two_iff_integrable_sq_norm
            (continuous_boseDiffWeight k).aestronglyMeasurable).mp (memLp_boseDiffWeight k)
            |>.congr (Eventually.of_forall fun a => by simp [Real.norm_eq_abs, sq_abs]))
          (integrable_exp_neg_half_abs_scale.const_mul _) (boseDiffWeight_sq_le k)
    _ = boseDiffConst k * ∫ a : ℝ, Real.exp (-(1 / 2 * |a|)) := integral_const_mul _ _
    _ ≤ boseDiffConst k * (8 * Real.pi) :=
        mul_le_mul_of_nonneg_left integral_exp_neg_half_abs_le (boseDiffConst_nonneg k)
    _ = 8 * Real.pi * boseDiffConst k := by ring

/-- **Explicit dilation-difference bound.** -/
theorem norm_boseDilateDiff_le_explicit (k n : ℕ) :
    ‖boseDilateDiff k n‖ ≤
      Real.sqrt (8 * Real.pi * boseDiffConst k) * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k) :=
  (norm_boseDilateDiff_le k n).trans
    (mul_le_mul_of_nonneg_right (toReal_eLpNorm_boseDiffWeight_le k) (by positivity))

/-- `√(8π A_k) (n+1)^{-1/2-k} ≤ √(8π) · 18√(2π) · e^{-k}` once `n + 1 ≥ e³ (2k+2)`. -/
theorem norm_boseDilateDiff_le_exp (k n : ℕ)
    (hn : Real.exp 3 * (2 * k + 2) ≤ (n : ℝ) + 1) :
    ‖boseDilateDiff k n‖ ≤
      Real.sqrt (8 * Real.pi) * (18 * Real.sqrt (2 * Real.pi)) * Real.exp (-(k : ℝ)) := by
  refine (norm_boseDilateDiff_le_explicit k n).trans ?_
  set K : ℝ := 18 * Real.sqrt (2 * Real.pi) with hK
  set m : ℝ := 2 * k + 2 with hm
  have hm0 : 0 < m := by positivity
  have hK0 : 0 ≤ K := by positivity
  -- `√(8π A_k) ≤ √(8π) K m^{k+1} e^{(k+1)/2}`
  have hfact : ((2 * k + 2).factorial : ℝ) ≤ m ^ (2 * k + 2) := by
    rw [hm]
    exact_mod_cast Nat.factorial_le_pow (2 * k + 2)
  have hA : Real.sqrt (8 * Real.pi * boseDiffConst k) ≤
      Real.sqrt (8 * Real.pi) * (K * (m ^ (k + 1) * Real.exp ((1 + k) / 2))) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ K * (m ^ (k + 1) * Real.exp ((1 + k) / 2))),
      ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    unfold boseDiffConst
    rw [← hK]
    have he : Real.exp (1 + k) = Real.exp ((1 + k) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hpow : (m ^ (k + 1)) ^ 2 = m ^ (2 * k + 2) := by rw [← pow_mul]; ring_nf
    rw [he]
    have : K ^ 2 * (((2 * k + 2).factorial : ℝ) * Real.exp ((1 + k) / 2) ^ 2) ≤
        K ^ 2 * (m ^ (2 * k + 2) * Real.exp ((1 + k) / 2) ^ 2) := by gcongr
    calc 8 * Real.pi * (K ^ 2 * (((2 * k + 2).factorial : ℝ) * Real.exp ((1 + k) / 2) ^ 2))
        ≤ 8 * Real.pi * (K ^ 2 * (m ^ (2 * k + 2) * Real.exp ((1 + k) / 2) ^ 2)) := by gcongr
      _ = 8 * Real.pi * (K * (m ^ (k + 1) * Real.exp ((1 + k) / 2))) ^ 2 := by
        rw [← hpow]; ring
  -- `(n+1)^{-1/2-k} ≤ (e³ m)^{-1/2-k}`
  have hN0 : 0 < Real.exp 3 * m := by positivity
  have hN : ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k) ≤ (Real.exp 3 * m) ^ (-(1 / 2 : ℝ) - k) :=
    Real.rpow_le_rpow_of_nonpos hN0 hn (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hsplit : (Real.exp 3 * m) ^ (-(1 / 2 : ℝ) - k) =
      Real.exp (-(3 / 2) - 3 * k) * m ^ (-(1 / 2 : ℝ) - k) := by
    rw [Real.mul_rpow (Real.exp_pos 3).le hm0.le, ← Real.exp_mul]; congr 2; ring
  -- `m^{k+1} · m^{-1/2-k} = √m ≤ √2 e^{k}`
  have hmpow : m ^ (k + 1) * m ^ (-(1 / 2 : ℝ) - k) = Real.sqrt m := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0, Real.sqrt_eq_rpow]
    congr 1; push_cast; ring
  have hsqrtm : Real.sqrt m ≤ Real.sqrt 2 * Real.exp k := by
    rw [← Real.sqrt_sq (Real.exp_pos (k : ℝ)).le, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have h1 := Real.add_one_le_exp (2 * (k : ℝ))
    rw [← Real.exp_nat_mul] at *
    have h2 : Real.exp (2 * (k : ℝ)) = Real.exp ((2 : ℕ) * (k : ℝ)) := by norm_num
    rw [hm]; push_cast at h1 ⊢; nlinarith [Real.exp_pos (2 * (k : ℝ))]
  calc Real.sqrt (8 * Real.pi * boseDiffConst k) * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ) - k)
      ≤ (Real.sqrt (8 * Real.pi) * (K * (m ^ (k + 1) * Real.exp ((1 + k) / 2)))) *
          (Real.exp (-(3 / 2) - 3 * k) * m ^ (-(1 / 2 : ℝ) - k)) := by
        rw [← hsplit]; gcongr
    _ = Real.sqrt (8 * Real.pi) * K * (m ^ (k + 1) * m ^ (-(1 / 2 : ℝ) - k)) *
          (Real.exp ((1 + k) / 2) * Real.exp (-(3 / 2) - 3 * k)) := by ring
    _ ≤ Real.sqrt (8 * Real.pi) * K * (Real.sqrt 2 * Real.exp k) *
          (Real.exp ((1 + k) / 2) * Real.exp (-(3 / 2) - 3 * k)) := by
        rw [hmpow]; gcongr
    _ = Real.sqrt (8 * Real.pi) * K * (Real.sqrt 2 * Real.exp (-1 - (3 / 2) * k)) := by
        rw [← Real.exp_add]; ring_nf; rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ Real.sqrt (8 * Real.pi) * K * Real.exp (-(k : ℝ)) := by
        gcongr
        have hs2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : Real.exp (-1 - 3 / 2 * k) * Real.exp 1 ≤ Real.exp (-(k : ℝ)) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        nlinarith [Real.exp_pos (-1 - 3 / 2 * (k : ℝ)), Real.sqrt_nonneg 2]

/-- **Logarithmic scale law.** There is `B > 0` such that for every `ε ∈ (0, B]` and every
index `n` with `n + 1 ≥ e³(2 log(B/ε) + 4)` some dilation difference based at `n + 1` has norm
at most `ε`.  So coefficients beyond `O(log 1/ε)` are not pinned at accuracy `ε`. -/
theorem exists_log_scale_dilation_freedom :
    ∃ B : ℝ, 0 < B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ B → ∀ n : ℕ,
      Real.exp 3 * (2 * Real.log (B / ε) + 4) ≤ (n : ℝ) + 1 →
        ∃ k : ℕ, ‖boseDilateDiff k n‖ ≤ ε := by
  set B : ℝ := Real.sqrt (8 * Real.pi) * (18 * Real.sqrt (2 * Real.pi)) with hB
  have hB0 : 0 < B := by positivity
  refine ⟨B, hB0, fun ε hε hεB n hn => ⟨⌈Real.log (B / ε)⌉₊, ?_⟩⟩
  set k := ⌈Real.log (B / ε)⌉₊ with hk
  have hlog0 : 0 ≤ Real.log (B / ε) := Real.log_nonneg ((one_le_div hε).mpr hεB)
  have hk1 : (k : ℝ) < Real.log (B / ε) + 1 := Nat.ceil_lt_add_one hlog0
  have hkge : Real.log (B / ε) ≤ k := Nat.le_ceil _
  have hn' : Real.exp 3 * (2 * k + 2) ≤ (n : ℝ) + 1 := by
    refine le_trans ?_ hn
    have h2 : 2 * (k : ℝ) + 2 ≤ 2 * Real.log (B / ε) + 4 := by linarith
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos 3).le
  refine (norm_boseDilateDiff_le_exp k n hn').trans ?_
  rw [← hB]
  have : Real.exp (-(k : ℝ)) ≤ ε / B := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (div_pos hε hB0), inv_div]
    calc B / ε = Real.exp (Real.log (B / ε)) := (Real.exp_log (div_pos hB0 hε)).symm
      _ ≤ Real.exp k := Real.exp_le_exp.mpr hkge
  calc B * Real.exp (-(k : ℝ)) ≤ B * (ε / B) := mul_le_mul_of_nonneg_left this hB0.le
    _ = ε := by field_simp

end RHTower
