import GaloisForLFunctions.RHTower.XiWardGlobalCapAndFiniteHeadArithmetic
import GaloisForLFunctions.RHTower.XiSliceGaussianTailHeightBounds
import GaloisForLFunctions.RHTower.XiSliceHeatGaussianSharpThreshold
import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.HTGeometry.GaussianPolynomialScaledTails
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial Mehler Transforms, Exact Head–Tail Cumulant Splitting, Subconvexity-Free RvM Tail Asymptotics, and Multi-Pair Threshold Escalation

This file couples the exact polynomial Mehler heat identity with the horizontal Xi-slice
head–tail factorization, establishes exact additive cumulant splitting for `sliceTruncPoly`,
computes the asymptotic leading constants and uniform remainders of the distant tail cumulants
`xiSliceGaussianTailMass`, `(xiSliceGaussianTailQuadratic).re`, and `xiSliceGaussianTailFourth`
by discrete summation by parts against `N(T) - M(T) = O(log T)` (without subconvexity or
logarithmic-derivative bounds), and proves multi-pair Mehler threshold escalation beyond the
single-pair `1/4` threshold and the `1/3` vacuum barrier.

## Main results

1. **General polynomial Mehler transform and exact full-slice Mehler heat bracket**
   (`integrable_and_integral_gaussDensity_poly`,
   `integrable_and_integral_gaussDensity_mul_exp_sq_poly`,
   `integrable_and_mehler_bracket_xiSliceProduct`):
   For every real polynomial `P : ℝ[X]`, heat `lam > 0`, and quadratic tilt `a` with `2 a lam < 1`,
   `∫ gaussDensity (lam/2) u * (P(x+u) exp(a(x+u)²)) du` equals the closed-form Mehler transform
   `σ^{-1/2} exp((a/σ) x²) (forwardPolyHeat (lam/(2σ)) P)(x/σ)` with `σ = 1 - 2 a lam`.
   Applied to `xiSliceGaussianFiniteHeadRealPoly t R` (`R ≥ 4`), this yields an unconditional
   two-sided closed-form Mehler heat bracket for the heated real Xi slice at every height `t ∈ ℝ`.
2. **Exact cumulant additivity and head–tail cumulant splitting of `sliceTruncPoly`**
   (`coeff_one_sliceTruncPoly`, `polySecondCumulant_sliceTruncPoly`,
   `coeff_one_sliceTruncPoly_eq_head_add_sdiff`,
   `polySecondCumulant_sliceTruncPoly_eq_head_add_sdiff`):
   At every real height `t ∈ ℝ` (including real zeros of `Ξ`), the first two polynomial cumulants
   `P.coeff 1` and `P.coeff 1 ^ 2 - 2 * P.coeff 2` of `sliceTruncPoly t S` equal the exact spectral
   sums `∑ (xiSliceGaussianReciprocal t q).re` and `∑ ((xiSliceGaussianReciprocal t q) ^ 2).re` over
   `sliceTrunc S`, split additively across `sliceTruncPoly t H * sliceTruncPoly t (S \ H)`, and
   satisfy uniform bounds by `xiSliceGaussianTailMass` and `xiSliceGaussianTailFourth`.
3. **Subconvexity-free Riemann–von Mangoldt summation-by-parts cumulant asymptotics**
   (`exists_xiSliceGaussianTail_cumulant_asymptotics`):
   Using only `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder` and discrete Abel summation on
   paired upper/lower ordinate bins around `t`, uniformly for `T₁ ≤ t`, `8 ≤ R`, and `8 R ≤ t`:
   * `|xiSliceGaussianTailMass t H - log(t/(2π)) / (π R)| ≤ C₁ (log t / R² + log t / t)`,
   * `|(xiSliceGaussianTailQuadratic t H).re - log(t/(2π)) / (π R)| ≤ C₁ (log t / R² + log t / t)`,
   * `|xiSliceGaussianTailFourth t H - log(t/(2π)) / (3π R³)| ≤ C₁ (log t / R⁴ + log t / (t² R))`.
4. **Multi-pair Mehler threshold escalation (`1/4 → 16/57 → 4/11`)**
   (`deriv_deriv_gaussianMultiPairHeat_two_neg`,
   `exists_dense_gaussianMultiPairHeat_two_deriv2_neg`,
   `exists_multiplicity_deriv_deriv_gaussianMultiPairHeat_neg`,
   `exists_dense_multiPair_gaussianMultiPairHeat_deriv2_neg`):
   Via Stein's Gaussian identity, the origin curvature of the `m`-pair Gaussian model
   `(x² - δ²)^{2m} exp(a x²)` under heat `lam` is already negative at `m = 2` for all
   `0 < a lam < 16/57` (`16/57 > 1/4`), and for large `m` at `δ = √((3/2) m lam / (1 - 2 a lam))`
   is negative for every `0 < a lam < 4/11` (`4/11 > 1/3`), showing that scalar Gaussian tail
   replacement fails even above the `1/3` vacuum threshold unless the finite head is kept exact.
-/

open Complex Filter Topology MeasureTheory Set Polynomial
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## 1. General polynomial Mehler transform and exact full-slice Mehler heat bracket -/

/-- Taylor expansion of a real polynomial `P` around `c` evaluated at `c + v`. -/
theorem eval_add_eq_sum_taylor (P : ℝ[X]) (c v : ℝ) :
    P.eval (c + v) =
      ∑ j ∈ Finset.range (P.natDegree + 1), (hasseDeriv j P).eval c * v ^ j := by
  rw [show c + v = v + c by ring, ← taylor_eval, eval_eq_sum_range' (n := P.natDegree + 1)
    (by rw [natDegree_taylor]; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylor_coeff]

/-- Real Gaussian convolution of a polynomial `P(c + v)` against `gaussDensity s` (`s > 0`) equals
`(forwardPolyHeat s P).eval c`. -/
theorem integrable_and_integral_gaussDensity_poly {s : ℝ} (hs : 0 < s) (P : ℝ[X]) (c : ℝ) :
    Integrable (fun v : ℝ => gaussDensity s v * P.eval (c + v)) ∧
      ∫ v : ℝ, gaussDensity s v * P.eval (c + v) = (forwardPolyHeat s P).eval c := by
  set N := P.natDegree + 1
  have hexp : (fun v : ℝ => gaussDensity s v * P.eval (c + v)) =
      fun v => ∑ j ∈ Finset.range N,
        (hasseDeriv j P).eval c * (gaussDensity s v * v ^ j) := by
    funext v
    rw [eval_add_eq_sum_taylor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun v : ℝ => gaussDensity s v * P.eval (c + v)) := by
    rw [hexp]
    exact integrable_finset_sum _ fun j _ =>
      (DeBruijn.integrable_gaussDensity_mul_pow hs j).const_mul _
  refine ⟨hint, ?_⟩
  rw [hexp, integral_finset_sum _ (fun j _ =>
    (DeBruijn.integrable_gaussDensity_mul_pow hs j).const_mul _)]
  simp_rw [integral_const_mul]
  let f : ℕ → ℝ := fun j => (hasseDeriv j P).eval c * ∫ v : ℝ, gaussDensity s v * v ^ j
  have hc0 : ∀ j, N ≤ j → f j = 0 := by
    intro j hj
    dsimp only [f]
    rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ (by omega), eval_zero, zero_mul]
  have hext : ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range (2 * N), f j := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    exact hc0 j hj
  change ∑ j ∈ Finset.range N, f j = (forwardPolyHeat s P).eval c
  rw [hext, DeBruijn.sum_range_two_mul]
  unfold forwardPolyHeat
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hodd : f (2 * m + 1) = 0 := by
    dsimp only [f]
    rw [DeBruijn.integral_gaussDensity_mul_pow_odd s m, mul_zero]
  rw [hodd, add_zero]
  dsimp only [f]
  rw [DeBruijn.integral_gaussDensity_mul_pow_even hs m, eval_mul, eval_C]
  have hfac := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := 2 * m)) P
  rw [LinearMap.smul_apply] at hfac
  rw [← hfac, eval_smul, nsmul_eq_mul]
  have hf2 : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- Closed-form Mehler transform of `x ↦ P.eval x * exp(a x²)` at Gaussian heat `lam`:
`σ^{-1/2} exp((a/σ) x²) * (forwardPolyHeat (lam/(2σ)) P).eval (x/σ)` with
`σ = DeBruijn.gaussianModelScale a lam = 1 - 2 a lam`. -/
def mehlerPolyTransform (a lam : ℝ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  DeBruijn.gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
    Real.exp (a / DeBruijn.gaussianModelScale a lam * x ^ 2) *
      (forwardPolyHeat (lam / (2 * DeBruijn.gaussianModelScale a lam)) P).eval
        (x / DeBruijn.gaussianModelScale a lam)

theorem mehlerPolyTransform_C_mul (a lam c : ℝ) (P : ℝ[X]) (x : ℝ) :
    mehlerPolyTransform a lam (C c * P) x = c * mehlerPolyTransform a lam P x := by
  unfold mehlerPolyTransform
  rw [forwardPolyHeat_C_mul, eval_mul, eval_C]
  ring

theorem mehlerPolyTransform_add (a lam : ℝ) (P Q : ℝ[X]) (x : ℝ) :
    mehlerPolyTransform a lam (P + Q) x =
      mehlerPolyTransform a lam P x + mehlerPolyTransform a lam Q x := by
  unfold mehlerPolyTransform
  rw [forwardPolyHeat_add, eval_add]
  ring

/-- **General polynomial Mehler identity.**
For `lam > 0`, `2 a lam < 1`, and any real polynomial `P : ℝ[X]`, `u ↦ g_{lam/2}(u) P(x+u) e^{a(x+u)²}`
is integrable and its integral equals `mehlerPolyTransform a lam P x`. -/
theorem integrable_and_integral_gaussDensity_mul_exp_sq_poly {a lam : ℝ}
    (hlam : 0 < lam) (hconv : 2 * a * lam < 1) (P : ℝ[X]) (x : ℝ) :
    Integrable (fun u : ℝ =>
      gaussDensity (lam / 2) u * (P.eval (x + u) * Real.exp (a * (x + u) ^ 2))) ∧
      ∫ u : ℝ, gaussDensity (lam / 2) u * (P.eval (x + u) * Real.exp (a * (x + u) ^ 2)) =
        mehlerPolyTransform a lam P x := by
  have hm := DeBruijn.gaussianModelScale_pos hconv
  have hs : 0 < lam / (2 * DeBruijn.gaussianModelScale a lam) :=
    div_pos hlam (mul_pos zero_lt_two hm)
  obtain ⟨hi, hv⟩ := integrable_and_integral_gaussDensity_poly hs P
    (x / DeBruijn.gaussianModelScale a lam)
  have harg (u : ℝ) : x + u = x / DeBruijn.gaussianModelScale a lam +
      (u - 2 * a * lam * x / DeBruijn.gaussianModelScale a lam) := by
    field_simp [hm.ne']
    dsimp only [DeBruijn.gaussianModelScale]
    ring
  have hs_eq : (lam / DeBruijn.gaussianModelScale a lam) / 2 =
      lam / (2 * DeBruijn.gaussianModelScale a lam) := by ring
  have hf : (fun u : ℝ =>
      gaussDensity (lam / 2) u * (P.eval (x + u) * Real.exp (a * (x + u) ^ 2))) =
      fun u => (DeBruijn.gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        Real.exp (a / DeBruijn.gaussianModelScale a lam * x ^ 2)) *
          ((fun v => gaussDensity (lam / (2 * DeBruijn.gaussianModelScale a lam)) v *
            P.eval (x / DeBruijn.gaussianModelScale a lam + v))
              (u - 2 * a * lam * x / DeBruijn.gaussianModelScale a lam)) := by
    funext u
    rw [mul_comm (P.eval (x + u)), ← mul_assoc,
      DeBruijn.gaussDensity_mul_exp_sq_mehler hlam hconv x u, hs_eq, harg u]
    ring
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact (hi.comp_sub_right _).const_mul _
  · rw [hf, integral_const_mul, integral_sub_right_eq_self
      (fun v : ℝ => gaussDensity (lam / (2 * DeBruijn.gaussianModelScale a lam)) v *
        P.eval (x / DeBruijn.gaussianModelScale a lam + v)), hv]
    rfl

/-- Coefficientwise real part of a complex polynomial `Q : ℂ[X]`. -/
def complexPolyRe (Q : ℂ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (Q.natDegree + 1), C (Q.coeff k).re * X ^ k

/-- Evaluating `complexPolyRe Q` at a real point `x` recovers `(Q.eval (x : ℂ)).re`. -/
theorem eval_complexPolyRe (Q : ℂ[X]) (x : ℝ) :
    (complexPolyRe Q).eval x = (Q.eval (x : ℂ)).re := by
  unfold complexPolyRe
  rw [eval_finset_sum, Q.eval_eq_sum_range, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, ← Complex.ofReal_pow]
  simp [Complex.mul_re]

/-- Complex polynomial representing `xiSliceGaussianFiniteHead t R`. -/
def xiSliceGaussianFiniteHeadComplexPoly (t R : ℝ) : ℂ[X] :=
  C (xiSliceGaussianFiniteHeadScalar t R) *
    ∏ q ∈ xiSliceGaussianRadiusHead t R, (X ^ 2 + C ((xiSpectralPoint q - (t : ℂ)) ^ 2))

theorem eval_xiSliceGaussianFiniteHeadComplexPoly (t R : ℝ) (z : ℂ) :
    (xiSliceGaussianFiniteHeadComplexPoly t R).eval z = xiSliceGaussianFiniteHead t R z := by
  unfold xiSliceGaussianFiniteHeadComplexPoly xiSliceGaussianFiniteHead
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  simp

/-- Real polynomial whose evaluation on `ℝ` equals `(xiSliceGaussianFiniteHead t R (x : ℂ)).re` for
every `t, R ∈ ℝ` (without any nonvanishing hypothesis on `Ξ(t)`). -/
def xiSliceGaussianFiniteHeadRealPoly (t R : ℝ) : ℝ[X] :=
  complexPolyRe (xiSliceGaussianFiniteHeadComplexPoly t R)

theorem eval_xiSliceGaussianFiniteHeadRealPoly (t R x : ℝ) :
    (xiSliceGaussianFiniteHeadRealPoly t R).eval x =
      (xiSliceGaussianFiniteHead t R (x : ℂ)).re := by
  unfold xiSliceGaussianFiniteHeadRealPoly
  rw [eval_complexPolyRe, eval_xiSliceGaussianFiniteHeadComplexPoly]

theorem eval_xiSliceGaussianFiniteHeadRealPoly_nonneg (t R x : ℝ) :
    0 ≤ (xiSliceGaussianFiniteHeadRealPoly t R).eval x := by
  rw [eval_xiSliceGaussianFiniteHeadRealPoly]
  exact xiSliceGaussianFiniteHead_ofReal_re_nonneg t R x

/-- When `Ξ(t) ≠ 0` and `R ≥ 0`, `xiSliceGaussianFiniteHeadRealPoly t R` coincides with
`C (XiC t ^ 2).re * expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))`. -/
theorem xiSliceGaussianFiniteHeadRealPoly_eq_of_XiC_ne_zero {t R : ℝ} (ht : XiC t ≠ 0)
    (hR : 0 ≤ R) :
    xiSliceGaussianFiniteHeadRealPoly t R =
      C (XiC t ^ 2).re * expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)) := by
  apply Polynomial.funext
  intro x
  rw [eval_xiSliceGaussianFiniteHeadRealPoly, eval_mul, eval_C, expand_eval]
  have hhead := xiSliceGaussianFiniteHead_eq_XiC_sq_mul_eval_sliceTruncPoly ht hR (x : ℂ)
  have h0 := xiSliceGaussianFiniteHead_eq_XiC_sq_mul_eval_sliceTruncPoly ht hR 0
  have him0 : (XiC t ^ 2).im = 0 := by
    have h0' := xiSliceGaussianFiniteHead_ofReal_im_eq_zero t R 0
    rw [Complex.ofReal_zero, h0, zero_pow (by decide : 2 ≠ 0), eval_map_algebraMap,
      show algebraMap ℝ ℂ 0 = (0 : ℂ) by simp] at h0'
    have hev0 : aeval (0 : ℂ) (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)) = 1 := by
      rw [aeval_def, ← eval_map,
        show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, eval_map_algebraMap]
      simp [eval_zero_sliceTruncPoly]
    rw [hev0, mul_one] at h0'
    exact h0'
  have hevx : ((sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).map
      (algebraMap ℝ ℂ)).eval ((x : ℂ) ^ 2) =
      (((sliceTruncPoly t (xiSliceGaussianRadiusHead t R)).eval (x ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, eval_map_algebraMap]
    rfl
  rw [hhead, hevx]
  simp [Complex.mul_re, him0]

/-- On the real axis, `(xiSliceProduct t x).re ≥ 0` for all `t, x ∈ ℝ`. -/
theorem xiSliceProduct_ofReal_re_nonneg (t x : ℝ) :
    0 ≤ (xiSliceProduct t (x : ℂ)).re := by
  have hprod := congrArg Complex.re
    (xiSliceProduct_eq_gaussianFiniteHead_mul_tail t (R := 4) (by norm_num) (x : ℂ))
  rw [xiSliceGaussianFiniteHead_ofReal_eq_re,
    xiSliceGaussianTail_real_eq_norm t (by norm_num : (4 : ℝ) ≤ 4) x,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hprod
  rw [hprod]
  exact mul_nonneg (xiSliceGaussianFiniteHead_ofReal_re_nonneg t 4 x) (norm_nonneg _)

/-- **Exact two-sided closed-form Mehler heat bracket for the horizontal Xi slice.**
For every height `t ∈ ℝ`, cutoff `R ≥ 4`, and heat `lam > 0` with `2 a lam < 1`
(where `a = (xiSliceGaussianTailQuadratic t H).re`, `B = xiSliceGaussianTailFourth t H`, and
`P = xiSliceGaussianFiniteHeadRealPoly t R`), the Gaussian heat convolution of `(xiSliceProduct t).re`
is integrable and sandwiched on all of `ℝ` between two exact `mehlerPolyTransform` evaluations. -/
theorem integrable_and_mehler_bracket_xiSliceProduct (t : ℝ) {R lam : ℝ} (hR : 4 ≤ R)
    (hlam : 0 < lam)
    (hconv : 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re * lam < 1)
    (x : ℝ) :
    let H := xiSliceGaussianRadiusHead t R
    let a := (xiSliceGaussianTailQuadratic t H).re
    let B := xiSliceGaussianTailFourth t H
    let P := xiSliceGaussianFiniteHeadRealPoly t R
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * (xiSliceProduct t ((x + u : ℝ) : ℂ)).re) ∧
      mehlerPolyTransform a lam P x - B * mehlerPolyTransform a lam (X ^ 4 * P) x ≤
        ∫ u : ℝ, gaussDensity (lam / 2) u * (xiSliceProduct t ((x + u : ℝ) : ℂ)).re ∧
      ∫ u : ℝ, gaussDensity (lam / 2) u * (xiSliceProduct t ((x + u : ℝ) : ℂ)).re ≤
        mehlerPolyTransform a lam P x := by
  dsimp only
  set H := xiSliceGaussianRadiusHead t R
  set a := (xiSliceGaussianTailQuadratic t H).re
  set B := xiSliceGaussianTailFourth t H
  set P := xiSliceGaussianFiniteHeadRealPoly t R
  obtain ⟨hiP, hvP⟩ := integrable_and_integral_gaussDensity_mul_exp_sq_poly hlam hconv P x
  obtain ⟨hi4, hv4⟩ := integrable_and_integral_gaussDensity_mul_exp_sq_poly hlam hconv (X ^ 4 * P) x
  have hcont : Continuous (fun u : ℝ =>
      gaussDensity (lam / 2) u * (xiSliceProduct t ((x + u : ℝ) : ℂ)).re) := by
    refine Continuous.mul ?_ ?_
    · unfold gaussDensity
      fun_prop
    · exact Complex.continuous_re.comp
        ((differentiable_xiSliceProduct t).continuous.comp
          (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)))
  have hg0 : ∀ u : ℝ, 0 ≤ gaussDensity (lam / 2) u := fun u => by
    unfold gaussDensity; positivity
  have hpt : ∀ u : ℝ,
      0 ≤ (xiSliceProduct t ((x + u : ℝ) : ℂ)).re ∧
      (xiSliceProduct t ((x + u : ℝ) : ℂ)).re ≤ P.eval (x + u) * Real.exp (a * (x + u) ^ 2) ∧
      P.eval (x + u) * Real.exp (a * (x + u) ^ 2) -
        B * ((X ^ 4 * P).eval (x + u) * Real.exp (a * (x + u) ^ 2)) ≤
          (xiSliceProduct t ((x + u : ℝ) : ℂ)).re := by
    intro u
    have hbr := xiSliceProduct_real_gaussian_bracket t hR (x + u)
    dsimp only at hbr
    have hev : P.eval (x + u) = (xiSliceGaussianFiniteHead t R ((x + u : ℝ) : ℂ)).re :=
      eval_xiSliceGaussianFiniteHeadRealPoly t R (x + u)
    have hev4 : (X ^ 4 * P).eval (x + u) = (x + u) ^ 4 * P.eval (x + u) := by simp
    refine ⟨xiSliceProduct_ofReal_re_nonneg t (x + u), ?_, ?_⟩
    · rw [hev]; linarith [hbr.1]
    · rw [hev4, hev]
      linarith [hbr.2]
  have hint_slice : Integrable (fun u : ℝ =>
      gaussDensity (lam / 2) u * (xiSliceProduct t ((x + u : ℝ) : ℂ)).re) := by
    refine hiP.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hg0 u) (hpt u).1)]
    exact mul_le_mul_of_nonneg_left (hpt u).2.1 (hg0 u)
  refine ⟨hint_slice, ?_, ?_⟩
  · have hlow_int : Integrable (fun u : ℝ =>
        gaussDensity (lam / 2) u * (P.eval (x + u) * Real.exp (a * (x + u) ^ 2)) -
          B * (gaussDensity (lam / 2) u *
            ((X ^ 4 * P).eval (x + u) * Real.exp (a * (x + u) ^ 2)))) :=
      hiP.sub (hi4.const_mul B)
    have hle := integral_mono hlow_int hint_slice fun u => by
      have := mul_le_mul_of_nonneg_left (hpt u).2.2 (hg0 u)
      linarith
    rw [integral_sub hiP (hi4.const_mul B), integral_const_mul, hvP, hv4] at hle
    exact hle
  · have hle := integral_mono hint_slice hiP fun u =>
      mul_le_mul_of_nonneg_left (hpt u).2.1 (hg0 u)
    rwa [hvP] at hle

/-! ## 2. Exact cumulant additivity and head–tail cumulant splitting of `sliceTruncPoly` -/

/-- The second logarithmic cumulant `e₁² - 2 e₂ = ∑ w_q²` of a polynomial `1 + e₁ y + e₂ y² + ⋯`. -/
def polySecondCumulant (P : ℝ[X]) : ℝ :=
  P.coeff 1 ^ 2 - 2 * P.coeff 2

theorem coeff_one_mul_of_coeff_zero_one {P Q : ℝ[X]} (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    (P * Q).coeff 1 = P.coeff 1 + Q.coeff 1 := by
  rw [polynomial_coeff_mul_one, hP, hQ]
  ring

theorem polySecondCumulant_mul_of_coeff_zero_one {P Q : ℝ[X]} (hP : P.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1) :
    polySecondCumulant (P * Q) = polySecondCumulant P + polySecondCumulant Q := by
  unfold polySecondCumulant
  rw [coeff_one_mul_of_coeff_zero_one hP hQ, polynomial_coeff_mul_two, hP, hQ]
  ring

theorem coeff_zero_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, (f i).coeff 0 = 1) :
    (∏ i ∈ s, f i).coeff 0 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero,
      ← coeff_zero_eq_eval_zero, hf a (Finset.mem_insert_self a s),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), mul_one]

theorem coeff_one_prod_of_coeff_zero_one {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, (f i).coeff 0 = 1) :
    (∏ i ∈ s, f i).coeff 1 = ∑ i ∈ s, (f i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      coeff_one_mul_of_coeff_zero_one (hf a (Finset.mem_insert_self a s))
        (coeff_zero_prod_eq_one s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem polySecondCumulant_prod_of_coeff_zero_one {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, (f i).coeff 0 = 1) :
    polySecondCumulant (∏ i ∈ s, f i) = ∑ i ∈ s, polySecondCumulant (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polySecondCumulant]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      polySecondCumulant_mul_of_coeff_zero_one (hf a (Finset.mem_insert_self a s))
        (coeff_zero_prod_eq_one s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Sums over a symmetric truncation `sliceTrunc S` pair every upper copy with its mirror. -/
theorem sum_sliceTrunc {M : Type*} [AddCommMonoid M] (f : XiZeroCopy → M)
    (S : Finset XiZeroCopy) :
    ∑ q ∈ sliceTrunc S, f q =
      (∑ q ∈ sliceTruncCrit S, f q) +
        ∑ q ∈ sliceTruncUp S, (f q + f (xiZeroCopyLineConjEquiv q)) := by
  classical
  have hd1 : Disjoint (sliceTruncCrit S) (sliceTruncUp S) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have h1' := (mem_sliceTruncCrit.mp h1).2
    have h2' := (mem_sliceTruncUp.mp h2).2
    unfold XiCopyCritical XiCopyUpper at *
    linarith
  have hd2 : Disjoint (sliceTruncCrit S ∪ sliceTruncUp S)
      ((sliceTruncUp S).map xiZeroCopyLineConjEquiv.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp h2
    have hup := (mem_sliceTruncUp.mp hr).2
    unfold XiCopyUpper at hup
    simp only [Equiv.coe_toEmbedding] at h1
    have him := im_xiSpectralPoint_lineConj r
    rcases Finset.mem_union.mp h1 with h | h
    · have hc := (mem_sliceTruncCrit.mp h).2
      unfold XiCopyCritical at hc
      linarith
    · have hu := (mem_sliceTruncUp.mp h).2
      unfold XiCopyUpper at hu
      linarith
  unfold sliceTrunc
  rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_map, add_assoc,
    ← Finset.sum_add_distrib]
  rfl

private theorem re_xiSliceGaussianReciprocal_of_critical (t : ℝ) {q : XiZeroCopy}
    (hq : XiCopyCritical q) :
    sliceAtom t q = (xiSliceGaussianReciprocal t q).re ∧
      sliceAtom t q ^ 2 = ((xiSliceGaussianReciprocal t q) ^ 2).re := by
  unfold XiCopyCritical at hq
  set d : ℝ := (xiSpectralPoint q).re - t
  have hz : xiSpectralPoint q - (t : ℂ) = (d : ℂ) :=
    Complex.ext (by simp [d]) (by simpa using hq)
  have hn : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 = d ^ 2 := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold sliceAtom xiSliceGaussianReciprocal
  rw [hn, hz, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  exact ⟨one_div _, by ring⟩

private theorem re_xiSliceGaussianReciprocal_pair_of_upper (t : ℝ) {q : XiZeroCopy}
    (hq : XiCopyUpper q) :
    2 * sliceAtom t q - 4 * sliceDefect t q =
      (xiSliceGaussianReciprocal t q).re +
        (xiSliceGaussianReciprocal t (xiZeroCopyLineConjEquiv q)).re ∧
    (2 * sliceAtom t q - 4 * sliceDefect t q) ^ 2 - 2 * sliceAtom t q ^ 2 =
      ((xiSliceGaussianReciprocal t q) ^ 2).re +
        ((xiSliceGaussianReciprocal t (xiZeroCopyLineConjEquiv q)) ^ 2).re := by
  unfold XiCopyUpper at hq
  set d : ℝ := (xiSpectralPoint q).re - t
  set e : ℝ := (xiSpectralPoint q).im
  have he : 0 < e := hq
  have hNpos : 0 < d ^ 2 + e ^ 2 := by positivity
  have hz : xiSpectralPoint q - (t : ℂ) = (d : ℂ) + (e : ℂ) * I := by
    apply Complex.ext <;> simp [d, e]
  have hzc : xiSpectralPoint (xiZeroCopyLineConjEquiv q) - (t : ℂ) =
      (d : ℂ) - (e : ℂ) * I := by
    rw [xiSpectralPoint_lineConj]
    apply Complex.ext <;> simp [d, e]
  have hN : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 = d ^ 2 + e ^ 2 := by
    rw [Complex.sq_norm, hz, Complex.normSq_apply]
    simp
    ring
  have hrec1 : xiSliceGaussianReciprocal t q =
      (((d ^ 2 - e ^ 2) / (d ^ 2 + e ^ 2) ^ 2 : ℝ) : ℂ) +
        ((-(2 * d * e) / (d ^ 2 + e ^ 2) ^ 2 : ℝ) : ℂ) * I := by
    unfold xiSliceGaussianReciprocal
    rw [hz]
    have hprod : ((d : ℂ) + (e : ℂ) * I) * ((d : ℂ) - (e : ℂ) * I) =
        ((d ^ 2 + e ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    have hne1 : (d : ℂ) + (e : ℂ) * I ≠ 0 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      linarith
    have hNc : ((d ^ 2 + e ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNpos.ne'
    have hinv : (((d : ℂ) + (e : ℂ) * I) ^ 2)⁻¹ =
        ((d : ℂ) - (e : ℂ) * I) ^ 2 / ((d ^ 2 + e ^ 2 : ℝ) : ℂ) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hNc), ← hprod, mul_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hne1)]
    rw [hinv]
    push_cast
    field_simp [hNc]
    ring_nf
    rw [I_sq]
    ring
  have hrec2 : xiSliceGaussianReciprocal t (xiZeroCopyLineConjEquiv q) =
      starRingEnd ℂ (xiSliceGaussianReciprocal t q) := by
    unfold xiSliceGaussianReciprocal
    rw [xiSpectralPoint_lineConj]
    have ht : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [← ht, ← map_sub, ← map_pow, ← map_inv₀]
  have hre1 : (xiSliceGaussianReciprocal t q).re = (d ^ 2 - e ^ 2) / (d ^ 2 + e ^ 2) ^ 2 := by
    rw [hrec1]; simp
  have him1 : (xiSliceGaussianReciprocal t q).im = -(2 * d * e) / (d ^ 2 + e ^ 2) ^ 2 := by
    rw [hrec1]; simp
  have hre_conj : ∀ w : ℂ, (starRingEnd ℂ w).re = w.re := Complex.conj_re
  have hsq_re : ∀ w : ℂ, (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := fun w => by
    rw [sq, Complex.mul_re]
    ring
  have hN4 : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 4 = (d ^ 2 + e ^ 2) ^ 2 := by
    calc ‖xiSpectralPoint q - (t : ℂ)‖ ^ 4 = (‖xiSpectralPoint q - (t : ℂ)‖ ^ 2) ^ 2 := by ring
      _ = (d ^ 2 + e ^ 2) ^ 2 := by rw [hN]
  unfold sliceAtom sliceDefect
  rw [hN, hN4, show (xiSpectralPoint q).im = e from rfl, hrec2, ← map_pow,
    hre_conj, hre_conj, hsq_re, hre1, him1]
  constructor
  · field_simp [hNpos.ne']
    ring
  · field_simp [hNpos.ne']
    ring

theorem coeff_zero_sliceTruncPoly (t : ℝ) (S : Finset XiZeroCopy) :
    (sliceTruncPoly t S).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_sliceTruncPoly]

/-- **Exact first polynomial cumulant of `sliceTruncPoly t S` at every height `t ∈ ℝ`.**
Without any nonvanishing hypothesis on `Ξ(t)`, `(sliceTruncPoly t S).coeff 1` equals the sum of
`(xiSliceGaussianReciprocal t q).re` over `sliceTrunc S`. -/
theorem coeff_one_sliceTruncPoly (t : ℝ) (S : Finset XiZeroCopy) :
    (sliceTruncPoly t S).coeff 1 =
      ∑ q ∈ sliceTrunc S, (xiSliceGaussianReciprocal t q).re := by
  have h0_lin : ∀ a : ℝ, (1 + C a * X : ℝ[X]).coeff 0 = 1 := fun a => by
    rw [coeff_zero_eq_eval_zero]; simp
  have h1_lin : ∀ a : ℝ, (1 + C a * X : ℝ[X]).coeff 1 = a := fun a => by
    rw [coeff_add, ← C_1, coeff_C, if_neg one_ne_zero, coeff_C_mul, coeff_X_one, mul_one, zero_add]
  have h0_quad : ∀ b c : ℝ, (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 0 = 1 := fun b c => by
    rw [coeff_zero_eq_eval_zero]; simp
  have h1_quad : ∀ b c : ℝ, (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 1 = b := fun b c => by
    rw [coeff_add, coeff_add, ← C_1, coeff_C, if_neg one_ne_zero, coeff_C_mul, coeff_X_one,
      coeff_C_mul, coeff_X_pow, if_neg (by decide : ¬ (1 : ℕ) = 2)]
    ring
  unfold sliceTruncPoly
  rw [coeff_one_mul_of_coeff_zero_one
      (coeff_zero_prod_eq_one _ _ fun q _ => h0_lin _)
      (coeff_zero_prod_eq_one _ _ fun q _ => by
        rw [DeBruijn.slicePairFactor_eq]; exact h0_quad _ _),
    coeff_one_prod_of_coeff_zero_one _ _ (fun q _ => h0_lin _),
    coeff_one_prod_of_coeff_zero_one _ _ (fun q _ => by
      rw [DeBruijn.slicePairFactor_eq]; exact h0_quad _ _),
    sum_sliceTrunc]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [h1_lin, (re_xiSliceGaussianReciprocal_of_critical t (mem_sliceTruncCrit.mp hq).2).1]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [DeBruijn.slicePairFactor_eq, h1_quad,
      (re_xiSliceGaussianReciprocal_pair_of_upper t (mem_sliceTruncUp.mp hq).2).1]

/-- **Exact second polynomial cumulant of `sliceTruncPoly t S` at every height `t ∈ ℝ`.**
Without any nonvanishing hypothesis on `Ξ(t)`, `polySecondCumulant (sliceTruncPoly t S)` equals the
sum of `((xiSliceGaussianReciprocal t q) ^ 2).re` over `sliceTrunc S`. -/
theorem polySecondCumulant_sliceTruncPoly (t : ℝ) (S : Finset XiZeroCopy) :
    polySecondCumulant (sliceTruncPoly t S) =
      ∑ q ∈ sliceTrunc S, ((xiSliceGaussianReciprocal t q) ^ 2).re := by
  have h0_lin : ∀ a : ℝ, (1 + C a * X : ℝ[X]).coeff 0 = 1 := fun a => by
    rw [coeff_zero_eq_eval_zero]; simp
  have h2_lin : ∀ a : ℝ, polySecondCumulant (1 + C a * X) = a ^ 2 := fun a => by
    unfold polySecondCumulant
    have h1 : (1 + C a * X : ℝ[X]).coeff 1 = a := by
      rw [coeff_add, ← C_1, coeff_C, if_neg one_ne_zero, coeff_C_mul, coeff_X_one, mul_one,
        zero_add]
    have h2 : (1 + C a * X : ℝ[X]).coeff 2 = 0 := by
      rw [coeff_add, ← C_1, coeff_C, if_neg (by decide), coeff_C_mul, coeff_X,
        if_neg (by decide : ¬ (1 : ℕ) = 2), mul_zero, add_zero]
    rw [h1, h2]; ring
  have h0_quad : ∀ b c : ℝ, (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 0 = 1 := fun b c => by
    rw [coeff_zero_eq_eval_zero]; simp
  have h2_quad : ∀ b c : ℝ, polySecondCumulant (1 + C b * X + C c * X ^ 2) = b ^ 2 - 2 * c :=
    fun b c => by
      unfold polySecondCumulant
      have h1 : (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 1 = b := by
        rw [coeff_add, coeff_add, ← C_1, coeff_C, if_neg one_ne_zero, coeff_C_mul, coeff_X_one,
          coeff_C_mul, coeff_X_pow, if_neg (by decide : ¬ (1 : ℕ) = 2)]
        ring
      have h2 : (1 + C b * X + C c * X ^ 2 : ℝ[X]).coeff 2 = c := by
        rw [coeff_add, coeff_add, ← C_1, coeff_C, if_neg (by decide), coeff_C_mul, coeff_X,
          if_neg (by decide : ¬ (1 : ℕ) = 2), coeff_C_mul, coeff_X_pow, if_pos rfl]
        ring
      rw [h1, h2]
  unfold sliceTruncPoly
  rw [polySecondCumulant_mul_of_coeff_zero_one
      (coeff_zero_prod_eq_one _ _ fun q _ => h0_lin _)
      (coeff_zero_prod_eq_one _ _ fun q _ => by
        rw [DeBruijn.slicePairFactor_eq]; exact h0_quad _ _),
    polySecondCumulant_prod_of_coeff_zero_one _ _ (fun q _ => h0_lin _),
    polySecondCumulant_prod_of_coeff_zero_one _ _ (fun q _ => by
      rw [DeBruijn.slicePairFactor_eq]; exact h0_quad _ _),
    sum_sliceTrunc]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [h2_lin, (re_xiSliceGaussianReciprocal_of_critical t (mem_sliceTruncCrit.mp hq).2).2]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [DeBruijn.slicePairFactor_eq, h2_quad,
      (re_xiSliceGaussianReciprocal_pair_of_upper t (mem_sliceTruncUp.mp hq).2).2]

/-- Because `xiSliceGaussianRadiusHead t R` is invariant under `xiZeroCopyLineConjEquiv`,
`sliceTrunc` commutes with removing `xiSliceGaussianRadiusHead t R`. -/
theorem sliceTrunc_sdiff_xiSliceGaussianRadiusHead (t R : ℝ) (S : Finset XiZeroCopy) :
    sliceTrunc (S \ xiSliceGaussianRadiusHead t R) =
      sliceTrunc S \ xiSliceGaussianRadiusHead t R := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  ext q
  simp only [sliceTrunc, Finset.mem_sdiff, Finset.mem_union, mem_sliceTruncCrit,
    mem_sliceTruncUp, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ((⟨⟨hqS, hqH⟩, hc⟩ | ⟨⟨hqS, hqH⟩, hu⟩) | ⟨r, ⟨⟨hrS, hrH⟩, hu⟩, rfl⟩)
    · exact ⟨Or.inl (Or.inl ⟨hqS, hc⟩), hqH⟩
    · exact ⟨Or.inl (Or.inr ⟨hqS, hu⟩), hqH⟩
    · exact ⟨Or.inr ⟨r, ⟨hrS, hu⟩, rfl⟩,
        fun h => hrH ((mem_xiSliceGaussianRadiusHead_lineConj_iff t R r).mp h)⟩
  · rintro ⟨(⟨hqS, hc⟩ | ⟨hqS, hu⟩) | ⟨r, ⟨hrS, hu⟩, rfl⟩, hqH⟩
    · exact Or.inl (Or.inl ⟨⟨hqS, hqH⟩, hc⟩)
    · exact Or.inl (Or.inr ⟨⟨hqS, hqH⟩, hu⟩)
    · exact Or.inr ⟨r, ⟨⟨hrS, fun hrH =>
        hqH ((mem_xiSliceGaussianRadiusHead_lineConj_iff t R r).mpr hrH)⟩, hu⟩, rfl⟩

/-- **Exact additive head–tail splitting of the first cumulant of `sliceTruncPoly`.** -/
theorem coeff_one_sliceTruncPoly_eq_head_add_sdiff (t : ℝ) {H S : Finset XiZeroCopy}
    (hHS : H ⊆ S) :
    (sliceTruncPoly t S).coeff 1 =
      (sliceTruncPoly t H).coeff 1 + (sliceTruncPoly t (S \ H)).coeff 1 := by
  rw [DeBruijn.sliceTruncPoly_eq_head_mul_sdiff t hHS,
    coeff_one_mul_of_coeff_zero_one (coeff_zero_sliceTruncPoly t H)
      (coeff_zero_sliceTruncPoly t (S \ H))]

/-- **Exact additive head–tail splitting of the second cumulant of `sliceTruncPoly`.** -/
theorem polySecondCumulant_sliceTruncPoly_eq_head_add_sdiff (t : ℝ) {H S : Finset XiZeroCopy}
    (hHS : H ⊆ S) :
    polySecondCumulant (sliceTruncPoly t S) =
      polySecondCumulant (sliceTruncPoly t H) +
        polySecondCumulant (sliceTruncPoly t (S \ H)) := by
  rw [DeBruijn.sliceTruncPoly_eq_head_mul_sdiff t hHS,
    polySecondCumulant_mul_of_coeff_zero_one (coeff_zero_sliceTruncPoly t H)
      (coeff_zero_sliceTruncPoly t (S \ H))]

/-- Uniform bound on the truncated tail's first cumulant by `xiSliceGaussianTailMass`. -/
theorem abs_coeff_one_sliceTruncPoly_sdiff_le (t R : ℝ) (S : Finset XiZeroCopy) :
    |(sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)).coeff 1| ≤
      xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  rw [coeff_one_sliceTruncPoly, sliceTrunc_sdiff_xiSliceGaussianRadiusHead]
  have hout : ∀ q ∈ sliceTrunc S \ H, q ∉ H := fun _ hq => (Finset.mem_sdiff.mp hq).2
  calc |∑ q ∈ sliceTrunc S \ H, (xiSliceGaussianReciprocal t q).re|
      ≤ ∑ q ∈ sliceTrunc S \ H, |(xiSliceGaussianReciprocal t q).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ sliceTrunc S \ H, ‖xiSliceGaussianReciprocal t q‖ :=
        Finset.sum_le_sum fun q _ => Complex.abs_re_le_norm _
    _ ≤ xiSliceGaussianTailMass t H := by
        rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖) hout]
        exact (summable_norm_xiSliceGaussianTail t H).sum_le_tsum _ (fun _ _ => norm_nonneg _)

/-- Uniform bound on the truncated tail's second cumulant by `xiSliceGaussianTailFourth`. -/
theorem abs_polySecondCumulant_sliceTruncPoly_sdiff_le (t R : ℝ) (S : Finset XiZeroCopy) :
    |polySecondCumulant (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R))| ≤
      xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  rw [polySecondCumulant_sliceTruncPoly, sliceTrunc_sdiff_xiSliceGaussianRadiusHead]
  have hout : ∀ q ∈ sliceTrunc S \ H, q ∉ H := fun _ hq => (Finset.mem_sdiff.mp hq).2
  calc |∑ q ∈ sliceTrunc S \ H, ((xiSliceGaussianReciprocal t q) ^ 2).re|
      ≤ ∑ q ∈ sliceTrunc S \ H, |((xiSliceGaussianReciprocal t q) ^ 2).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ sliceTrunc S \ H, ‖xiSliceGaussianReciprocal t q‖ ^ 2 :=
        Finset.sum_le_sum fun q _ =>
          (Complex.abs_re_le_norm _).trans_eq (norm_pow _ 2)
    _ ≤ xiSliceGaussianTailFourth t H := by
        rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖ ^ 2) hout]
        exact (summable_sq_norm_xiSliceGaussianTail t H).sum_le_tsum _
          (fun _ _ => sq_nonneg _)

/-- Along `S → atTop`, the first cumulant of `sliceTruncPoly t (S \ H)` converges unconditionally to
`(xiSliceGaussianTailQuadratic t H).re` at every height `t ∈ ℝ`. -/
theorem tendsto_coeff_one_sliceTruncPoly_sdiff (t R : ℝ) :
    Tendsto (fun S : Finset XiZeroCopy =>
      (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)).coeff 1) atTop
      (𝓝 (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  have hs : Summable (fun q : {q : XiZeroCopy // q ∉ H} =>
      (xiSliceGaussianReciprocal t q).re) :=
    (summable_norm_xiSliceGaussianTail t H).of_norm_bounded fun q => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hsum_eq : (xiSliceGaussianTailQuadratic t H).re =
      ∑' q : {q : XiZeroCopy // q ∉ H}, (xiSliceGaussianReciprocal t q).re := by
    unfold xiSliceGaussianTailQuadratic
    exact Complex.re_tsum (summable_norm_xiSliceGaussianTail t H).of_norm
  rw [hsum_eq]
  let g : Finset XiZeroCopy → Finset {q : XiZeroCopy // q ∉ H} := fun A =>
    (A \ H).subtype (fun q => q ∉ H)
  have hg : Tendsto g atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun F => ?_
    refine ⟨F.map ⟨Subtype.val, Subtype.val_injective⟩, fun A hA x hx => ?_⟩
    simp only [g, Finset.mem_subtype, Finset.mem_sdiff]
    exact ⟨hA (Finset.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hlim := (hs.hasSum.comp hg).comp tendsto_sliceTrunc
  refine hlim.congr fun S => ?_
  simp only [Function.comp_apply, g]
  rw [coeff_one_sliceTruncPoly, sliceTrunc_sdiff_xiSliceGaussianRadiusHead]
  exact Finset.sum_subtype_of_mem (fun q => (xiSliceGaussianReciprocal t q).re)
    (fun _ hq => (Finset.mem_sdiff.mp hq).2)

/-- Along `S → atTop`, the second cumulant of `sliceTruncPoly t (S \ H)` converges unconditionally
to `∑' q : {q // q ∉ H}, ((xiSliceGaussianReciprocal t q) ^ 2).re` at every height `t ∈ ℝ`. -/
theorem tendsto_polySecondCumulant_sliceTruncPoly_sdiff (t R : ℝ) :
    Tendsto (fun S : Finset XiZeroCopy =>
      polySecondCumulant (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R))) atTop
      (𝓝 (∑' q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R},
        ((xiSliceGaussianReciprocal t q) ^ 2).re)) := by
  classical
  set H := xiSliceGaussianRadiusHead t R
  have hs : Summable (fun q : {q : XiZeroCopy // q ∉ H} =>
      ((xiSliceGaussianReciprocal t q) ^ 2).re) :=
    (summable_sq_norm_xiSliceGaussianTail t H).of_norm_bounded fun q => by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans_eq (norm_pow _ 2)
  let g : Finset XiZeroCopy → Finset {q : XiZeroCopy // q ∉ H} := fun A =>
    (A \ H).subtype (fun q => q ∉ H)
  have hg : Tendsto g atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun F => ?_
    refine ⟨F.map ⟨Subtype.val, Subtype.val_injective⟩, fun A hA x hx => ?_⟩
    simp only [g, Finset.mem_subtype, Finset.mem_sdiff]
    exact ⟨hA (Finset.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hlim := (hs.hasSum.comp hg).comp tendsto_sliceTrunc
  refine hlim.congr fun S => ?_
  simp only [Function.comp_apply, g]
  rw [polySecondCumulant_sliceTruncPoly, sliceTrunc_sdiff_xiSliceGaussianRadiusHead]
  exact Finset.sum_subtype_of_mem (fun q => ((xiSliceGaussianReciprocal t q) ^ 2).re)
    (fun _ hq => (Finset.mem_sdiff.mp hq).2)

/-! ## 3. Subconvexity-free Riemann–von Mangoldt summation-by-parts cumulant asymptotics -/

private theorem sum_Ico_sub_succ (f : ℕ → ℝ) {N K : ℕ} (hNK : N ≤ K) :
    ∑ k ∈ Finset.Ico N K, (f k - f (k + 1)) = f N - f K := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNK
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Finset.sum_Ico_succ_top (Nat.le_add_right N d), ih (Nat.le_add_right N d)]
    ring

/-- Discrete Abel summation on `Finset.Ico N K` against a nonnegative antitone weight `w`. -/
theorem abs_sum_Ico_diff_mul_antitone_le {E w : ℕ → ℝ} {N K : ℕ} {M : ℝ} (hNK : N ≤ K)
    (hM : 0 ≤ M) (hwK : 0 ≤ w K) (hE : ∀ k : ℕ, N ≤ k → k ≤ K → |E k| ≤ M)
    (hw : ∀ k : ℕ, N ≤ k → k < K → w (k + 1) ≤ w k) :
    |∑ k ∈ Finset.Ico N K, (E (k + 1) - E k) * w k| ≤ 2 * M * w N := by
  have hid : ∀ d : ℕ,
      ∑ k ∈ Finset.Ico N (N + d), (E (k + 1) - E k) * w k =
        E (N + d) * w (N + d) - E N * w N +
          ∑ k ∈ Finset.Ico N (N + d), E (k + 1) * (w k - w (k + 1)) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, Finset.sum_Ico_succ_top (Nat.le_add_right N d),
        Finset.sum_Ico_succ_top (Nat.le_add_right N d), ih]
      ring
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNK
  have hwN : w (N + d) ≤ w N := by
    have htel := sum_Ico_sub_succ w (Nat.le_add_right N d)
    have hsum0 : 0 ≤ ∑ k ∈ Finset.Ico N (N + d), (w k - w (k + 1)) :=
      Finset.sum_nonneg fun k hk => sub_nonneg.mpr
        (hw k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2)
    linarith
  have hwN0 : 0 ≤ w N := hwK.trans hwN
  rw [hid d]
  have h1 : |E (N + d) * w (N + d) - E N * w N| ≤ M * w (N + d) + M * w N := by
    calc |E (N + d) * w (N + d) - E N * w N|
        ≤ |E (N + d) * w (N + d)| + |E N * w N| := abs_sub _ _
      _ = |E (N + d)| * w (N + d) + |E N| * w N := by
          rw [abs_mul, abs_mul, abs_of_nonneg hwK, abs_of_nonneg hwN0]
      _ ≤ M * w (N + d) + M * w N := add_le_add
          (mul_le_mul_of_nonneg_right (hE (N + d) (Nat.le_add_right N d) le_rfl) hwK)
          (mul_le_mul_of_nonneg_right (hE N le_rfl (Nat.le_add_right N d)) hwN0)
  have h2 : |∑ k ∈ Finset.Ico N (N + d), E (k + 1) * (w k - w (k + 1))| ≤
      M * (w N - w (N + d)) := by
    calc |∑ k ∈ Finset.Ico N (N + d), E (k + 1) * (w k - w (k + 1))|
        ≤ ∑ k ∈ Finset.Ico N (N + d), |E (k + 1) * (w k - w (k + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico N (N + d), M * (w k - w (k + 1)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
          have hwk : 0 ≤ w k - w (k + 1) := sub_nonneg.mpr (hw k hk1 hk2)
          rw [abs_mul, abs_of_nonneg hwk]
          exact mul_le_mul_of_nonneg_right (hE (k + 1) (by omega) (by omega)) hwk
      _ = M * ∑ k ∈ Finset.Ico N (N + d), (w k - w (k + 1)) := (Finset.mul_sum _ _ _).symm
      _ = M * (w N - w (N + d)) := by rw [sum_Ico_sub_succ w (Nat.le_add_right N d)]
  exact (abs_add_le _ _).trans (by linarith)

private theorem inv_pow_two_sub_telescoping {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 1 / (k : ℝ) ^ 2 - (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) ∧
      1 / (k : ℝ) ^ 2 - (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) ≤
        1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have heqL : 1 / (k : ℝ) ^ 2 - (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) =
      1 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) := by
    field_simp; ring
  have heqR : 1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2 =
      (2 * (k : ℝ) - 1) / (((k : ℝ) - 1) ^ 2 * (k : ℝ) ^ 2) := by
    field_simp; ring
  rw [heqL, heqR]
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hk2, sq_nonneg ((k : ℝ) - 2)]

private theorem inv_pow_three_le_telescoping {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 3 ≤ 1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have heqR : 1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2 =
      (2 * (k : ℝ) - 1) / (((k : ℝ) - 1) ^ 2 * (k : ℝ) ^ 2) := by
    field_simp; ring
  rw [heqR, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hk2, sq_nonneg ((k : ℝ) - 2)]

private theorem inv_pow_four_sub_telescoping {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 1 / (k : ℝ) ^ 4 - (1 / 3) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3) ∧
      1 / (k : ℝ) ^ 4 - (1 / 3) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3) ≤
        6 * (1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4) := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have heqL : 1 / (k : ℝ) ^ 4 - (1 / 3) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3) =
      (6 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3) / (3 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) := by
    field_simp; ring
  have heqR : 6 * (1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4) =
      6 * ((k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4) / (((k : ℝ) - 1) ^ 4 * (k : ℝ) ^ 4) := by
    field_simp; ring
  rw [heqL, heqR]
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum1 : 6 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3 ≤ 17 * (k : ℝ) ^ 2 := by
    nlinarith only [hk2]
  have hkm4 : ((k : ℝ) - 1) ^ 4 ≤ (k : ℝ) ^ 4 :=
    pow_le_pow_left₀ hkm1.le (by linarith) 4
  have hkp3 : (k : ℝ) ^ 3 ≤ ((k : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ hk0.le (by linarith) 3
  have hdiff4 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4 := by
    have : (k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4 - (k : ℝ) ^ 3 =
        3 * (k : ℝ) ^ 2 * ((k : ℝ) - 2) + 4 * (k : ℝ) - 1 := by ring
    have : 0 ≤ 3 * (k : ℝ) ^ 2 * ((k : ℝ) - 2) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hL : (6 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3) * (((k : ℝ) - 1) ^ 4 * (k : ℝ) ^ 4) ≤
      17 * (k : ℝ) ^ 10 := by
    calc (6 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3) * (((k : ℝ) - 1) ^ 4 * (k : ℝ) ^ 4)
        ≤ (17 * (k : ℝ) ^ 2) * ((k : ℝ) ^ 4 * (k : ℝ) ^ 4) :=
          mul_le_mul hnum1 (mul_le_mul_of_nonneg_right hkm4 (by positivity))
            (by positivity) (by positivity)
      _ = 17 * (k : ℝ) ^ 10 := by ring
  have hR : 18 * (k : ℝ) ^ 10 ≤
      6 * ((k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4) * (3 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) := by
    calc 18 * (k : ℝ) ^ 10
        = (6 * (k : ℝ) ^ 3) * (3 * (k : ℝ) ^ 4 * (k : ℝ) ^ 3) := by ring
      _ ≤ 6 * ((k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4) * (3 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hkp3 (by positivity))
            (by positivity) (by linarith [pow_pos hk0 3])
  linarith [pow_pos hk0 10]

private theorem inv_pow_five_le_telescoping {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 5 ≤ 1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have heqR : 1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4 =
      ((k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4) / (((k : ℝ) - 1) ^ 4 * (k : ℝ) ^ 4) := by
    field_simp; ring
  have hkm4 : ((k : ℝ) - 1) ^ 4 ≤ (k : ℝ) ^ 4 :=
    pow_le_pow_left₀ hkm1.le (by linarith) 4
  have hdiff4 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4 := by
    have : (k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4 - (k : ℝ) ^ 3 =
        3 * (k : ℝ) ^ 2 * ((k : ℝ) - 2) + 4 * (k : ℝ) - 1 := by ring
    have : 0 ≤ 3 * (k : ℝ) ^ 2 * ((k : ℝ) - 2) := mul_nonneg (by positivity) (by linarith)
    linarith
  rw [heqR, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc ((k : ℝ) - 1) ^ 4 * (k : ℝ) ^ 4
      ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hkm4 (by positivity)
    _ = (k : ℝ) ^ 3 * (k : ℝ) ^ 5 := by ring
    _ ≤ ((k : ℝ) ^ 4 - ((k : ℝ) - 1) ^ 4) * (k : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hdiff4 (by positivity)

private theorem sum_range_succ_div_two_pow_le (D : ℕ) :
    ∑ m ∈ Finset.range D, ((m : ℝ) + 1) / (2 : ℝ) ^ m ≤ 4 := by
  let g : ℕ → ℝ := fun m => (2 * (m : ℝ) + 4) / (2 : ℝ) ^ m
  have hstep : ∀ m : ℕ, ((m : ℝ) + 1) / (2 : ℝ) ^ m = g m - g (m + 1) := by
    intro m
    dsimp only [g]
    rw [Nat.cast_succ, pow_succ]
    field_simp
    ring
  have htel : ∑ m ∈ Finset.range D, ((m : ℝ) + 1) / (2 : ℝ) ^ m = g 0 - g D := by
    induction D with
    | zero => simp [g]
    | succ d ih =>
      rw [Finset.sum_range_succ, ih, hstep d]
      ring
  have hg0 : g 0 = 4 := by simp [g]
  have hgD : 0 ≤ g D := by dsimp only [g]; positivity
  linarith

private theorem abs_log_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |Real.log (1 - u)| ≤ 2 * u := by
  have h1u : 0 < 1 - u := by linarith
  have hle0 : Real.log (1 - u) ≤ 0 := Real.log_nonpos h1u.le (by linarith)
  rw [abs_of_nonpos hle0, ← Real.log_inv]
  have hinv : (1 - u)⁻¹ ≤ Real.exp (2 * u) := by
    calc (1 - u)⁻¹ = 1 + u / (1 - u) := by field_simp [h1u.ne']; ring
      _ ≤ 1 + 2 * u := by
          have : u / (1 - u) ≤ 2 * u := by
            rw [div_le_iff₀ h1u]; nlinarith
          linarith
      _ ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  calc Real.log (1 - u)⁻¹ ≤ Real.log (Real.exp (2 * u)) :=
        Real.log_le_log (inv_pos.mpr h1u) hinv
    _ = 2 * u := Real.log_exp (2 * u)

/-- Exact convexity bounds on the unit increment of `routeKSmoothRVMCount`. -/
theorem routeKSmoothRVMCount_unit_increment_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ routeKSmoothRVMCount (x + 1) - routeKSmoothRVMCount x -
          Real.log (x / (2 * Real.pi)) / (2 * Real.pi) ∧
      routeKSmoothRVMCount (x + 1) - routeKSmoothRVMCount x -
          Real.log (x / (2 * Real.pi)) / (2 * Real.pi) ≤
        1 / (2 * Real.pi * x) := by
  have hx1 : 0 < x + 1 := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  have hup_log : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div hx1.ne' hx.ne']
    calc Real.log ((x + 1) / x)
        = Real.log (1 + 1 / x) := by congr 1; field_simp
      _ ≤ Real.log (Real.exp (1 / x)) :=
          Real.log_le_log (by positivity) (by linarith [Real.add_one_le_exp (1 / x)])
      _ = 1 / x := Real.log_exp _
  have hlo_log : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
    have h1 : Real.log (x / (x + 1)) ≤ -(1 / (x + 1)) := by
      calc Real.log (x / (x + 1))
          = Real.log (1 + (-(1 / (x + 1)))) := by congr 1; field_simp; ring
        _ ≤ Real.log (Real.exp (-(1 / (x + 1)))) :=
            Real.log_le_log (by positivity) (by linarith [Real.add_one_le_exp (-(1 / (x + 1)))])
        _ = -(1 / (x + 1)) := Real.log_exp _
    rw [Real.log_div hx.ne' hx1.ne'] at h1
    linarith
  have hbase : Real.log routeKRVMBase = Real.log (2 * Real.pi) + 1 := by
    rw [routeKRVMBase, Real.log_mul hpi.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hdiff : routeKSmoothRVMCount (x + 1) - routeKSmoothRVMCount x -
      Real.log (x / (2 * Real.pi)) / (2 * Real.pi) =
      ((Real.log (x + 1) - Real.log x) + x * (Real.log (x + 1) - Real.log x) - 1) /
        (2 * Real.pi) := by
    rw [routeKSmoothRVMCount_sub_eq hx hx1, hbase, Real.log_div hx.ne' hpi.ne']
    field_simp [Real.pi_ne_zero]
    ring
  rw [hdiff]
  constructor
  · refine div_nonneg ?_ hpi.le
    have hmul : x / (x + 1) ≤ x * (Real.log (x + 1) - Real.log x) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlo_log hx.le
    have hsum1 : 1 / (x + 1) + x / (x + 1) = 1 := by field_simp; ring
    linarith
  · rw [show 1 / (2 * Real.pi * x) = (1 / x) / (2 * Real.pi) by ring]
    refine div_le_div_of_nonneg_right ?_ hpi.le
    have hmul : x * (Real.log (x + 1) - Real.log x) ≤ 1 := by
      calc x * (Real.log (x + 1) - Real.log x) ≤ x * (1 / x) :=
            mul_le_mul_of_nonneg_left hup_log hx.le
        _ = 1 := by field_simp
    linarith

/-- Paired upper/lower smooth RvM increment around `t`: the linear `±k/t` terms cancel! -/
theorem abs_paired_routeKSmoothRVMCount_sub_main_le {t : ℝ} {k : ℕ} (ht : 8 ≤ t)
    (hk : (k : ℝ) ≤ t / 2) :
    |(routeKSmoothRVMCount (t + (k : ℝ) + 1) - routeKSmoothRVMCount (t + (k : ℝ))) +
      (routeKSmoothRVMCount (t - (k : ℝ)) - routeKSmoothRVMCount (t - (k : ℝ) - 1)) -
      Real.log (t / (2 * Real.pi)) / Real.pi| ≤
      3 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 < t := by linarith
  have hxp : 0 < t + (k : ℝ) := by linarith
  have hxm : 0 < t - (k : ℝ) - 1 := by linarith
  obtain ⟨hp0, hp1⟩ := routeKSmoothRVMCount_unit_increment_bounds hxp
  obtain ⟨hm0, hm1⟩ := routeKSmoothRVMCount_unit_increment_bounds hxm
  have hxm_eq : t - (k : ℝ) - 1 + 1 = t - (k : ℝ) := by ring
  rw [hxm_eq] at hm0 hm1
  set u : ℝ := (t + (k : ℝ) * ((k : ℝ) + 1)) / t ^ 2
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu_half : u ≤ 1 / 2 := by
    dsimp only [u]
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [ht, hk, hk0]
  have hprod : ((t + (k : ℝ)) / (2 * Real.pi)) * ((t - (k : ℝ) - 1) / (2 * Real.pi)) =
      (t / (2 * Real.pi)) ^ 2 * (1 - u) := by
    dsimp only [u]
    field_simp [ht0.ne', Real.pi_ne_zero]
    ring
  have hlog_pair : Real.log ((t + (k : ℝ)) / (2 * Real.pi)) / (2 * Real.pi) +
      Real.log ((t - (k : ℝ) - 1) / (2 * Real.pi)) / (2 * Real.pi) -
      Real.log (t / (2 * Real.pi)) / Real.pi =
      Real.log (1 - u) / (2 * Real.pi) := by
    have h1u : 0 < 1 - u := by linarith
    have hlogp := Real.log_mul (div_pos hxp (by positivity)).ne' (div_pos hxm (by positivity)).ne'
    rw [hprod, Real.log_mul (pow_pos (div_pos ht0 (by positivity)) 2).ne' h1u.ne',
      Real.log_pow, Nat.cast_ofNat] at hlogp
    field_simp [Real.pi_ne_zero]
    linarith
  set Ep := routeKSmoothRVMCount (t + (k : ℝ) + 1) - routeKSmoothRVMCount (t + (k : ℝ)) -
    Real.log ((t + (k : ℝ)) / (2 * Real.pi)) / (2 * Real.pi)
  set Em := routeKSmoothRVMCount (t - (k : ℝ)) - routeKSmoothRVMCount (t - (k : ℝ) - 1) -
    Real.log ((t - (k : ℝ) - 1) / (2 * Real.pi)) / (2 * Real.pi)
  have hdecomp : (routeKSmoothRVMCount (t + (k : ℝ) + 1) - routeKSmoothRVMCount (t + (k : ℝ))) +
      (routeKSmoothRVMCount (t - (k : ℝ)) - routeKSmoothRVMCount (t - (k : ℝ) - 1)) -
      Real.log (t / (2 * Real.pi)) / Real.pi =
      Ep + Em + Real.log (1 - u) / (2 * Real.pi) := by
    dsimp only [Ep, Em]; linarith
  have hEp_le : |Ep| ≤ 1 / (2 * Real.pi * t) := by
    rw [abs_of_nonneg hp0]
    exact hp1.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  have hEm_le : |Em| ≤ 3 / (2 * Real.pi * t) := by
    rw [abs_of_nonneg hm0]
    refine hm1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [ht, hk, hpi]
  have hlog_le : |Real.log (1 - u) / (2 * Real.pi)| ≤
      1 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    calc |Real.log (1 - u)| / (2 * Real.pi)
        ≤ (2 * u) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right (abs_log_one_sub_le hu0 hu_half) (by positivity)
      _ = 1 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) := by
          dsimp only [u]; field_simp [ht0.ne', Real.pi_ne_zero]; ring
  rw [hdecomp]
  calc |Ep + Em + Real.log (1 - u) / (2 * Real.pi)|
      ≤ |Ep + Em| + |Real.log (1 - u) / (2 * Real.pi)| := abs_add_le _ _
    _ ≤ |Ep| + |Em| + |Real.log (1 - u) / (2 * Real.pi)| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 1 / (2 * Real.pi * t) + 3 / (2 * Real.pi * t) +
          (1 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2)) :=
        add_le_add (add_le_add hEp_le hEm_le) hlog_le
    _ = 3 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) := by
        field_simp [ht0.ne', Real.pi_ne_zero]; ring



private theorem xiCopiesPos_mono {a b : ℝ} (hab : a ≤ b) :
    xiCopiesPos a ⊆ xiCopiesPos b := fun _ hq =>
  mem_xiCopiesPos.mpr ⟨(mem_xiCopiesPos.mp hq).1.trans hab, (mem_xiCopiesPos.mp hq).2⟩

private theorem card_xiCopiesPos_sdiff_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((xiCopiesPos b \ xiCopiesPos a).card : ℝ) =
      (xiZeroCount b : ℝ) - (xiZeroCount a : ℝ) := by
  have hsub := xiCopiesPos_mono hab
  have haC : ((xiCopiesPos a).card : ℝ) = (xiZeroCount a : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos ha
  have hbC : ((xiCopiesPos b).card : ℝ) = (xiZeroCount b : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos (ha.trans hab)
  rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), hbC, haC]

private theorem card_xiCopiesPos_le_mul_log {C T₀ T : ℝ} (hC : 0 < C) (hT₀ : 4 ≤ T₀)
    (hbase : routeKRVMBase ≤ T₀)
    (hclose : ∀ U : ℝ, T₀ ≤ U → |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U)
    (hT : T₀ ≤ T) :
    ((xiCopiesPos T).card : ℝ) ≤ (1 + C) * T * Real.log T := by
  have hT4 : 4 ≤ T := hT₀.trans hT
  have hT0 : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hC1 : ((xiCopiesPos T).card : ℝ) = (xiZeroCount T : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos hT0.le
  have hrem := (abs_le.mp (hclose T hT)).2
  have hM : routeKSmoothRVMCount T ≤ T * Real.log T := by
    unfold routeKSmoothRVMCount
    have hdiv : T / routeKRVMBase ≤ T :=
      div_le_self hT0.le one_lt_routeKRVMBase.le
    have hlog_le : Real.log (T / routeKRVMBase) ≤ Real.log T :=
      Real.log_le_log (div_pos hT0 routeKRVMBase_pos) hdiv
    have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h1 : T / (2 * Real.pi) * Real.log (T / routeKRVMBase) ≤
        T / (2 * Real.pi) * Real.log T :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    have h2 : T / (2 * Real.pi) * Real.log T ≤ (1 / 6) * (T * Real.log T) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ T * Real.log T := by positivity
      nlinarith
    have hTlog : 4 ≤ T * Real.log T := by nlinarith
    linarith
  rw [hC1]
  have hCT : C * Real.log T ≤ C * T * Real.log T := by
    have : 0 ≤ C * Real.log T := by positivity
    nlinarith
  linarith

private theorem card_xiCopiesPos_sdiff_width_two_le {C T₀ a b : ℝ} (hC : 0 < C)
    (hT₀ : 4 ≤ T₀) (hbase : routeKRVMBase + 2 ≤ T₀)
    (hclose : ∀ U : ℝ, T₀ ≤ U → |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U)
    (ha : T₀ ≤ a) (hab : a ≤ b) (hba : b ≤ a + 2) :
    ((xiCopiesPos b \ xiCopiesPos a).card : ℝ) ≤ (2 * C + 2) * Real.log (a + 2) := by
  have ha4 : 4 ≤ a := hT₀.trans ha
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have ha_base : routeKRVMBase < b := lt_of_lt_of_le (by linarith) (ha.trans hab)
  have ha2_base : routeKRVMBase < a + 2 := by linarith
  have hMb : routeKSmoothRVMCount b ≤ routeKSmoothRVMCount (a + 2) := by
    rcases eq_or_lt_of_le hba with rfl | hlt
    · exact le_rfl
    · exact (routeKSmoothRVMCount_strictMonoOn ha_base ha2_base hlt).le
  have h1 := routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove ha4 (le_add_of_nonneg_right zero_le_one) le_rfl
  have h2 := routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove (T := a + 1) (U := a + 2)
    (by linarith) (by linarith) (by linarith)
  have hlog1 : Real.log a ≤ Real.log (a + 2) := Real.log_le_log ha0 (by linarith)
  have hlog2 : Real.log (a + 1) ≤ Real.log (a + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlogb : Real.log b ≤ Real.log (a + 2) := Real.log_le_log hb0 hba
  have hrem_a := (abs_le.mp (hclose a ha)).1
  have hrem_b := (abs_le.mp (hclose b (ha.trans hab))).2
  have hCa : C * Real.log a ≤ C * Real.log (a + 2) := mul_le_mul_of_nonneg_left hlog1 hC.le
  have hCb : C * Real.log b ≤ C * Real.log (a + 2) := mul_le_mul_of_nonneg_left hlogb hC.le
  rw [card_xiCopiesPos_sdiff_eq ha0.le hab]
  linarith

private def upperOrdBin (t : ℝ) (k : ℕ) : Finset XiZeroCopy :=
  xiCopiesPos (t + (k : ℝ) + 1) \ xiCopiesPos (t + (k : ℝ))

private def lowerOrdBin (t : ℝ) (k : ℕ) : Finset XiZeroCopy :=
  xiCopiesPos (t - (k : ℝ)) \ xiCopiesPos (t - (k : ℝ) - 1)

private def pairedOrdWindow (t : ℝ) (N K : ℕ) : Finset XiZeroCopy :=
  (xiCopiesPos (t + (K : ℝ)) \ xiCopiesPos (t + (N : ℝ))) ∪
    (xiCopiesPos (t - (N : ℝ)) \ xiCopiesPos (t - (K : ℝ)))

private theorem sum_pairedOrdWindow_eq_sum_Ico (f : XiZeroCopy → ℝ) {t : ℝ} {N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKt : (K : ℝ) < t) :
    ∑ q ∈ pairedOrdWindow t N K, f q =
      ∑ k ∈ Finset.Ico N K, (∑ q ∈ upperOrdBin t k, f q + ∑ q ∈ lowerOrdBin t k, f q) := by
  classical
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdisj_UL : Disjoint (xiCopiesPos (t + (K : ℝ)) \ xiCopiesPos (t + (N : ℝ)))
      (xiCopiesPos (t - (N : ℝ)) \ xiCopiesPos (t - (K : ℝ))) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have h1' := (Finset.mem_sdiff.mp h1).2
    obtain ⟨h2a, h2b⟩ := mem_xiCopiesPos.mp (Finset.mem_sdiff.mp h2).1
    rw [abs_of_pos h2b] at h2a
    exact h1' (mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos h2b]; linarith, h2b⟩)
  unfold pairedOrdWindow
  rw [Finset.sum_union hdisj_UL]
  have hsdiff_step : ∀ {A B C : Finset XiZeroCopy}, A ⊆ B → B ⊆ C →
      ∑ q ∈ C \ A, f q = ∑ q ∈ B \ A, f q + ∑ q ∈ C \ B, f q := by
    intro A B C hAB hBC
    have heq : C \ A = (B \ A) ∪ (C \ B) := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun ⟨hC, hA⟩ => by by_cases hB : q ∈ B; exact Or.inl ⟨hB, hA⟩; exact Or.inr ⟨hC, hB⟩,
        fun h => h.elim (fun ⟨hB, hA⟩ => ⟨hBC hB, hA⟩) (fun ⟨hC, hB⟩ => ⟨hC, fun hA => hB (hAB hA)⟩)⟩
    have hdisj : Disjoint (B \ A) (C \ B) := by
      rw [Finset.disjoint_left]
      exact fun q h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
    rw [heq, Finset.sum_union hdisj]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNK
  have hup : ∀ m : ℕ,
      ∑ q ∈ xiCopiesPos (t + ((N + m : ℕ) : ℝ)) \ xiCopiesPos (t + (N : ℝ)), f q =
        ∑ k ∈ Finset.Ico N (N + m), ∑ q ∈ upperOrdBin t k, f q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hsdiff_step (xiCopiesPos_mono (by push_cast; linarith))
        (xiCopiesPos_mono (by push_cast; linarith)), ih,
        Nat.add_succ, Finset.sum_Ico_succ_top (Nat.le_add_right N m)]
      have hcast : t + ((N + m + 1 : ℕ) : ℝ) = t + ((N + m : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]; rfl
  have hlo : ∀ m : ℕ,
      ∑ q ∈ xiCopiesPos (t - (N : ℝ)) \ xiCopiesPos (t - ((N + m : ℕ) : ℝ)), f q =
        ∑ k ∈ Finset.Ico N (N + m), ∑ q ∈ lowerOrdBin t k, f q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hsdiff_step (B := xiCopiesPos (t - ((N + m : ℕ) : ℝ)))
        (xiCopiesPos_mono (by push_cast; linarith))
        (xiCopiesPos_mono (by push_cast; linarith)), ih,
        Nat.add_succ, Finset.sum_Ico_succ_top (Nat.le_add_right N m), add_comm]
      have hcast : t - ((N + m + 1 : ℕ) : ℝ) = t - ((N + m : ℕ) : ℝ) - 1 := by push_cast; ring
      rw [hcast]; rfl
  rw [hup d, hlo d, ← Finset.sum_add_distrib]

private theorem norm_sq_xiSpectralPoint_sub_of_bin {t : ℝ} {k : ℕ} {q : XiZeroCopy}
    (hk : 1 ≤ k) (hq : q ∈ upperOrdBin t k ∨ q ∈ lowerOrdBin t k) :
    (k : ℝ) ^ 2 ≤ ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 ∧
      ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have hN : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 =
      ((q.1 : ℂ).im - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero, hre]
    ring
  have him2 := xiSpectralPoint_im_sq_lt_quarter q
  have him0 : 0 ≤ (xiSpectralPoint q).im ^ 2 := sq_nonneg _
  have hord : (k : ℝ) ≤ |(q.1 : ℂ).im - t| ∧ |(q.1 : ℂ).im - t| ≤ (k : ℝ) + 1 := by
    rcases hq with h | h
    · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp h
      obtain ⟨h1a, h1b⟩ := mem_xiCopiesPos.mp h1
      rw [abs_of_pos h1b] at h1a
      have hgt : t + (k : ℝ) < (q.1 : ℂ).im := lt_of_not_ge fun hle =>
        h2 (mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos h1b]; exact hle, h1b⟩)
      rw [abs_of_pos (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp h
      obtain ⟨h1a, h1b⟩ := mem_xiCopiesPos.mp h1
      rw [abs_of_pos h1b] at h1a
      have hgt : t - (k : ℝ) - 1 < (q.1 : ℂ).im := lt_of_not_ge fun hle =>
        h2 (mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos h1b]; exact hle, h1b⟩)
      rw [abs_of_neg (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hsq_lo : (k : ℝ) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hord.1 2
    rwa [sq_abs] at this
  have hsq_hi : ((q.1 : ℂ).im - t) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hord.2 2
    rwa [sq_abs] at this
  rw [hN]
  exact ⟨by linarith, by nlinarith only [hsq_hi, him2, hk1]⟩

private theorem reciprocal_bin_discretization {t : ℝ} {k : ℕ} {q : XiZeroCopy}
    (hk : 2 ≤ k) (hq : q ∈ upperOrdBin t k ∨ q ∈ lowerOrdBin t k) :
    |‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2| ≤ 8 / (k : ℝ) ^ 3 ∧
      |‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4| ≤ 32 / (k : ℝ) ^ 5 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  obtain ⟨hlo, hhi⟩ := norm_sq_xiSpectralPoint_sub_of_bin (by omega) hq
  set D2 := ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2
  have hD2_pos : 0 < D2 := lt_of_lt_of_le (by positivity) hlo
  have hrec : ‖xiSliceGaussianReciprocal t q‖ = 1 / D2 := by
    rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, one_div]
  have hb1_lo : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / D2 := one_div_le_one_div_of_le hD2_pos hhi
  have hb1_hi : 1 / D2 ≤ 1 / (k : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hlo
  have hb2_lo : 1 / ((k : ℝ) + 2) ^ 4 ≤ (1 / D2) ^ 2 := by
    calc 1 / ((k : ℝ) + 2) ^ 4 = (1 / ((k : ℝ) + 2) ^ 2) ^ 2 := by ring
      _ ≤ (1 / D2) ^ 2 := pow_le_pow_left₀ (by positivity) hb1_lo 2
  have hb2_hi : (1 / D2) ^ 2 ≤ 1 / (k : ℝ) ^ 4 := by
    calc (1 / D2) ^ 2 ≤ (1 / (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hb1_hi 2
      _ = 1 / (k : ℝ) ^ 4 := by ring
  rw [hrec]
  constructor
  · rw [abs_of_nonpos (by linarith), neg_sub]
    calc 1 / (k : ℝ) ^ 2 - 1 / D2
        ≤ 1 / (k : ℝ) ^ 2 - 1 / ((k : ℝ) + 2) ^ 2 := by linarith
      _ = (4 * (k : ℝ) + 4) / ((k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2) := by field_simp; ring
      _ ≤ 8 / (k : ℝ) ^ 3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (4 * (k : ℝ) + 4) * (k : ℝ) ^ 3 ≤ 6 * (k : ℝ) ^ 4 := by nlinarith only [hk2]
          have h2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 :=
            pow_le_pow_left₀ hk0.le (by linarith) 2
          have h3 : 8 * (k : ℝ) ^ 4 ≤ 8 * ((k : ℝ) ^ 2 * ((k : ℝ) + 2) ^ 2) := by
            have : (k : ℝ) ^ 4 = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
              (by norm_num)
          linarith [pow_pos hk0 4]
  · rw [abs_of_nonpos (by linarith), neg_sub]
    calc 1 / (k : ℝ) ^ 4 - (1 / D2) ^ 2
        ≤ 1 / (k : ℝ) ^ 4 - 1 / ((k : ℝ) + 2) ^ 4 := by linarith
      _ = (8 * (k : ℝ) ^ 3 + 24 * (k : ℝ) ^ 2 + 32 * (k : ℝ) + 16) /
            ((k : ℝ) ^ 4 * ((k : ℝ) + 2) ^ 4) := by field_simp; ring
      _ ≤ 32 / (k : ℝ) ^ 5 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hnum : 8 * (k : ℝ) ^ 3 + 24 * (k : ℝ) ^ 2 + 32 * (k : ℝ) + 16 ≤
              30 * (k : ℝ) ^ 3 := by nlinarith only [hk2, sq_nonneg ((k : ℝ) - 2)]
          have h1 : (8 * (k : ℝ) ^ 3 + 24 * (k : ℝ) ^ 2 + 32 * (k : ℝ) + 16) * (k : ℝ) ^ 5 ≤
              30 * (k : ℝ) ^ 8 := by
            calc (8 * (k : ℝ) ^ 3 + 24 * (k : ℝ) ^ 2 + 32 * (k : ℝ) + 16) * (k : ℝ) ^ 5
                ≤ (30 * (k : ℝ) ^ 3) * (k : ℝ) ^ 5 :=
                  mul_le_mul_of_nonneg_right hnum (by positivity)
              _ = 30 * (k : ℝ) ^ 8 := by ring
          have h2 : (k : ℝ) ^ 4 ≤ ((k : ℝ) + 2) ^ 4 :=
            pow_le_pow_left₀ hk0.le (by linarith) 4
          have h3 : 32 * (k : ℝ) ^ 8 ≤ 32 * ((k : ℝ) ^ 4 * ((k : ℝ) + 2) ^ 4) := by
            have : (k : ℝ) ^ 8 = (k : ℝ) ^ 4 * (k : ℝ) ^ 4 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
              (by norm_num)
          linarith [pow_pos hk0 8]


private theorem sum_biUnion_nonneg_le {α β : Type*} [DecidableEq β] (s : Finset α)
    (g : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion g, f b ≤ ∑ a ∈ s, ∑ b ∈ g a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : ∑ b ∈ g a ∪ s.biUnion g, f b ≤
        ∑ b ∈ g a, f b + ∑ b ∈ s.biUnion g, f b := by
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ b ∈ g a ∩ s.biUnion g, f b := Finset.sum_nonneg fun b _ => hf b
      linarith
    linarith

private theorem nat_cast_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    linarith

private theorem sum_far_ordinate_inv_pow_le {C T₀ t : ℝ} (hC : 0 < C) (hT₀ : 4 ≤ T₀)
    (hbase : routeKRVMBase ≤ T₀)
    (hclose : ∀ U : ℝ, T₀ ≤ U → |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U)
    (htT : T₀ ≤ t) (ht8 : 8 ≤ t) (G : Finset XiZeroCopy)
    (hG : ∀ r ∈ G, t < (r.1 : ℂ).im) :
    ∑ r ∈ G, 1 / ((r.1 : ℂ).im) ^ 2 ≤ 16 * (1 + C) * Real.log t / t ∧
      ∑ r ∈ G, 1 / ((r.1 : ℂ).im) ^ 4 ≤ 16 * (1 + C) * Real.log t / t ^ 3 := by
  classical
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  set D : ℕ := G.sup (fun r => Nat.ceil ((r.1 : ℂ).im / t)) + 1
  let shell : ℕ → Finset XiZeroCopy := fun m =>
    xiCopiesPos ((2 : ℝ) ^ (m + 1) * t) \ xiCopiesPos ((2 : ℝ) ^ m * t)
  have hcov : G ⊆ (Finset.range D).biUnion shell := by
    have htel : ∀ n : ℕ, (Finset.range n).biUnion shell =
        xiCopiesPos ((2 : ℝ) ^ n * t) \ xiCopiesPos t := by
      intro n
      induction n with
      | zero => simp [shell]
      | succ n ih =>
        rw [Finset.range_add_one, Finset.biUnion_insert, ih]
        ext q
        simp only [shell, Finset.mem_union, Finset.mem_sdiff]
        have hsub1 := xiCopiesPos_mono (a := t) (b := (2 : ℝ) ^ n * t)
          (by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)])
        have hsub2 := xiCopiesPos_mono (a := (2 : ℝ) ^ n * t) (b := (2 : ℝ) ^ (n + 1) * t)
          (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n])
        exact ⟨fun h => h.elim (fun ⟨h1, h2⟩ => ⟨h1, fun htq => h2 (hsub1 htq)⟩)
            (fun ⟨h1, h2⟩ => ⟨hsub2 h1, h2⟩),
          fun ⟨h1, h2⟩ => by
            by_cases hm : q ∈ xiCopiesPos ((2 : ℝ) ^ n * t)
            · exact Or.inr ⟨hm, h2⟩
            · exact Or.inl ⟨h1, hm⟩⟩
    rw [htel D]
    intro r hr
    have hrt : t < (r.1 : ℂ).im := hG r hr
    have hr0 : 0 < (r.1 : ℂ).im := lt_trans ht0 hrt
    have hceil_le : Nat.ceil ((r.1 : ℂ).im / t) ≤ G.sup (fun x => Nat.ceil ((x.1 : ℂ).im / t)) :=
      Finset.le_sup hr
    have hle_D : (r.1 : ℂ).im / t ≤ (D : ℝ) := by
      calc (r.1 : ℂ).im / t ≤ (Nat.ceil ((r.1 : ℂ).im / t) : ℝ) := Nat.le_ceil _
        _ ≤ (D : ℝ) := by exact_mod_cast Nat.le_succ_of_le hceil_le
    have hle_pow : (r.1 : ℂ).im ≤ (2 : ℝ) ^ D * t := by
      have := (div_le_iff₀ ht0).mp (hle_D.trans (nat_cast_le_two_pow D))
      linarith
    rw [Finset.mem_sdiff, mem_xiCopiesPos, mem_xiCopiesPos, abs_of_pos hr0]
    exact ⟨⟨hle_pow, hr0⟩, fun h => not_lt_of_ge h.1 hrt⟩
  have hshell_card : ∀ m : ℕ, ((shell m).card : ℝ) ≤
      4 * (1 + C) * (2 : ℝ) ^ m * t * ((m : ℝ) + 1) * Real.log t := by
    intro m
    have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hTm : T₀ ≤ (2 : ℝ) ^ (m + 1) * t := htT.trans (by nlinarith)
    have hle1 : ((shell m).card : ℝ) ≤ ((xiCopiesPos ((2 : ℝ) ^ (m + 1) * t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have hle2 := card_xiCopiesPos_le_mul_log hC hT₀ hbase hclose hTm
    have hpow_t : (2 : ℝ) ^ (m + 1) * t ≤ t ^ (m + 2) := by
      calc (2 : ℝ) ^ (m + 1) * t ≤ t ^ (m + 1) * t :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by linarith) (m + 1)) ht0.le
        _ = t ^ (m + 2) := by rw [pow_succ]
    have hlog_m : Real.log ((2 : ℝ) ^ (m + 1) * t) ≤ 2 * ((m : ℝ) + 1) * Real.log t := by
      calc Real.log ((2 : ℝ) ^ (m + 1) * t)
          ≤ Real.log (t ^ (m + 2)) := Real.log_le_log (by positivity) hpow_t
        _ = ((m + 2 : ℕ) : ℝ) * Real.log t := Real.log_pow t (m + 2)
        _ ≤ 2 * ((m : ℝ) + 1) * Real.log t := by
            push_cast
            exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg m]) hlog0
    calc ((shell m).card : ℝ)
        ≤ (1 + C) * ((2 : ℝ) ^ (m + 1) * t) * Real.log ((2 : ℝ) ^ (m + 1) * t) :=
          hle1.trans hle2
      _ ≤ (1 + C) * ((2 : ℝ) ^ (m + 1) * t) * (2 * ((m : ℝ) + 1) * Real.log t) :=
          mul_le_mul_of_nonneg_left hlog_m (by positivity)
      _ = 4 * (1 + C) * (2 : ℝ) ^ m * t * ((m : ℝ) + 1) * Real.log t := by
          rw [pow_succ]; ring
  have hshell_im : ∀ m : ℕ, ∀ r ∈ shell m, (2 : ℝ) ^ m * t < (r.1 : ℂ).im := by
    intro m r hr
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hr
    have hr0 := (mem_xiCopiesPos.mp h1).2
    exact lt_of_not_ge fun hle =>
      h2 (mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hr0]; exact hle, hr0⟩)
  constructor
  · calc ∑ r ∈ G, 1 / ((r.1 : ℂ).im) ^ 2
        ≤ ∑ r ∈ (Finset.range D).biUnion shell, 1 / ((r.1 : ℂ).im) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => by positivity)
      _ ≤ ∑ m ∈ Finset.range D, ∑ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 2 :=
          sum_biUnion_nonneg_le _ _ _ (fun _ => by positivity)
      _ ≤ ∑ m ∈ Finset.range D,
            (4 * (1 + C) * Real.log t / t) * (((m : ℝ) + 1) / (2 : ℝ) ^ m) := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hterm : ∀ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 2 ≤ 1 / ((2 : ℝ) ^ m * t) ^ 2 :=
            fun r hr => one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ (by positivity) (hshell_im m r hr).le 2)
          calc ∑ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 2
              ≤ ∑ _r ∈ shell m, 1 / ((2 : ℝ) ^ m * t) ^ 2 := Finset.sum_le_sum hterm
            _ = ((shell m).card : ℝ) * (1 / ((2 : ℝ) ^ m * t) ^ 2) := by simp
            _ ≤ (4 * (1 + C) * (2 : ℝ) ^ m * t * ((m : ℝ) + 1) * Real.log t) *
                  (1 / ((2 : ℝ) ^ m * t) ^ 2) :=
                mul_le_mul_of_nonneg_right (hshell_card m) (by positivity)
            _ = (4 * (1 + C) * Real.log t / t) * (((m : ℝ) + 1) / (2 : ℝ) ^ m) := by
                have hp : ((2 : ℝ) ^ m) ≠ 0 := pow_ne_zero m two_ne_zero
                field_simp [ht0.ne', hp]; ring
      _ = (4 * (1 + C) * Real.log t / t) *
            ∑ m ∈ Finset.range D, ((m : ℝ) + 1) / (2 : ℝ) ^ m :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (4 * (1 + C) * Real.log t / t) * 4 :=
          mul_le_mul_of_nonneg_left (sum_range_succ_div_two_pow_le D) (by positivity)
      _ = 16 * (1 + C) * Real.log t / t := by ring
  · calc ∑ r ∈ G, 1 / ((r.1 : ℂ).im) ^ 4
        ≤ ∑ r ∈ (Finset.range D).biUnion shell, 1 / ((r.1 : ℂ).im) ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => by positivity)
      _ ≤ ∑ m ∈ Finset.range D, ∑ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 4 :=
          sum_biUnion_nonneg_le _ _ _ (fun _ => by positivity)
      _ ≤ ∑ m ∈ Finset.range D,
            (4 * (1 + C) * Real.log t / t ^ 3) * (((m : ℝ) + 1) / (2 : ℝ) ^ m) := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hterm : ∀ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 4 ≤ 1 / ((2 : ℝ) ^ m * t) ^ 4 :=
            fun r hr => one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ (by positivity) (hshell_im m r hr).le 4)
          have hpow4 : (2 : ℝ) ^ m * (2 : ℝ) ^ m ≤ ((2 : ℝ) ^ m) ^ 4 := by
            have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
            nlinarith [sq_nonneg ((2 : ℝ) ^ m)]
          calc ∑ r ∈ shell m, 1 / ((r.1 : ℂ).im) ^ 4
              ≤ ∑ _r ∈ shell m, 1 / ((2 : ℝ) ^ m * t) ^ 4 := Finset.sum_le_sum hterm
            _ = ((shell m).card : ℝ) * (1 / ((2 : ℝ) ^ m * t) ^ 4) := by simp
            _ ≤ (4 * (1 + C) * (2 : ℝ) ^ m * t * ((m : ℝ) + 1) * Real.log t) *
                  (1 / ((2 : ℝ) ^ m * t) ^ 4) :=
                mul_le_mul_of_nonneg_right (hshell_card m) (by positivity)
            _ ≤ (4 * (1 + C) * Real.log t / t ^ 3) * (((m : ℝ) + 1) / (2 : ℝ) ^ m) := by
                rw [mul_pow, div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
                have hp : 0 < ((2 : ℝ) ^ m) ^ 4 * t ^ 4 := by positivity
                rw [div_mul_eq_mul_div, div_le_iff₀ hp]
                have hnonneg : 0 ≤ 4 * (1 + C) * ((m : ℝ) + 1) * Real.log t * t ^ 4 := by positivity
                calc 4 * (1 + C) * (2 : ℝ) ^ m * t * ((m : ℝ) + 1) * Real.log t *
                      (t ^ 3 * (2 : ℝ) ^ m)
                    = (4 * (1 + C) * ((m : ℝ) + 1) * Real.log t * t ^ 4) *
                        ((2 : ℝ) ^ m * (2 : ℝ) ^ m) := by ring
                  _ ≤ (4 * (1 + C) * ((m : ℝ) + 1) * Real.log t * t ^ 4) *
                        (((2 : ℝ) ^ m) ^ 4) := mul_le_mul_of_nonneg_left hpow4 hnonneg
                  _ = 4 * (1 + C) * Real.log t * ((m : ℝ) + 1) *
                        (((2 : ℝ) ^ m) ^ 4 * t ^ 4) := by ring
      _ = (4 * (1 + C) * Real.log t / t ^ 3) *
            ∑ m ∈ Finset.range D, ((m : ℝ) + 1) / (2 : ℝ) ^ m :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (4 * (1 + C) * Real.log t / t ^ 3) * 4 :=
          mul_le_mul_of_nonneg_left (sum_range_succ_div_two_pow_le D) (by positivity)
      _ = 16 * (1 + C) * Real.log t / t ^ 3 := by ring

private theorem inv_pow_four_le_telescoping {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 4 ≤ 1 / ((k : ℝ) - 1) ^ 3 - 1 / (k : ℝ) ^ 3 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have heqR : 1 / ((k : ℝ) - 1) ^ 3 - 1 / (k : ℝ) ^ 3 =
      (3 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1) / (((k : ℝ) - 1) ^ 3 * (k : ℝ) ^ 3) := by
    field_simp; ring
  have hkm3 : ((k : ℝ) - 1) ^ 3 ≤ (k : ℝ) ^ 3 :=
    pow_le_pow_left₀ hkm1.le (by linarith) 3
  have hnum : (k : ℝ) ^ 2 ≤ 3 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1 := by
    nlinarith only [hk2, sq_nonneg ((k : ℝ) - 1)]
  rw [heqR, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc ((k : ℝ) - 1) ^ 3 * (k : ℝ) ^ 3
      ≤ (k : ℝ) ^ 3 * (k : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hkm3 (by positivity)
    _ = (k : ℝ) ^ 2 * (k : ℝ) ^ 4 := by ring
    _ ≤ (3 * (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1) * (k : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)

private theorem compl_pairedOrdWindow_le {C T₀ t R : ℝ} (hC : 0 < C) (hT₀ : 4 ≤ T₀)
    (hbase : routeKRVMBase + 2 ≤ T₀)
    (hclose : ∀ U : ℝ, T₀ ≤ U → |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U)
    (htT : 2 * T₀ + 16 ≤ t) (ht64 : 64 ≤ t) (hR8 : 8 ≤ R) (hRt : 8 * R ≤ t)
    (F : Finset {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R}) :
    let N := Nat.floor R + 1
    let K := Nat.floor (t / 2)
    let S := (F.map ⟨Subtype.val, Subtype.val_injective⟩).filter
      (fun q => q ∉ pairedOrdWindow t N K)
    ∑ q ∈ S, ‖xiSliceGaussianReciprocal t q‖ ≤
      300 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) ∧
    ∑ q ∈ S, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      4200 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
  classical
  intro N K S
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R := by linarith
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]; linarith [Real.exp_one_lt_d9]
  have hlog0 : 0 ≤ Real.log t := by linarith
  have hRN : R < (N : ℝ) := by
    dsimp only [N]; push_cast; exact Nat.lt_floor_add_one R
  have hNR1 : (N : ℝ) ≤ R + 1 := by
    dsimp only [N]; push_cast; linarith [Nat.floor_le hR0.le]
  have hKt2 : (K : ℝ) ≤ t / 2 := by
    dsimp only [K]; exact Nat.floor_le (by positivity)
  have ht3K : t / 3 ≤ (K : ℝ) := by
    have : t / 2 - 1 < (K : ℝ) := by
      dsimp only [K]; linarith [Nat.lt_floor_add_one (t / 2)]
    linarith
  have hbase0 : routeKRVMBase ≤ T₀ := by linarith
  have htT0 : T₀ ≤ t := by linarith
  -- Partition `S` into 5 regions.
  set S1 := S.filter (fun q => 0 < (q.1 : ℂ).im ∧ t - (N : ℝ) < (q.1 : ℂ).im ∧
    (q.1 : ℂ).im ≤ t + (N : ℝ))
  set S2 := S.filter (fun q => 0 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ t - (K : ℝ))
  set S3 := S.filter (fun q => -t ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im < 0)
  set S4 := S.filter (fun q => t + (K : ℝ) < (q.1 : ℂ).im)
  set S5 := S.filter (fun q => (q.1 : ℂ).im < -t)
  have hcovS : S ⊆ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 := by
    intro q hq
    have hnotP : q ∉ pairedOrdWindow t N K := (Finset.mem_filter.mp hq).2
    have him_ne : (q.1 : ℂ).im ≠ 0 := xiSupport_im_ne_zero q.1
    simp only [S1, S2, S3, S4, S5, Finset.mem_union, Finset.mem_filter]
    rcases lt_or_gt_of_ne him_ne with hneg | hpos
    · rcases lt_or_ge (q.1 : ℂ).im (-t) with hfar | hmid
      · exact Or.inr ⟨hq, hfar⟩
      · exact Or.inl (Or.inl (Or.inr ⟨hq, hmid, hneg⟩))
    · rcases le_or_gt (q.1 : ℂ).im (t - (K : ℝ)) with hlow | hgt1
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hq, hpos, hlow⟩)))
      · rcases le_or_gt (q.1 : ℂ).im (t - (N : ℝ)) with hL | hgt2
        · exfalso
          apply hnotP
          unfold pairedOrdWindow
          refine Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨?_, ?_⟩))
          · exact mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; exact hL, hpos⟩
          · intro hmem
            have := (mem_xiCopiesPos.mp hmem).1
            rw [abs_of_pos hpos] at this
            linarith
        · rcases le_or_gt (q.1 : ℂ).im (t + (N : ℝ)) with hcol | hgt3
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hq, hpos, hgt2, hcol⟩)))
          · rcases le_or_gt (q.1 : ℂ).im (t + (K : ℝ)) with hU | hfar
            · exfalso
              apply hnotP
              unfold pairedOrdWindow
              refine Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨?_, ?_⟩))
              · exact mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; exact hU, hpos⟩
              · intro hmem
                have := (mem_xiCopiesPos.mp hmem).1
                rw [abs_of_pos hpos] at this
                linarith
            · exact Or.inl (Or.inr ⟨hq, hfar⟩)
  have hsum_split : ∀ g : XiZeroCopy → ℝ, (∀ q, 0 ≤ g q) →
      ∑ q ∈ S, g q ≤ ∑ q ∈ S1, g q + ∑ q ∈ S2, g q + ∑ q ∈ S3, g q +
        ∑ q ∈ S4, g q + ∑ q ∈ S5, g q := by
    intro g hg
    have hu : ∀ A B : Finset XiZeroCopy, ∑ q ∈ A ∪ B, g q ≤ ∑ q ∈ A, g q + ∑ q ∈ B, g q := by
      intro A B
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ q ∈ A ∩ B, g q := Finset.sum_nonneg fun q _ => hg q
      linarith
    calc ∑ q ∈ S, g q
        ≤ ∑ q ∈ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5, g q :=
          Finset.sum_le_sum_of_subset_of_nonneg hcovS (fun q _ _ => hg q)
      _ ≤ _ := by
          linarith [hu (S1 ∪ S2 ∪ S3 ∪ S4) S5, hu (S1 ∪ S2 ∪ S3) S4,
            hu (S1 ∪ S2) S3, hu S1 S2]
  -- Bound `S1` (collar around `t ± R`).
  have hS1_notH : ∀ q ∈ S1, R < ‖xiSpectralPoint q - (t : ℂ)‖ := by
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hqS).1
    exact lt_of_not_ge fun hle => x.2 ((mem_xiSliceGaussianRadiusHead t R x.1).mpr hle)
  have hS1_sub : S1 ⊆ (xiCopiesPos (t + R + 1) \ xiCopiesPos (t + R - 1)) ∪
      (xiCopiesPos (t - R + 1) \ xiCopiesPos (t - R - 1)) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    obtain ⟨hpos, hlo, hhi⟩ := hq'.2
    have hdR := hS1_notH q hq
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have hNsq : ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 =
        ((q.1 : ℂ).im - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero, hre]
      ring
    have him2 := xiSpectralPoint_im_sq_lt_quarter q
    have hRsq : R ^ 2 < ((q.1 : ℂ).im - t) ^ 2 + 1 / 4 := by
      have := pow_lt_pow_left₀ hdR hR0.le (by decide : 2 ≠ 0)
      linarith
    have hgap : (R - 1) ^ 2 < ((q.1 : ℂ).im - t) ^ 2 := by nlinarith only [hRsq, hR8]
    have habs_gt : R - 1 < |(q.1 : ℂ).im - t| := by
      by_contra hle
      push Not at hle
      have := pow_le_pow_left₀ (abs_nonneg _) hle 2
      rw [sq_abs] at this
      linarith
    rw [Finset.mem_union]
    rcases le_or_gt t (q.1 : ℂ).im with hge | hlt
    · left
      rw [abs_of_nonneg (by linarith)] at habs_gt
      refine Finset.mem_sdiff.mpr ⟨mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; linarith, hpos⟩,
        fun hm => ?_⟩
      have := (mem_xiCopiesPos.mp hm).1
      rw [abs_of_pos hpos] at this
      linarith
    · right
      rw [abs_of_neg (by linarith)] at habs_gt
      refine Finset.mem_sdiff.mpr ⟨mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; linarith, hpos⟩,
        fun hm => ?_⟩
      have := (mem_xiCopiesPos.mp hm).1
      rw [abs_of_pos hpos] at this
      linarith
  have hS1_card : (S1.card : ℝ) ≤ 8 * (1 + C) * Real.log t := by
    have hcard_le : (S1.card : ℝ) ≤
        ((xiCopiesPos (t + R + 1) \ xiCopiesPos (t + R - 1)).card : ℝ) +
          ((xiCopiesPos (t - R + 1) \ xiCopiesPos (t - R - 1)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hS1_sub).trans (Finset.card_union_le _ _)
    have hc1 := card_xiCopiesPos_sdiff_width_two_le hC hT₀ hbase hclose
      (a := t + R - 1) (b := t + R + 1) (by linarith) (by linarith) (by linarith)
    have hc2 := card_xiCopiesPos_sdiff_width_two_le hC hT₀ hbase hclose
      (a := t - R - 1) (b := t - R + 1) (by linarith) (by linarith) (by linarith)
    have hlog_u : Real.log (t + R - 1 + 2) ≤ 2 * Real.log t := by
      calc Real.log (t + R - 1 + 2) ≤ Real.log (t ^ 2) :=
            Real.log_le_log (by positivity) (by nlinarith only [ht64, hRt])
        _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
    have hlog_l : Real.log (t - R - 1 + 2) ≤ Real.log t :=
      Real.log_le_log (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlog_u (by positivity : 0 ≤ 2 * C + 2),
      mul_le_mul_of_nonneg_left hlog_l (by positivity : 0 ≤ 2 * C + 2)]
  -- Distance helper: `|(q.1 : ℂ).im - t| ≤ ‖xiSpectralPoint q - t‖`.
  have hdist_ge_im : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - t| ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := by
    intro q
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    simpa only [Complex.sub_re, Complex.ofReal_re, hre] using
      Complex.abs_re_le_norm (xiSpectralPoint q - (t : ℂ))
  have hrec_le_of_dist : ∀ {q : XiZeroCopy} {B : ℝ}, 0 < B →
      B ≤ ‖xiSpectralPoint q - (t : ℂ)‖ →
      ‖xiSliceGaussianReciprocal t q‖ ≤ 1 / B ^ 2 ∧
        ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤ 1 / B ^ 4 := by
    intro q B hB hd
    have h1 : ‖xiSliceGaussianReciprocal t q‖ ≤ 1 / B ^ 2 := by
      rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div]
      exact one_div_le_one_div_of_le (sq_pos_of_pos hB) (pow_le_pow_left₀ hB.le hd 2)
    refine ⟨h1, ?_⟩
    calc ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤ (1 / B ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 1 / B ^ 4 := by ring
  -- Bounds for `S1`.
  have hS1_b1 : ∑ q ∈ S1, ‖xiSliceGaussianReciprocal t q‖ ≤
      8 * (1 + C) * Real.log t / R ^ 2 := by
    calc ∑ q ∈ S1, ‖xiSliceGaussianReciprocal t q‖
        ≤ ∑ _q ∈ S1, 1 / R ^ 2 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist hR0 (hS1_notH q hq).le).1
      _ = (S1.card : ℝ) * (1 / R ^ 2) := by simp
      _ ≤ (8 * (1 + C) * Real.log t) * (1 / R ^ 2) :=
          mul_le_mul_of_nonneg_right hS1_card (by positivity)
      _ = 8 * (1 + C) * Real.log t / R ^ 2 := by ring
  have hS1_b2 : ∑ q ∈ S1, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      8 * (1 + C) * Real.log t / R ^ 4 := by
    calc ∑ q ∈ S1, ‖xiSliceGaussianReciprocal t q‖ ^ 2
        ≤ ∑ _q ∈ S1, 1 / R ^ 4 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist hR0 (hS1_notH q hq).le).2
      _ = (S1.card : ℝ) * (1 / R ^ 4) := by simp
      _ ≤ (8 * (1 + C) * Real.log t) * (1 / R ^ 4) :=
          mul_le_mul_of_nonneg_right hS1_card (by positivity)
      _ = 8 * (1 + C) * Real.log t / R ^ 4 := by ring
  -- Bounds for `S2` (`0 < Im q ≤ t - K`).
  have hS2_card : (S2.card : ℝ) ≤ (1 + C) * t * Real.log t := by
    have hsub : S2 ⊆ xiCopiesPos t := fun q hq => by
      obtain ⟨_, hpos, hle⟩ := Finset.mem_filter.mp hq
      exact mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; linarith [Nat.cast_nonneg K], hpos⟩
    exact (by exact_mod_cast Finset.card_le_card hsub : (S2.card : ℝ) ≤ _).trans
      (card_xiCopiesPos_le_mul_log hC hT₀ hbase0 hclose htT0)
  have hS2_dist : ∀ q ∈ S2, t / 3 ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := fun q hq => by
    obtain ⟨_, _, hle⟩ := Finset.mem_filter.mp hq
    refine (le_trans ?_ (le_abs_self (t - (q.1 : ℂ).im))).trans
      ((abs_sub_comm _ _).trans_le (hdist_ge_im q))
    linarith
  have hS2_b1 : ∑ q ∈ S2, ‖xiSliceGaussianReciprocal t q‖ ≤
      9 * (1 + C) * Real.log t / t := by
    calc ∑ q ∈ S2, ‖xiSliceGaussianReciprocal t q‖
        ≤ ∑ _q ∈ S2, 1 / (t / 3) ^ 2 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist (by positivity) (hS2_dist q hq)).1
      _ = (S2.card : ℝ) * (9 / t ^ 2) := by simp; ring
      _ ≤ ((1 + C) * t * Real.log t) * (9 / t ^ 2) :=
          mul_le_mul_of_nonneg_right hS2_card (by positivity)
      _ = 9 * (1 + C) * Real.log t / t := by field_simp [ht0.ne']; ring
  have hRt_pow : ∀ A : ℝ, 0 ≤ A → A / t ^ 3 ≤ A / (t ^ 2 * R) := fun A hA =>
    div_le_div_of_nonneg_left hA (by positivity)
      (by have : R ≤ t := by linarith; calc t ^ 2 * R ≤ t ^ 2 * t :=
            mul_le_mul_of_nonneg_left this (by positivity)
          _ = t ^ 3 := by ring)
  have hS2_b2 : ∑ q ∈ S2, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      81 * (1 + C) * Real.log t / (t ^ 2 * R) := by
    refine (le_trans ?_ (hRt_pow (81 * (1 + C) * Real.log t) (by positivity)))
    calc ∑ q ∈ S2, ‖xiSliceGaussianReciprocal t q‖ ^ 2
        ≤ ∑ _q ∈ S2, 1 / (t / 3) ^ 4 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist (by positivity) (hS2_dist q hq)).2
      _ = (S2.card : ℝ) * (81 / t ^ 4) := by simp; ring
      _ ≤ ((1 + C) * t * Real.log t) * (81 / t ^ 4) :=
          mul_le_mul_of_nonneg_right hS2_card (by positivity)
      _ = 81 * (1 + C) * Real.log t / t ^ 3 := by field_simp [ht0.ne']; ring
  -- Bounds for `S3` (`-t ≤ Im q < 0`).
  have hS3_card : (S3.card : ℝ) ≤ (1 + C) * t * Real.log t := by
    have hsub : S3.map xiZeroCopyConjEquiv.toEmbedding ⊆ xiCopiesPos t := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hr
      obtain ⟨_, hge, hneg⟩ := Finset.mem_filter.mp hq
      simp only [Equiv.coe_toEmbedding]
      rw [mem_xiCopiesPos, xiZeroCopyConjEquiv_im]
      exact ⟨by rw [abs_of_pos (by linarith)]; linarith, by linarith⟩
    have hcard_eq : (S3.map xiZeroCopyConjEquiv.toEmbedding).card = S3.card := Finset.card_map _
    exact (by exact_mod_cast (hcard_eq ▸ Finset.card_le_card hsub) : (S3.card : ℝ) ≤ _).trans
      (card_xiCopiesPos_le_mul_log hC hT₀ hbase0 hclose htT0)
  have hS3_dist : ∀ q ∈ S3, t ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := fun q hq => by
    obtain ⟨_, _, hneg⟩ := Finset.mem_filter.mp hq
    exact (le_trans (by linarith) (le_abs_self (t - (q.1 : ℂ).im))).trans
      ((abs_sub_comm _ _).trans_le (hdist_ge_im q))
  have hS3_b1 : ∑ q ∈ S3, ‖xiSliceGaussianReciprocal t q‖ ≤
      (1 + C) * Real.log t / t := by
    calc ∑ q ∈ S3, ‖xiSliceGaussianReciprocal t q‖
        ≤ ∑ _q ∈ S3, 1 / t ^ 2 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist ht0 (hS3_dist q hq)).1
      _ = (S3.card : ℝ) * (1 / t ^ 2) := by simp
      _ ≤ ((1 + C) * t * Real.log t) * (1 / t ^ 2) :=
          mul_le_mul_of_nonneg_right hS3_card (by positivity)
      _ = (1 + C) * Real.log t / t := by field_simp [ht0.ne']
  have hS3_b2 : ∑ q ∈ S3, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      (1 + C) * Real.log t / (t ^ 2 * R) := by
    refine (le_trans ?_ (hRt_pow ((1 + C) * Real.log t) (by positivity)))
    calc ∑ q ∈ S3, ‖xiSliceGaussianReciprocal t q‖ ^ 2
        ≤ ∑ _q ∈ S3, 1 / t ^ 4 := Finset.sum_le_sum fun q hq =>
          (hrec_le_of_dist ht0 (hS3_dist q hq)).2
      _ = (S3.card : ℝ) * (1 / t ^ 4) := by simp
      _ ≤ ((1 + C) * t * Real.log t) * (1 / t ^ 4) :=
          mul_le_mul_of_nonneg_right hS3_card (by positivity)
      _ = (1 + C) * Real.log t / t ^ 3 := by field_simp [ht0.ne']
  -- Bounds for `S4` (`Im q > t + K`).
  have hS4_far := sum_far_ordinate_inv_pow_le hC hT₀ hbase0 hclose htT0 (by linarith) S4
    fun q hq => by
      have := (Finset.mem_filter.mp hq).2
      linarith [Nat.cast_nonneg K]
  have hS4_dist : ∀ q ∈ S4, (q.1 : ℂ).im / 4 ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := fun q hq => by
    have hgt := (Finset.mem_filter.mp hq).2
    refine (le_trans ?_ (le_abs_self ((q.1 : ℂ).im - t))).trans (hdist_ge_im q)
    linarith [ht3K]
  have hS4_b1 : ∑ q ∈ S4, ‖xiSliceGaussianReciprocal t q‖ ≤
      256 * (1 + C) * Real.log t / t := by
    calc ∑ q ∈ S4, ‖xiSliceGaussianReciprocal t q‖
        ≤ ∑ q ∈ S4, 16 * (1 / ((q.1 : ℂ).im) ^ 2) := Finset.sum_le_sum fun q hq => by
          have him0 : 0 < (q.1 : ℂ).im := by
            have := (Finset.mem_filter.mp hq).2; linarith [Nat.cast_nonneg K]
          refine (hrec_le_of_dist (by positivity) (hS4_dist q hq)).1.trans_eq ?_
          ring
      _ = 16 * ∑ q ∈ S4, 1 / ((q.1 : ℂ).im) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 16 * (16 * (1 + C) * Real.log t / t) :=
          mul_le_mul_of_nonneg_left hS4_far.1 (by norm_num)
      _ = 256 * (1 + C) * Real.log t / t := by ring
  have hS4_b2 : ∑ q ∈ S4, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      4096 * (1 + C) * Real.log t / (t ^ 2 * R) := by
    refine (le_trans ?_ (hRt_pow (4096 * (1 + C) * Real.log t) (by positivity)))
    calc ∑ q ∈ S4, ‖xiSliceGaussianReciprocal t q‖ ^ 2
        ≤ ∑ q ∈ S4, 256 * (1 / ((q.1 : ℂ).im) ^ 4) := Finset.sum_le_sum fun q hq => by
          have him0 : 0 < (q.1 : ℂ).im := by
            have := (Finset.mem_filter.mp hq).2; linarith [Nat.cast_nonneg K]
          refine (hrec_le_of_dist (by positivity) (hS4_dist q hq)).2.trans_eq ?_
          ring
      _ = 256 * ∑ q ∈ S4, 1 / ((q.1 : ℂ).im) ^ 4 := (Finset.mul_sum _ _ _).symm
      _ ≤ 256 * (16 * (1 + C) * Real.log t / t ^ 3) :=
          mul_le_mul_of_nonneg_left hS4_far.2 (by norm_num)
      _ = 4096 * (1 + C) * Real.log t / t ^ 3 := by ring
  -- Bounds for `S5` (`Im q < -t`).
  set S5c := S5.map xiZeroCopyConjEquiv.toEmbedding
  have hS5_far := sum_far_ordinate_inv_pow_le hC hT₀ hbase0 hclose htT0 (by linarith) S5c
    fun r hr => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hr
      simp only [Equiv.coe_toEmbedding]
      rw [xiZeroCopyConjEquiv_im]
      have := (Finset.mem_filter.mp hq).2
      linarith
  have hS5_b1 : ∑ q ∈ S5, ‖xiSliceGaussianReciprocal t q‖ ≤
      16 * (1 + C) * Real.log t / t := by
    calc ∑ q ∈ S5, ‖xiSliceGaussianReciprocal t q‖
        ≤ ∑ q ∈ S5, 1 / (((xiZeroCopyConjEquiv q).1 : ℂ).im) ^ 2 :=
          Finset.sum_le_sum fun q hq => by
            have hneg := (Finset.mem_filter.mp hq).2
            have him_c : 0 < (((xiZeroCopyConjEquiv q).1 : ℂ).im) := by
              rw [xiZeroCopyConjEquiv_im]; linarith
            have hd : (((xiZeroCopyConjEquiv q).1 : ℂ).im) ≤
                ‖xiSpectralPoint q - (t : ℂ)‖ := by
              refine (le_trans ?_ (le_abs_self (t - (q.1 : ℂ).im))).trans
                ((abs_sub_comm _ _).trans_le (hdist_ge_im q))
              rw [xiZeroCopyConjEquiv_im]; linarith
            exact (hrec_le_of_dist him_c hd).1
      _ = ∑ r ∈ S5c, 1 / ((r.1 : ℂ).im) ^ 2 := (Finset.sum_map _ _ _).symm
      _ ≤ 16 * (1 + C) * Real.log t / t := hS5_far.1
  have hS5_b2 : ∑ q ∈ S5, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      16 * (1 + C) * Real.log t / (t ^ 2 * R) := by
    refine (le_trans ?_ (hRt_pow (16 * (1 + C) * Real.log t) (by positivity)))
    calc ∑ q ∈ S5, ‖xiSliceGaussianReciprocal t q‖ ^ 2
        ≤ ∑ q ∈ S5, 1 / (((xiZeroCopyConjEquiv q).1 : ℂ).im) ^ 4 :=
          Finset.sum_le_sum fun q hq => by
            have hneg := (Finset.mem_filter.mp hq).2
            have him_c : 0 < (((xiZeroCopyConjEquiv q).1 : ℂ).im) := by
              rw [xiZeroCopyConjEquiv_im]; linarith
            have hd : (((xiZeroCopyConjEquiv q).1 : ℂ).im) ≤
                ‖xiSpectralPoint q - (t : ℂ)‖ := by
              refine (le_trans ?_ (le_abs_self (t - (q.1 : ℂ).im))).trans
                ((abs_sub_comm _ _).trans_le (hdist_ge_im q))
              rw [xiZeroCopyConjEquiv_im]; linarith
            exact (hrec_le_of_dist him_c hd).2
      _ = ∑ r ∈ S5c, 1 / ((r.1 : ℂ).im) ^ 4 := (Finset.sum_map _ _ _).symm
      _ ≤ 16 * (1 + C) * Real.log t / t ^ 3 := hS5_far.2
  have h1 := hsum_split (fun q => ‖xiSliceGaussianReciprocal t q‖) (fun _ => norm_nonneg _)
  have h2 := hsum_split (fun q => ‖xiSliceGaussianReciprocal t q‖ ^ 2) (fun _ => sq_nonneg _)
  have hpos1 : 0 ≤ (1 + C) * (Real.log t / R ^ 2) := by positivity
  have hpos2 : 0 ≤ (1 + C) * (Real.log t / t) := by positivity
  have hpos3 : 0 ≤ (1 + C) * (Real.log t / R ^ 4) := by positivity
  have hpos4 : 0 ≤ (1 + C) * (Real.log t / (t ^ 2 * R)) := by positivity
  refine ⟨?_, ?_⟩
  · have hsum1 : 8 * (1 + C) * Real.log t / R ^ 2 + 9 * (1 + C) * Real.log t / t +
        (1 + C) * Real.log t / t + 256 * (1 + C) * Real.log t / t +
        16 * (1 + C) * Real.log t / t =
        8 * ((1 + C) * (Real.log t / R ^ 2)) + 282 * ((1 + C) * (Real.log t / t)) := by ring
    have htarget1 : 300 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) =
        300 * ((1 + C) * (Real.log t / R ^ 2)) + 300 * ((1 + C) * (Real.log t / t)) := by ring
    linarith
  · have hsum2 : 8 * (1 + C) * Real.log t / R ^ 4 + 81 * (1 + C) * Real.log t / (t ^ 2 * R) +
        (1 + C) * Real.log t / (t ^ 2 * R) + 4096 * (1 + C) * Real.log t / (t ^ 2 * R) +
        16 * (1 + C) * Real.log t / (t ^ 2 * R) =
        8 * ((1 + C) * (Real.log t / R ^ 4)) + 4194 * ((1 + C) * (Real.log t / (t ^ 2 * R))) := by
      ring
    have htarget2 : 4200 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) =
        4200 * ((1 + C) * (Real.log t / R ^ 4)) +
          4200 * ((1 + C) * (Real.log t / (t ^ 2 * R))) := by ring
    linarith

private theorem pairedOrdWindow_asymptotics {C T₀ t R : ℝ} (hC : 0 < C) (hT₀ : 4 ≤ T₀)
    (hbase : routeKRVMBase + 2 ≤ T₀)
    (hclose : ∀ U : ℝ, T₀ ≤ U → |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U)
    (htT : 2 * T₀ + 16 ≤ t) (ht64 : 64 ≤ t) (hR8 : 8 ≤ R) (hRt : 8 * R ≤ t) :
    let N := Nat.floor R + 1
    let K := Nat.floor (t / 2)
    |∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ -
        Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
      400 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) ∧
    |∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2 -
        Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3)| ≤
      4500 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
  classical
  intro N K
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]; linarith [Real.exp_one_lt_d9]
  have hlog0 : 0 ≤ Real.log t := by linarith
  have hlog_main_pos : 0 ≤ Real.log (t / (2 * Real.pi)) / Real.pi :=
    div_nonneg (Real.log_nonneg (by rw [ one_le_div (by positivity) ]; linarith [Real.pi_lt_four]))
      hpi.le
  have hlog_main_le : Real.log (t / (2 * Real.pi)) / Real.pi ≤ Real.log t := by
    have h1 : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
      Real.log_le_log (by positivity) (div_le_self ht0.le (by linarith))
    calc Real.log (t / (2 * Real.pi)) / Real.pi
        ≤ Real.log t / Real.pi := div_le_div_of_nonneg_right h1 hpi.le
      _ ≤ Real.log t / 1 := div_le_div_of_nonneg_left hlog0 zero_lt_one (by linarith)
      _ = Real.log t := div_one _
  have hRN : R < (N : ℝ) := by dsimp only [N]; push_cast; exact Nat.lt_floor_add_one R
  have hNR1 : (N : ℝ) ≤ R + 1 := by dsimp only [N]; push_cast; linarith [Nat.floor_le hR0.le]
  have hN9 : 9 ≤ N := by
    have : 8 ≤ Nat.floor R := Nat.le_floor hR8
    dsimp only [N]; omega
  have hNm1_R : R / 2 ≤ (N : ℝ) - 1 := by linarith
  have hKt2 : (K : ℝ) ≤ t / 2 := by dsimp only [K]; exact Nat.floor_le (by positivity)
  have ht3K : t / 3 ≤ (K : ℝ) := by
    have : t / 2 - 1 < (K : ℝ) := by dsimp only [K]; linarith [Nat.lt_floor_add_one (t / 2)]
    linarith
  have hNK : N ≤ K := by
    have : (N : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast this.le
  have hKt : (K : ℝ) < t := by linarith
  let ΔN : ℕ → ℝ := fun k => ((upperOrdBin t k).card : ℝ) + ((lowerOrdBin t k).card : ℝ)
  let ΔM : ℕ → ℝ := fun k =>
    (routeKSmoothRVMCount (t + (k : ℝ) + 1) - routeKSmoothRVMCount (t + (k : ℝ))) +
      (routeKSmoothRVMCount (t - (k : ℝ)) - routeKSmoothRVMCount (t - (k : ℝ) - 1))
  let E : ℕ → ℝ := fun j =>
    ((xiZeroCount (t + (j : ℝ)) : ℝ) - routeKSmoothRVMCount (t + (j : ℝ))) -
      ((xiZeroCount (t - (j : ℝ)) : ℝ) - routeKSmoothRVMCount (t - (j : ℝ)))
  have hΔN_eq : ∀ k ∈ Finset.Ico N K, ΔN k = ΔM k + (E (k + 1) - E k) := by
    intro k hk
    have hk2 : (k : ℝ) < (K : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).2
    have hcu : ((upperOrdBin t k).card : ℝ) =
        (xiZeroCount (t + (k : ℝ) + 1) : ℝ) - (xiZeroCount (t + (k : ℝ)) : ℝ) :=
      card_xiCopiesPos_sdiff_eq (by positivity) (by linarith)
    have hcl : ((lowerOrdBin t k).card : ℝ) =
        (xiZeroCount (t - (k : ℝ)) : ℝ) - (xiZeroCount (t - (k : ℝ) - 1) : ℝ) :=
      card_xiCopiesPos_sdiff_eq (by linarith) (by linarith)
    dsimp only [ΔN, ΔM, E]
    rw [hcu, hcl]
    push_cast
    ring
  have hΔN_le : ∀ k ∈ Finset.Ico N K, ΔN k ≤ 8 * (1 + C) * Real.log t := by
    intro k hk
    have hkK : (k : ℝ) < (K : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).2
    have hcu := card_xiCopiesPos_sdiff_width_two_le hC hT₀ hbase hclose
      (a := t + (k : ℝ)) (b := t + (k : ℝ) + 1) (by linarith [Nat.cast_nonneg k])
      (by linarith) (by linarith)
    have hcl := card_xiCopiesPos_sdiff_width_two_le hC hT₀ hbase hclose
      (a := t - (k : ℝ) - 1) (b := t - (k : ℝ)) (by linarith) (by linarith) (by linarith)
    have hlogu : Real.log (t + (k : ℝ) + 2) ≤ 2 * Real.log t := by
      calc Real.log (t + (k : ℝ) + 2) ≤ Real.log (t ^ 2) :=
            Real.log_le_log (by linarith [Nat.cast_nonneg k]) (by nlinarith only [ht64, hkK, hKt2])
        _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
    have hlogl : Real.log (t - (k : ℝ) - 1 + 2) ≤ Real.log t :=
      Real.log_le_log (by linarith) (by linarith [ (show (2 : ℝ) ≤ (k : ℝ) by
        have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (by omega : 2 ≤ k)) ])
    dsimp only [ΔN]
    nlinarith [mul_le_mul_of_nonneg_left hlogu (by positivity : 0 ≤ 2 * C + 2),
      mul_le_mul_of_nonneg_left hlogl (by positivity : 0 ≤ 2 * C + 2)]
  have hE_le : ∀ j : ℕ, N ≤ j → j ≤ K → |E j| ≤ 3 * C * Real.log t := by
    intro j _ hjK
    have hj : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hjK
    have hu := hclose (t + (j : ℝ)) (by linarith [Nat.cast_nonneg j])
    have hl := hclose (t - (j : ℝ)) (by linarith)
    have hlogu : Real.log (t + (j : ℝ)) ≤ 2 * Real.log t := by
      calc Real.log (t + (j : ℝ)) ≤ Real.log (t ^ 2) :=
            Real.log_le_log (by linarith [Nat.cast_nonneg j]) (by nlinarith only [ht64, hj, hKt2])
        _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
    have hlogl : Real.log (t - (j : ℝ)) ≤ Real.log t :=
      Real.log_le_log (by linarith) (by linarith [Nat.cast_nonneg j])
    dsimp only [E]
    refine (abs_sub _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hlogu hC.le, mul_le_mul_of_nonneg_left hlogl hC.le]
  -- Telescoping bounds on `∑ 1/k^p`.
  have hsum_k3 : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 3 ≤ 4 / R ^ 2 := by
    calc ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 3
        ≤ ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k hk =>
            inv_pow_three_le_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)
      _ = 1 / ((N : ℝ) - 1) ^ 2 - 1 / ((K : ℝ) - 1) ^ 2 := by
          have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1) ^ 2) hNK
          convert this using 2 with k
          push_cast; ring
      _ ≤ 1 / ((N : ℝ) - 1) ^ 2 := sub_le_self _ (by positivity)
      _ ≤ 1 / (R / 2) ^ 2 := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) hNm1_R 2)
      _ = 4 / R ^ 2 := by ring
  have hsum_k5 : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 5 ≤ 16 / R ^ 4 := by
    calc ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 5
        ≤ ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4) :=
          Finset.sum_le_sum fun k hk =>
            inv_pow_five_le_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)
      _ = 1 / ((N : ℝ) - 1) ^ 4 - 1 / ((K : ℝ) - 1) ^ 4 := by
          have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1) ^ 4) hNK
          convert this using 2 with k
          push_cast; ring
      _ ≤ 1 / ((N : ℝ) - 1) ^ 4 := sub_le_self _ (by positivity)
      _ ≤ 1 / (R / 2) ^ 4 := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) hNm1_R 4)
      _ = 16 / R ^ 4 := by ring
  have hsum_k2_le : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 ≤ 2 / R := by
    calc ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) :=
          Finset.sum_le_sum fun k hk => by
            have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
              have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (by omega : 2 ≤ k)
            have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
              have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
              have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
              field_simp; ring
            rw [heq]
            exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      _ = 1 / ((N : ℝ) - 1) - 1 / ((K : ℝ) - 1) := by
          have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1)) hNK
          convert this using 2 with k
          push_cast; ring
      _ ≤ 1 / ((N : ℝ) - 1) := sub_le_self _ (div_nonneg zero_le_one (by linarith))
      _ ≤ 1 / (R / 2) := one_div_le_one_div_of_le (by positivity) hNm1_R
      _ = 2 / R := by ring
  have hsum_k4_le : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 ≤ 8 / R ^ 3 := by
    calc ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4
        ≤ ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) ^ 3 - 1 / (k : ℝ) ^ 3) :=
          Finset.sum_le_sum fun k hk =>
            inv_pow_four_le_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)
      _ = 1 / ((N : ℝ) - 1) ^ 3 - 1 / ((K : ℝ) - 1) ^ 3 := by
          have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1) ^ 3) hNK
          convert this using 2 with k
          push_cast; ring
      _ ≤ 1 / ((N : ℝ) - 1) ^ 3 := sub_le_self _ (by positivity)
      _ ≤ 1 / (R / 2) ^ 3 := one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) hNm1_R 3)
      _ = 8 / R ^ 3 := by ring
  -- Part 1: `TailMass` paired window asymptotic.
  have hpart1 : |∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ -
      Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
      400 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
    rw [sum_pairedOrdWindow_eq_sum_Ico _ (by omega) hNK hKt]
    -- Step 1a: discretization `‖rec‖ → 1/k^2`.
    have hdisc1 : |∑ k ∈ Finset.Ico N K,
          (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ +
            ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖) -
        ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 2)| ≤
        256 * (1 + C) * Real.log t / R ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      calc |∑ k ∈ Finset.Ico N K,
            ((∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ +
              ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖) -
              ΔN k * (1 / (k : ℝ) ^ 2))|
          ≤ ∑ k ∈ Finset.Ico N K, ΔN k * (8 / (k : ℝ) ^ 3) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            have hk2 : 2 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
            have heq : (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ +
                ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖) -
                ΔN k * (1 / (k : ℝ) ^ 2) =
                (∑ q ∈ upperOrdBin t k, (‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2)) +
                  (∑ q ∈ lowerOrdBin t k,
                    (‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2)) := by
              dsimp only [ΔN]
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
              simp only [Finset.sum_const, nsmul_eq_mul]
              ring
            rw [heq]
            refine (abs_add_le _ _).trans ?_
            have hu : |∑ q ∈ upperOrdBin t k,
                (‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2)| ≤
                ((upperOrdBin t k).card : ℝ) * (8 / (k : ℝ) ^ 3) := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ q ∈ upperOrdBin t k, |‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2|
                  ≤ ∑ _q ∈ upperOrdBin t k, 8 / (k : ℝ) ^ 3 := Finset.sum_le_sum fun q hq =>
                    (reciprocal_bin_discretization hk2 (Or.inl hq)).1
                _ = ((upperOrdBin t k).card : ℝ) * (8 / (k : ℝ) ^ 3) := by simp
            have hl : |∑ q ∈ lowerOrdBin t k,
                (‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2)| ≤
                ((lowerOrdBin t k).card : ℝ) * (8 / (k : ℝ) ^ 3) := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ q ∈ lowerOrdBin t k, |‖xiSliceGaussianReciprocal t q‖ - 1 / (k : ℝ) ^ 2|
                  ≤ ∑ _q ∈ lowerOrdBin t k, 8 / (k : ℝ) ^ 3 := Finset.sum_le_sum fun q hq =>
                    (reciprocal_bin_discretization hk2 (Or.inr hq)).1
                _ = ((lowerOrdBin t k).card : ℝ) * (8 / (k : ℝ) ^ 3) := by simp
            dsimp only [ΔN]; linarith
        _ ≤ ∑ k ∈ Finset.Ico N K, (64 * (1 + C) * Real.log t) * (1 / (k : ℝ) ^ 3) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have := mul_le_mul_of_nonneg_right (hΔN_le k hk) (by positivity : 0 ≤ 8 / (k : ℝ) ^ 3)
            linarith
        _ = (64 * (1 + C) * Real.log t) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 3 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (64 * (1 + C) * Real.log t) * (4 / R ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_k3 (by positivity)
        _ = 256 * (1 + C) * Real.log t / R ^ 2 := by ring
    -- Step 1b: Abel summation `ΔN k → ΔM k`.
    have habel1 : |∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 2) -
        ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 2)| ≤
        6 * C * Real.log t / R ^ 2 := by
      have heq : ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 2) -
          ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 2) =
          ∑ k ∈ Finset.Ico N K, (E (k + 1) - E k) * (1 / (k : ℝ) ^ 2) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hΔN_eq k hk]; ring
      rw [heq]
      refine (abs_sum_Ico_diff_mul_antitone_le hNK (by positivity) (by positivity) hE_le
        fun k hkN _ => ?_).trans ?_
      · have hk0 : (0 : ℝ) < (k : ℝ) := by
          have : 1 ≤ k := by omega
          exact_mod_cast this
        exact one_div_le_one_div_of_le (sq_pos_of_pos hk0)
          (pow_le_pow_left₀ hk0.le (by push_cast; linarith) 2)
      · calc 2 * (3 * C * Real.log t) * (1 / (N : ℝ) ^ 2)
            ≤ 2 * (3 * C * Real.log t) * (1 / R ^ 2) :=
              mul_le_mul_of_nonneg_left
                (one_div_le_one_div_of_le (sq_pos_of_pos hR0) (pow_le_pow_left₀ hR0.le hRN.le 2))
                (by positivity)
          _ = 6 * C * Real.log t / R ^ 2 := by ring
    -- Step 1c: smooth increment `ΔM k → log(t/(2π))/π`.
    have hsmooth1 : |∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 2) -
        (Real.log (t / (2 * Real.pi)) / Real.pi) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2| ≤
        2 * Real.log t / t := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      calc |∑ k ∈ Finset.Ico N K,
            (ΔM k - Real.log (t / (2 * Real.pi)) / Real.pi) * (1 / (k : ℝ) ^ 2)|
          ≤ ∑ k ∈ Finset.Ico N K, ((1 / t) * (1 / (k : ℝ) ^ 2) + 1 / t ^ 2) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            have hkK : (k : ℝ) ≤ t / 2 :=
              (by exact_mod_cast (Finset.mem_Ico.mp hk).2.le : (k : ℝ) ≤ (K : ℝ)).trans hKt2
            have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
              have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (by omega : 1 ≤ k)
            rw [abs_mul, abs_of_pos (by positivity)]
            have hpm := abs_paired_routeKSmoothRVMCount_sub_main_le (by linarith) hkK
            have h1 : 3 / (Real.pi * t) ≤ 1 / t := by
              rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
            have h2 : (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) * (1 / (k : ℝ) ^ 2) ≤
                1 / t ^ 2 := by
              have hkk : (k : ℝ) * ((k : ℝ) + 1) ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
              rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [sq_pos_of_pos ht0]
            calc |ΔM k - Real.log (t / (2 * Real.pi)) / Real.pi| * (1 / (k : ℝ) ^ 2)
                ≤ (3 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2)) *
                    (1 / (k : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_right hpm (by positivity)
              _ = 3 / (Real.pi * t) * (1 / (k : ℝ) ^ 2) +
                    (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) * (1 / (k : ℝ) ^ 2) := by ring
              _ ≤ (1 / t) * (1 / (k : ℝ) ^ 2) + 1 / t ^ 2 :=
                  add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
        _ = (1 / t) * (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2) +
              ((K - N : ℕ) : ℝ) * (1 / t ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
              nsmul_eq_mul]
        _ ≤ (1 / t) * (2 / R) + (t / 2) * (1 / t ^ 2) := by
            refine add_le_add (mul_le_mul_of_nonneg_left hsum_k2_le (by positivity)) ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact (by exact_mod_cast Nat.sub_le K N : ((K - N : ℕ) : ℝ) ≤ (K : ℝ)).trans hKt2
        _ ≤ 1 / t + 1 / t := by
            have h1 : (1 / t) * (2 / R) ≤ 1 / t := by
              have : 2 / R ≤ 1 := by rw [div_le_one hR0]; linarith
              nlinarith [one_div_pos.mpr ht0]
            have h2 : (t / 2) * (1 / t ^ 2) ≤ 1 / t := by
              rw [show (t / 2) * (1 / t ^ 2) = 1 / (2 * t) by field_simp [ht0.ne']; ring]
              exact one_div_le_one_div_of_le ht0 (by linarith)
            linarith
        _ ≤ 2 * Real.log t / t := by
            rw [show 1 / t + 1 / t = 2 / t by ring]
            exact div_le_div_of_nonneg_right (by linarith) ht0.le
    -- Step 1d: telescoping `∑ 1/k^2 → 1/R`.
    have htel1 : |(Real.log (t / (2 * Real.pi)) / Real.pi) *
          (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2) -
        Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
        5 * Real.log t / R ^ 2 + 3 * Real.log t / t := by
      have hsub : |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - 1 / R| ≤ 5 / R ^ 2 + 3 / t := by
        have h1 : |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - (1 / (N : ℝ) - 1 / (K : ℝ))| ≤
            4 / R ^ 2 := by
          have htel := sum_Ico_sub_succ (fun k : ℕ => 1 / (k : ℝ)) hNK
          have htel' : ∑ k ∈ Finset.Ico N K, (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) =
              1 / (N : ℝ) - 1 / (K : ℝ) := by
            convert htel using 2 with k; push_cast; rfl
          rw [← htel', ← Finset.sum_sub_distrib, abs_of_nonneg
            (Finset.sum_nonneg fun k hk =>
              (inv_pow_two_sub_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)).1)]
          calc ∑ k ∈ Finset.Ico N K, (1 / (k : ℝ) ^ 2 - (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)))
              ≤ ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) ^ 2 - 1 / (k : ℝ) ^ 2) :=
                Finset.sum_le_sum fun k hk =>
                  (inv_pow_two_sub_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)).2
            _ = 1 / ((N : ℝ) - 1) ^ 2 - 1 / ((K : ℝ) - 1) ^ 2 := by
                have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1) ^ 2) hNK
                convert this using 2 with k; push_cast; ring
            _ ≤ 1 / (R / 2) ^ 2 := (sub_le_self _ (by positivity)).trans
                (one_div_le_one_div_of_le (by positivity)
                  (pow_le_pow_left₀ (by positivity) hNm1_R 2))
            _ = 4 / R ^ 2 := by ring
        have h2 : |1 / (N : ℝ) - 1 / R| ≤ 1 / R ^ 2 := by
          have hNpos : 0 < (N : ℝ) := lt_trans hR0 hRN
          rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hR0 hRN.le)), neg_sub]
          calc 1 / R - 1 / (N : ℝ) = ((N : ℝ) - R) / (R * (N : ℝ)) := by field_simp; ring
            _ ≤ 1 / R ^ 2 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith only [hNR1, hRN, hR0]
        have h3 : 1 / (K : ℝ) ≤ 3 / t := by
          calc 1 / (K : ℝ) ≤ 1 / (t / 3) := one_div_le_one_div_of_le (by positivity) ht3K
            _ = 3 / t := by ring
        have hsplit : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - 1 / R =
            (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - (1 / (N : ℝ) - 1 / (K : ℝ))) +
              (1 / (N : ℝ) - 1 / R) - 1 / (K : ℝ) := by ring
        rw [hsplit]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (by linarith [one_div_pos.mpr (lt_of_lt_of_le (by positivity) ht3K)])]
        linarith [abs_add_le
          (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - (1 / (N : ℝ) - 1 / (K : ℝ)))
          (1 / (N : ℝ) - 1 / R)]
      have hrew : (Real.log (t / (2 * Real.pi)) / Real.pi) *
            (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2) -
          Real.log (t / (2 * Real.pi)) / (Real.pi * R) =
          (Real.log (t / (2 * Real.pi)) / Real.pi) *
            (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - 1 / R) := by
        field_simp [Real.pi_ne_zero, hR0.ne']; ring
      rw [hrew, abs_mul, abs_of_nonneg hlog_main_pos]
      calc (Real.log (t / (2 * Real.pi)) / Real.pi) *
            |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2 - 1 / R|
          ≤ Real.log t * (5 / R ^ 2 + 3 / t) :=
            mul_le_mul hlog_main_le hsub (abs_nonneg _) hlog0
        _ = 5 * Real.log t / R ^ 2 + 3 * Real.log t / t := by ring
    -- Triangle inequality for Part 1.
    set A1 := ∑ k ∈ Finset.Ico N K,
      (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ +
        ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖)
    set A2 := ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 2)
    set A3 := ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 2)
    set A4 := (Real.log (t / (2 * Real.pi)) / Real.pi) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2
    set A5 := Real.log (t / (2 * Real.pi)) / (Real.pi * R)
    have htri : |A1 - A5| ≤ |A1 - A2| + |A2 - A3| + |A3 - A4| + |A4 - A5| := by
      have : A1 - A5 = (A1 - A2) + (A2 - A3) + (A3 - A4) + (A4 - A5) := by ring
      rw [this]
      linarith [abs_add_le ((A1 - A2) + (A2 - A3) + (A3 - A4)) (A4 - A5),
        abs_add_le ((A1 - A2) + (A2 - A3)) (A3 - A4), abs_add_le (A1 - A2) (A2 - A3)]
    have hp1 : 0 ≤ Real.log t / R ^ 2 := by positivity
    have hp2 : 0 ≤ Real.log t / t := by positivity
    have hpC1 : 0 ≤ C * (Real.log t / R ^ 2) := by positivity
    have hpC2 : 0 ≤ C * (Real.log t / t) := by positivity
    have hsum_err : 256 * (1 + C) * Real.log t / R ^ 2 + 6 * C * Real.log t / R ^ 2 +
        2 * Real.log t / t + (5 * Real.log t / R ^ 2 + 3 * Real.log t / t) =
        261 * (Real.log t / R ^ 2) + 262 * (C * (Real.log t / R ^ 2)) +
          5 * (Real.log t / t) := by ring
    have htarget : 400 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) =
        400 * (Real.log t / R ^ 2) + 400 * (C * (Real.log t / R ^ 2)) +
          400 * (Real.log t / t) + 400 * (C * (Real.log t / t)) := by ring
    linarith
  refine ⟨hpart1, ?_⟩
  -- Part 2: `TailFourth` paired window asymptotic.
  rw [sum_pairedOrdWindow_eq_sum_Ico _ (by omega) hNK hKt]
  -- Step 2a: discretization `‖rec‖^2 → 1/k^4`.
  have hdisc2 : |∑ k ∈ Finset.Ico N K,
        (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2 +
          ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2) -
      ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 4)| ≤
      4096 * (1 + C) * Real.log t / R ^ 4 := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.Ico N K,
          ((∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2 +
            ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2) -
            ΔN k * (1 / (k : ℝ) ^ 4))|
        ≤ ∑ k ∈ Finset.Ico N K, ΔN k * (32 / (k : ℝ) ^ 5) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          have hk2 : 2 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
          have heq : (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2 +
              ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2) -
              ΔN k * (1 / (k : ℝ) ^ 4) =
              (∑ q ∈ upperOrdBin t k, (‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4)) +
                (∑ q ∈ lowerOrdBin t k,
                  (‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4)) := by
            dsimp only [ΔN]
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
          rw [heq]
          refine (abs_add_le _ _).trans ?_
          have hu : |∑ q ∈ upperOrdBin t k,
              (‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4)| ≤
              ((upperOrdBin t k).card : ℝ) * (32 / (k : ℝ) ^ 5) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ q ∈ upperOrdBin t k, |‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4|
                ≤ ∑ _q ∈ upperOrdBin t k, 32 / (k : ℝ) ^ 5 := Finset.sum_le_sum fun q hq =>
                  (reciprocal_bin_discretization hk2 (Or.inl hq)).2
              _ = ((upperOrdBin t k).card : ℝ) * (32 / (k : ℝ) ^ 5) := by simp
          have hl : |∑ q ∈ lowerOrdBin t k,
              (‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4)| ≤
              ((lowerOrdBin t k).card : ℝ) * (32 / (k : ℝ) ^ 5) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ q ∈ lowerOrdBin t k, |‖xiSliceGaussianReciprocal t q‖ ^ 2 - 1 / (k : ℝ) ^ 4|
                ≤ ∑ _q ∈ lowerOrdBin t k, 32 / (k : ℝ) ^ 5 := Finset.sum_le_sum fun q hq =>
                  (reciprocal_bin_discretization hk2 (Or.inr hq)).2
              _ = ((lowerOrdBin t k).card : ℝ) * (32 / (k : ℝ) ^ 5) := by simp
          dsimp only [ΔN]; linarith
      _ ≤ ∑ k ∈ Finset.Ico N K, (256 * (1 + C) * Real.log t) * (1 / (k : ℝ) ^ 5) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have := mul_le_mul_of_nonneg_right (hΔN_le k hk) (by positivity : 0 ≤ 32 / (k : ℝ) ^ 5)
          linarith
      _ = (256 * (1 + C) * Real.log t) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 5 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (256 * (1 + C) * Real.log t) * (16 / R ^ 4) :=
          mul_le_mul_of_nonneg_left hsum_k5 (by positivity)
      _ = 4096 * (1 + C) * Real.log t / R ^ 4 := by ring
  -- Step 2b: Abel summation `ΔN k → ΔM k` against `1/k^4`.
  have habel2 : |∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 4) -
      ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 4)| ≤
      6 * C * Real.log t / R ^ 4 := by
    have heq : ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 4) -
        ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 4) =
        ∑ k ∈ Finset.Ico N K, (E (k + 1) - E k) * (1 / (k : ℝ) ^ 4) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hΔN_eq k hk]; ring
    rw [heq]
    refine (abs_sum_Ico_diff_mul_antitone_le hNK (by positivity) (by positivity) hE_le
      fun k hkN _ => ?_).trans ?_
    · have hk0 : (0 : ℝ) < (k : ℝ) := by
        have : 1 ≤ k := by omega
        exact_mod_cast this
      exact one_div_le_one_div_of_le (pow_pos hk0 4)
        (pow_le_pow_left₀ hk0.le (by push_cast; linarith) 4)
    · calc 2 * (3 * C * Real.log t) * (1 / (N : ℝ) ^ 4)
          ≤ 2 * (3 * C * Real.log t) * (1 / R ^ 4) :=
            mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le (pow_pos hR0 4) (pow_le_pow_left₀ hR0.le hRN.le 4))
              (by positivity)
        _ = 6 * C * Real.log t / R ^ 4 := by ring
  -- Step 2c: smooth increment `ΔM k → log(t/(2π))/π` against `1/k^4`.
  have hsmooth2 : |∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 4) -
      (Real.log (t / (2 * Real.pi)) / Real.pi) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4| ≤
      4 * Real.log t / R ^ 4 + 6 * Real.log t / (t ^ 2 * R) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hraw : |∑ k ∈ Finset.Ico N K,
          (ΔM k - Real.log (t / (2 * Real.pi)) / Real.pi) * (1 / (k : ℝ) ^ 4)| ≤
        8 / (t * R ^ 3) + 2 / (t ^ 2 * R) := by
      calc |∑ k ∈ Finset.Ico N K,
            (ΔM k - Real.log (t / (2 * Real.pi)) / Real.pi) * (1 / (k : ℝ) ^ 4)|
          ≤ ∑ k ∈ Finset.Ico N K,
              ((1 / t) * (1 / (k : ℝ) ^ 4) + (1 / t ^ 2) * (1 / (k : ℝ) ^ 2)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
            have hkK : (k : ℝ) ≤ t / 2 :=
              (by exact_mod_cast (Finset.mem_Ico.mp hk).2.le : (k : ℝ) ≤ (K : ℝ)).trans hKt2
            have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
              have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (by omega : 1 ≤ k)
            rw [abs_mul, abs_of_pos (by positivity)]
            have hpm := abs_paired_routeKSmoothRVMCount_sub_main_le (by linarith) hkK
            have h1 : 3 / (Real.pi * t) ≤ 1 / t := by
              rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
            have h2 : (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) * (1 / (k : ℝ) ^ 4) ≤
                (1 / t ^ 2) * (1 / (k : ℝ) ^ 2) := by
              have hkk : (k : ℝ) * ((k : ℝ) + 1) ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
              have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
              rw [div_mul_div_comm, div_mul_div_comm, mul_one, mul_one,
                div_le_div_iff₀ (by positivity) (by positivity)]
              calc (k : ℝ) * ((k : ℝ) + 1) * (t ^ 2 * (k : ℝ) ^ 2)
                  ≤ (2 * (k : ℝ) ^ 2) * (t ^ 2 * (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right hkk (by positivity)
                _ = 2 * (t ^ 2 * (k : ℝ) ^ 4) := by ring
                _ ≤ Real.pi * t ^ 2 * (k : ℝ) ^ 4 := by
                    have : 0 ≤ t ^ 2 * (k : ℝ) ^ 4 := by positivity
                    nlinarith
            calc |ΔM k - Real.log (t / (2 * Real.pi)) / Real.pi| * (1 / (k : ℝ) ^ 4)
                ≤ (3 / (Real.pi * t) + (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2)) *
                    (1 / (k : ℝ) ^ 4) :=
                  mul_le_mul_of_nonneg_right hpm (by positivity)
              _ = 3 / (Real.pi * t) * (1 / (k : ℝ) ^ 4) +
                    (k : ℝ) * ((k : ℝ) + 1) / (Real.pi * t ^ 2) * (1 / (k : ℝ) ^ 4) := by ring
              _ ≤ (1 / t) * (1 / (k : ℝ) ^ 4) + (1 / t ^ 2) * (1 / (k : ℝ) ^ 2) :=
                  add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
        _ = (1 / t) * (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4) +
              (1 / t ^ 2) * (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ (1 / t) * (8 / R ^ 3) + (1 / t ^ 2) * (2 / R) := add_le_add
            (mul_le_mul_of_nonneg_left hsum_k4_le (by positivity))
            (mul_le_mul_of_nonneg_left hsum_k2_le (by positivity))
        _ = 8 / (t * R ^ 3) + 2 / (t ^ 2 * R) := by ring
    have hamgm : 8 / (t * R ^ 3) ≤ 4 / R ^ 4 + 4 / (t ^ 2 * R) := by
      have hnum : 2 * t * R ≤ t ^ 2 + R ^ 3 := by
        have hR23 : R ^ 2 ≤ R ^ 3 := by
          calc R ^ 2 = R ^ 2 * 1 := by ring
            _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = R ^ 3 := by ring
        nlinarith only [sq_nonneg (t - R), hR23]
      have hrhs : 4 / R ^ 4 + 4 / (t ^ 2 * R) = 4 * (t ^ 2 + R ^ 3) / (t ^ 2 * R ^ 4) := by
        field_simp [ht0.ne', hR0.ne']; ring
      rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
      calc 8 * (t ^ 2 * R ^ 4) = (4 * t * R ^ 3) * (2 * t * R) := by ring
        _ ≤ (4 * t * R ^ 3) * (t ^ 2 + R ^ 3) :=
            mul_le_mul_of_nonneg_left hnum (by positivity)
        _ = 4 * (t ^ 2 + R ^ 3) * (t * R ^ 3) := by ring
    have h1 : 8 / (t * R ^ 3) + 2 / (t ^ 2 * R) ≤ 4 / R ^ 4 + 6 / (t ^ 2 * R) := by linarith
    have h2 : 4 / R ^ 4 + 6 / (t ^ 2 * R) ≤
        4 * Real.log t / R ^ 4 + 6 * Real.log t / (t ^ 2 * R) := add_le_add
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
    exact hraw.trans (h1.trans h2)
  -- Step 2d: telescoping `∑ 1/k^4 → 1/(3 R^3)`.
  have htel2 : |(Real.log (t / (2 * Real.pi)) / Real.pi) *
        (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4) -
      Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3)| ≤
      98 * Real.log t / R ^ 4 + 9 * Real.log t / (t ^ 2 * R) := by
    have hsub : |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 - 1 / (3 * R ^ 3)| ≤
        98 / R ^ 4 + 9 / (t ^ 2 * R) := by
      have h1 : |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 -
          (1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / (K : ℝ) ^ 3)| ≤ 96 / R ^ 4 := by
        have htel := sum_Ico_sub_succ (fun k : ℕ => 1 / (k : ℝ) ^ 3) hNK
        have htel' : ∑ k ∈ Finset.Ico N K, (1 / 3) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3) =
            (1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / (K : ℝ) ^ 3) := by
          rw [← Finset.mul_sum]; congr 1
          convert htel using 2 with k; push_cast; rfl
        rw [← htel', ← Finset.sum_sub_distrib, abs_of_nonneg
          (Finset.sum_nonneg fun k hk =>
            (inv_pow_four_sub_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)).1)]
        calc ∑ k ∈ Finset.Ico N K,
              (1 / (k : ℝ) ^ 4 - (1 / 3) * (1 / (k : ℝ) ^ 3 - 1 / ((k : ℝ) + 1) ^ 3))
            ≤ ∑ k ∈ Finset.Ico N K, 6 * (1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4) :=
              Finset.sum_le_sum fun k hk =>
                (inv_pow_four_sub_telescoping (by have := (Finset.mem_Ico.mp hk).1; omega)).2
          _ = 6 * ∑ k ∈ Finset.Ico N K, (1 / ((k : ℝ) - 1) ^ 4 - 1 / (k : ℝ) ^ 4) :=
              (Finset.mul_sum _ _ _).symm
          _ = 6 * (1 / ((N : ℝ) - 1) ^ 4 - 1 / ((K : ℝ) - 1) ^ 4) := by
              congr 1
              have := sum_Ico_sub_succ (fun k : ℕ => 1 / ((k : ℝ) - 1) ^ 4) hNK
              convert this using 2 with k; push_cast; ring
          _ ≤ 6 * (1 / (R / 2) ^ 4) := mul_le_mul_of_nonneg_left
              ((sub_le_self _ (by positivity)).trans
                (one_div_le_one_div_of_le (by positivity)
                  (pow_le_pow_left₀ (by positivity) hNm1_R 4))) (by norm_num)
          _ = 96 / R ^ 4 := by ring
      have h2 : |(1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / R ^ 3)| ≤ 2 / R ^ 4 := by
        have hNpos : 0 < (N : ℝ) := lt_trans hR0 hRN
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
          abs_of_nonpos (sub_nonpos.mpr
            (one_div_le_one_div_of_le (pow_pos hR0 3) (pow_le_pow_left₀ hR0.le hRN.le 3))),
          neg_sub]
        have hdiff3 : (N : ℝ) ^ 3 - R ^ 3 ≤ 4 * R ^ 2 := by
          have : (N : ℝ) ^ 3 ≤ (R + 1) ^ 3 := pow_le_pow_left₀ hNpos.le hNR1 3
          nlinarith only [this, hR8]
        calc (1 / 3) * (1 / R ^ 3 - 1 / (N : ℝ) ^ 3)
            = ((N : ℝ) ^ 3 - R ^ 3) / (3 * R ^ 3 * (N : ℝ) ^ 3) := by field_simp; ring
          _ ≤ 2 / R ^ 4 := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              have hRN3 : R ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hR0.le hRN.le 3
              calc ((N : ℝ) ^ 3 - R ^ 3) * R ^ 4
                  ≤ (4 * R ^ 2) * R ^ 4 := mul_le_mul_of_nonneg_right hdiff3 (by positivity)
                _ = 4 * R ^ 6 := by ring
                _ ≤ 6 * R ^ 6 := by nlinarith [pow_pos hR0 6]
                _ = 2 * (3 * R ^ 3 * R ^ 3) := by ring
                _ ≤ 2 * (3 * R ^ 3 * (N : ℝ) ^ 3) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hRN3 (by positivity)) (by norm_num)
      have h3 : (1 / 3) * (1 / (K : ℝ) ^ 3) ≤ 9 / (t ^ 2 * R) := by
        have ht2R : t ^ 2 * R ≤ t ^ 3 := by
          have : R ≤ t := by linarith
          calc t ^ 2 * R ≤ t ^ 2 * t := mul_le_mul_of_nonneg_left this (by positivity)
            _ = t ^ 3 := by ring
        calc (1 / 3) * (1 / (K : ℝ) ^ 3)
            ≤ (1 / 3) * (1 / (t / 3) ^ 3) := mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le (by positivity)
                (pow_le_pow_left₀ (by positivity) ht3K 3)) (by norm_num)
          _ = 9 / t ^ 3 := by ring
          _ ≤ 9 / (t ^ 2 * R) := div_le_div_of_nonneg_left (by norm_num) (by positivity) ht2R
      have hsplit : ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 - 1 / (3 * R ^ 3) =
          (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 -
            (1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / (K : ℝ) ^ 3)) +
            (1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / R ^ 3) - (1 / 3) * (1 / (K : ℝ) ^ 3) := by ring
      rw [hsplit]
      refine (abs_sub _ _).trans ?_
      have hKpos : 0 < (K : ℝ) := lt_of_lt_of_le (by positivity) ht3K
      rw [abs_of_pos (by positivity)]
      linarith [abs_add_le
        (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 -
          (1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / (K : ℝ) ^ 3))
        ((1 / 3) * (1 / (N : ℝ) ^ 3 - 1 / R ^ 3))]
    have hrew : (Real.log (t / (2 * Real.pi)) / Real.pi) *
          (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4) -
        Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3) =
        (Real.log (t / (2 * Real.pi)) / Real.pi) *
          (∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 - 1 / (3 * R ^ 3)) := by
      field_simp [Real.pi_ne_zero, hR0.ne']; ring
    rw [hrew, abs_mul, abs_of_nonneg hlog_main_pos]
    calc (Real.log (t / (2 * Real.pi)) / Real.pi) *
          |∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4 - 1 / (3 * R ^ 3)|
        ≤ Real.log t * (98 / R ^ 4 + 9 / (t ^ 2 * R)) :=
          mul_le_mul hlog_main_le hsub (abs_nonneg _) hlog0
      _ = 98 * Real.log t / R ^ 4 + 9 * Real.log t / (t ^ 2 * R) := by ring
  -- Triangle inequality for Part 2.
  set B1 := ∑ k ∈ Finset.Ico N K,
    (∑ q ∈ upperOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2 +
      ∑ q ∈ lowerOrdBin t k, ‖xiSliceGaussianReciprocal t q‖ ^ 2)
  set B2 := ∑ k ∈ Finset.Ico N K, ΔN k * (1 / (k : ℝ) ^ 4)
  set B3 := ∑ k ∈ Finset.Ico N K, ΔM k * (1 / (k : ℝ) ^ 4)
  set B4 := (Real.log (t / (2 * Real.pi)) / Real.pi) * ∑ k ∈ Finset.Ico N K, 1 / (k : ℝ) ^ 4
  set B5 := Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3)
  have htri2 : |B1 - B5| ≤ |B1 - B2| + |B2 - B3| + |B3 - B4| + |B4 - B5| := by
    have : B1 - B5 = (B1 - B2) + (B2 - B3) + (B3 - B4) + (B4 - B5) := by ring
    rw [this]
    linarith [abs_add_le ((B1 - B2) + (B2 - B3) + (B3 - B4)) (B4 - B5),
      abs_add_le ((B1 - B2) + (B2 - B3)) (B3 - B4), abs_add_le (B1 - B2) (B2 - B3)]
  have hp1 : 0 ≤ Real.log t / R ^ 4 := by positivity
  have hp2 : 0 ≤ Real.log t / (t ^ 2 * R) := by positivity
  have hpC1 : 0 ≤ C * (Real.log t / R ^ 4) := by positivity
  have hpC2 : 0 ≤ C * (Real.log t / (t ^ 2 * R)) := by positivity
  have hsum_err2 : 4096 * (1 + C) * Real.log t / R ^ 4 + 6 * C * Real.log t / R ^ 4 +
      (4 * Real.log t / R ^ 4 + 6 * Real.log t / (t ^ 2 * R)) +
      (98 * Real.log t / R ^ 4 + 9 * Real.log t / (t ^ 2 * R)) =
      4198 * (Real.log t / R ^ 4) + 4102 * (C * (Real.log t / R ^ 4)) +
        15 * (Real.log t / (t ^ 2 * R)) := by ring
  have htarget2 : 4500 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) =
      4500 * (Real.log t / R ^ 4) + 4500 * (C * (Real.log t / R ^ 4)) +
        4500 * (Real.log t / (t ^ 2 * R)) + 4500 * (C * (Real.log t / (t ^ 2 * R))) := by ring
  linarith

/-- **Subconvexity-free Riemann–von Mangoldt summation-by-parts cumulant asymptotics.**
Using only `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder` and `xiCopiesPos`, there exist
explicit constants `C₁ > 0` and `T₁ ≥ 64` such that for all `T₁ ≤ t`, `8 ≤ R`, and `8 R ≤ t`
(with `H = xiSliceGaussianRadiusHead t R`):
1. `|xiSliceGaussianTailMass t H - log(t/(2π)) / (π R)| ≤ C₁ (log t / R² + log t / t)`,
2. `|(xiSliceGaussianTailQuadratic t H).re - log(t/(2π)) / (π R)| ≤ C₁ (log t / R² + log t / t)`,
3. `|xiSliceGaussianTailFourth t H - log(t/(2π)) / (3π R³)| ≤ C₁ (log t / R⁴ + log t / (t² R))`. -/
theorem exists_xiSliceGaussianTail_cumulant_asymptotics :
    ∃ C₁ T₁ : ℝ, 0 < C₁ ∧ 64 ≤ T₁ ∧ ∀ t R : ℝ,
      T₁ ≤ t → 8 ≤ R → 8 * R ≤ t →
        let H := xiSliceGaussianRadiusHead t R
        |xiSliceGaussianTailMass t H - Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
          C₁ * (Real.log t / R ^ 2 + Real.log t / t) ∧
        |(xiSliceGaussianTailQuadratic t H).re - Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
          C₁ * (Real.log t / R ^ 2 + Real.log t / t) ∧
        |xiSliceGaussianTailFourth t H - Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3)| ≤
          C₁ * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
  classical
  obtain ⟨C, hC, T₀', hT₀', hclose'⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  set T₀ : ℝ := max T₀' (routeKRVMBase + 2)
  have hT₀4 : 4 ≤ T₀ := hT₀'.trans (le_max_left _ _)
  have hbase : routeKRVMBase + 2 ≤ T₀ := le_max_right _ _
  have hclose : ∀ U : ℝ, T₀ ≤ U →
      |(xiZeroCount U : ℝ) - routeKSmoothRVMCount U| ≤ C * Real.log U :=
    fun U hU => hclose' U ((le_max_left _ _).trans hU)
  set T₁ : ℝ := max (2 * T₀ + 16) 64
  set C₁ : ℝ := 9000 * (1 + C)
  refine ⟨C₁, T₁, by dsimp only [C₁]; positivity, le_max_right _ _,
    fun t R ht hR8 hRt => ?_⟩
  intro H
  have htT : 2 * T₀ + 16 ≤ t := (le_max_left _ _).trans ht
  have ht64 : 64 ≤ t := (le_max_right _ _).trans ht
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  set N := Nat.floor R + 1
  set K := Nat.floor (t / 2)
  have hRN : R < (N : ℝ) := by dsimp only [N]; push_cast; exact Nat.lt_floor_add_one R
  -- Every `q ∈ pairedOrdWindow t N K` lies outside `H`.
  have hout : ∀ q ∈ pairedOrdWindow t N K, q ∉ H := by
    intro q hq
    rw [mem_xiSliceGaussianRadiusHead]
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have hdist : |(q.1 : ℂ).im - t| ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re, hre] using
        Complex.abs_re_le_norm (xiSpectralPoint q - (t : ℂ))
    have him_N : (N : ℝ) ≤ |(q.1 : ℂ).im - t| := by
      rcases Finset.mem_union.mp hq with h | h
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp h
        have hpos := (mem_xiCopiesPos.mp h1).2
        have hgt : t + (N : ℝ) < (q.1 : ℂ).im := lt_of_not_ge fun hle =>
          h2 (mem_xiCopiesPos.mpr ⟨by rw [abs_of_pos hpos]; exact hle, hpos⟩)
        rw [abs_of_pos (by linarith)]; linarith
      · obtain ⟨h1, _⟩ := Finset.mem_sdiff.mp h
        obtain ⟨h1a, hpos⟩ := mem_xiCopiesPos.mp h1
        rw [abs_of_pos hpos] at h1a
        rw [abs_of_neg (by linarith)]; linarith
    exact not_le.mpr (lt_of_lt_of_le hRN (him_N.trans hdist))
  -- Lower bounds: `pairedOrdWindow ≤ tsum`.
  have hlo_mass : ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ≤
      xiSliceGaussianTailMass t H := by
    rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖) hout]
    exact (summable_norm_xiSliceGaussianTail t H).sum_le_tsum _ (fun _ _ => norm_nonneg _)
  have hlo_fourth : ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      xiSliceGaussianTailFourth t H := by
    rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖ ^ 2) hout]
    exact (summable_sq_norm_xiSliceGaussianTail t H).sum_le_tsum _ (fun _ _ => sq_nonneg _)
  -- Upper bounds: `tsum ≤ pairedOrdWindow + compl_bound`.
  have hhi_mass : xiSliceGaussianTailMass t H ≤
      ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ +
        300 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
    refine (summable_norm_xiSliceGaussianTail t H).tsum_le_of_sum_le fun F => ?_
    let e : {q : XiZeroCopy // q ∉ H} ↪ XiZeroCopy := ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : ∑ x ∈ F, ‖xiSliceGaussianReciprocal t x.1‖ =
        ∑ q ∈ F.map e, ‖xiSliceGaussianReciprocal t q‖ := (Finset.sum_map F e _).symm
    rw [hmap, ← Finset.sum_filter_add_sum_filter_not (F.map e) (fun q => q ∈ pairedOrdWindow t N K)]
    have hsub : (F.map e).filter (fun q => q ∈ pairedOrdWindow t N K) ⊆ pairedOrdWindow t N K :=
      fun _ hq => (Finset.mem_filter.mp hq).2
    exact add_le_add
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _)
      (compl_pairedOrdWindow_le hC hT₀4 hbase hclose htT ht64 hR8 hRt F).1
  have hhi_fourth : xiSliceGaussianTailFourth t H ≤
      ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2 +
        4200 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
    refine (summable_sq_norm_xiSliceGaussianTail t H).tsum_le_of_sum_le fun F => ?_
    let e : {q : XiZeroCopy // q ∉ H} ↪ XiZeroCopy := ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : ∑ x ∈ F, ‖xiSliceGaussianReciprocal t x.1‖ ^ 2 =
        ∑ q ∈ F.map e, ‖xiSliceGaussianReciprocal t q‖ ^ 2 := (Finset.sum_map F e _).symm
    rw [hmap, ← Finset.sum_filter_add_sum_filter_not (F.map e) (fun q => q ∈ pairedOrdWindow t N K)]
    have hsub : (F.map e).filter (fun q => q ∈ pairedOrdWindow t N K) ⊆ pairedOrdWindow t N K :=
      fun _ hq => (Finset.mem_filter.mp hq).2
    exact add_le_add
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _)
      (compl_pairedOrdWindow_le hC hT₀4 hbase hclose htT ht64 hR8 hRt F).2
  obtain ⟨hp_mass, hp_fourth⟩ := pairedOrdWindow_asymptotics hC hT₀4 hbase hclose htT ht64 hR8 hRt
  dsimp only at hp_mass hp_fourth
  have hmass_err : |xiSliceGaussianTailMass t H -
      Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
      700 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
    have h1 : |xiSliceGaussianTailMass t H -
        ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖| ≤
        300 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlo_mass)]
      linarith
    have htri := abs_add_le
      (xiSliceGaussianTailMass t H - ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖)
      (∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ -
        Real.log (t / (2 * Real.pi)) / (Real.pi * R))
    rw [sub_add_sub_cancel] at htri
    linarith
  have hfourth_err : |xiSliceGaussianTailFourth t H -
      Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3)| ≤
      8700 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
    have h1 : |xiSliceGaussianTailFourth t H -
        ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2| ≤
        4200 * (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlo_fourth)]
      linarith
    have htri := abs_add_le
      (xiSliceGaussianTailFourth t H -
        ∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2)
      (∑ q ∈ pairedOrdWindow t N K, ‖xiSliceGaussianReciprocal t q‖ ^ 2 -
        Real.log (t / (2 * Real.pi)) / (3 * Real.pi * R ^ 3))
    rw [sub_add_sub_cancel] at htri
    linarith
  -- Transfer `TailMass` asymptotic to `(TailQuadratic).re` via `norm_xiSliceGaussianTailQuadratic_sub_mass_le`.
  have hquad_diff : |(xiSliceGaussianTailQuadratic t H).re - xiSliceGaussianTailMass t H| ≤
      xiSliceGaussianTailMass t H / R := by
    calc |(xiSliceGaussianTailQuadratic t H).re - xiSliceGaussianTailMass t H|
        = |(xiSliceGaussianTailQuadratic t H - (xiSliceGaussianTailMass t H : ℂ)).re| := by simp
      _ ≤ ‖xiSliceGaussianTailQuadratic t H - (xiSliceGaussianTailMass t H : ℂ)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ xiSliceGaussianTailMass t H / R := norm_xiSliceGaussianTailQuadratic_sub_mass_le t hR0
  have hmass_upper : xiSliceGaussianTailMass t H ≤
      (701 * (1 + C)) * (Real.log t / R) + (700 * (1 + C)) * (Real.log t / t) := by
    have hmain_le : Real.log (t / (2 * Real.pi)) / (Real.pi * R) ≤ Real.log t / R := by
      have h1 : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
        Real.log_le_log (by positivity) (div_le_self ht0.le (by linarith [Real.pi_gt_three]))
      calc Real.log (t / (2 * Real.pi)) / (Real.pi * R)
          ≤ Real.log t / (Real.pi * R) := div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ Real.log t / (1 * R) := div_le_div_of_nonneg_left hlog0 hR0
            (mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hR0.le)
        _ = Real.log t / R := by ring
    have hR2_le : Real.log t / R ^ 2 ≤ Real.log t / R :=
      div_le_div_of_nonneg_left hlog0 hR0 (by nlinarith only [hR8])
    have hm := (abs_le.mp hmass_err).2
    have : Real.log t / R ≤ (1 + C) * (Real.log t / R) := by
      have : 0 ≤ C * (Real.log t / R) := by positivity
      linarith
    have hrew : 700 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) =
        700 * ((1 + C) * (Real.log t / R ^ 2)) + 700 * ((1 + C) * (Real.log t / t)) := by ring
    have h700 : (1 + C) * (Real.log t / R ^ 2) ≤ (1 + C) * (Real.log t / R) :=
      mul_le_mul_of_nonneg_left hR2_le (by positivity)
    linarith
  have hquad_div_R : xiSliceGaussianTailMass t H / R ≤
      701 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
    have htR_le : Real.log t / (t * R) ≤ Real.log t / t :=
      div_le_div_of_nonneg_left hlog0 ht0 (by nlinarith only [hR8, ht0])
    calc xiSliceGaussianTailMass t H / R
        ≤ ((701 * (1 + C)) * (Real.log t / R) + (700 * (1 + C)) * (Real.log t / t)) / R :=
          div_le_div_of_nonneg_right hmass_upper hR0.le
      _ = 701 * (1 + C) * (Real.log t / R ^ 2) + 700 * (1 + C) * (Real.log t / (t * R)) := by
          field_simp [hR0.ne']; ring
      _ ≤ 701 * (1 + C) * (Real.log t / R ^ 2) + 701 * (1 + C) * (Real.log t / t) := by
          refine add_le_add le_rfl ?_
          calc 700 * (1 + C) * (Real.log t / (t * R))
              ≤ 700 * (1 + C) * (Real.log t / t) :=
                mul_le_mul_of_nonneg_left htR_le (by positivity)
            _ ≤ 701 * (1 + C) * (Real.log t / t) := by
                have : 0 ≤ (1 + C) * (Real.log t / t) := by positivity
                linarith
      _ = 701 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by ring
  have hquad_err : |(xiSliceGaussianTailQuadratic t H).re -
      Real.log (t / (2 * Real.pi)) / (Real.pi * R)| ≤
      1401 * (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by
    have htri := abs_add_le
      ((xiSliceGaussianTailQuadratic t H).re - xiSliceGaussianTailMass t H)
      (xiSliceGaussianTailMass t H - Real.log (t / (2 * Real.pi)) / (Real.pi * R))
    rw [sub_add_sub_cancel] at htri
    linarith [hquad_diff.trans hquad_div_R]
  have hp1 : 0 ≤ (1 + C) * (Real.log t / R ^ 2 + Real.log t / t) := by positivity
  have hp2 : 0 ≤ (1 + C) * (Real.log t / R ^ 4 + Real.log t / (t ^ 2 * R)) := by positivity
  dsimp only [C₁]
  exact ⟨by linarith, by linarith, by linarith⟩
