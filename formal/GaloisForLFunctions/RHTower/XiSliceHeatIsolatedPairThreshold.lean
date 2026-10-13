import GaloisForLFunctions.RHTower.XiSliceHeatHermiteRepresentation
import GaloisForLFunctions.RHTower.DeBruijnDefectPairPersistence
import GaloisForLFunctions.RHTower.XiSliceHeatTransferNoSlack
import GaloisForLFunctions.RHTower.XiSliceHeatPerPairPositivity
import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The WD heat threshold of an isolated off-line pair

Let `S(t, y) = ξ(½+y+it) ξ(½−y+it)` and `T_n(λ, 0, t)` the heated slice coefficients.

**Theorem** (`re_xiSliceHeatTransfer_two_neg_of_offline_zero`).  Let `ρ = ½ + b + iγ` (`b > 0`) be a
zero of `ξ` and `λ > 0`.  Write `g = xiPairQuotient γ b` (so `Ξ = ((z − γ)² + b²) g`) and
`G(y) = g(γ − iy) g(γ + iy)`.  If

  `|∫ g₂(w) (b² − λw²)² (G(√λ w) − g(γ)²) dw| < √(2π)(4b²λ − 12λ²) g(γ)²`,

with `g₂(w) = (w² − 1)e^{−w²/2}`, then `Re T₂(λ, 0, γ) < 0`; hence `λ ≤ λ_WD`
(`le_wdHeatThreshold_of_offline_pair`).

At the ordinate the slice factors as `S(γ, y) = (b² − y²)² G(y)` (`xiSliceProduct_eq_pair_mul`), and
`g(γ) = Ξ(γ)/b²` is real (`xiPairQuotient_self_eq`).  The Hermite representation
`∫ g₂(w) S(γ, √λ w) dw = 2√(2π) λ T₂(λ, 0, γ)` (`integral_hermiteGauss_mul_xiSliceProduct`) and the
Gaussian moments `∫ g₂(w)(b² − λw²)² dw = √(2π)(12λ² − 4b²λ)` (`integral_hermiteGauss_two_mul_pairSlice`)
split `2√(2π)λ T₂` into `√(2π)(12λ² − 4b²λ) g(γ)²` plus the cofactor deviation.  The main term is
negative exactly when `3λ < b²`.

So when the cofactor varies little on the scale `√λ`, the WD threshold is at least the per-pair heat
`b²/3`, which matches the per-pair upper bound `λ_WD ≤ sup b²/3` (`mem_wdHeatAdmissible_of_im_sq_le`).
With the de Bruijn–Newman analogue `Λ₊ > t` for `2t < b²`
(`DeBruijn.lt_newmanConstant_of_offline_zero`) both thresholds are attained by isolated deepest pairs,
in the ratio `(b²/3)/(b²/2) = 2/3` (`isolatedDeepestPair_threshold_bounds`).
-/

open Complex MeasureTheory Polynomial Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

theorem hermiteGauss_two (x : ℝ) : hermiteGauss 2 x = (x ^ 2 - 1) * Real.exp (-(x ^ 2 / 2)) := by
  unfold hermiteGauss
  congr 1
  simp [hermite_succ]
  ring

theorem exp_neg_sq_half_eq (w : ℝ) :
    Real.exp (-(w ^ 2 / 2)) = Real.sqrt (2 * Real.pi) * gaussDensity (1 / 2) w := by
  unfold gaussDensity
  have hpos : (0 : ℝ) < 4 * Real.pi * (1 / 2) := by positivity
  rw [show 4 * Real.pi * (1 / 2) = 2 * Real.pi by ring, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow, show w ^ 2 / (4 * (1 / 2)) = w ^ 2 / 2 by ring]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

theorem integrable_exp_neg_sq_half_mul_pow (k : ℕ) :
    Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * w ^ k) := by
  refine ((integrable_gaussDensity_mul_pow (by norm_num : (0 : ℝ) < 1 / 2) k).const_mul
    (Real.sqrt (2 * Real.pi))).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [exp_neg_sq_half_eq]
  ring

theorem integral_exp_neg_sq_half_mul_pow_even (m : ℕ) :
    ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * w ^ (2 * m)
      = Real.sqrt (2 * Real.pi) * ((2 * m).factorial * (1 / 2 : ℝ) ^ m / m.factorial) := by
  simp_rw [exp_neg_sq_half_eq, mul_assoc]
  rw [integral_const_mul, integral_gaussDensity_mul_pow_even (by norm_num : (0 : ℝ) < 1 / 2)]

/-- `∫ g₂(w) (b² − λw²)² dw = √(2π)(12λ² − 4b²λ)`. -/
theorem integral_hermiteGauss_two_mul_pairSlice (b lam : ℝ) :
    ∫ w : ℝ, hermiteGauss 2 w * (b ^ 2 - lam * w ^ 2) ^ 2
      = Real.sqrt (2 * Real.pi) * (12 * lam ^ 2 - 4 * b ^ 2 * lam) := by
  set c : ℕ → ℝ := fun m => if m = 0 then -b ^ 4 else if m = 1 then b ^ 4 + 2 * b ^ 2 * lam
    else if m = 2 then -2 * b ^ 2 * lam - lam ^ 2 else lam ^ 2 with hc
  have e : ∀ w : ℝ, hermiteGauss 2 w * (b ^ 2 - lam * w ^ 2) ^ 2
      = ∑ m ∈ Finset.range 4, c m * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * m)) := by
    intro w; rw [hermiteGauss_two]; simp [Finset.sum_range_succ, hc]; ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun m _ => (integrable_exp_neg_sq_half_mul_pow (2 * m)).const_mul _)]
  simp_rw [integral_const_mul, integral_exp_neg_sq_half_mul_pow_even]
  simp [Finset.sum_range_succ, hc, Nat.factorial]
  ring

theorem integrable_hermiteGauss_two_mul_pairSlice (b lam : ℝ) :
    Integrable (fun w : ℝ => hermiteGauss 2 w * (b ^ 2 - lam * w ^ 2) ^ 2) := by
  have hsum : Integrable (fun w : ℝ => (-b ^ 4) * (Real.exp (-(w ^ 2 / 2)) * w ^ 0)
      + (b ^ 4 + 2 * b ^ 2 * lam) * (Real.exp (-(w ^ 2 / 2)) * w ^ 2)
      + (-2 * b ^ 2 * lam - lam ^ 2) * (Real.exp (-(w ^ 2 / 2)) * w ^ 4)
      + lam ^ 2 * (Real.exp (-(w ^ 2 / 2)) * w ^ 6)) :=
    ((((integrable_exp_neg_sq_half_mul_pow 0).const_mul _).add
      ((integrable_exp_neg_sq_half_mul_pow 2).const_mul _)).add
      ((integrable_exp_neg_sq_half_mul_pow 4).const_mul _)).add
      ((integrable_exp_neg_sq_half_mul_pow 6).const_mul _)
  refine hsum.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [hermiteGauss_two]
  ring

/-- At the ordinate of an off-line zero `½ + b + iγ`, the slice factors as
`S(γ, y) = (b² − y²)² · g(γ − iy) g(γ + iy)` with `g = xiPairQuotient γ b`. -/
theorem xiSliceProduct_eq_pair_mul {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (y : ℂ) :
    xiSliceProduct γ y = ((b : ℂ) ^ 2 - y ^ 2) ^ 2 *
      (xiPairQuotient γ b ((γ : ℂ) - y * I) * xiPairQuotient γ b ((γ : ℂ) + y * I)) := by
  have h1 : xi (1 / 2 + y + γ * I) = XiC ((γ : ℂ) - y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have h2 : xi (1 / 2 - y + γ * I) = XiC ((γ : ℂ) + y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have q1 : ((γ : ℂ) - y * I - γ) ^ 2 + (b : ℂ) ^ 2 = (b : ℂ) ^ 2 - y ^ 2 := by
    ring_nf; rw [I_sq]; ring
  have q2 : ((γ : ℂ) + y * I - γ) ^ 2 + (b : ℂ) ^ 2 = (b : ℂ) ^ 2 - y ^ 2 := by
    ring_nf; rw [I_sq]; ring
  unfold xiSliceProduct
  rw [h1, h2, XiC_eq_quadratic_mul_xiPairQuotient hb hz, XiC_eq_quadratic_mul_xiPairQuotient hb hz,
    q1, q2]
  ring

/-- The cofactor is real at the ordinate: `g(γ) = Ξ(γ)/b²`. -/
theorem xiPairQuotient_self_eq {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0) :
    xiPairQuotient γ b γ = (((XiC γ).re / b ^ 2 : ℝ) : ℂ) := by
  have h := XiC_eq_quadratic_mul_xiPairQuotient hb hz γ
  rw [sub_self, zero_pow two_ne_zero, zero_add] at h
  have him : (XiC (γ : ℂ)).im = 0 := by
    have h' := XiC_conj ((γ : ℂ))
    rw [Complex.conj_ofReal] at h'
    exact Complex.conj_eq_iff_im.mp h'.symm
  have hb2 : (b : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hb.ne')
  have hg : xiPairQuotient γ b γ = XiC (γ : ℂ) / ((b ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [eq_div_iff hb2, h]; ring
  rw [hg]
  apply Complex.ext
  · rw [Complex.div_ofReal_re, Complex.ofReal_re]
  · rw [Complex.div_ofReal_im, Complex.ofReal_im, him, zero_div]

/-- **The order-two heated coefficient is negative below the per-pair WD time.**  Let
`½ + b + iγ` be a zero of `ξ` and `0 < 3λ < b²`.  If the cofactor slice
`G(y) = g(γ − iy) g(γ + iy)` deviates from `G(0) = g(γ)²` by less than the Hermite budget
`√(2π)(4b²λ − 12λ²)|g(γ)|²` (weighted by `g₂(w)(b² − λw²)²` at `y = √λ w`), then
`Re T₂(λ, 0, γ) < 0`. -/
theorem re_xiSliceHeatTransfer_two_neg_of_offline_zero {γ b lam : ℝ} (hb : 0 < b)
    (hlam : 0 < lam) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hvar : ‖∫ w : ℝ, (hermiteGauss 2 w : ℂ) *
        (((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (xiPairQuotient γ b ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            xiPairQuotient γ b ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I)
              - xiPairQuotient γ b γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (4 * b ^ 2 * lam - 12 * lam ^ 2) * ‖xiPairQuotient γ b γ‖ ^ 2) :
    (xiSliceHeatTransfer lam 0 γ 2).re < 0 := by
  set sl := Real.sqrt lam with hsl
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  set g := xiPairQuotient γ b with hgdef
  set r : ℝ := (XiC γ).re / b ^ 2 with hr
  have hgr : g γ = (r : ℂ) := xiPairQuotient_self_eq hb hz
  set E : ℂ := ∫ w : ℝ, (hermiteGauss 2 w : ℂ) *
      (((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 *
        (g ((γ : ℂ) - ((sl * w : ℝ) : ℂ) * I) * g ((γ : ℂ) + ((sl * w : ℝ) : ℂ) * I) - g γ ^ 2))
    with hE
  set M : ℝ := ∫ w : ℝ, hermiteGauss 2 w * (b ^ 2 - lam * w ^ 2) ^ 2 with hM
  have hMval : M = Real.sqrt (2 * Real.pi) * (12 * lam ^ 2 - 4 * b ^ 2 * lam) :=
    integral_hermiteGauss_two_mul_pairSlice b lam
  -- the main part
  have hP : ∀ w : ℝ, ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2
      = (((b ^ 2 - lam * w ^ 2) ^ 2 : ℝ) : ℂ) := by
    intro w; push_cast; rw [← hsl2]; push_cast; ring
  have hmainInt : Integrable (fun w : ℝ => (hermiteGauss 2 w : ℂ) *
      (((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2)) := by
    refine ((integrable_hermiteGauss_two_mul_pairSlice b lam).ofReal.mul_const (g γ ^ 2)).congr
      (Filter.Eventually.of_forall fun w => ?_)
    show ((hermiteGauss 2 w * (b ^ 2 - lam * w ^ 2) ^ 2 : ℝ) : ℂ) * g γ ^ 2 = _
    rw [← hsl2]
    push_cast
    ring
  have hmain : ∫ w : ℝ, (hermiteGauss 2 w : ℂ) *
      (((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2) = (M : ℂ) * g γ ^ 2 := by
    rw [hM, ← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hP]; push_cast; ring
  -- the Hermite representation and the split
  have hH := integral_hermiteGauss_mul_xiSliceProduct hlam.le γ 2
  have hSint := integrable_hermiteGauss_mul_xiSliceProduct hlam.le γ 2
  have hsplit : ∫ w : ℝ, (hermiteGauss 2 w : ℂ) * xiSliceProduct γ ((sl * w : ℝ) : ℂ)
      = (M : ℂ) * g γ ^ 2 + E := by
    rw [← hmain, hE, ← integral_add hmainInt]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [xiSliceProduct_eq_pair_mul hb hz]
      ring
    · refine (hSint.sub hmainInt).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply, xiSliceProduct_eq_pair_mul hb hz]
      ring
  rw [hsplit] at hH
  -- take real parts
  set T := xiSliceHeatTransfer lam 0 γ 2 with hT
  have hc : (0 : ℝ) < Real.sqrt (2 * Real.pi) * sl ^ 2 * (Nat.factorial 2 : ℝ) := by
    rw [hsl2]; positivity
  have hre := congrArg Complex.re hH
  rw [Complex.re_ofReal_mul, Complex.add_re, hgr] at hre
  have hMr : ((M : ℂ) * (r : ℂ) ^ 2).re = M * r ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hMr] at hre
  have hEle : E.re ≤ ‖E‖ := Complex.re_le_norm E
  have hgn : ‖g γ‖ ^ 2 = r ^ 2 := by rw [hgr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hgn] at hvar
  have hvar' : ‖E‖ < Real.sqrt (2 * Real.pi) * (4 * b ^ 2 * lam - 12 * lam ^ 2) * r ^ 2 := by
    simpa [hE, hsl] using hvar
  have hsum : M * r ^ 2 + E.re < 0 := by
    rw [hMval]; nlinarith
  by_contra hTnn
  push Not at hTnn
  have : 0 ≤ Real.sqrt (2 * Real.pi) * sl ^ 2 * (Nat.factorial 2 : ℝ) * T.re :=
    mul_nonneg hc.le hTnn
  linarith

/-- **The WD threshold is at least the per-pair time of a slowly varying off-line pair.**  Under the
hypotheses of `re_xiSliceHeatTransfer_two_neg_of_offline_zero`, `λ ≤ λ_WD`. -/
theorem le_wdHeatThreshold_of_offline_pair {γ b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hvar : ‖∫ w : ℝ, (hermiteGauss 2 w : ℂ) *
        (((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (xiPairQuotient γ b ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            xiPairQuotient γ b ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I)
              - xiPairQuotient γ b γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (4 * b ^ 2 * lam - 12 * lam ^ 2) * ‖xiPairQuotient γ b γ‖ ^ 2) :
    lam ≤ wdHeatThreshold := by
  by_contra h
  push Not at h
  have hadm := mem_wdHeatAdmissible_of_lt h γ 2
  have hneg := re_xiSliceHeatTransfer_two_neg_of_offline_zero hb hlam hz hvar
  have := (Complex.le_def.mp hadm).1
  simp only [Complex.zero_re] at this
  linarith

/-- **Two-sided threshold law for the deepest isolated pair.**  Let `½ + b + iγ` be a zero of `ξ` of
maximal depth (`(Re ρ − ½)² ≤ b²` for every zero `ρ`).  If its cofactor satisfies the Hermite
variation bound at heat `λ` and the Gaussian variation bound at time `t` (`2t < b²`), then

  `λ ≤ λ_WD ≤ b²/3`  and  `t < Λ₊ ≤ b²/2`.

So both RH-equivalent thresholds sit at their per-pair values, in the ratio `2/3`. -/
theorem isolatedDeepestPair_threshold_bounds {γ b lam t : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    (ht : 0 < t) (htb : 2 * t < b ^ 2) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hmax : ∀ ρ : ℂ, xi ρ = 0 → (ρ.re - 1 / 2) ^ 2 ≤ b ^ 2)
    (hvarWD : ‖∫ w : ℝ, (hermiteGauss 2 w : ℂ) *
        (((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (xiPairQuotient γ b ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            xiPairQuotient γ b ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I)
              - xiPairQuotient γ b γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (4 * b ^ 2 * lam - 12 * lam ^ 2) * ‖xiPairQuotient γ b γ‖ ^ 2)
    (hvarN : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - 2 * t) : ℂ) * I)
        (Real.sqrt (b ^ 2 - 2 * t) / 2),
      xiPairQuotient γ b z ≠ 0 ∧ ∫ u : ℝ, gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖
          * ‖xiPairQuotient γ b (z - I * u) - xiPairQuotient γ b z‖
          < 3 * (b ^ 2 - 2 * t) / 4 * ‖xiPairQuotient γ b z‖) :
    lam ≤ wdHeatThreshold ∧ wdHeatThreshold ≤ b ^ 2 / 3 ∧
      t < newmanConstant ∧ newmanConstant ≤ b ^ 2 / 2 := by
  refine ⟨le_wdHeatThreshold_of_offline_pair hb hlam hz hvarWD, ?_,
    lt_newmanConstant_of_offline_zero hb ht htb hz hvarN, ?_⟩
  · refine csInf_le wdHeatAdmissible_bddBelow (mem_wdHeatAdmissible_of_im_sq_le (by positivity) ?_)
    intro q
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint, Complex.mul_im]
    have h := hmax _ (xi_xiZeroCopy_eq_zero q)
    rw [him]
    nlinarith
  · have h := newmanConstant_le_of_zeros_im_sq_le (s := 0) le_rfl (sq_nonneg b) (fun z hz0 => by
      rw [riemannHeat_zero] at hz0
      have h' := hmax _ hz0
      have hre : (1 / 2 + I * z : ℂ).re = 1 / 2 - z.im := by simp; ring
      rw [hre] at h'
      nlinarith)
    linarith

end

end RHTower.DeBruijn
