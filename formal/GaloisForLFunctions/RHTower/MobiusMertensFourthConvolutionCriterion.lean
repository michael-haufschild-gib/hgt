import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Fourth additive Mertens convolution criterion

The first nonlinear even rung squares the exact second-Cesaro/Mertens series.  If

`U(N) = sum_{a+b=N} M(a)M(b)` and `W(N) = sum_{a+b=N} U(a)U(b)`,

then

`Phi(x)^4 = (1-exp(-x))^4 sum_N W(N) exp(-Nx)`.

A one-sided `W(N) <= N^(5+o(1))` estimate therefore gives every strict half-power bound for the
Mobius--Laplace transform and hence RH.  Conversely, the classical all-strict-half-power Mertens
estimate gives this quartic source family.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Fourth additive convolution of Mertens partial sums, grouped as the self-convolution of the
already formalized second-Cesaro sequence. -/
def mobiusMertensFourthConvolution (N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    mobiusAdditiveTriangleSecondCesaro ab.1 *
      mobiusAdditiveTriangleSecondCesaro ab.2

/-- Fourth Mertens-convolution coefficients are real. -/
theorem mobiusMertensFourthConvolution_im_eq_zero (N : ℕ) :
    (mobiusMertensFourthConvolution N).im = 0 := by
  simp [mobiusMertensFourthConvolution, Complex.mul_im,
    mobiusAdditiveTriangleSecondCesaro_im_eq_zero]

private theorem sum_antidiagonal_secondCesaroWeighted_eq
    (q : ℂ) (N : ℕ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
      (mobiusAdditiveTriangleSecondCesaro ab.1 * q ^ ab.1) *
        (mobiusAdditiveTriangleSecondCesaro ab.2 * q ^ ab.2)) =
      mobiusMertensFourthConvolution N * q ^ N := by
  rw [mobiusMertensFourthConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 = N :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [← hsum, pow_add]
  ring

/-- The quartic coefficient series is absolutely summable at every positive Laplace scale. -/
theorem summable_mobiusMertensFourthConvolution_mul_exp_neg
    {x : ℝ} (hx : 0 < x) :
    Summable (fun N : ℕ => mobiusMertensFourthConvolution N *
      Complex.exp (-(x : ℂ)) ^ N) := by
  let q : ℂ := Complex.exp (-(x : ℂ))
  have hU : Summable (fun N : ℕ =>
      mobiusAdditiveTriangleSecondCesaro N * q ^ N) := by
    simpa only [q] using summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx
  have hconv :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hU.norm hU.norm
  apply Summable.of_norm
  simpa only [sum_antidiagonal_secondCesaroWeighted_eq, q] using hconv

/-- Cauchy product for the second-Cesaro series. -/
theorem tsum_secondCesaro_mul_tsum_secondCesaro_eq_tsum_fourthConvolution
    {x : ℝ} (hx : 0 < x) :
    (∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
      Complex.exp (-(x : ℂ)) ^ N) *
        (∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
          Complex.exp (-(x : ℂ)) ^ N) =
      ∑' N : ℕ, mobiusMertensFourthConvolution N *
        Complex.exp (-(x : ℂ)) ^ N := by
  let q : ℂ := Complex.exp (-(x : ℂ))
  have hU : Summable (fun N : ℕ =>
      mobiusAdditiveTriangleSecondCesaro N * q ^ N) := by
    simpa only [q] using summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hU.norm hU.norm]
  apply tsum_congr
  intro N
  simpa only [q] using sum_antidiagonal_secondCesaroWeighted_eq q N

/-- Exact fourth-power Abel identity. -/
theorem mobiusDiscreteLaplaceTransform_pow_four_eq_one_sub_exp_pow_four_mul_tsum
    {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x ^ 4 =
      (1 - Complex.exp (-(x : ℂ))) ^ 4 *
        ∑' N : ℕ, mobiusMertensFourthConvolution N *
          Complex.exp (-(x : ℂ)) ^ N := by
  let F : ℂ := mobiusDiscreteLaplaceTransform x
  let q : ℂ := Complex.exp (-(x : ℂ))
  let S : ℂ := ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N * q ^ N
  let W : ℂ := ∑' N : ℕ, mobiusMertensFourthConvolution N * q ^ N
  have hsq : F * F = (1 - q) ^ 2 * S := by
    simpa only [F, q, S] using
      mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_sq_mul_tsum_secondCesaro hx
  have hprod : S * S = W := by
    simpa only [S, W, q] using
      tsum_secondCesaro_mul_tsum_secondCesaro_eq_tsum_fourthConvolution hx
  calc
    mobiusDiscreteLaplaceTransform x ^ 4 = (F * F) * (F * F) := by
      dsimp only [F]
      ring
    _ = ((1 - q) ^ 2 * S) * ((1 - q) ^ 2 * S) := by rw [hsq]
    _ = (1 - q) ^ 4 * (S * S) := by ring
    _ = (1 - q) ^ 4 * W := by rw [hprod]
    _ = _ := by rfl

/-- Real part of a weighted quartic coefficient. -/
theorem mobiusMertensFourthConvolution_mul_exp_pow_re_eq (x : ℝ) (N : ℕ) :
    (mobiusMertensFourthConvolution N * Complex.exp (-(x : ℂ)) ^ N).re =
      (mobiusMertensFourthConvolution N).re * Real.exp (-x) ^ N := by
  have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    norm_cast
  rw [Complex.mul_re, mobiusMertensFourthConvolution_im_eq_zero, zero_mul, sub_zero]
  congr 1
  have hp := congrArg (fun z : ℂ => (z ^ N).re) hexp
  calc
    (Complex.exp (-(x : ℂ)) ^ N).re =
        (((Real.exp (-x) : ℝ) : ℂ) ^ N).re := hp
    _ = Real.exp (-x) ^ N := by norm_cast

/-- Generic one-sided comparison at the fourth-convolution level. -/
theorem norm_pow_four_mobiusDiscreteLaplaceTransform_le_of_fourthConvolutionUpper
    (b : ℕ → ℝ)
    (hupper : ∀ N : ℕ, (mobiusMertensFourthConvolution N).re ≤ b N)
    {x : ℝ} (hx : 0 < x)
    (hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x)))) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
      (1 - Real.exp (-x)) ^ 4 *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hWc := summable_mobiusMertensFourthConvolution_mul_exp_neg hx
  have hWr : Summable (fun N : ℕ =>
      (mobiusMertensFourthConvolution N).re * r ^ N) := by
    have hmap := hWc.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    simpa [Function.comp_def, r] using
      (mobiusMertensFourthConvolution_mul_exp_pow_re_eq x N).symm
  have hbPow : Summable (fun N : ℕ => b N * r ^ N) := by
    convert hb using 1
    funext N
    congr 1
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have htsumLe :
      (∑' N : ℕ, (mobiusMertensFourthConvolution N).re * r ^ N) ≤
        ∑' N : ℕ, b N * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) hWr hbPow
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hrPos.le N)
  let F : ℂ := mobiusDiscreteLaplaceTransform x
  have hFim : F.im = 0 := by
    exact mobiusDiscreteLaplaceTransform_im_eq_zero hx
  have hsqRe : (F * F).re = ‖F‖ ^ 2 := by
    rw [Complex.mul_re, hFim, zero_mul, sub_zero, Complex.sq_norm,
      Complex.normSq_apply, hFim]
    ring
  have hsqIm : (F * F).im = 0 := by
    rw [Complex.mul_im, hFim]
    ring
  have hleft : (F ^ 4).re = ‖F‖ ^ 4 := by
    calc
      (F ^ 4).re = ((F * F) * (F * F)).re := by ring_nf
      _ = (F * F).re * (F * F).re := by
        rw [Complex.mul_re, hsqIm, zero_mul, sub_zero]
      _ = ‖F‖ ^ 4 := by rw [hsqRe]; ring
  have hfactor : (1 - Complex.exp (-(x : ℂ))) = ((1 - r : ℝ) : ℂ) := by
    have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      norm_cast
    rw [hexp]
    simp [r]
  have hright :
      (((1 - Complex.exp (-(x : ℂ))) ^ 4) *
        ∑' N : ℕ, mobiusMertensFourthConvolution N *
          Complex.exp (-(x : ℂ)) ^ N).re =
      (1 - r) ^ 4 * ∑' N : ℕ,
        (mobiusMertensFourthConvolution N).re * r ^ N := by
    rw [Complex.mul_re]
    have haRe : (((1 - Complex.exp (-(x : ℂ))) ^ 4)).re = (1 - r) ^ 4 := by
      rw [hfactor]
      norm_cast
    have haIm : (((1 - Complex.exp (-(x : ℂ))) ^ 4)).im = 0 := by
      rw [hfactor]
      norm_cast
    rw [haRe, haIm, zero_mul, sub_zero]
    rw [Complex.re_tsum hWc]
    congr 1
    apply tsum_congr
    intro N
    exact mobiusMertensFourthConvolution_mul_exp_pow_re_eq x N
  have heq : ‖F‖ ^ 4 =
      (1 - r) ^ 4 * ∑' N : ℕ,
        (mobiusMertensFourthConvolution N).re * r ^ N := by
    calc
      ‖F‖ ^ 4 = (F ^ 4).re := hleft.symm
      _ = (((1 - Complex.exp (-(x : ℂ))) ^ 4) *
          ∑' N : ℕ, mobiusMertensFourthConvolution N *
            Complex.exp (-(x : ℂ)) ^ N).re := by
        dsimp only [F]
        rw [mobiusDiscreteLaplaceTransform_pow_four_eq_one_sub_exp_pow_four_mul_tsum hx]
      _ = (1 - r) ^ 4 * ∑' N : ℕ,
          (mobiusMertensFourthConvolution N).re * r ^ N := hright
  rw [show ‖mobiusDiscreteLaplaceTransform x‖ = ‖F‖ by rfl, heq]
  calc
    (1 - r) ^ 4 *
        (∑' N : ℕ, (mobiusMertensFourthConvolution N).re * r ^ N) ≤
      (1 - r) ^ 4 * (∑' N : ℕ, b N * r ^ N) :=
        mul_le_mul_of_nonneg_left htsumLe (by positivity)
    _ = (1 - Real.exp (-x)) ^ 4 *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
      congr 1
      apply tsum_congr
      intro N
      congr 1
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- One-sided `N^(5+o(1))` source at the first nonlinear even rung. -/
def MobiusMertensFourthConvolutionSubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusMertensFourthConvolution N).re ≤
      C * ((N : ℝ) + 1) ^ (5 + ε)

/-- Explicit Gamma constant for the quartic Abel estimate. -/
def mobiusMertensFourthConvolutionSubpowerAbelConstant (ε : ℝ) : ℝ :=
  1 + Real.exp 1 * 2 ^ (5 + ε) * Real.Gamma (6 + ε)

theorem mobiusMertensFourthConvolutionSubpowerAbelConstant_nonneg
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ mobiusMertensFourthConvolutionSubpowerAbelConstant ε := by
  dsimp [mobiusMertensFourthConvolutionSubpowerAbelConstant]
  have hgamma := (Real.Gamma_pos_of_pos (by linarith : 0 < 6 + ε)).le
  positivity

/-- A one-sided `N^(5+epsilon)` estimate gives the fourth-power bound of exponent
`2+epsilon`. -/
theorem norm_pow_four_mobiusDiscreteLaplaceTransform_le_of_fourthConvolutionSubpowerUpperBound
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsource : ∀ N : ℕ, (mobiusMertensFourthConvolution N).re ≤
      C * ((N : ℝ) + 1) ^ (5 + ε))
    {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
      C * mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
        x ^ (-(2 + ε)) := by
  let r : ℝ := 5 + ε
  let b : ℕ → ℝ := fun N => C * ((N : ℝ) + 1) ^ r
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le hr hx
  have hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x))) := by
    have hmul := hmoment.1.mul_left C
    apply hmul.congr
    intro N
    dsimp [b]
    ring
  have hfour :=
    norm_pow_four_mobiusDiscreteLaplaceTransform_le_of_fourthConvolutionUpper
      b (by simpa only [b, r] using hsource) hx hb
  have hgamma : 0 ≤ Real.Gamma (r + 1) :=
    (Real.Gamma_pos_of_pos (by dsimp [r]; linarith)).le
  have hX : 1 ≤ (1 / x) ^ (r + 1) := by
    apply Real.one_le_rpow
    · exact (one_le_div hx).2 hxOne
    · linarith
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hxOne
  have hmomentCoarse :
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
        mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1) := by
    calc
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
          1 + Real.exp x * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) :=
        hmoment.2
      _ ≤ 1 + Real.exp 1 * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
        have hfactor : 0 ≤ 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hexp hfactor]
      _ ≤ (1 + Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
          (1 / x) ^ (r + 1) := by
        calc
          1 + Real.exp 1 * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) =
              1 + (Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
                (1 / x) ^ (r + 1) := by ring
          _ ≤ (1 / x) ^ (r + 1) +
              (Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
                (1 / x) ^ (r + 1) := by linarith
          _ = (1 + Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
              (1 / x) ^ (r + 1) := by ring
      _ = mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1) := by
        dsimp [mobiusMertensFourthConvolutionSubpowerAbelConstant, r]
        ring_nf
  have htsum :
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
        C * (mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1)) := by
    calc
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) =
          C * ∑' N : ℕ,
            ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x)) := by
        rw [← hmoment.1.tsum_mul_left C]
        apply tsum_congr
        intro N
        dsimp [b]
        ring
      _ ≤ C * (mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1)) := mul_le_mul_of_nonneg_left hmomentCoarse hC
  have honeSub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  have honeSubNonneg : 0 ≤ 1 - Real.exp (-x) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have htsumNonneg : 0 ≤ ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
    apply tsum_nonneg
    intro N
    dsimp [b]
    positivity
  have hfactorFour : (1 - Real.exp (-x)) ^ 4 ≤ x ^ 4 :=
    pow_le_pow_left₀ honeSubNonneg honeSub 4
  have hraw : ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
      x ^ 4 * (C * (mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
        (1 / x) ^ (r + 1))) := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
          (1 - Real.exp (-x)) ^ 4 *
            ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := hfour
      _ ≤ x ^ 4 * ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right hfactorFour htsumNonneg
      _ ≤ x ^ 4 * (C * (mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := mul_le_mul_of_nonneg_left htsum (by positivity)
  have hInvPow : (1 / x) ^ (r + 1) = x ^ (-(r + 1)) := by
    rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  have hxMul : x ^ 4 * x ^ (-(r + 1)) = x ^ (-(2 + ε)) := by
    calc
      x ^ 4 * x ^ (-(r + 1)) = x ^ (4 : ℝ) * x ^ (-(r + 1)) := by
        congr 1
        exact (Real.rpow_natCast x 4).symm
      _ = x ^ ((4 : ℝ) + (-(r + 1))) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-(2 + ε)) := by
        congr 1
        dsimp [r]
        ring
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
        x ^ 4 * (C * (mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := hraw
    _ = C * mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
        (x ^ 4 * x ^ (-(r + 1))) := by rw [hInvPow]; ring
    _ = C * mobiusMertensFourthConvolutionSubpowerAbelConstant ε *
        x ^ (-(2 + ε)) := by rw [hxMul]

/-- Every quartic one-sided source family gives every strict half-power decay estimate. -/
theorem mobiusMertensFourthConvolutionSubpowerUpperBound_implies_allStrictHalfPowerDecay
    (hupper : MobiusMertensFourthConvolutionSubpowerUpperBound) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := 4 * b - 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hsource⟩ := hupper ε hε
  let S : ℝ := C * mobiusMertensFourthConvolutionSubpowerAbelConstant ε
  let D : ℝ := S + 1
  have hS : 0 ≤ S := mul_nonneg hC
    (mobiusMertensFourthConvolutionSubpowerAbelConstant_nonneg hε)
  rw [isBigO_iff]
  refine ⟨D, ?_⟩
  have hOneNhds : ∀ᶠ x : ℝ in nhds 0, x < 1 := Iio_mem_nhds (by norm_num)
  have hOne : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x < 1 :=
    Filter.Eventually.filter_mono inf_le_left hOneNhds
  filter_upwards [self_mem_nhdsWithin, hOne] with x hx hxOne
  change 0 < x at hx
  change x < 1 at hxOne
  have hfour :=
    norm_pow_four_mobiusDiscreteLaplaceTransform_le_of_fourthConvolutionSubpowerUpperBound
      hε hC hsource hx hxOne.le
  have hrpowFour : (x ^ (-b)) ^ 4 = x ^ (-(2 + ε)) := by
    calc
      (x ^ (-b)) ^ 4 = (x ^ (-b)) ^ (4 : ℝ) :=
        (Real.rpow_natCast (x ^ (-b)) 4).symm
      _ = x ^ ((-b) * 4) := (Real.rpow_mul hx.le (-b) 4).symm
      _ = x ^ (-(2 + ε)) := by
        have hExp : (-b) * 4 = -(2 + ε) := by
          dsimp [ε]
          ring
        rw [hExp]
  rw [← hrpowFour] at hfour
  have hSle : S ≤ D ^ 4 := by
    dsimp [D]
    nlinarith [sq_nonneg S, sq_nonneg (S ^ 2 + 2 * S)]
  have hpowPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx _
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hright : 0 ≤ D * x ^ (-b) := mul_nonneg hD hpowPos.le
  have htargetPow : ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤
      (D * x ^ (-b)) ^ 4 := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 4 ≤ S * (x ^ (-b)) ^ 4 := by
        simpa only [S] using hfour
      _ ≤ D ^ 4 * (x ^ (-b)) ^ 4 :=
        mul_le_mul_of_nonneg_right hSle (by positivity)
      _ = (D * x ^ (-b)) ^ 4 := by ring
  have hroot : ‖mobiusDiscreteLaplaceTransform x‖ ≤ D * x ^ (-b) :=
    le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hright htargetPow
  rw [Real.norm_eq_abs, abs_of_pos hpowPos]
  exact hroot

/-- **Quartic additive-Mertens criterion for RH.** -/
theorem mobiusMertensFourthConvolutionSubpowerUpperBound_implies_riemannHypothesis
    (hupper : MobiusMertensFourthConvolutionSubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusMertensFourthConvolutionSubpowerUpperBound_implies_allStrictHalfPowerDecay hupper)

/-- Classical Mertens half-power cancellation supplies the quartic source at exponent
`5+o(1)`. -/
theorem mobiusMertensAllStrictHalfPowerBound_implies_fourthConvolutionSubpowerUpperBound
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensFourthConvolutionSubpowerUpperBound := by
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hM⟩ := hMertens δ hδ
  refine ⟨C ^ 4, by positivity, ?_⟩
  intro N
  let X : ℝ := (N : ℝ) + 1
  have hX : 0 < X := by dsimp [X]; positivity
  have hU := norm_mobiusAdditiveTriangleSecondCesaro_le_of_mertensBound
    hδ hC hM
  calc
    (mobiusMertensFourthConvolution N).re ≤ ‖mobiusMertensFourthConvolution N‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        ‖mobiusAdditiveTriangleSecondCesaro ab.1 *
          mobiusAdditiveTriangleSecondCesaro ab.2‖ := by
      rw [mobiusMertensFourthConvolution]
      exact norm_sum_le _ _
    _ ≤ ∑ _ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
        C ^ 4 * X ^ (4 + 4 * δ) := by
      apply Finset.sum_le_sum
      intro ab hab
      have hsum : ab.1 + ab.2 = N :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have haN : ab.1 ≤ N := by omega
      have hbN : ab.2 ≤ N := by omega
      have haBase : (ab.1 : ℝ) + 1 ≤ X := by
        dsimp [X]
        exact_mod_cast Nat.add_le_add_right haN 1
      have hbBase : (ab.2 : ℝ) + 1 ≤ X := by
        dsimp [X]
        exact_mod_cast Nat.add_le_add_right hbN 1
      have hExp : 0 ≤ 2 + 2 * δ := by linarith
      have haPow : ((ab.1 : ℝ) + 1) ^ (2 + 2 * δ) ≤ X ^ (2 + 2 * δ) :=
        Real.rpow_le_rpow (by positivity) haBase hExp
      have hbPow : ((ab.2 : ℝ) + 1) ^ (2 + 2 * δ) ≤ X ^ (2 + 2 * δ) :=
        Real.rpow_le_rpow (by positivity) hbBase hExp
      rw [norm_mul]
      calc
        ‖mobiusAdditiveTriangleSecondCesaro ab.1‖ *
            ‖mobiusAdditiveTriangleSecondCesaro ab.2‖ ≤
          (C ^ 2 * ((ab.1 : ℝ) + 1) ^ (2 + 2 * δ)) *
            (C ^ 2 * ((ab.2 : ℝ) + 1) ^ (2 + 2 * δ)) :=
              mul_le_mul (hU ab.1) (hU ab.2) (norm_nonneg _)
                (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _))
        _ ≤ (C ^ 2 * X ^ (2 + 2 * δ)) *
            (C ^ 2 * X ^ (2 + 2 * δ)) := by
          gcongr
        _ = C ^ 4 * (X ^ (2 + 2 * δ) * X ^ (2 + 2 * δ)) := by ring
        _ = C ^ 4 * X ^ ((2 + 2 * δ) + (2 + 2 * δ)) := by
          apply congrArg (fun y : ℝ => C ^ 4 * y)
          exact (Real.rpow_add hX _ _).symm
        _ = C ^ 4 * X ^ (4 + 4 * δ) := by
          congr 1
          ring_nf
    _ = ((N : ℝ) + 1) * (C ^ 4 * X ^ (4 + 4 * δ)) := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
      norm_cast
    _ = C ^ 4 * ((N : ℝ) + 1) ^ (5 + ε) := by
      have hδε : 4 * δ = ε := by dsimp [δ]; ring
      rw [show (N : ℝ) + 1 = X by rfl, hδε]
      calc
        X * (C ^ 4 * X ^ (4 + ε)) = C ^ 4 * (X * X ^ (4 + ε)) := by ring
        _ = C ^ 4 * (X ^ (1 : ℝ) * X ^ (4 + ε)) := by rw [Real.rpow_one]
        _ = C ^ 4 * X ^ ((1 : ℝ) + (4 + ε)) := by
          congr 1
          exact (Real.rpow_add hX _ _).symm
        _ = C ^ 4 * X ^ (5 + ε) := by ring_nf

/-- Exact conditional equivalence interface after supplying classical Littlewood. -/
theorem mobiusMertensFourthConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensFourthConvolutionSubpowerUpperBound ↔ RiemannHypothesis := by
  constructor
  · exact mobiusMertensFourthConvolutionSubpowerUpperBound_implies_riemannHypothesis
  · intro hRH
    exact mobiusMertensAllStrictHalfPowerBound_implies_fourthConvolutionSubpowerUpperBound
      (hLittlewood hRH)

end

end RHTower
