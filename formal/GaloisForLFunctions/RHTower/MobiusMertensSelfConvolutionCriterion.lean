import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Second-Cesàro additive Möbius criterion

One more finite cumulative sum turns the additive Möbius triangle into the additive
self-convolution of the Mertens partial sums.  Its ordinary generating function is therefore the
Möbius--Laplace square divided by two geometric factors.  A one-sided `N^(2+o(1))` upper bound is
enough for every strict half-power Möbius--Laplace estimate and hence RH.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Second cumulative sum of the additive Möbius convolution. -/
def mobiusAdditiveTriangleSecondCesaro (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), mobiusAdditiveTriangle k

/-- Mertens partial sum, with the harmless zero coefficient included. -/
def mobiusMertensPartialSum (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), mobiusComplexCoefficient n

/-- Additive self-convolution of the Mertens partial sums. -/
def mobiusMertensSelfConvolution (N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.antidiagonal N,
    mobiusMertensPartialSum ab.1 * mobiusMertensPartialSum ab.2

private theorem mk_partialSums_eq_mul_geometricPowerSeries (c : ℕ → ℂ) :
    PowerSeries.mk (fun N => ∑ k ∈ Finset.range (N + 1), c k) =
      PowerSeries.mk c * PowerSeries.mk (fun _n => (1 : ℂ)) := by
  ext N
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i _j => c i * (1 : ℂ)) N]
  simp

/-- Exact finite identity: the twice-cumulative Möbius triangle is one antidiagonal additive
self-convolution of Mertens partial sums. -/
theorem mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution (N : ℕ) :
    mobiusAdditiveTriangleSecondCesaro N = mobiusMertensSelfConvolution N := by
  let A : PowerSeries ℂ := PowerSeries.mk mobiusComplexCoefficient
  let C : PowerSeries ℂ := PowerSeries.mk mobiusAdditiveConvolution
  let T : PowerSeries ℂ := PowerSeries.mk mobiusAdditiveTriangle
  let U : PowerSeries ℂ := PowerSeries.mk mobiusAdditiveTriangleSecondCesaro
  let M : PowerSeries ℂ := PowerSeries.mk mobiusMertensPartialSum
  let G : PowerSeries ℂ := PowerSeries.mk fun _n => (1 : ℂ)
  have hC : C = A * A := by
    ext k
    simp only [C, A, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      mobiusAdditiveConvolution]
  have hT : T = C * G := by
    simpa only [T, C, G, mobiusAdditiveTriangle] using
      mk_partialSums_eq_mul_geometricPowerSeries mobiusAdditiveConvolution
  have hU : U = T * G := by
    simpa only [U, T, G, mobiusAdditiveTriangleSecondCesaro] using
      mk_partialSums_eq_mul_geometricPowerSeries mobiusAdditiveTriangle
  have hM : M = A * G := by
    simpa only [M, A, G, mobiusMertensPartialSum] using
      mk_partialSums_eq_mul_geometricPowerSeries mobiusComplexCoefficient
  have hseries : U = M * M := by
    rw [hU, hT, hC, hM]
    ring
  have hcoeff := congrArg (PowerSeries.coeff N) hseries
  simpa only [U, M, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    mobiusMertensSelfConvolution] using hcoeff

/-- Crude cubic bound used only to justify the second Abel summation. -/
theorem norm_mobiusAdditiveTriangleSecondCesaro_le (N : ℕ) :
    ‖mobiusAdditiveTriangleSecondCesaro N‖ ≤ ((N : ℝ) + 1) ^ 3 := by
  rw [mobiusAdditiveTriangleSecondCesaro]
  calc
    ‖∑ k ∈ Finset.range (N + 1), mobiusAdditiveTriangle k‖ ≤
        ∑ k ∈ Finset.range (N + 1), ‖mobiusAdditiveTriangle k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), ((k : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_mobiusAdditiveTriangle_le k
    _ ≤ ∑ _k ∈ Finset.range (N + 1), ((N : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N := by simpa using Finset.mem_range.mp hk
      gcongr
    _ = ((N : ℝ) + 1) ^ 3 := by
      simp
      ring

/-- Second cumulative Möbius triangles are real. -/
theorem mobiusAdditiveTriangleSecondCesaro_im_eq_zero (N : ℕ) :
    (mobiusAdditiveTriangleSecondCesaro N).im = 0 := by
  simp [mobiusAdditiveTriangleSecondCesaro, mobiusAdditiveTriangle_im_eq_zero]

/-- Cubic growth makes the second-Cesàro Abel series converge at every positive scale. -/
theorem summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg
    {x : ℝ} (hx : 0 < x) :
    Summable (fun N : ℕ => mobiusAdditiveTriangleSecondCesaro N *
      Complex.exp (-(x : ℂ)) ^ N) := by
  have h0 := summable_pow_mul_exp_neg 0 hx
  have h1 := summable_pow_mul_exp_neg 1 hx
  have h2 := summable_pow_mul_exp_neg 2 hx
  have h3 := summable_pow_mul_exp_neg 3 hx
  have hmajor : Summable (fun N : ℕ =>
      (((N : ℝ) + 1) ^ 3) * Real.exp (-((N : ℝ) * x))) := by
    have hs := h3.add ((h2.mul_left 3).add ((h1.mul_left 3).add h0))
    convert hs using 1
    funext N
    change (((N : ℝ) + 1) ^ 3) * Real.exp (-((N : ℝ) * x)) =
      (N : ℝ) ^ 3 * Real.exp (-((N : ℝ) * x)) +
        (3 * ((N : ℝ) ^ 2 * Real.exp (-((N : ℝ) * x))) +
          (3 * ((N : ℝ) ^ 1 * Real.exp (-((N : ℝ) * x))) +
            (N : ℝ) ^ 0 * Real.exp (-((N : ℝ) * x))))
    ring
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hmajor
  rw [norm_mul, norm_exp_neg_pow_eq]
  exact mul_le_mul_of_nonneg_right
    (norm_mobiusAdditiveTriangleSecondCesaro_le N) (Real.exp_pos _).le

/-- Exact double-Abel identity for the second cumulative additive triangle. -/
theorem mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_sq_mul_tsum_secondCesaro
    {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
      (1 - Complex.exp (-(x : ℂ))) ^ 2 *
        ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
          Complex.exp (-(x : ℂ)) ^ N := by
  have htriangle := summable_mobiusAdditiveTriangle_mul_exp_neg hx
  have hsecond := summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx
  have habel :
      (∑' N : ℕ, mobiusAdditiveTriangle N * Complex.exp (-(x : ℂ)) ^ N) =
        (1 - Complex.exp (-(x : ℂ))) *
          ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
            Complex.exp (-(x : ℂ)) ^ N := by
    simpa only [mobiusAdditiveTriangleSecondCesaro] using
      tsum_mul_pow_eq_one_sub_mul_tsum_partialSums
        mobiusAdditiveTriangle (Complex.exp (-(x : ℂ))) htriangle hsecond
  calc
    mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x =
        (1 - Complex.exp (-(x : ℂ))) *
          ∑' N : ℕ, mobiusAdditiveTriangle N *
            Complex.exp (-(x : ℂ)) ^ N :=
      mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle hx
    _ = (1 - Complex.exp (-(x : ℂ))) *
          ((1 - Complex.exp (-(x : ℂ))) *
            ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
              Complex.exp (-(x : ℂ)) ^ N) := by rw [habel]
    _ = (1 - Complex.exp (-(x : ℂ))) ^ 2 *
          ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
            Complex.exp (-(x : ℂ)) ^ N := by ring

/-- Real part of a weighted second-Cesàro term. -/
theorem mobiusAdditiveTriangleSecondCesaro_mul_exp_pow_re_eq (x : ℝ) (N : ℕ) :
    (mobiusAdditiveTriangleSecondCesaro N * Complex.exp (-(x : ℂ)) ^ N).re =
      (mobiusAdditiveTriangleSecondCesaro N).re * Real.exp (-x) ^ N := by
  have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    norm_cast
  rw [Complex.mul_re, mobiusAdditiveTriangleSecondCesaro_im_eq_zero, zero_mul, sub_zero]
  congr 1
  have hp := congrArg (fun z : ℂ => (z ^ N).re) hexp
  calc
    (Complex.exp (-(x : ℂ)) ^ N).re =
        (((Real.exp (-x) : ℝ) : ℂ) ^ N).re := hp
    _ = Real.exp (-x) ^ N := by norm_cast

/-- Generic one-sided comparison after two Abel summations. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_sq_mul_tsum_of_secondCesaroUpper
    (b : ℕ → ℝ)
    (hupper : ∀ N : ℕ, (mobiusAdditiveTriangleSecondCesaro N).re ≤ b N)
    {x : ℝ} (hx : 0 < x)
    (hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x)))) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      (1 - Real.exp (-x)) ^ 2 *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hrLt : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsecondC := summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx
  have hsecondR : Summable (fun N : ℕ =>
      (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N) := by
    have hmap := hsecondC.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    simpa [Function.comp_def, r] using
      (mobiusAdditiveTriangleSecondCesaro_mul_exp_pow_re_eq x N).symm
  have hbPow : Summable (fun N : ℕ => b N * r ^ N) := by
    convert hb using 1
    funext N
    congr 1
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have htsumLe :
      (∑' N : ℕ, (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N) ≤
        ∑' N : ℕ, b N * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) hsecondR hbPow
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hrPos.le N)
  have hleft :
      (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re =
        ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 := by
    rw [Complex.mul_re, mobiusDiscreteLaplaceTransform_im_eq_zero hx,
      zero_mul, sub_zero, Complex.sq_norm, Complex.normSq_apply,
      mobiusDiscreteLaplaceTransform_im_eq_zero hx]
    ring
  have hfactor : (1 - Complex.exp (-(x : ℂ))) = ((1 - r : ℝ) : ℂ) := by
    have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      norm_cast
    rw [hexp]
    simp [r]
  have hright :
      (((1 - Complex.exp (-(x : ℂ))) ^ 2) *
        ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
          Complex.exp (-(x : ℂ)) ^ N).re =
      (1 - r) ^ 2 * ∑' N : ℕ,
        (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N := by
    rw [Complex.mul_re]
    have haRe : (((1 - Complex.exp (-(x : ℂ))) ^ 2)).re = (1 - r) ^ 2 := by
      rw [hfactor]
      norm_cast
    have haIm : (((1 - Complex.exp (-(x : ℂ))) ^ 2)).im = 0 := by
      rw [hfactor]
      norm_cast
    rw [haRe, haIm, zero_mul, sub_zero]
    rw [Complex.re_tsum hsecondC]
    congr 1
    apply tsum_congr
    intro N
    exact mobiusAdditiveTriangleSecondCesaro_mul_exp_pow_re_eq x N
  have heq : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
      (1 - r) ^ 2 * ∑' N : ℕ,
        (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 =
          (mobiusDiscreteLaplaceTransform x * mobiusDiscreteLaplaceTransform x).re := hleft.symm
      _ = (((1 - Complex.exp (-(x : ℂ))) ^ 2) *
          ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N *
            Complex.exp (-(x : ℂ)) ^ N).re := by
        rw [mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_sq_mul_tsum_secondCesaro hx]
      _ = (1 - r) ^ 2 * ∑' N : ℕ,
          (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N := hright
  rw [heq]
  calc
    (1 - r) ^ 2 *
        (∑' N : ℕ, (mobiusAdditiveTriangleSecondCesaro N).re * r ^ N) ≤
      (1 - r) ^ 2 * (∑' N : ℕ, b N * r ^ N) :=
        mul_le_mul_of_nonneg_left htsumLe (sq_nonneg _)
    _ = (1 - Real.exp (-x)) ^ 2 *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
      congr 1
      apply tsum_congr
      intro N
      congr 1
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- One-sided `N^(2+o(1))` estimate for the second cumulative additive Möbius triangle. -/
def MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveTriangleSecondCesaro N).re ≤
      C * ((N : ℝ) + 1) ^ (2 + ε)

/-- Classical all-strict-half-power Mertens estimate, stated as a finite arithmetic source. -/
def MobiusMertensAllStrictHalfPowerBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)

/-- The classical Mertens half-power family gives the second-Cesàro source family by the exact
self-convolution identity. -/
theorem mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hM⟩ := hMertens δ hδ
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro N
  let X : ℝ := (N : ℝ) + 1
  have hX : 0 < X := by dsimp [X]; positivity
  have hθ : 0 ≤ (1 / 2 : ℝ) + δ := by linarith
  rw [mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution]
  calc
    (mobiusMertensSelfConvolution N).re ≤ ‖mobiusMertensSelfConvolution N‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ ab ∈ Finset.antidiagonal N,
        ‖mobiusMertensPartialSum ab.1 * mobiusMertensPartialSum ab.2‖ := by
      rw [mobiusMertensSelfConvolution]
      exact norm_sum_le _ _
    _ ≤ ∑ _ab ∈ Finset.antidiagonal N,
        C ^ 2 * X ^ (1 + 2 * δ) := by
      apply Finset.sum_le_sum
      intro ab hab
      have habSum : ab.1 + ab.2 = N := Finset.mem_antidiagonal.mp hab
      have haN : ab.1 ≤ N := by omega
      have hbN : ab.2 ≤ N := by omega
      have haBase : (ab.1 : ℝ) + 1 ≤ X := by
        dsimp [X]
        exact_mod_cast Nat.add_le_add_right haN 1
      have hbBase : (ab.2 : ℝ) + 1 ≤ X := by
        dsimp [X]
        exact_mod_cast Nat.add_le_add_right hbN 1
      have haPow : ((ab.1 : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) ≤
          X ^ ((1 / 2 : ℝ) + δ) :=
        Real.rpow_le_rpow (by positivity) haBase hθ
      have hbPow : ((ab.2 : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) ≤
          X ^ ((1 / 2 : ℝ) + δ) :=
        Real.rpow_le_rpow (by positivity) hbBase hθ
      have ha := hM ab.1
      have hb := hM ab.2
      rw [norm_mul]
      calc
        ‖mobiusMertensPartialSum ab.1‖ * ‖mobiusMertensPartialSum ab.2‖ ≤
            (C * ((ab.1 : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) *
              (C * ((ab.2 : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) :=
          mul_le_mul ha hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        _ ≤ (C * X ^ ((1 / 2 : ℝ) + δ)) *
              (C * X ^ ((1 / 2 : ℝ) + δ)) := by
          gcongr
        _ = C ^ 2 *
              (X ^ ((1 / 2 : ℝ) + δ) * X ^ ((1 / 2 : ℝ) + δ)) := by ring
        _ = C ^ 2 * X ^ (((1 / 2 : ℝ) + δ) + ((1 / 2 : ℝ) + δ)) := by
          apply congrArg (fun y : ℝ => C ^ 2 * y)
          exact (Real.rpow_add hX _ _).symm
        _ = C ^ 2 * X ^ (1 + 2 * δ) := by
          congr 1
          ring
    _ = ((N : ℝ) + 1) * (C ^ 2 * X ^ (1 + 2 * δ)) := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
      norm_cast
    _ = C ^ 2 * ((N : ℝ) + 1) ^ (2 + ε) := by
      have hδeq : 2 * δ = ε := by dsimp [δ]; ring
      rw [show (N : ℝ) + 1 = X by rfl, hδeq]
      calc
        X * (C ^ 2 * X ^ (1 + ε)) = C ^ 2 * (X * X ^ (1 + ε)) := by ring
        _ = C ^ 2 * (X ^ (1 : ℝ) * X ^ (1 + ε)) := by rw [Real.rpow_one]
        _ = C ^ 2 * X ^ ((1 : ℝ) + (1 + ε)) := by
          congr 1
          exact (Real.rpow_add hX _ _).symm
        _ = C ^ 2 * X ^ (2 + ε) := by ring

/-- Explicit Gamma constant for the second-Cesàro subpower Abel estimate. -/
def mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant (ε : ℝ) : ℝ :=
  1 + Real.exp 1 * 2 ^ (2 + ε) * Real.Gamma (3 + ε)

theorem mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant_nonneg
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε := by
  dsimp [mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant]
  have hgamma := (Real.Gamma_pos_of_pos (by linarith : 0 < 3 + ε)).le
  positivity

/-- A one-sided `N^(2+ε)` second-Cesàro estimate gives the square bound of exponent `1+ε`. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_of_secondCesaroSubpowerUpperBound
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsource : ∀ N : ℕ, (mobiusAdditiveTriangleSecondCesaro N).re ≤
      C * ((N : ℝ) + 1) ^ (2 + ε))
    {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      C * mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
        x ^ (-(1 + ε)) := by
  let r : ℝ := 2 + ε
  let b : ℕ → ℝ := fun N => C * ((N : ℝ) + 1) ^ r
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le hr hx
  have hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x))) := by
    have hmul := hmoment.1.mul_left C
    convert hmul using 1
    funext N
    dsimp [b]
    ring
  have hsquare :=
    norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_sq_mul_tsum_of_secondCesaroUpper
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
        mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
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
      _ = mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1) := by
        dsimp [mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant, r]
        ring
  have htsum :
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
        C * (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
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
      _ ≤ C * (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
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
  have hfactorSq : (1 - Real.exp (-x)) ^ 2 ≤ x ^ 2 := by nlinarith
  have hraw : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      x ^ 2 * (C * (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
        (1 / x) ^ (r + 1))) := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
          (1 - Real.exp (-x)) ^ 2 *
            ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := hsquare
      _ ≤ x ^ 2 * ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right hfactorSq htsumNonneg
      _ ≤ x ^ 2 * (C * (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := mul_le_mul_of_nonneg_left htsum (sq_nonneg x)
  have hInvPow : (1 / x) ^ (r + 1) = x ^ (-(r + 1)) := by
    rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  have hxMul : x ^ 2 * x ^ (-(r + 1)) = x ^ (-(1 + ε)) := by
    calc
      x ^ 2 * x ^ (-(r + 1)) = x ^ (2 : ℝ) * x ^ (-(r + 1)) := by
        congr 1
        exact (Real.rpow_natCast x 2).symm
      _ = x ^ ((2 : ℝ) + (-(r + 1))) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-(1 + ε)) := by
        congr 1
        dsimp [r]
        ring
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
        x ^ 2 * (C * (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := hraw
    _ = C * mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
        (x ^ 2 * x ^ (-(r + 1))) := by rw [hInvPow]; ring
    _ = C * mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε *
        x ^ (-(1 + ε)) := by rw [hxMul]

/-- Every second-Cesàro subpower upper estimate gives every strict half-power decay estimate. -/
theorem mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_allStrictHalfPowerDecay
    (hupper : MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := 2 * b - 1
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hsource⟩ := hupper ε hε
  let S : ℝ := C * mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant ε
  let D : ℝ := S + 1
  have hS : 0 ≤ S := mul_nonneg hC
    (mobiusAdditiveTriangleSecondCesaroSubpowerAbelConstant_nonneg hε)
  rw [isBigO_iff]
  refine ⟨D, ?_⟩
  have hOneNhds : ∀ᶠ x : ℝ in nhds 0, x < 1 := Iio_mem_nhds (by norm_num)
  have hOne : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x < 1 :=
    Filter.Eventually.filter_mono inf_le_left hOneNhds
  filter_upwards [self_mem_nhdsWithin, hOne] with x hx hxOne
  change 0 < x at hx
  change x < 1 at hxOne
  have hsq := norm_sq_mobiusDiscreteLaplaceTransform_le_of_secondCesaroSubpowerUpperBound
    hε hC hsource hx hxOne.le
  have hrpowSq : (x ^ (-b)) ^ 2 = x ^ (-(1 + ε)) := by
    calc
      (x ^ (-b)) ^ 2 = (x ^ (-b)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (x ^ (-b)) 2).symm
      _ = x ^ ((-b) * 2) := (Real.rpow_mul hx.le (-b) 2).symm
      _ = x ^ (-(1 + ε)) := by
        have hExp : (-b) * 2 = -(1 + ε) := by
          dsimp [ε]
          ring
        rw [hExp]
  rw [← hrpowSq] at hsq
  have hSle : S ≤ D ^ 2 := by
    dsimp [D]
    nlinarith [sq_nonneg S]
  have hpowPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx _
  have htargetSq : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      (D * x ^ (-b)) ^ 2 := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤ S * (x ^ (-b)) ^ 2 := by
        simpa only [S] using hsq
      _ ≤ D ^ 2 * (x ^ (-b)) ^ 2 :=
        mul_le_mul_of_nonneg_right hSle (sq_nonneg _)
      _ = (D * x ^ (-b)) ^ 2 := by ring
  have hnorm := norm_nonneg (mobiusDiscreteLaplaceTransform x)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hright : 0 ≤ D * x ^ (-b) := mul_nonneg hD hpowPos.le
  rw [Real.norm_eq_abs, abs_of_pos hpowPos]
  nlinarith

/-- **Second-Cesàro Möbius criterion for RH.** -/
theorem mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
    (hupper : MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_allStrictHalfPowerDecay hupper)

/-- The classical Mertens source also supplies the complete strict-half-power Laplace family.
This connector lets every Laplace-energy converse reuse the single Littlewood premise. -/
theorem mobiusMertensAllStrictHalfPowerBound_implies_allStrictHalfPowerDecay
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay :=
  mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_allStrictHalfPowerDecay
    (mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound hMertens)

/-- The classical all-strict-half-power Mertens estimate reaches RH through the exact
self-convolution and double-Abel bridge. -/
theorem mobiusMertensAllStrictHalfPowerBound_implies_riemannHypothesis
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    RiemannHypothesis :=
  mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
    (mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound hMertens)

/-- Exact equivalence interface once the classical Littlewood direction `RH → Mertens
all-strict-half-power` is supplied. -/
theorem mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_iff_riemannHypothesis_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound ↔ RiemannHypothesis := by
  constructor
  · exact mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
  · intro hRH
    exact mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound
      (hLittlewood hRH)

end

end RHTower
