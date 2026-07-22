import GaloisForLFunctions.RHTower.MobiusMertensFourthConvolutionCriterion

/-!
# Möbius even-additive convolution order law

All even additive-convolution orders of Mertens partial sums obey one exact Abel mechanism.  For
`k > 0`, the critical one-sided source exponent is `3k - 1`: an all-epsilon upper bound at this
order gives every strict half-power bound for the Möbius--Laplace transform and therefore RH.
Conversely, the classical all-strict-half-power Mertens estimate supplies the source at every
order.  The module also identifies the existing quadratic and quartic criteria as the first two
rungs of this universal hierarchy.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Additive Cauchy-convolution powers, with the zeroth power equal to the delta sequence. -/
def additiveConvolutionPower (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, N => if N = 0 then 1 else 0
  | k + 1, N => ∑ ab ∈ Finset.antidiagonal N,
      additiveConvolutionPower a k ab.1 * a ab.2

private theorem sum_antidiagonal_additiveConvolutionPower_weighted_eq
    (a : ℕ → ℂ) (q : ℂ) (k N : ℕ) :
    (∑ ab ∈ Finset.antidiagonal N,
      (additiveConvolutionPower a k ab.1 * q ^ ab.1) *
        (a ab.2 * q ^ ab.2)) =
      additiveConvolutionPower a (k + 1) N * q ^ N := by
  rw [additiveConvolutionPower, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 = N := Finset.mem_antidiagonal.mp hab
  rw [← hsum, pow_add]
  ring_nf

theorem summable_norm_additiveConvolutionPower_mul_pow
    (a : ℕ → ℂ) (q : ℂ)
    (ha : Summable (fun N : ℕ => ‖a N * q ^ N‖)) :
    ∀ k : ℕ, Summable (fun N : ℕ =>
      ‖additiveConvolutionPower a k N * q ^ N‖) := by
  intro k
  induction k with
  | zero =>
      have hbase : (fun N : ℕ =>
          ‖additiveConvolutionPower a 0 N * q ^ N‖) =
          fun N : ℕ => if N = 0 then (1 : ℝ) else 0 := by
        funext N
        split_ifs with h
        · subst N
          simp [additiveConvolutionPower]
        · simp [additiveConvolutionPower, h]
      rw [hbase]
      exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | succ k ih =>
      have hconv :=
        summable_norm_sum_mul_antidiagonal_of_summable_norm ih ha
      convert hconv using 1
      funext N
      rw [sum_antidiagonal_additiveConvolutionPower_weighted_eq]

theorem tsum_additiveConvolutionPower_mul_pow
    (a : ℕ → ℂ) (q : ℂ)
    (ha : Summable (fun N : ℕ => ‖a N * q ^ N‖)) (k : ℕ) :
    (∑' N : ℕ, a N * q ^ N) ^ k =
      ∑' N : ℕ, additiveConvolutionPower a k N * q ^ N := by
  induction k with
  | zero =>
      rw [pow_zero]
      have hbase : (fun N : ℕ =>
          additiveConvolutionPower a 0 N * q ^ N) =
          fun N : ℕ => if N = 0 then (1 : ℂ) else 0 := by
        funext N
        split_ifs with h
        · subst N
          simp [additiveConvolutionPower]
        · simp [additiveConvolutionPower, h]
      rw [hbase]
      exact (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).tsum_eq.symm
  | succ k ih =>
      rw [pow_succ, ih]
      have hk := summable_norm_additiveConvolutionPower_mul_pow a q ha k
      rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hk ha]
      apply tsum_congr
      intro N
      exact sum_antidiagonal_additiveConvolutionPower_weighted_eq a q k N

theorem additiveConvolutionPower_one (a : ℕ → ℂ) (N : ℕ) :
    additiveConvolutionPower a 1 N = a N := by
  rw [show 1 = 0 + 1 by omega, additiveConvolutionPower]
  rw [Finset.sum_eq_single (0, N)]
  · simp [additiveConvolutionPower]
  · intro ab hab habNe
    have habSum : ab.1 + ab.2 = N := Finset.mem_antidiagonal.mp hab
    have haNe : ab.1 ≠ 0 := by
      intro ha
      apply habNe
      apply Prod.ext
      · exact ha
      · omega
    simp [additiveConvolutionPower, haNe]
  · simp

/-- Sharp universal order transfer for additive convolution powers. -/
theorem norm_additiveConvolutionPower_succ_le
    (a : ℕ → ℂ) {A α : ℝ} (hA : 0 ≤ A) (hα : 0 ≤ α)
    (ha : ∀ N : ℕ, ‖a N‖ ≤ A * ((N : ℝ) + 1) ^ α)
    (j N : ℕ) :
    ‖additiveConvolutionPower a (j + 1) N‖ ≤
      A ^ (j + 1) * ((N : ℝ) + 1) ^ (((j + 1 : ℕ) : ℝ) * α + j) := by
  induction j generalizing N with
  | zero =>
      simpa [additiveConvolutionPower_one] using ha N
  | succ j ih =>
      let X : ℝ := (N : ℝ) + 1
      have hX : 0 < X := by dsimp [X]; positivity
      rw [show j + 1 + 1 = j + 2 by omega]
      rw [additiveConvolutionPower]
      calc
        ‖∑ ab ∈ Finset.antidiagonal N,
            additiveConvolutionPower a (j + 1) ab.1 * a ab.2‖ ≤
            ∑ ab ∈ Finset.antidiagonal N,
              ‖additiveConvolutionPower a (j + 1) ab.1 * a ab.2‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _ab ∈ Finset.antidiagonal N,
            A ^ (j + 2) * X ^ (((j + 2 : ℕ) : ℝ) * α + j) := by
          apply Finset.sum_le_sum
          intro ab hab
          have habSum : ab.1 + ab.2 = N := Finset.mem_antidiagonal.mp hab
          have haN : ab.1 ≤ N := by omega
          have hbN : ab.2 ≤ N := by omega
          have haBase : (ab.1 : ℝ) + 1 ≤ X := by
            dsimp [X]
            exact add_le_add (Nat.cast_le.mpr haN) le_rfl
          have hbBase : (ab.2 : ℝ) + 1 ≤ X := by
            dsimp [X]
            exact add_le_add (Nat.cast_le.mpr hbN) le_rfl
          have hprevExp : 0 ≤ (((j + 1 : ℕ) : ℝ) * α + j) := by positivity
          have haPow : ((ab.1 : ℝ) + 1) ^ (((j + 1 : ℕ) : ℝ) * α + j) ≤
              X ^ (((j + 1 : ℕ) : ℝ) * α + j) :=
            Real.rpow_le_rpow (by positivity) haBase hprevExp
          have hbPow : ((ab.2 : ℝ) + 1) ^ α ≤ X ^ α :=
            Real.rpow_le_rpow (by positivity) hbBase hα
          rw [norm_mul]
          calc
            ‖additiveConvolutionPower a (j + 1) ab.1‖ * ‖a ab.2‖ ≤
                (A ^ (j + 1) *
                  ((ab.1 : ℝ) + 1) ^ (((j + 1 : ℕ) : ℝ) * α + j)) *
                  (A * ((ab.2 : ℝ) + 1) ^ α) :=
              mul_le_mul (ih ab.1) (ha ab.2) (norm_nonneg _)
                (mul_nonneg (pow_nonneg hA _)
                  (Real.rpow_nonneg (by positivity) _))
            _ ≤ (A ^ (j + 1) * X ^ (((j + 1 : ℕ) : ℝ) * α + j)) *
                (A * X ^ α) := by
              gcongr
            _ = A ^ (j + 2) *
                (X ^ (((j + 1 : ℕ) : ℝ) * α + j) * X ^ α) := by
              rw [pow_succ]
              ring_nf
            _ = A ^ (j + 2) *
                X ^ ((((j + 1 : ℕ) : ℝ) * α + j) + α) := by
              congr 1
              exact (Real.rpow_add hX _ _).symm
            _ = A ^ (j + 2) * X ^ (((j + 2 : ℕ) : ℝ) * α + j) := by
              congr 1
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
              ring_nf
        _ = ((N : ℝ) + 1) *
            (A ^ (j + 2) * X ^ (((j + 2 : ℕ) : ℝ) * α + j)) := by
          rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
          norm_cast
        _ = A ^ (j + 2) *
            ((N : ℝ) + 1) ^
              (((j + 2 : ℕ) : ℝ) * α + (((j + 1 : ℕ) : ℝ))) := by
          rw [show (N : ℝ) + 1 = X by rfl]
          calc
            X * (A ^ (j + 2) * X ^ (((j + 2 : ℕ) : ℝ) * α + j)) =
                A ^ (j + 2) *
                  (X ^ (1 : ℝ) * X ^ (((j + 2 : ℕ) : ℝ) * α + j)) := by
              rw [Real.rpow_one]
              ring_nf
            _ = A ^ (j + 2) *
                X ^ ((1 : ℝ) + (((j + 2 : ℕ) : ℝ) * α + j)) := by
              congr 1
              exact (Real.rpow_add hX _ _).symm
            _ = A ^ (j + 2) *
                X ^ (((j + 2 : ℕ) : ℝ) * α + (((j + 1 : ℕ) : ℝ))) := by
              congr 1
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
              ring_nf

/-- The `2k`-fold additive Mertens convolution, grouped into `k` quadratic blocks. -/
def mobiusMertensEvenConvolution (k N : ℕ) : ℂ :=
  additiveConvolutionPower mobiusAdditiveTriangleSecondCesaro k N

theorem additiveConvolutionPower_im_eq_zero
    (a : ℕ → ℂ) (ha : ∀ N : ℕ, (a N).im = 0) (k N : ℕ) :
    (additiveConvolutionPower a k N).im = 0 := by
  induction k generalizing N with
  | zero =>
      by_cases hN : N = 0 <;> simp [additiveConvolutionPower, hN]
  | succ k ih =>
      simp [additiveConvolutionPower, Complex.mul_im, ih, ha]

theorem mobiusMertensEvenConvolution_im_eq_zero (k N : ℕ) :
    (mobiusMertensEvenConvolution k N).im = 0 := by
  exact additiveConvolutionPower_im_eq_zero _
    mobiusAdditiveTriangleSecondCesaro_im_eq_zero k N

theorem summable_norm_mobiusMertensEvenConvolution_mul_exp_neg
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Summable (fun N : ℕ => ‖mobiusMertensEvenConvolution k N *
      Complex.exp (-(x : ℂ)) ^ N‖) := by
  apply summable_norm_additiveConvolutionPower_mul_pow
  exact (summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx).norm

/-- Exact all-even Abel identity. -/
theorem mobiusDiscreteLaplaceTransform_pow_even_eq_one_sub_exp_pow_even_mul_tsum
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    mobiusDiscreteLaplaceTransform x ^ (2 * k) =
      (1 - Complex.exp (-(x : ℂ))) ^ (2 * k) *
        ∑' N : ℕ, mobiusMertensEvenConvolution k N *
          Complex.exp (-(x : ℂ)) ^ N := by
  let F : ℂ := mobiusDiscreteLaplaceTransform x
  let q : ℂ := Complex.exp (-(x : ℂ))
  let U : ℂ := ∑' N : ℕ, mobiusAdditiveTriangleSecondCesaro N * q ^ N
  have hsq : F ^ 2 = (1 - q) ^ 2 * U := by
    simpa only [F, q, U, pow_two] using
      mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_sq_mul_tsum_secondCesaro hx
  have hUnorm : Summable (fun N : ℕ =>
      ‖mobiusAdditiveTriangleSecondCesaro N * q ^ N‖) := by
    simpa only [q] using
      (summable_mobiusAdditiveTriangleSecondCesaro_mul_exp_neg hx).norm
  have hpow : U ^ k = ∑' N : ℕ, mobiusMertensEvenConvolution k N * q ^ N := by
    simpa only [U, mobiusMertensEvenConvolution] using
      tsum_additiveConvolutionPower_mul_pow
        mobiusAdditiveTriangleSecondCesaro q hUnorm k
  calc
    mobiusDiscreteLaplaceTransform x ^ (2 * k) = (F ^ 2) ^ k := by
      simp only [F, pow_mul]
    _ = ((1 - q) ^ 2 * U) ^ k := by rw [hsq]
    _ = (1 - q) ^ (2 * k) * U ^ k := by rw [mul_pow, pow_mul]
    _ = (1 - q) ^ (2 * k) *
        ∑' N : ℕ, mobiusMertensEvenConvolution k N * q ^ N := by rw [hpow]
    _ = _ := by rfl

theorem mobiusMertensEvenConvolution_mul_exp_pow_re_eq
    (k : ℕ) (x : ℝ) (N : ℕ) :
    (mobiusMertensEvenConvolution k N * Complex.exp (-(x : ℂ)) ^ N).re =
      (mobiusMertensEvenConvolution k N).re * Real.exp (-x) ^ N := by
  have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    norm_cast
  rw [Complex.mul_re, mobiusMertensEvenConvolution_im_eq_zero, zero_mul, sub_zero]
  congr 1
  have hp := congrArg (fun z : ℂ => (z ^ N).re) hexp
  calc
    (Complex.exp (-(x : ℂ)) ^ N).re =
        (((Real.exp (-x) : ℝ) : ℂ) ^ N).re := hp
    _ = Real.exp (-x) ^ N := by norm_cast

/-- Generic one-sided comparison at every even additive-convolution order. -/
theorem norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionUpper
    (k : ℕ) (b : ℕ → ℝ)
    (hupper : ∀ N : ℕ, (mobiusMertensEvenConvolution k N).re ≤ b N)
    {x : ℝ} (hx : 0 < x)
    (hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x)))) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
      (1 - Real.exp (-x)) ^ (2 * k) *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
  let r : ℝ := Real.exp (-x)
  have hrPos : 0 < r := Real.exp_pos _
  have hrLe : r ≤ 1 := by
    dsimp [r]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hconvNorm := summable_norm_mobiusMertensEvenConvolution_mul_exp_neg hx k
  have hconvC : Summable (fun N : ℕ =>
      mobiusMertensEvenConvolution k N * Complex.exp (-(x : ℂ)) ^ N) :=
    hconvNorm.of_norm
  have hconvR : Summable (fun N : ℕ =>
      (mobiusMertensEvenConvolution k N).re * r ^ N) := by
    have hmap := hconvC.map Complex.reCLM Complex.reCLM.continuous
    convert hmap using 1
    funext N
    simpa [r] using
      (mobiusMertensEvenConvolution_mul_exp_pow_re_eq k x N).symm
  have hbPow : Summable (fun N : ℕ => b N * r ^ N) := by
    convert hb using 1
    funext N
    congr 1
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring_nf
  have htsumLe :
      (∑' N : ℕ, (mobiusMertensEvenConvolution k N).re * r ^ N) ≤
        ∑' N : ℕ, b N * r ^ N := by
    apply Summable.tsum_le_tsum (fun N => ?_) hconvR hbPow
    exact mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hrPos.le N)
  let F : ℂ := mobiusDiscreteLaplaceTransform x
  have hFim : F.im = 0 := mobiusDiscreteLaplaceTransform_im_eq_zero hx
  have hsqRe : (F * F).re = ‖F‖ ^ 2 := by
    rw [Complex.mul_re, hFim, zero_mul, sub_zero, Complex.sq_norm,
      Complex.normSq_apply, hFim]
    ring_nf
  have hsqIm : (F * F).im = 0 := by
    rw [Complex.mul_im, hFim]
    ring_nf
  have hFF : F * F = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using hsqRe
    · simpa only [Complex.ofReal_im] using hsqIm
  have hleft : (F ^ (2 * k)).re = ‖F‖ ^ (2 * k) := by
    calc
      (F ^ (2 * k)).re = ((F ^ 2) ^ k).re := by rw [pow_mul]
      _ = ((F * F) ^ k).re := by rw [pow_two]
      _ = ((((‖F‖ ^ 2 : ℝ) : ℂ)) ^ k).re := by rw [hFF]
      _ = (‖F‖ ^ 2) ^ k := by norm_cast
      _ = ‖F‖ ^ (2 * k) := by rw [pow_mul]
  have hfactor : (1 - Complex.exp (-(x : ℂ))) = ((1 - r : ℝ) : ℂ) := by
    have hexp : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      norm_cast
    rw [hexp]
    simp [r]
  have hright :
      (((1 - Complex.exp (-(x : ℂ))) ^ (2 * k)) *
        ∑' N : ℕ, mobiusMertensEvenConvolution k N *
          Complex.exp (-(x : ℂ)) ^ N).re =
      (1 - r) ^ (2 * k) * ∑' N : ℕ,
        (mobiusMertensEvenConvolution k N).re * r ^ N := by
    rw [Complex.mul_re]
    have haRe : (((1 - Complex.exp (-(x : ℂ))) ^ (2 * k))).re =
        (1 - r) ^ (2 * k) := by
      rw [hfactor]
      norm_cast
    have haIm : (((1 - Complex.exp (-(x : ℂ))) ^ (2 * k))).im = 0 := by
      rw [hfactor]
      norm_cast
    rw [haRe, haIm, zero_mul, sub_zero]
    rw [Complex.re_tsum hconvC]
    congr 1
    apply tsum_congr
    intro N
    exact mobiusMertensEvenConvolution_mul_exp_pow_re_eq k x N
  have heq : ‖F‖ ^ (2 * k) =
      (1 - r) ^ (2 * k) * ∑' N : ℕ,
        (mobiusMertensEvenConvolution k N).re * r ^ N := by
    calc
      ‖F‖ ^ (2 * k) = (F ^ (2 * k)).re := hleft.symm
      _ = (((1 - Complex.exp (-(x : ℂ))) ^ (2 * k)) *
          ∑' N : ℕ, mobiusMertensEvenConvolution k N *
            Complex.exp (-(x : ℂ)) ^ N).re := by
        dsimp only [F]
        rw [mobiusDiscreteLaplaceTransform_pow_even_eq_one_sub_exp_pow_even_mul_tsum hx k]
      _ = (1 - r) ^ (2 * k) * ∑' N : ℕ,
          (mobiusMertensEvenConvolution k N).re * r ^ N := hright
  rw [show ‖mobiusDiscreteLaplaceTransform x‖ = ‖F‖ by rfl, heq]
  calc
    (1 - r) ^ (2 * k) *
        (∑' N : ℕ, (mobiusMertensEvenConvolution k N).re * r ^ N) ≤
      (1 - r) ^ (2 * k) * (∑' N : ℕ, b N * r ^ N) :=
        mul_le_mul_of_nonneg_left htsumLe
          (pow_nonneg (sub_nonneg.mpr hrLe) _)
    _ = (1 - Real.exp (-x)) ^ (2 * k) *
        ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
      congr 1
      apply tsum_congr
      intro N
      congr 1
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf

/-- One-sided critical-order upper control at the `2k`-fold additive Mertens level. -/
def MobiusMertensEvenConvolutionSubpowerUpperBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusMertensEvenConvolution k N).re ≤
      C * ((N : ℝ) + 1) ^ (3 * (k : ℝ) - 1 + ε)

def mobiusMertensEvenConvolutionSubpowerAbelConstant (k : ℕ) (ε : ℝ) : ℝ :=
  1 + Real.exp 1 * 2 ^ (3 * (k : ℝ) - 1 + ε) *
    Real.Gamma (3 * (k : ℝ) + ε)

theorem mobiusMertensEvenConvolutionSubpowerAbelConstant_nonneg
    {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ mobiusMertensEvenConvolutionSubpowerAbelConstant k ε := by
  dsimp [mobiusMertensEvenConvolutionSubpowerAbelConstant]
  have hgamma := (Real.Gamma_pos_of_pos (by positivity :
    0 < 3 * (k : ℝ) + ε)).le
  positivity

theorem norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionSubpowerUpperBound
    {k : ℕ} (hk : 0 < k) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsource : ∀ N : ℕ, (mobiusMertensEvenConvolution k N).re ≤
      C * ((N : ℝ) + 1) ^ (3 * (k : ℝ) - 1 + ε))
    {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
      C * mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
        x ^ (-((k : ℝ) + ε)) := by
  let r : ℝ := 3 * (k : ℝ) - 1 + ε
  let b : ℕ → ℝ := fun N => C * ((N : ℝ) + 1) ^ r
  have hr : 0 ≤ r := by
    dsimp [r]
    have hkR : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le hr hx
  have hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x))) := by
    have hmul := hmoment.1.mul_left C
    convert hmul using 1
    funext N
    dsimp [b]
    ring_nf
  have heven :=
    norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionUpper
      k b (by simpa only [b, r] using hsource) hx hb
  have hgamma : 0 ≤ Real.Gamma (r + 1) :=
    (Real.Gamma_pos_of_pos (by dsimp [r]; positivity)).le
  have hX : 1 ≤ (1 / x) ^ (r + 1) := by
    apply Real.one_le_rpow
    · exact (one_le_div hx).2 hxOne
    · linarith
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hxOne
  have hmomentCoarse :
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
        mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
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
      _ = mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
          (1 / x) ^ (r + 1) := by
        dsimp [mobiusMertensEvenConvolutionSubpowerAbelConstant, r]
        ring_nf
  have htsum :
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
        C * (mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
          (1 / x) ^ (r + 1)) := by
    calc
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) =
          C * ∑' N : ℕ,
            ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x)) := by
        rw [← hmoment.1.tsum_mul_left C]
        apply tsum_congr
        intro N
        dsimp [b]
        ring_nf
      _ ≤ C * (mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
          (1 / x) ^ (r + 1)) := mul_le_mul_of_nonneg_left hmomentCoarse hC
  have honeSub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  have honeSubNonneg : 0 ≤ 1 - Real.exp (-x) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have htsumNonneg : 0 ≤ ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
    apply tsum_nonneg
    intro N
    dsimp [b]
    positivity
  have hfactorEven :
      (1 - Real.exp (-x)) ^ (2 * k) ≤ x ^ (2 * k) :=
    pow_le_pow_left₀ honeSubNonneg honeSub _
  have hraw : ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
      x ^ (2 * k) *
        (C * (mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
          (1 / x) ^ (r + 1))) := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
          (1 - Real.exp (-x)) ^ (2 * k) *
            ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := heven
      _ ≤ x ^ (2 * k) * ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right hfactorEven htsumNonneg
      _ ≤ x ^ (2 * k) *
          (C * (mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
            (1 / x) ^ (r + 1))) :=
        mul_le_mul_of_nonneg_left htsum (by positivity)
  have hInvPow : (1 / x) ^ (r + 1) = x ^ (-(r + 1)) := by
    rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  have hxMul : x ^ (2 * k) * x ^ (-(r + 1)) = x ^ (-((k : ℝ) + ε)) := by
    calc
      x ^ (2 * k) * x ^ (-(r + 1)) =
          x ^ ((2 * k : ℕ) : ℝ) * x ^ (-(r + 1)) := by
        congr 1
        exact (Real.rpow_natCast x (2 * k)).symm
      _ = x ^ (((2 * k : ℕ) : ℝ) + (-(r + 1))) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-((k : ℝ) + ε)) := by
        congr 1
        dsimp [r]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring_nf
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
        x ^ (2 * k) *
          (C * (mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
            (1 / x) ^ (r + 1))) := hraw
    _ = C * mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
        (x ^ (2 * k) * x ^ (-(r + 1))) := by rw [hInvPow]; ring_nf
    _ = C * mobiusMertensEvenConvolutionSubpowerAbelConstant k ε *
        x ^ (-((k : ℝ) + ε)) := by rw [hxMul]

theorem mobiusMertensEvenConvolutionSubpowerUpperBound_implies_allStrictHalfPowerDecay
    {k : ℕ} (hk : 0 < k)
    (hupper : MobiusMertensEvenConvolutionSubpowerUpperBound k) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := 2 * (k : ℝ) * b - k
  have hε : 0 < ε := by
    dsimp [ε]
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    nlinarith
  obtain ⟨C, hC, hsource⟩ := hupper ε hε
  let S : ℝ := C * mobiusMertensEvenConvolutionSubpowerAbelConstant k ε
  let D : ℝ := S + 1
  have hS : 0 ≤ S := mul_nonneg hC
    (mobiusMertensEvenConvolutionSubpowerAbelConstant_nonneg hk hε)
  rw [isBigO_iff]
  refine ⟨D, ?_⟩
  have hOneNhds : ∀ᶠ x : ℝ in nhds 0, x < 1 := Iio_mem_nhds (by norm_num)
  have hOne : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x < 1 :=
    Filter.Eventually.filter_mono inf_le_left hOneNhds
  filter_upwards [self_mem_nhdsWithin, hOne] with x hx hxOne
  change 0 < x at hx
  change x < 1 at hxOne
  have heven :=
    norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionSubpowerUpperBound
      hk hε hC hsource hx hxOne.le
  have hrpowEven : (x ^ (-b)) ^ (2 * k) = x ^ (-((k : ℝ) + ε)) := by
    calc
      (x ^ (-b)) ^ (2 * k) = (x ^ (-b)) ^ (((2 * k : ℕ) : ℝ)) :=
        (Real.rpow_natCast (x ^ (-b)) (2 * k)).symm
      _ = x ^ ((-b) * (((2 * k : ℕ) : ℝ))) :=
        (Real.rpow_mul hx.le (-b) (((2 * k : ℕ) : ℝ))).symm
      _ = x ^ (-((k : ℝ) + ε)) := by
        congr 1
        dsimp [ε]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring_nf
  rw [← hrpowEven] at heven
  have hDOne : 1 ≤ D := by dsimp [D]; linarith
  have hSD : S ≤ D := by dsimp [D]; linarith
  have hpowNe : 2 * k ≠ 0 := by omega
  have hSle : S ≤ D ^ (2 * k) :=
    hSD.trans (le_self_pow₀ hDOne hpowNe)
  have hpowPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx _
  have hD : 0 ≤ D := hDOne.trans' zero_le_one
  have hright : 0 ≤ D * x ^ (-b) := mul_nonneg hD hpowPos.le
  have htargetPow : ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
      (D * x ^ (-b)) ^ (2 * k) := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ (2 * k) ≤
          S * (x ^ (-b)) ^ (2 * k) := by
        simpa only [S] using heven
      _ ≤ D ^ (2 * k) * (x ^ (-b)) ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hSle (by positivity)
      _ = (D * x ^ (-b)) ^ (2 * k) := by rw [mul_pow]
  have hroot : ‖mobiusDiscreteLaplaceTransform x‖ ≤ D * x ^ (-b) :=
    le_of_pow_le_pow_left₀ hpowNe hright htargetPow
  rw [Real.norm_eq_abs, abs_of_pos hpowPos]
  exact hroot

theorem mobiusMertensEvenConvolutionSubpowerUpperBound_implies_riemannHypothesis
    {k : ℕ} (hk : 0 < k)
    (hupper : MobiusMertensEvenConvolutionSubpowerUpperBound k) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusMertensEvenConvolutionSubpowerUpperBound_implies_allStrictHalfPowerDecay hk hupper)

theorem mobiusMertensAllStrictHalfPowerBound_implies_evenConvolutionSubpowerUpperBound
    {k : ℕ} (hk : 0 < k)
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensEvenConvolutionSubpowerUpperBound k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  intro ε hε
  let δ : ℝ := ε / (2 * ((j + 1 : ℕ) : ℝ))
  have hjR : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hM⟩ := hMertens δ hδ
  let A : ℝ := C ^ 2
  let α : ℝ := 2 + 2 * δ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hU : ∀ N : ℕ, ‖mobiusAdditiveTriangleSecondCesaro N‖ ≤
      A * ((N : ℝ) + 1) ^ α := by
    intro N
    simpa only [A, α] using
      norm_mobiusAdditiveTriangleSecondCesaro_le_of_mertensBound
        hδ hC hM N
  refine ⟨A ^ (j + 1), pow_nonneg hA _, ?_⟩
  intro N
  have hconv := norm_additiveConvolutionPower_succ_le
    mobiusAdditiveTriangleSecondCesaro hA hα hU j N
  have hexp : (((j + 1 : ℕ) : ℝ) * α + j) =
      3 * (((j + 1 : ℕ) : ℝ)) - 1 + ε := by
    dsimp [α, δ]
    have hne : (2 * (((j + 1 : ℕ) : ℝ))) ≠ 0 := by positivity
    field_simp [hne]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf
  calc
    (mobiusMertensEvenConvolution (j + 1) N).re ≤
        ‖mobiusMertensEvenConvolution (j + 1) N‖ := Complex.re_le_norm _
    _ ≤ A ^ (j + 1) *
        ((N : ℝ) + 1) ^ (((j + 1 : ℕ) : ℝ) * α + j) := by
      simpa only [mobiusMertensEvenConvolution] using hconv
    _ = A ^ (j + 1) *
        ((N : ℝ) + 1) ^
          (3 * (((j + 1 : ℕ) : ℝ)) - 1 + ε) := by rw [hexp]

theorem mobiusMertensEvenConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens
    {k : ℕ} (hk : 0 < k)
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensEvenConvolutionSubpowerUpperBound k ↔ RiemannHypothesis := by
  constructor
  · exact mobiusMertensEvenConvolutionSubpowerUpperBound_implies_riemannHypothesis hk
  · intro hRH
    exact mobiusMertensAllStrictHalfPowerBound_implies_evenConvolutionSubpowerUpperBound
      hk (hLittlewood hRH)

theorem mobiusMertensEvenConvolution_one (N : ℕ) :
    mobiusMertensEvenConvolution 1 N = mobiusAdditiveTriangleSecondCesaro N := by
  exact additiveConvolutionPower_one _ N

theorem mobiusMertensEvenConvolution_two (N : ℕ) :
    mobiusMertensEvenConvolution 2 N = mobiusMertensFourthConvolution N := by
  change (∑ ab ∈ Finset.antidiagonal N,
    additiveConvolutionPower mobiusAdditiveTriangleSecondCesaro 1 ab.1 *
      mobiusAdditiveTriangleSecondCesaro ab.2) =
    ∑ ab ∈ Finset.antidiagonal N,
      mobiusAdditiveTriangleSecondCesaro ab.1 *
        mobiusAdditiveTriangleSecondCesaro ab.2
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [additiveConvolutionPower_one]

end

end RHTower
