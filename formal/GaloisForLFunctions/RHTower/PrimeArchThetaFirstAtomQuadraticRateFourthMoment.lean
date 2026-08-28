import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderMomentBounds

/-!
# Quadratic-rate rational certificate for the first theta atom's fourth moment

A curvature-preserving quadratic upper envelope for the local Liouville rate avoids the large
QPoly convolution in the high-order quadrature.  Four exact kernel-checked block pairs prove the
critical lower box `0.0029627 < thetaCuspAtomRawEvenMoment 2 1` without native evaluation.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

namespace ThetaQuadraticRate

def rateA (j : ℕ) : ℚ :=
  (3.14159265358979323847 : ℚ) *
      ThetaRationalQuadrature.thirtySecondExpUpper ^ j * 2 - 5 / 2

def rateB (j : ℕ) : ℚ :=
  (3.14159265358979323847 : ℚ) *
      ThetaRationalQuadrature.thirtySecondExpUpper ^ j * (1011 / 500)

def delta (j : ℕ) (y : ℝ) : ℝ :=
  (rateA j : ℝ) * y + (rateB j : ℝ) * y ^ 2

def localCert (j : ℕ) (y : ℝ) : ℝ :=
  (expNegTruncPoly 6).eval (delta j y)

def sourceCoeff (j q : ℕ) : ℚ :=
  if q = 0 then
    (6.28318530717958647692 : ℚ) *
      ThetaRationalQuadrature.thirtySecondExpLower ^ j - 3
  else
    (6.28318530717958647692 : ℚ) *
      ThetaRationalQuadrature.thirtySecondExpLower ^ j *
      (2 ^ q / (q.factorial : ℚ))

def localCoeff (j m l : ℕ) : ℚ :=
  ((-1 : ℚ) ^ m) / (m.factorial : ℚ) * (m.choose l : ℚ) *
    rateA j ^ l * rateB j ^ (m - l)

def shiftedPowMass (n s : ℕ) (a h : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℚ) * a ^ k * h ^ (n - k + s + 1) /
      (n - k + s + 1 : ℚ)

def lowerMass (r j : ℕ) : ℚ :=
  (12.5663706143591729538 : ℚ) * (0.0432139182637 : ℚ) *
    ThetaRationalQuadrature.endpointLower j *
      (∑ m ∈ Finset.range 6,
        ∑ l ∈ Finset.range (m + 1),
          ∑ q ∈ Finset.range 9,
            sourceCoeff j q * localCoeff j m l *
              shiftedPowMass (2 * r) (q + (2 * m - l)) ((j : ℚ) / 64) (1 / 64))

def lowerBlock (r b : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 8, lowerMass r (8 * b + k)

end ThetaQuadraticRate

theorem thetaCuspFirstSourceTaylorLower64_eval_eq_quadraticSourceSum
    (j : ℕ) (y : ℝ) :
    (thetaCuspFirstSourceTaylorLower64 j).eval y =
      ∑ q ∈ Finset.range 9,
        (ThetaQuadraticRate.sourceCoeff j q : ℚ) * y ^ q := by
  rw [thetaCuspFirstSourceTaylorLower64]
  simp only [eval_sub, eval_mul, eval_C]
  rw [thetaCuspExpTwoTaylorEightPolynomial_eval,
    ← thetaRationalQuadrature_thirtySecondExpLower_cast]
  norm_num [ThetaQuadraticRate.sourceCoeff, Finset.sum_range_succ]
  ring

theorem thetaQuadraticRate_localCert_eq_sum
    (j : ℕ) (y : ℝ) :
    ThetaQuadraticRate.localCert j y =
      ∑ m ∈ Finset.range 6,
        ∑ l ∈ Finset.range (m + 1),
          (ThetaQuadraticRate.localCoeff j m l : ℚ) * y ^ (2 * m - l) := by
  rw [ThetaQuadraticRate.localCert, eval_expNegTruncPoly]
  apply Finset.sum_congr rfl
  intro m hm
  rw [ThetaQuadraticRate.delta, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hlmem
  have hllt : l < m + 1 := Finset.mem_range.mp hlmem
  have hl : l ≤ m := by omega
  have hyexp : y ^ l * (y ^ 2) ^ (m - l) = y ^ (2 * m - l) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [ThetaQuadraticRate.localCoeff]
  push_cast
  rw [mul_pow, mul_pow]
  rw [show (ThetaQuadraticRate.rateA j : ℝ) ^ l * y ^ l *
        ((ThetaQuadraticRate.rateB j : ℝ) ^ (m - l) * (y ^ 2) ^ (m - l)) *
          (m.choose l : ℝ) =
      (ThetaQuadraticRate.rateA j : ℝ) ^ l *
        (ThetaQuadraticRate.rateB j : ℝ) ^ (m - l) * (m.choose l : ℝ) *
          (y ^ l * (y ^ 2) ^ (m - l)) by ring, hyexp]
  ring

theorem intervalIntegral_shiftedPow_eq_mass
    (n s : ℕ) (a h : ℚ) :
    (∫ y : ℝ in 0..(h : ℝ), ((a : ℝ) + y) ^ n * y ^ s) =
      (ThetaQuadraticRate.shiftedPowMass n s a h : ℚ) := by
  rw [show (fun y : ℝ => ((a : ℝ) + y) ^ n * y ^ s) =
      fun y : ℝ => ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℚ) * a ^ k : ℚ) * y ^ (n - k + s) by
    funext y
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    rw [pow_add]
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · rw [ThetaQuadraticRate.shiftedPowMass]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    have hk' : k ≤ n := by omega
    rw [Nat.cast_sub hk']
    ring
  · intro k hk
    exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _

theorem thetaCuspExpTwoTaylorEightUpperPolynomial_eval_le_quadratic
    {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    thetaCuspExpTwoTaylorEightUpperPolynomial.eval y ≤
      1 + 2 * y + (1011 / 500 : ℝ) * y ^ 2 := by
  have hpow (n : ℕ) : y ^ (n + 2) ≤ y ^ 2 * (1 / 64 : ℝ) ^ n := by
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyh n) (sq_nonneg y)
  have h1 := hpow 1
  have h2 := hpow 2
  have h3 := hpow 3
  have h4 := hpow 4
  have h5 := hpow 5
  have h6 := hpow 6
  have h7 := hpow 7
  rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
    thetaCuspExpTwoTaylorEightPolynomial_eval]
  norm_num at h1 h2 h3 h4 h5 h6 h7 ⊢
  nlinarith [sq_nonneg y]

theorem thetaCuspFirstRateTaylorUpperDelta64_eval_le_quadratic
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (thetaCuspFirstRateTaylorUpperDelta64 j).eval y ≤
      ThetaQuadraticRate.delta j y := by
  have hpoly := thetaCuspExpTwoTaylorEightUpperPolynomial_eval_le_quadratic hy hyh
  have hup : 0 ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hscale : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ j := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hpoly 1) hscale
  rw [thetaCuspFirstRateTaylorUpperDelta64]
  simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
  rw [ThetaQuadraticRate.delta, ThetaQuadraticRate.rateA,
    ThetaQuadraticRate.rateB]
  push_cast
  rw [thetaRationalQuadrature_thirtySecondExpUpper_cast]
  nlinarith

theorem thetaQuadraticRate_delta_nonneg
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ThetaQuadraticRate.delta j y := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper ^ j := one_le_pow₀ hbase
  rw [ThetaQuadraticRate.delta, ThetaQuadraticRate.rateA,
    ThetaQuadraticRate.rateB]
  push_cast
  rw [thetaRationalQuadrature_thirtySecondExpUpper_cast]
  have hA : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ j * 2 - 5 / 2 := by
    nlinarith
  positivity

theorem thetaQuadraticRate_delta_le_one
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    ThetaQuadraticRate.delta j y ≤ 1 := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : thetaCuspThirtySecondExpTaylorUpper ^ j ≤
      thetaCuspThirtySecondExpTaylorUpper ^ 64 :=
    pow_le_pow_right₀ hbase (by omega)
  have hy2 := mul_self_le_mul_self hy hyh
  rw [ThetaQuadraticRate.delta, ThetaQuadraticRate.rateA,
    ThetaQuadraticRate.rateB]
  push_cast
  rw [thetaRationalQuadrature_thirtySecondExpUpper_cast]
  have hcap :
      ((3.14159265358979323847 : ℝ) *
          thetaCuspThirtySecondExpTaylorUpper ^ 64 * 2 - 5 / 2) * (1 / 64) +
        ((3.14159265358979323847 : ℝ) *
          thetaCuspThirtySecondExpTaylorUpper ^ 64 * (1011 / 500)) *
            (1 / 64) ^ 2 < 1 := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hA0 : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ j * 2 - 5 / 2 := by
    have hjpow : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper ^ j := one_le_pow₀ hbase
    nlinarith
  have hB0 : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ j * (1011 / 500) := by positivity
  have hpowA :
      (3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ j * 2 - 5 / 2 ≤
        (3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ 64 * 2 - 5 / 2 := by
    nlinarith
  have hpowB :
      (3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ j * (1011 / 500) ≤
        (3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ 64 * (1011 / 500) := by
    nlinarith
  have hA64 : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ 64 * 2 - 5 / 2 := hA0.trans hpowA
  have hB64 : 0 ≤ (3.14159265358979323847 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ 64 * (1011 / 500) := by positivity
  have hmA :
      ((3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ j * 2 - 5 / 2) * y ≤
        ((3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ 64 * 2 - 5 / 2) * (1 / 64) :=
    (mul_le_mul_of_nonneg_right hpowA hy).trans
      (mul_le_mul_of_nonneg_left hyh hA64)
  have hmB :
      ((3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ j * (1011 / 500)) * y ^ 2 ≤
        ((3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ 64 * (1011 / 500)) * (1 / 64) ^ 2 :=
    (mul_le_mul_of_nonneg_right hpowB (sq_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (by simpa [pow_two] using hy2) hB64)
  linarith

theorem thetaQuadraticRate_local_pos
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    0 < ThetaQuadraticRate.localCert j y := by
  rw [ThetaQuadraticRate.localCert]
  exact expNegTruncPoly_six_eval_pos_of_mem_unit
    (thetaQuadraticRate_delta_nonneg j hy)
    (thetaQuadraticRate_delta_le_one hj hy hyh)

theorem thetaQuadraticRate_local_le_exp
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ThetaQuadraticRate.localCert j y ≤ Real.exp (-ThetaQuadraticRate.delta j y) := by
  have ht := thetaQuadraticRate_delta_nonneg j hy
  rw [ThetaQuadraticRate.localCert]
  rcases ht.eq_or_lt with hzero | hpos
  · rw [← hzero]
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 6) (by norm_num) hpos
    norm_num at h
    exact h.le

theorem thetaCuspFirstGibbsQuadraticLower64_le
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        ThetaQuadraticRate.localCert j y ≤
      thetaCuspLiouvilleGibbsAtom 1 ((j : ℝ) / 64 + y) := by
  have hrate0 :=
    (thetaCuspFirstLiouvilleRate_taylor_bounds64 (j := j) hy hyh).2
  have hdelta := thetaCuspFirstRateTaylorUpperDelta64_eval_le_quadratic j hy hyh
  have hrate : thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y) ≤
      thetaCuspFirstRateTaylorUpperEndpoint64 j + ThetaQuadraticRate.delta j y :=
    hrate0.trans (add_le_add (le_refl _) hdelta)
  have hendpoint :=
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_le_exp hj
  have hlocal := thetaQuadraticRate_local_le_exp j hy
  have hlocal0 := (thetaQuadraticRate_local_pos hj hy hyh).le
  by_cases hendpoint0 :
      0 ≤ thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j
  · rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
    calc
      (0.0432139182637 : ℝ) *
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            ThetaQuadraticRate.localCert j y ≤
          Real.exp (-Real.pi) *
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            ThetaQuadraticRate.localCert j y := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_lower hendpoint0)
          hlocal0
      _ ≤ Real.exp (-Real.pi) *
            Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) *
            Real.exp (-ThetaQuadraticRate.delta j y) := by gcongr
      _ = Real.exp (-Real.pi) *
            Real.exp (-(thetaCuspFirstRateTaylorUpperEndpoint64 j +
              ThetaQuadraticRate.delta j y)) := by
        rw [show -(thetaCuspFirstRateTaylorUpperEndpoint64 j +
            ThetaQuadraticRate.delta j y) =
          -thetaCuspFirstRateTaylorUpperEndpoint64 j +
            -ThetaQuadraticRate.delta j y by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-Real.pi) *
            Real.exp (-thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y)) := by
        gcongr
  · have hendpointNeg :
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j ≤ 0 :=
      le_of_not_ge hendpoint0
    have hleft : (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        ThetaQuadraticRate.localCert j y ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hendpointNeg) hlocal0
    exact hleft.trans (by
      rw [thetaCuspLiouvilleGibbsAtom_apply]
      positivity)

def thetaCuspFirstAtomQuadraticLowerCertificate64
    (r j : ℕ) (y : ℝ) : ℝ :=
  (12.5663706143591729538 : ℝ) * ((j : ℝ) / 64 + y) ^ (2 * r) *
    (thetaCuspFirstSourceTaylorLower64 j).eval y *
    ((0.0432139182637 : ℝ) *
      thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
      ThetaQuadraticRate.localCert j y)

theorem continuous_thetaCuspFirstAtomQuadraticLowerCertificate64
    (r j : ℕ) : Continuous (thetaCuspFirstAtomQuadraticLowerCertificate64 r j) := by
  unfold thetaCuspFirstAtomQuadraticLowerCertificate64
    ThetaQuadraticRate.localCert ThetaQuadraticRate.delta
  fun_prop

theorem thetaCuspFirstAtomQuadraticLowerCertificate64_le_density
    {r j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    thetaCuspFirstAtomQuadraticLowerCertificate64 r j y ≤
      2 * (((j : ℝ) / 64 + y) ^ (2 * r) *
        thetaCuspSourceTerm ((j : ℝ) / 64 + y) 1) := by
  let x : ℝ := (j : ℝ) / 64 + y
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hs := thetaCuspFirstSourceTaylorLower64_eval_le_actual j hy
  have hs0 := thetaCuspFirstSourceTaylorLower64_eval_nonneg j hy
  have hg := thetaCuspFirstGibbsQuadraticLower64_le hj hy hyh
  have hactualG0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualS0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := hs0.trans hs
  have houter : (12.5663706143591729538 : ℝ) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  by_cases hg0 : 0 ≤
      (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        ThetaQuadraticRate.localCert j y
  · rw [thetaCuspFirstAtomQuadraticLowerCertificate64]
    change (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
        (thetaCuspFirstSourceTaylorLower64 j).eval y *
        ((0.0432139182637 : ℝ) *
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
          ThetaQuadraticRate.localCert j y) ≤
      2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
    rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
    calc
      (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
            (thetaCuspFirstSourceTaylorLower64 j).eval y *
            ((0.0432139182637 : ℝ) *
              thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
              ThetaQuadraticRate.localCert j y) ≤
          (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
            (thetaCuspFirstSourceTaylorLower64 j).eval y *
            thetaCuspLiouvilleGibbsAtom 1 x := by
        exact mul_le_mul_of_nonneg_left hg
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0)
      _ ≤ (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
            (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs
            (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hactualG0
      _ ≤ (4 * Real.pi) * x ^ (2 * r) *
            (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualS0)
          hactualG0
      _ = 2 * (x ^ (2 * r) *
            (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
              thetaCuspLiouvilleGibbsAtom 1 x)) := by ring
  · have hgNonpos :
        (0.0432139182637 : ℝ) *
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
          ThetaQuadraticRate.localCert j y ≤ 0 := le_of_not_ge hg0
    rw [thetaCuspFirstAtomQuadraticLowerCertificate64]
    change (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
        (thetaCuspFirstSourceTaylorLower64 j).eval y *
        ((0.0432139182637 : ℝ) *
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
          ThetaQuadraticRate.localCert j y) ≤
      2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
    have hprefix : 0 ≤ (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
        (thetaCuspFirstSourceTaylorLower64 j).eval y :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0
    have hleft : (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
        (thetaCuspFirstSourceTaylorLower64 j).eval y *
        ((0.0432139182637 : ℝ) *
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
          ThetaQuadraticRate.localCert j y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hprefix hgNonpos
    have hsource0 : 0 ≤ thetaCuspSourceTerm x 1 := by
      rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
      exact mul_nonneg (mul_nonneg (by positivity) hactualS0) hactualG0
    have hright : 0 ≤ 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) :=
      mul_nonneg (by norm_num) <|
        mul_nonneg (pow_nonneg hx0 _) hsource0
    exact hleft.trans hright

theorem thetaCuspFirstAtomQuadraticLowerCertificate64_eq_sum
    (r j : ℕ) (y : ℝ) :
    thetaCuspFirstAtomQuadraticLowerCertificate64 r j y =
      (12.5663706143591729538 : ℝ) * (0.0432139182637 : ℝ) *
        (ThetaRationalQuadrature.endpointLower j : ℚ) *
        (∑ m ∈ Finset.range 6,
          ∑ l ∈ Finset.range (m + 1),
            ∑ q ∈ Finset.range 9,
              (ThetaQuadraticRate.sourceCoeff j q : ℝ) *
                (ThetaQuadraticRate.localCoeff j m l : ℝ) *
                (((j : ℝ) / 64 + y) ^ (2 * r) * y ^ (q + (2 * m - l)))) := by
  rw [thetaCuspFirstAtomQuadraticLowerCertificate64,
    thetaCuspFirstSourceTaylorLower64_eval_eq_quadraticSourceSum,
    thetaQuadraticRate_localCert_eq_sum,
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem intervalIntegral_thetaCuspFirstAtomQuadraticLowerCertificate64_eq_mass
    (r j : ℕ) :
    (∫ y in (0 : ℝ)..1 / 64,
      thetaCuspFirstAtomQuadraticLowerCertificate64 r j y) =
      (ThetaQuadraticRate.lowerMass r j : ℚ) := by
  rw [show thetaCuspFirstAtomQuadraticLowerCertificate64 r j = fun y : ℝ =>
      (12.5663706143591729538 : ℝ) * (0.0432139182637 : ℝ) *
        (ThetaRationalQuadrature.endpointLower j : ℚ) *
        (∑ m ∈ Finset.range 6,
          ∑ l ∈ Finset.range (m + 1),
            ∑ q ∈ Finset.range 9,
              (ThetaQuadraticRate.sourceCoeff j q : ℝ) *
                (ThetaQuadraticRate.localCoeff j m l : ℝ) *
                (((j : ℝ) / 64 + y) ^ (2 * r) * y ^ (q + (2 * m - l)))) by
    funext y
    exact thetaCuspFirstAtomQuadraticLowerCertificate64_eq_sum r j y]
  rw [intervalIntegral.integral_const_mul,
    ThetaQuadraticRate.lowerMass]
  push_cast
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q hq
        rw [intervalIntegral.integral_const_mul]
        congr 1
        convert intervalIntegral_shiftedPow_eq_mass
          (2 * r) (q + (2 * m - l)) ((j : ℚ) / 64) (1 / 64) using 1 <;>
          norm_num
      · intro q hq
        exact (by fun_prop : Continuous (fun y : ℝ =>
          (ThetaQuadraticRate.sourceCoeff j q : ℝ) *
            (ThetaQuadraticRate.localCoeff j m l : ℝ) *
            (((j : ℝ) / 64 + y) ^ (2 * r) *
              y ^ (q + (2 * m - l))))).intervalIntegrable _ _
    · intro l hl
      exact (by fun_prop : Continuous (fun y : ℝ =>
        ∑ q ∈ Finset.range 9,
          (ThetaQuadraticRate.sourceCoeff j q : ℝ) *
            (ThetaQuadraticRate.localCoeff j m l : ℝ) *
            (((j : ℝ) / 64 + y) ^ (2 * r) *
              y ^ (q + (2 * m - l))))).intervalIntegrable _ _
  · intro m hm
    exact (by fun_prop : Continuous (fun y : ℝ =>
      ∑ l ∈ Finset.range (m + 1),
        ∑ q ∈ Finset.range 9,
          (ThetaQuadraticRate.sourceCoeff j q : ℝ) *
            (ThetaQuadraticRate.localCoeff j m l : ℝ) *
            (((j : ℝ) / 64 + y) ^ (2 * r) *
              y ^ (q + (2 * m - l))))).intervalIntegrable _ _

def thetaCuspFirstAtomQuadraticLowerIntervalMass64 (r j : ℕ) : ℝ :=
  (ThetaQuadraticRate.lowerMass r j : ℚ)

theorem sum_firstAtomQuadraticLowerMass64_le_thetaCuspAtomRawEvenMoment
    (r : ℕ) :
    (∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomQuadraticLowerIntervalMass64 r j) ≤
      thetaCuspAtomRawEvenMoment r 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 64) :
      thetaCuspFirstAtomQuadraticLowerIntervalMass64 r j ≤
        ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    rw [thetaCuspFirstAtomQuadraticLowerIntervalMass64,
      ← intervalIntegral_thetaCuspFirstAtomQuadraticLowerCertificate64_eq_mass]
    calc
      (∫ y in (0 : ℝ)..1 / 64,
          thetaCuspFirstAtomQuadraticLowerCertificate64 r j y) ≤
          ∫ y in (0 : ℝ)..1 / 64, f (y + (j : ℝ) / 64) := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact (continuous_thetaCuspFirstAtomQuadraticLowerCertificate64 r j).intervalIntegrable _ _
        · exact (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
        · intro y hy
          simpa only [f, add_comm] using
            thetaCuspFirstAtomQuadraticLowerCertificate64_le_density hj hy.1 hy.2
      _ = ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> push_cast <;> ring
  have hsum :
      (∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomQuadraticLowerIntervalMass64 r j) ≤
        ∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 64) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hwindow : (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment r 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  exact hsum.trans (hjoin.le.trans (hwindow.trans hraw.le))

local macro "quadratic_rate_norm_num" : tactic =>
  `(tactic|
    norm_num (config := { maxSteps := 1000000 }) [
      ThetaQuadraticRate.lowerBlock,
      ThetaQuadraticRate.lowerMass,
      ThetaQuadraticRate.sourceCoeff,
      ThetaQuadraticRate.localCoeff,
      ThetaQuadraticRate.shiftedPowMass,
      ThetaQuadraticRate.rateA,
      ThetaQuadraticRate.rateB,
      ThetaRationalQuadrature.endpointLower,
      ThetaRationalQuadrature.roundDown,
      ThetaRationalQuadrature.upperIncrement,
      ThetaRationalQuadrature.thirtySecondExpUpper,
      ThetaRationalQuadrature.thirtySecondExpLower,
      ThetaRationalQuadrature.expTwoTaylorUpper,
      ThetaRationalQuadrature.expTwoTaylor,
      ThetaRationalQuadrature.expNeg,
      ThetaRationalQuadrature.eval,
      ThetaRationalQuadrature.pow,
      ThetaRationalQuadrature.mul,
      ThetaRationalQuadrature.add,
      ThetaRationalQuadrature.scale,
      ThetaRationalQuadrature.C,
      ThetaRationalQuadrature.X,
      Rat.floor_def,
      Nat.choose,
      Nat.factorial,
      Finset.sum_range_succ])

set_option maxRecDepth 60000 in
set_option maxHeartbeats 36000000 in
theorem twoThousandTwoHundredEightyEight_div_tenMillion_lt_quadraticLowerBlock_zero_one :
    (0.0002288 : ℚ) <
      ThetaQuadraticRate.lowerBlock 2 0 + ThetaQuadraticRate.lowerBlock 2 1 := by
  quadratic_rate_norm_num

set_option maxRecDepth 60000 in
set_option maxHeartbeats 36000000 in
theorem eighteenThousandSixHundredThirtyEight_div_tenMillion_lt_quadraticLowerBlock_two_three :
    (0.0018638 : ℚ) <
      ThetaQuadraticRate.lowerBlock 2 2 + ThetaQuadraticRate.lowerBlock 2 3 := by
  quadratic_rate_norm_num

set_option maxRecDepth 60000 in
set_option maxHeartbeats 36000000 in
theorem eightyFourThousandSixHundredTwentyFive_div_hundredMillion_lt_quadraticLowerBlock_four_five :
    (0.00084625 : ℚ) <
      ThetaQuadraticRate.lowerBlock 2 4 + ThetaQuadraticRate.lowerBlock 2 5 := by
  quadratic_rate_norm_num

set_option maxRecDepth 60000 in
set_option maxHeartbeats 36000000 in
theorem twoThousandThreeHundredEightyFive_div_hundredMillion_lt_quadraticLowerBlock_six_seven :
    (0.00002385 : ℚ) <
      ThetaQuadraticRate.lowerBlock 2 6 + ThetaQuadraticRate.lowerBlock 2 7 := by
  quadratic_rate_norm_num

theorem twentyNineThousandSixHundredTwentySeven_div_tenMillion_lt_sum_quadraticLowerMass64 :
    (0.0029627 : ℚ) <
      ∑ j ∈ Finset.range 64, ThetaQuadraticRate.lowerMass 2 j := by
  have h0 := twoThousandTwoHundredEightyEight_div_tenMillion_lt_quadraticLowerBlock_zero_one
  have h1 := eighteenThousandSixHundredThirtyEight_div_tenMillion_lt_quadraticLowerBlock_two_three
  have h2 := eightyFourThousandSixHundredTwentyFive_div_hundredMillion_lt_quadraticLowerBlock_four_five
  have h3 := twoThousandThreeHundredEightyFive_div_hundredMillion_lt_quadraticLowerBlock_six_seven
  norm_num [ThetaQuadraticRate.lowerBlock, Finset.sum_range_succ] at h0 h1 h2 h3 ⊢
  linarith

theorem twentyNineThousandSixHundredTwentySeven_div_tenMillion_lt_thetaCuspAtomRawEvenMoment_two_one_quadratic :
    (0.0029627 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  have hq := twentyNineThousandSixHundredTwentySeven_div_tenMillion_lt_sum_quadraticLowerMass64
  have hr : (0.0029627 : ℝ) <
      ∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomQuadraticLowerIntervalMass64 2 j := by
    simp only [thetaCuspFirstAtomQuadraticLowerIntervalMass64]
    have hmul : (29627 : ℚ) < 10000000 *
        ∑ j ∈ Finset.range 64, ThetaQuadraticRate.lowerMass 2 j := by
      norm_num at hq ⊢
      linarith
    have hmulR : (29627 : ℝ) < 10000000 *
        (∑ j ∈ Finset.range 64, ThetaQuadraticRate.lowerMass 2 j : ℚ) := by
      exact_mod_cast hmul
    norm_num at hmulR ⊢
    linarith
  exact hr.trans_le (sum_firstAtomQuadraticLowerMass64_le_thetaCuspAtomRawEvenMoment 2)

end

end RHTower
