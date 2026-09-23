import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryBalance
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain

/-!
# Cofinal summability of the order-growing boundary-jet packet

At every nonempty Gamma depth `N`, matching boundary-jet order `N` gives enough inverse prime-log decay to make every
actual von Mangoldt--Gamma source feature square summable.  The proof is unconditional and uses:

* the exact Taylor remainder bound for the oriented Gamma anomaly;
* the exact order-growing two-boundary residual;
* `Lambda(n) <= log n`;
* the already formalized Cauchy-condensation proof that
  `sum 1 / (n * log(n)^(2 : ℕ))` converges.

This proves the analytic existence of the full finite-depth `ell^(2 : ℕ)` source packet.  It does not
identify its limiting Gram with the completed prime--Gamma moment Hankel block.
-/

open Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- A family of summable logarithmic von Mangoldt majorants. -/
def vonMangoldtInverseLogPowerWeight (q n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n / Real.log n ^ (q + 3)

theorem vonMangoldtInverseLogPowerWeight_nonneg (q n : ℕ) :
    0 ≤ vonMangoldtInverseLogPowerWeight q n := by
  rcases n with _ | n
  · simp [vonMangoldtInverseLogPowerWeight, finiteVonMangoldtRealWeight]
  · exact div_nonneg (finiteVonMangoldtRealWeight_nonneg (n + 1))
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))) _)

/-- `Lambda(n) <= log n` reduces every exponent at least three to the condensed
`1/(n*log(n)^(2 : ℕ))` majorant. -/
theorem vonMangoldtInverseLogPowerWeight_le_invNatLogSq (q n : ℕ) :
    vonMangoldtInverseLogPowerWeight q n ≤
      (Real.log 2) ^ (-(q : ℤ)) * invNatLogSq n := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;>
      simp [vonMangoldtInverseLogPowerWeight, finiteVonMangoldtRealWeight, invNatLogSq]
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hnpos (by exact_mod_cast hn)
    have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    rw [vonMangoldtInverseLogPowerWeight, finiteVonMangoldtRealWeight, invNatLogSq]
    rw [zpow_neg, zpow_natCast]
    have hpow : Real.log 2 ^ q ≤ Real.log (n : ℝ) ^ q :=
      pow_le_pow_left₀ hlog2pos.le hlog2le q
    have hden : 0 < (n : ℝ) * Real.log (n : ℝ) ^ (q + 3) := by positivity
    calc
      (ArithmeticFunction.vonMangoldt n / (n : ℝ)) /
          Real.log (n : ℝ) ^ (q + 3) =
          ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) * Real.log (n : ℝ) ^ (q + 3)) := by ring
      _ ≤ Real.log (n : ℝ) /
            ((n : ℝ) * Real.log (n : ℝ) ^ (q + 3)) :=
        div_le_div_of_nonneg_right hvm hden.le
      _ = 1 / ((n : ℝ) * Real.log (n : ℝ) ^ (q + 2)) := by
        field_simp
        ring
      _ ≤ (Real.log 2 ^ q)⁻¹ *
            (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) := by
        have hlowpos :
            0 < (n : ℝ) * Real.log 2 ^ q * Real.log (n : ℝ) ^ 2 := by positivity
        rw [show (Real.log 2 ^ q)⁻¹ *
            (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) =
              1 / ((n : ℝ) * Real.log 2 ^ q * Real.log (n : ℝ) ^ 2) by
          field_simp]
        apply one_div_le_one_div_of_le hlowpos
        rw [pow_add]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow
            (sq_nonneg (Real.log (n : ℝ)))) hnpos.le

theorem summable_vonMangoldtInverseLogPowerWeight (q : ℕ) :
    Summable (vonMangoldtInverseLogPowerWeight q) := by
  exact Summable.of_nonneg_of_le (vonMangoldtInverseLogPowerWeight_nonneg q)
    (vonMangoldtInverseLogPowerWeight_le_invNatLogSq q)
    (summable_invNatLogSq.mul_left ((Real.log 2) ^ (-(q : ℤ))))

/-- Uniform rational bound for the order-`k` two-boundary residual on a sufficiently long real
prime-log ray. -/
theorem norm_twoBoundaryCauchyJetResidual_le
    (k : ℕ) (w : ℂ) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hw : 2 * ‖w‖ ≤ lambda) :
    ‖twoBoundaryCauchyJetResidual k (1 / 2) w (lambda : ℂ)‖ ≤
      (2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ / lambda ^ 2) ^ k *
        (2 / lambda) := by
  have hlpos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hl2 : 1 ≤ lambda ^ 2 := by nlinarith
  have hreal : 0 ≤ lambda ^ 2 - (1 / 4 : ℝ) := by nlinarith
  have hdenNorm :
      ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ =
        lambda ^ 2 - (1 / 4 : ℝ) := by
    calc
      ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ =
          ‖((lambda ^ 2 - (1 / 4 : ℝ) : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
      _ = |lambda ^ 2 - (1 / 4 : ℝ)| := Complex.norm_real _
      _ = lambda ^ 2 - (1 / 4 : ℝ) := abs_of_nonneg hreal
  have hdenLower : lambda ^ 2 / 2 ≤
      ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ := by
    rw [hdenNorm]
    nlinarith
  have hdenPos : 0 < ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ :=
    lt_of_lt_of_le (by positivity : 0 < lambda ^ 2 / 2) hdenLower
  have hratio :
      ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ /
          ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ ≤
        2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ / lambda ^ 2 := by
    apply (div_le_iff₀ hdenPos).2
    calc
      ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ =
          (2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ / lambda ^ 2) *
            (lambda ^ 2 / 2) := by field_simp
      _ ≤ (2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖ / lambda ^ 2) *
          ‖(lambda : ℂ) ^ 2 - (1 / 2 : ℂ) ^ 2‖ :=
        mul_le_mul_of_nonneg_left hdenLower (by positivity)
  have hplusLower : lambda / 2 ≤ ‖w + (lambda : ℂ)‖ := by
    have hreverse : ‖(lambda : ℂ)‖ - ‖-w‖ ≤ ‖(lambda : ℂ) - (-w)‖ :=
      norm_sub_norm_le (lambda : ℂ) (-w)
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos] at hreverse
    have hhalf : lambda / 2 ≤ lambda - ‖w‖ := by linarith
    calc
      lambda / 2 ≤ lambda - ‖w‖ := hhalf
      _ ≤ ‖(lambda : ℂ) - (-w)‖ := hreverse
      _ = ‖w + (lambda : ℂ)‖ := by congr 1; ring
  have hplusPos : 0 < ‖w + (lambda : ℂ)‖ :=
    lt_of_lt_of_le (by positivity : 0 < lambda / 2) hplusLower
  have hinv : 1 / ‖w + (lambda : ℂ)‖ ≤ 2 / lambda := by
    rw [show 2 / lambda = 1 / (lambda / 2) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) hplusLower
  rw [twoBoundaryCauchyJetResidual, twoBoundaryCauchyJetNormalizer,
    norm_div, norm_pow, norm_div]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hratio k)
    (by simpa only [one_div] using hinv)
    (by positivity) (by positivity)

/-- Absolute form of the exact Taylor remainder estimate for the oriented anomaly. -/
theorem abs_expNegOrientedRemainder_le_pow_div_factorial
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |expNegOrientedRemainder m x| ≤ x ^ m / (m.factorial : ℝ) := by
  rw [expNegOrientedRemainder, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  simpa only [expNegTruncError, abs_sub_comm] using
    expNegTruncError_le_pow_div_factorial m hx

/-- Closed power bound at the canonical depth-matched order `N`. -/
theorem norm_twoBoundaryCauchyOrderGrowingResidual_le
    (N : ℕ) (w : ℂ) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hw : 2 * ‖w‖ ≤ lambda) :
    ‖twoBoundaryCauchyJetResidual N (1 / 2) w (lambda : ℂ)‖ ≤
      (2 * (2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖) ^ N) /
        lambda ^ (2 * N + 1) := by
  have hl0 : lambda ≠ 0 := (lt_of_lt_of_le zero_lt_one hlambda).ne'
  refine (norm_twoBoundaryCauchyJetResidual_le N w hlambda hw).trans_eq ?_
  rw [div_pow]
  field_simp [pow_ne_zero _ hl0]
  ring

/-- The actual depth-`N` Gamma numerator grows by at most `log(n)^N`. -/
theorem norm_vonMangoldtAllDepthJetFeatureNumerator_le
    (N : ℕ) (i : Fin N) (n : ℕ) (hlog : 1 ≤ Real.log n) :
    ‖((Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ (i : ℕ) *
        expNegOrientedRemainder (N - (i : ℕ)) (Real.log n) : ℝ) : ℂ)‖ ≤
      Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ N := by
  have hweight : 0 ≤ finiteVonMangoldtRealWeight n :=
    finiteVonMangoldtRealWeight_nonneg n
  have hsqrt : 0 ≤ Real.sqrt (finiteVonMangoldtRealWeight n) := Real.sqrt_nonneg _
  have hlog0 : 0 ≤ Real.log n := zero_le_one.trans hlog
  have hrem := abs_expNegOrientedRemainder_le_pow_div_factorial
    (N - (i : ℕ)) hlog0
  have hfact : (1 : ℝ) ≤ ((N - (i : ℕ)).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos (N - (i : ℕ))
  have hfactpos : (0 : ℝ) < ((N - (i : ℕ)).factorial : ℕ) :=
    lt_of_lt_of_le zero_lt_one hfact
  have hrem' :
      |expNegOrientedRemainder (N - (i : ℕ)) (Real.log n)| ≤
        Real.log n ^ (N - (i : ℕ)) := by
    refine hrem.trans ?_
    apply (div_le_iff₀ hfactpos).2
    nlinarith [pow_nonneg hlog0 (N - (i : ℕ))]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hsqrt, abs_pow, abs_of_nonneg hlog0]
  calc
    Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ (i : ℕ) *
        |expNegOrientedRemainder (N - (i : ℕ)) (Real.log n)| ≤
      Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ (i : ℕ) *
        Real.log n ^ (N - (i : ℕ)) :=
      mul_le_mul_of_nonneg_left hrem'
        (mul_nonneg hsqrt (pow_nonneg hlog0 _))
    _ = Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ N := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt i.isLt)]

/-- Explicit constant in the full order-growing feature bound. -/
def orderGrowingCauchyFeatureBoundConstant (N : ℕ) (w : ℂ) : ℝ :=
  2 * (2 * ‖w ^ 2 - (1 / 2 : ℂ) ^ 2‖) ^ N

/-- Pointwise tail bound whose exponent is strong enough for unconditional condensation. -/
theorem normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature_le
    (N : ℕ) (i : Fin N) (w : ℂ) (n : ℕ)
    (hlog : 1 ≤ Real.log n) (hw : 2 * ‖w‖ ≤ Real.log n) :
    ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N w n‖ ^ 2 ≤
      orderGrowingCauchyFeatureBoundConstant N w ^ 2 *
        vonMangoldtInverseLogPowerWeight (2 * N - 1) n := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hlog
  have hweight : 0 ≤ finiteVonMangoldtRealWeight n :=
    finiteVonMangoldtRealWeight_nonneg n
  have hnum := norm_vonMangoldtAllDepthJetFeatureNumerator_le N i n hlog
  have hres := norm_twoBoundaryCauchyOrderGrowingResidual_le N w hlog hw
  have hnorm :
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
          N i N w n‖ ≤
        (Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ N) *
          (orderGrowingCauchyFeatureBoundConstant N w /
            Real.log n ^ (2 * N + 1)) := by
    rw [finiteVonMangoldtAllDepthJetBalancedCauchyFeature,
      finiteExponentialAllDepthJetBalancedCauchyFeature, norm_mul]
    exact mul_le_mul hnum hres (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hlogpos.le _))
  calc
    ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N w n‖ ^ 2 ≤
      ((Real.sqrt (finiteVonMangoldtRealWeight n) * Real.log n ^ N) *
        (orderGrowingCauchyFeatureBoundConstant N w /
          Real.log n ^ (2 * N + 1))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = orderGrowingCauchyFeatureBoundConstant N w ^ 2 *
        vonMangoldtInverseLogPowerWeight (2 * N - 1) n := by
      rw [vonMangoldtInverseLogPowerWeight]
      rw [show 2 * N - 1 + 3 = 2 * N + 2 by omega]
      have hsqrt := Real.sq_sqrt hweight
      field_simp [hlogpos.ne']
      rw [hsqrt]
      ring

/-- Every single Gamma-jet coordinate of the concrete order-growing packet lies in `ell^(2 : ℕ)` over
the actual von Mangoldt source atoms. -/
theorem summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature
    (N : ℕ) (i : Fin N) (w : ℂ) :
    Summable (fun n : ℕ =>
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N w n‖ ^ 2) := by
  have hlogTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    hlogTop.eventually_ge_atTop 1
  have hlogW : ∀ᶠ n : ℕ in atTop, 2 * ‖w‖ ≤ Real.log n :=
    hlogTop.eventually_ge_atTop (2 * ‖w‖)
  apply ((summable_vonMangoldtInverseLogPowerWeight (2 * N - 1)).mul_left
    (orderGrowingCauchyFeatureBoundConstant N w ^ 2)).of_norm_bounded_eventually_nat
  filter_upwards [hlogOne, hlogW] with n hn hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature_le N i w n hn hw

/-- The complete packet, jointly over the finite Gamma depth and all source atoms, lies in
`ell^(2 : ℕ)`.  The coordinate order is `Fin N × Nat`; swapping factors gives the aperture convention. -/
theorem summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyPacket
    (N : ℕ) (w : ℂ) :
    Summable (fun x : Fin N × ℕ =>
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N x.1 N w (x.2 + 2)‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨fun i => ?_, summable_of_hasFiniteSupport (Set.toFinite _)⟩
  exact (summable_nat_add_iff 2).mpr
    (summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature N i w)

/-- Entry formula for the finite order-growing Gram. -/
theorem finiteVonMangoldtAllDepthOrderGrowingCauchyGram_apply
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) (a b : Fin K) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w a b =
      ∑ pi : Fin M × Fin N,
        finiteVonMangoldtAllDepthJetBalancedCauchyFeature
            N pi.2 N (w a) ((pi.1 : ℕ) + 2) *
          star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
            N pi.2 N (w b) ((pi.1 : ℕ) + 2)) := by
  rw [finiteVonMangoldtAllDepthOrderGrowingCauchyGram,
    Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteVonMangoldtAllDepthOrderGrowingCauchyVector,
    finiteVonMangoldtAllDepthJetBalancedCauchyVector,
    WithLp.ofLp_toLp, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro pi hpi
  change star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
      N pi.2 N (w b) ((pi.1 : ℕ) + 2)) *
      star (star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N pi.2 N (w a) ((pi.1 : ℕ) + 2))) = _
  rw [star_star]
  ring

/-- One source-atom contribution to the limiting order-growing kernel. -/
def vonMangoldtAllDepthOrderGrowingCauchyKernelTerm
    (N : ℕ) (z w : ℂ) (n : ℕ) : ℂ :=
  ∑ i : Fin N,
    finiteVonMangoldtAllDepthJetBalancedCauchyFeature N i N z (n + 2) *
      star (finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N w (n + 2))

/-- Cross-kernel summability follows from the two square-summable source packets. -/
theorem summable_vonMangoldtAllDepthOrderGrowingCauchyKernelTerm
    (N : ℕ) (z w : ℂ) :
    Summable (vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N z w) := by
  apply summable_sum
  intro i hi
  have hz := (summable_nat_add_iff 2).mpr
    (summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature N i z)
  have hw := (summable_nat_add_iff 2).mpr
    (summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature N i w)
  apply Summable.of_norm_bounded
    (g := fun n =>
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N z (n + 2)‖ ^ 2 +
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        N i N w (n + 2)‖ ^ 2)
  · exact hz.add hw
  · intro n
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg
      (‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature N i N z (n + 2)‖ -
       ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature N i N w (n + 2)‖)]

/-- The genuine cofinal Euler-boundary kernel of the order-growing packet. -/
def infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel
    (N : ℕ) (z w : ℂ) : ℂ :=
  ∑' n : ℕ, vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N z w n

/-- Its finite aperture prefix. -/
def finiteVonMangoldtAllDepthOrderGrowingCauchyKernel
    (M N : ℕ) (z w : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M, vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N z w n

theorem finiteVonMangoldtAllDepthOrderGrowingCauchyKernel_tendsto
    (N : ℕ) (z w : ℂ) :
    Tendsto (fun M => finiteVonMangoldtAllDepthOrderGrowingCauchyKernel M N z w)
      atTop (𝓝 (infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel N z w)) := by
  exact (summable_vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N z w).hasSum.tendsto_sum_nat

/-- The finite source Gram is exactly the finite prefix of the common cofinal kernel. -/
theorem finiteVonMangoldtAllDepthOrderGrowingCauchyGram_eq_kernel
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) (a b : Fin K) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w a b =
      finiteVonMangoldtAllDepthOrderGrowingCauchyKernel M N (w a) (w b) := by
  rw [finiteVonMangoldtAllDepthOrderGrowingCauchyGram_apply,
    finiteVonMangoldtAllDepthOrderGrowingCauchyKernel]
  rw [Fintype.sum_prod_type]
  change (∑ x : Fin M,
      vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N (w a) (w b) (x : ℕ)) = _
  exact Fin.sum_univ_eq_sum_range
    (vonMangoldtAllDepthOrderGrowingCauchyKernelTerm N (w a) (w b)) M

/-- Entrywise cofinal convergence of every finite positive Gram packet. -/
theorem finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto
    (N : ℕ) {K : ℕ} (w : Fin K → ℂ) (a b : Fin K) :
    Tendsto (fun M => finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w a b)
      atTop
      (𝓝 (infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel N (w a) (w b))) := by
  apply (finiteVonMangoldtAllDepthOrderGrowingCauchyKernel_tendsto
    N (w a) (w b)).congr'
  filter_upwards with M
  exact (finiteVonMangoldtAllDepthOrderGrowingCauchyGram_eq_kernel M N w a b).symm

/-- The entrywise limit as a finite matrix. -/
def infiniteVonMangoldtAllDepthOrderGrowingCauchyGram
    (N : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  fun a b => infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel N (w a) (w b)

/-- Positivity survives the cofinal limit.  This closes the complete analytic positive-packet
construction independently of the still-open completed moment value identity. -/
theorem infiniteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef
    (N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (infiniteVonMangoldtAllDepthOrderGrowingCauchyGram N w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    have hba := (finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto N w b a).star
    have hab := finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto N w a b
    have hba' : Tendsto
        (fun M => finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w a b)
        atTop (𝓝 (star
          (infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel N (w b) (w a)))) := by
      apply hba.congr'
      filter_upwards with M
      have hherm :=
        (finiteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef M N w).isHermitian
      have hentry := congrFun (congrFun hherm a) b
      simpa only [Matrix.conjTranspose_apply] using hentry
    exact tendsto_nhds_unique hba' hab
  · intro c
    have hq : Tendsto
        (fun M => star c ⬝ᵥ
          (finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N w).mulVec c)
        atTop
        (𝓝 (star c ⬝ᵥ
          (infiniteVonMangoldtAllDepthOrderGrowingCauchyGram N w).mulVec c)) := by
      simp only [dotProduct, Matrix.mulVec]
      apply tendsto_finsetSum
      intro i hi
      apply Tendsto.mul tendsto_const_nhds
      apply tendsto_finsetSum
      intro j hj
      exact Tendsto.mul
        (finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto N w i j)
        tendsto_const_nhds
    exact isClosed_Ici.mem_of_tendsto hq
      (Filter.Eventually.of_forall fun M =>
        (finiteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef M N w)
          |>.dotProduct_mulVec_nonneg c)

end


end RHTower
