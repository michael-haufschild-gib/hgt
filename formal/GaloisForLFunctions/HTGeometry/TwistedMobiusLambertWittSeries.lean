import GaloisForLFunctions.HTGeometry.TwistedMobiusWittCompletion
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Twisted Möbius--Lambert series and the normalized Witt formation

For `a ≥ 0` and `‖z‖ < 1` put

`M_a(z) = ∑ μ(n) n^{-a} zⁿ / (1 - zⁿ)`,
`W_a(z) = exp (∑ μ(n) n^{-(a+1)} log (1 - zⁿ))`.

Both series converge normally on compact subsets of the unit disc; Lambert regrouping gives
`M_a(z) = ∑ K_a(m) zᵐ` with `K_a(m) = ∑_{d ∣ m} μ(d) d^{-a}`, and termwise differentiation gives
`M_a = -z W_a' / W_a`.  At `a = 0` Möbius inversion gives `M_0(z) = z` and `W_0(z) = e^{-z}`.
For `a > 0` the Cesàro means of `K_a` and the Abel means `(1 - r) M_a(r)` both tend to
`1 / ζ(1 + a) ∈ (0, 1)`; since a meromorphic germ at `1` has integral logarithmic residue,
`W_a` admits no meromorphic continuation through `z = 1`.
-/

open Set Filter Topology Complex
open scoped ArithmeticFunction.Moebius BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Lambert regrouping -/

theorem tsum_pnat_eq_tsum_nat_of_zero {f : ℕ → ℂ} (hf : f 0 = 0) :
    ∑' n : ℕ+, f n = ∑' n : ℕ, f n := by
  refine PNat.coe_injective.tsum_eq ?_
  intro n hn
  have : n ≠ 0 := by rintro rfl; exact hn hf
  exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩

/-- Lambert regrouping for bounded coefficients:
`∑ f(n) zⁿ/(1 - zⁿ) = ∑ (∑_{d ∣ m} f(d)) zᵐ` on the unit disc. -/
theorem tsum_lambert_eq_tsum_divisorSum {f : ℕ → ℂ} {B : ℝ} (hf : ∀ n, ‖f n‖ ≤ B) {z : ℂ}
    (hz : ‖z‖ < 1) :
    ∑' n : ℕ, f n * (z ^ n / (1 - z ^ n)) = ∑' m : ℕ, (∑ d ∈ m.divisors, f d) * z ^ m := by
  have hsum : Summable fun c : ℕ+ × ℕ+ => f c.1 * z ^ (c.1 * c.2 : ℕ) := by
    have h0 := summable_prod_mul_pow (𝕜 := ℝ) 0 (r := ‖z‖) (by simpa using hz)
    refine Summable.of_norm_bounded (h0.mul_left B) fun c => ?_
    rw [norm_mul, norm_pow]
    simp only [pow_zero, one_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (by positivity)
  have h1 : ∑' c : ℕ+ × ℕ+, f c.1 * z ^ (c.1 * c.2 : ℕ) =
      ∑' n : ℕ, f n * (z ^ n / (1 - z ^ n)) := by
    rw [hsum.tsum_prod, ← tsum_pnat_eq_tsum_nat_of_zero (by simp)]
    refine tsum_congr fun d => ?_
    have hzd : ‖z ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz d.ne_zero
    dsimp only
    rw [tsum_mul_left]
    congr 1
    simp only [pow_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun c => (z ^ (d : ℕ)) ^ c)]
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hzd, div_eq_mul_inv, mul_comm]
  have h2 : ∑' c : ℕ+ × ℕ+, f c.1 * z ^ (c.1 * c.2 : ℕ) =
      ∑' m : ℕ, (∑ d ∈ m.divisors, f d) * z ^ m := by
    have hs : Summable fun x => (fun c : ℕ+ × ℕ+ => f c.1 * z ^ (c.1 * c.2 : ℕ))
        (sigmaAntidiagonalEquivProd x) := sigmaAntidiagonalEquivProd.summable_iff.mpr hsum
    rw [← sigmaAntidiagonalEquivProd.tsum_eq, hs.tsum_sigma,
      ← tsum_pnat_eq_tsum_nat_of_zero (by simp)]
    refine tsum_congr fun e => ?_
    rw [tsum_fintype, Finset.sum_mul]
    simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
      Equiv.coe_fn_mk]
    rw [Finset.univ_eq_attach, (Nat.divisorsAntidiagonal e).sum_attach
      (fun x : ℕ × ℕ => f x.1 * z ^ (x.1 * x.2)),
      Nat.sum_divisorsAntidiagonal (fun x y => f x * z ^ (x * y))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]
  rw [← h1, h2]

/-! ## Elementary bounds on the disc -/

theorem norm_pow_div_one_sub_pow_le {z : ℂ} {r : ℝ} (hzr : ‖z‖ ≤ r) (hr : r < 1) (n : ℕ) :
    ‖z ^ n / (1 - z ^ n)‖ ≤ r ^ n / (1 - r) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, sub_self, div_zero, norm_zero]
    exact div_nonneg zero_le_one (by linarith)
  · have hzn : ‖z ^ n‖ ≤ r ^ n := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hzr n
    have hrn : r ^ n ≤ r := pow_le_of_le_one hr0 hr.le hn.ne'
    have hden : 1 - r ≤ ‖1 - z ^ n‖ := by
      have := norm_sub_norm_le (1 : ℂ) (z ^ n)
      rw [norm_one] at this
      linarith
    rw [norm_div]
    exact div_le_div₀ (by positivity) hzn (by linarith) hden

theorem norm_log_one_sub_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Complex.log (1 - w)‖ ≤ ‖w‖ / (1 - ‖w‖) := by
  have h := Complex.hasSum_taylorSeries_neg_log hw
  have h1 : HasSum (fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) (-Complex.log (1 - w)) := by
    have := (hasSum_nat_add_iff' 1).mpr h
    simpa using this
  have hg : HasSum (fun n : ℕ => ‖w‖ * ‖w‖ ^ n) (‖w‖ * (1 - ‖w‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg _) hw).mul_left _
  have hb := h1.norm_le_of_bounded hg fun n => by
    rw [norm_div, norm_pow, Complex.norm_natCast, pow_succ, mul_comm]
    apply div_le_self (by positivity)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [norm_neg] at hb
  rwa [div_eq_mul_inv]

theorem norm_log_one_sub_pow_le {z : ℂ} {r : ℝ} (hzr : ‖z‖ ≤ r) (hr : r < 1) (n : ℕ) :
    ‖Complex.log (1 - z ^ n)‖ ≤ r ^ n / (1 - r) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, sub_self, Complex.log_zero, norm_zero]
    exact div_nonneg zero_le_one (by linarith)
  · have hzn : ‖z ^ n‖ ≤ r ^ n := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hzr n
    have hrn : r ^ n ≤ r := pow_le_of_le_one hr0 hr.le hn.ne'
    have hzn1 : ‖z ^ n‖ < 1 := lt_of_le_of_lt (hzn.trans hrn) hr
    exact (norm_log_one_sub_le hzn1).trans
      (div_le_div₀ (by positivity) hzn (by linarith) (by linarith))

theorem exists_closedBall_of_isCompact_subset_ball {K : Set ℂ} (hK : IsCompact K)
    (hK1 : K ⊆ Metric.ball 0 1) : ∃ r, 0 ≤ r ∧ r < 1 ∧ K ⊆ Metric.closedBall 0 r := by
  obtain ⟨r', hr', hKr⟩ := exists_lt_subset_ball hK.isClosed hK1
  refine ⟨max r' 0, le_max_right _ _, max_lt hr' one_pos, fun z hz => ?_⟩
  have := hKr hz
  rw [Metric.mem_ball, dist_zero_right] at this
  rw [Metric.mem_closedBall, dist_zero_right]
  exact this.le.trans (le_max_left _ _)

/-! ## The twisted weights and the two series -/

/-- The twisted Möbius weight `μ(n) n^{-a}`. -/
def twistedMobiusWeight (a : ℝ) (n : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-a) : ℝ) : ℂ)

theorem norm_twistedMobiusWeight_le_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖twistedMobiusWeight a n‖ ≤ 1 := by
  rw [twistedMobiusWeight, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast this
  have h2 : |(n : ℝ) ^ (-a)| ≤ 1 := by
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Real.zero_rpow_le_one (-a)
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ofReal_twistedMobiusWittCoefficient (a : ℝ) (m : ℕ) :
    ((twistedMobiusWittCoefficient a m : ℝ) : ℂ) = ∑ d ∈ m.divisors, twistedMobiusWeight a d := by
  simp [twistedMobiusWittCoefficient, twistedMobiusWeight]

/-- The twisted Möbius--Lambert series `M_a(z) = ∑ μ(n) n^{-a} zⁿ/(1 - zⁿ)`. -/
def twistedMobiusLambert (a : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, twistedMobiusWeight a n * (z ^ n / (1 - z ^ n))

/-- The logarithmic Witt series `∑ μ(n) n^{-(a+1)} log(1 - zⁿ)` (principal logarithm, which is
the power-series branch on the unit disc). -/
def twistedMobiusWittLog (a : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, twistedMobiusWeight (a + 1) n * Complex.log (1 - z ^ n)

/-- The normalized Witt formation `W_a(z) = exp (∑ μ(n) n^{-(a+1)} log(1 - zⁿ))`. -/
def twistedMobiusWitt (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (twistedMobiusWittLog a z)

theorem twistedMobiusWitt_zero_point (a : ℝ) : twistedMobiusWitt a 0 = 1 := by
  have h : ∀ n : ℕ, twistedMobiusWeight (a + 1) n * Complex.log (1 - (0 : ℂ) ^ n) = 0 := by
    intro n
    rcases n with _ | n <;> simp
  simp only [twistedMobiusWitt, twistedMobiusWittLog, h, tsum_zero, Complex.exp_zero]

theorem twistedMobiusWitt_ne_zero (a : ℝ) (z : ℂ) : twistedMobiusWitt a z ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Normal convergence (Lambert series).**  On every compact subset of the unit disc the
Lambert series is dominated termwise by a summable sequence. -/
theorem twistedMobiusLambert_normal {a : ℝ} (ha : 0 ≤ a) {K : Set ℂ} (hK : IsCompact K)
    (hK1 : K ⊆ Metric.ball 0 1) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ z ∈ K, ‖twistedMobiusWeight a n * (z ^ n / (1 - z ^ n))‖ ≤ u n := by
  obtain ⟨r, hr0, hr1, hKr⟩ := exists_closedBall_of_isCompact_subset_ball hK hK1
  refine ⟨fun n => r ^ n / (1 - r),
    (summable_geometric_of_lt_one hr0 hr1).div_const _, fun n z hz => ?_⟩
  have hzr : ‖z‖ ≤ r := by simpa using hKr hz
  rw [norm_mul]
  calc _ ≤ 1 * (r ^ n / (1 - r)) :=
        mul_le_mul (norm_twistedMobiusWeight_le_one ha n) (norm_pow_div_one_sub_pow_le hzr hr1 n)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Normal convergence (logarithmic Witt series).** -/
theorem twistedMobiusWittLog_normal {a : ℝ} (ha : 0 ≤ a) {K : Set ℂ} (hK : IsCompact K)
    (hK1 : K ⊆ Metric.ball 0 1) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ z ∈ K, ‖twistedMobiusWeight (a + 1) n * Complex.log (1 - z ^ n)‖ ≤ u n := by
  obtain ⟨r, hr0, hr1, hKr⟩ := exists_closedBall_of_isCompact_subset_ball hK hK1
  refine ⟨fun n => r ^ n / (1 - r),
    (summable_geometric_of_lt_one hr0 hr1).div_const _, fun n z hz => ?_⟩
  have hzr : ‖z‖ ≤ r := by simpa using hKr hz
  rw [norm_mul]
  calc _ ≤ 1 * (r ^ n / (1 - r)) :=
        mul_le_mul (norm_twistedMobiusWeight_le_one (by linarith) n)
          (norm_log_one_sub_pow_le hzr hr1 n) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Lambert expansion.**  `M_a(z) = ∑ K_a(m) zᵐ` on the unit disc. -/
theorem twistedMobiusLambert_eq_tsum_coefficient {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ < 1) :
    twistedMobiusLambert a z = ∑' m : ℕ, (twistedMobiusWittCoefficient a m : ℂ) * z ^ m := by
  rw [twistedMobiusLambert, tsum_lambert_eq_tsum_divisorSum (norm_twistedMobiusWeight_le_one ha) hz]
  refine tsum_congr fun m => ?_
  rw [ofReal_twistedMobiusWittCoefficient]

/-! ## Termwise differentiation -/

theorem hasDerivAt_log_one_sub_pow {w : ℂ} (hw : ‖w‖ < 1) (n : ℕ) :
    HasDerivAt (fun v : ℂ => Complex.log (1 - v ^ n))
      (-((n : ℂ) * w ^ (n - 1)) / (1 - w ^ n)) w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hasDerivAt_const w (0 : ℂ)
  · have hmem : 1 - w ^ n ∈ Complex.slitPlane := by
      have : ‖-(w ^ n)‖ < 1 := by
        rw [norm_neg, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw hn.ne'
      simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one this
    exact ((hasDerivAt_pow n w).const_sub 1).clog hmem

/-- Termwise derivative of the logarithmic Witt series, and its differentiability. -/
theorem hasSum_deriv_twistedMobiusWittLog {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => twistedMobiusWeight (a + 1) n * (-((n : ℂ) * z ^ (n - 1)) / (1 - z ^ n)))
        (deriv (twistedMobiusWittLog a) z) ∧
      DifferentiableAt ℂ (twistedMobiusWittLog a) z := by
  set r := (‖z‖ + 1) / 2 with hr
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr.le
  set F : ℕ → ℂ → ℂ := fun n w => twistedMobiusWeight (a + 1) n * Complex.log (1 - w ^ n)
  have hFd : ∀ n, ∀ w ∈ Metric.ball (0 : ℂ) r, HasDerivAt (F n)
      (twistedMobiusWeight (a + 1) n * (-((n : ℂ) * w ^ (n - 1)) / (1 - w ^ n))) w := by
    intro n w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (hasDerivAt_log_one_sub_pow (hw.trans hr1) n).const_mul _
  have hF : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball 0 r) := fun n w hw =>
    (hFd n w hw).differentiableAt.differentiableWithinAt
  have hle : ∀ n, ∀ w ∈ Metric.ball (0 : ℂ) r, ‖F n w‖ ≤ r ^ n / (1 - r) := by
    intro n w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    simp only [F, norm_mul]
    calc _ ≤ 1 * (r ^ n / (1 - r)) :=
          mul_le_mul (norm_twistedMobiusWeight_le_one (by linarith) n)
            (norm_log_one_sub_pow_le hw.le hr1 n) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hu : Summable fun n : ℕ => r ^ n / (1 - r) :=
    (summable_geometric_of_lt_one hr0 hr1).div_const _
  have hzU : z ∈ Metric.ball (0 : ℂ) r := by rwa [Metric.mem_ball, dist_zero_right]
  have hL : twistedMobiusWittLog a = fun w => ∑' n, F n w := rfl
  refine ⟨?_, ?_⟩
  · have h := Complex.hasSum_deriv_of_summable_norm hu hF Metric.isOpen_ball hle hzU
    rw [hL]
    refine h.congr_fun fun n => ?_
    exact ((hFd n z hzU).deriv).symm
  · rw [hL]
    exact (Complex.differentiableOn_tsum_of_summable_norm hu hF Metric.isOpen_ball hle).differentiableAt
      (Metric.isOpen_ball.mem_nhds hzU)

theorem twistedMobiusWeight_succ_mul (a : ℝ) (n : ℕ) :
    twistedMobiusWeight (a + 1) n * (n : ℂ) = twistedMobiusWeight a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [twistedMobiusWeight]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h : (n : ℝ) ^ (-(a + 1)) * n = (n : ℝ) ^ (-a) := by
      rw [Real.rpow_neg hn'.le, Real.rpow_neg hn'.le, Real.rpow_add hn', Real.rpow_one]
      field_simp
    simp only [twistedMobiusWeight]
    rw [← h]
    push_cast
    ring

/-- `-z L_a'(z) = M_a(z)` on the unit disc. -/
theorem neg_mul_deriv_twistedMobiusWittLog {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ < 1) :
    -z * deriv (twistedMobiusWittLog a) z = twistedMobiusLambert a z := by
  rw [← (hasSum_deriv_twistedMobiusWittLog ha hz).1.tsum_eq, ← tsum_mul_left, twistedMobiusLambert]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpow : z * z ^ (n - 1) = z ^ n := by
      rw [← pow_succ']; congr 1; omega
    rw [← twistedMobiusWeight_succ_mul a n]
    field_simp
    rw [← hpow]
    ring

/-- **Logarithmic derivative.**  `M_a(z) = -z W_a'(z) / W_a(z)` on the unit disc. -/
theorem twistedMobiusLambert_eq_neg_mul_logDeriv {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ < 1) :
    twistedMobiusLambert a z = -z * logDeriv (twistedMobiusWitt a) z := by
  have hd := (hasSum_deriv_twistedMobiusWittLog ha hz).2
  have hW : HasDerivAt (twistedMobiusWitt a)
      (Complex.exp (twistedMobiusWittLog a z) * deriv (twistedMobiusWittLog a) z) z :=
    hd.hasDerivAt.cexp
  rw [logDeriv_apply, hW.deriv, twistedMobiusWitt,
    mul_div_cancel_left₀ _ (Complex.exp_ne_zero _), neg_mul_deriv_twistedMobiusWittLog ha hz]

/-- **Theorem, part 1.**  `M_a(z) = ∑ K_a(m) zᵐ = -z W_a'(z)/W_a(z)` on the unit disc. -/
theorem twistedMobiusLambert_law {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : ‖z‖ < 1) :
    twistedMobiusLambert a z = ∑' m : ℕ, (twistedMobiusWittCoefficient a m : ℂ) * z ^ m ∧
      twistedMobiusLambert a z = -z * logDeriv (twistedMobiusWitt a) z :=
  ⟨twistedMobiusLambert_eq_tsum_coefficient ha hz, twistedMobiusLambert_eq_neg_mul_logDeriv ha hz⟩

/-! ## Neutral grade -/

/-- `M_0(z) = z` on the unit disc. -/
theorem twistedMobiusLambert_zero {z : ℂ} (hz : ‖z‖ < 1) : twistedMobiusLambert 0 z = z := by
  rw [twistedMobiusLambert_eq_tsum_coefficient le_rfl hz, tsum_eq_single 1]
  · simp [twistedMobiusWittCoefficient_zero]
  · intro m hm
    simp [twistedMobiusWittCoefficient_zero, hm]

theorem deriv_twistedMobiusWittLog_zero {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (twistedMobiusWittLog 0) z = -1 := by
  by_cases hz0 : z = 0
  · subst hz0
    have h := (hasSum_deriv_twistedMobiusWittLog le_rfl hz).1
    have h1 : HasSum (fun n : ℕ => twistedMobiusWeight (0 + 1) n *
        (-((n : ℂ) * (0 : ℂ) ^ (n - 1)) / (1 - (0 : ℂ) ^ n))) (-1) := by
      convert hasSum_single (f := fun n : ℕ => twistedMobiusWeight (0 + 1) n *
        (-((n : ℂ) * (0 : ℂ) ^ (n - 1)) / (1 - (0 : ℂ) ^ n))) 1 ?_ using 1
      · simp [twistedMobiusWeight]
      · intro n hn
        rcases n with _ | _ | n
        · simp
        · exact absurd rfl hn
        · simp
    exact h.unique h1
  · have h := neg_mul_deriv_twistedMobiusWittLog le_rfl hz
    rw [twistedMobiusLambert_zero hz] at h
    have : -z * deriv (twistedMobiusWittLog 0) z = -z * (-1) := by rw [h]; ring
    exact mul_left_cancel₀ (neg_ne_zero.mpr hz0) this

/-- `∑ μ(n) n⁻¹ log(1 - zⁿ) = -z` on the unit disc. -/
theorem twistedMobiusWittLog_zero {z : ℂ} (hz : ‖z‖ < 1) : twistedMobiusWittLog 0 z = -z := by
  have hU : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℂ (twistedMobiusWittLog 0) (Metric.ball 0 1) := fun w hw =>
    (hasSum_deriv_twistedMobiusWittLog le_rfl
      (by simpa using hw)).2.differentiableWithinAt
  have hz' : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
  refine IsOpen.eqOn_of_deriv_eq hU (convex_ball 0 1).isPreconnected hdiff
    (differentiable_neg.differentiableOn) (fun w hw => ?_) (Metric.mem_ball_self one_pos) ?_ hz'
  · rw [deriv_twistedMobiusWittLog_zero (by simpa using hw), deriv_neg']
  · have h := twistedMobiusWitt_zero_point 0
    have h0 : ∀ n : ℕ, twistedMobiusWeight (0 + 1) n * Complex.log (1 - (0 : ℂ) ^ n) = 0 := by
      intro n; rcases n with _ | n <;> simp
    simp only [twistedMobiusWittLog, h0, tsum_zero, neg_zero]

/-- **Theorem, part 2.**  `W_0(z) = e^{-z}` on the unit disc. -/
theorem twistedMobiusWitt_zero {z : ℂ} (hz : ‖z‖ < 1) :
    twistedMobiusWitt 0 z = Complex.exp (-z) := by
  rw [twistedMobiusWitt, twistedMobiusWittLog_zero hz]

/-- **Theorem, part 2.**  `W_0` extends to a nonvanishing entire function. -/
theorem twistedMobiusWitt_zero_entire :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ z, F z ≠ 0) ∧
      ∀ z, ‖z‖ < 1 → twistedMobiusWitt 0 z = F z :=
  ⟨fun z => Complex.exp (-z), by fun_prop, fun _ => Complex.exp_ne_zero _,
    fun _ hz => twistedMobiusWitt_zero hz⟩


/-! ## Positive grade: Cesàro and Abel boundary index -/

/-- Divisor-sum swap: `∑_{m ≤ N} K_a(m) = ∑_{d ≤ N} μ(d) d^{-a} ⌊N/d⌋`. -/
theorem sum_Ioc_twistedMobiusWittCoefficient (a : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, twistedMobiusWittCoefficient a m =
      ∑ d ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a) * ((N / d : ℕ) : ℝ) := by
  simp only [twistedMobiusWittCoefficient]
  have h : ∀ m ∈ Finset.Ioc 0 N,
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a) =
        ∑ d ∈ Finset.Ioc 0 N,
          if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a) else 0 := by
    intro m hm
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    rw [Finset.mem_Ioc] at hm
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm.1, (Nat.le_of_dvd hm.1 hd).trans hm.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

theorem rpow_neg_mul_inv_eq {a : ℝ} {d : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ (-a) * (d : ℝ)⁻¹ = (d : ℝ) ^ (-(1 + a)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.rpow_neg hd'.le, Real.rpow_neg hd'.le, Real.rpow_add hd', Real.rpow_one, mul_inv,
    mul_comm]

/-- **Cesàro mean.**  For `a > 0`, `N⁻¹ ∑_{m ≤ N} K_a(m) → ∑ μ(d) d^{-(1+a)}`. -/
theorem tendsto_twistedMobiusWittCoefficient_cesaro {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.Ioc 0 N, twistedMobiusWittCoefficient a m) / N) atTop
      (𝓝 (twistedMobiusWittBoundaryIndex a)) := by
  set g : ℕ → ℕ → ℝ := fun N d => if d ∈ Finset.Ioc 0 N then
    (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a) * ((N / d : ℕ) : ℝ) / N else 0 with hg
  have hrepr : ∀ N : ℕ,
      (∑ m ∈ Finset.Ioc 0 N, twistedMobiusWittCoefficient a m) / N = ∑' d, g N d := by
    intro N
    rw [tsum_eq_sum (s := Finset.Ioc 0 N) (fun d hd => if_neg hd),
      sum_Ioc_twistedMobiusWittCoefficient, Finset.sum_div]
    exact Finset.sum_congr rfl fun d hd => (if_pos hd).symm
  simp_rw [hrepr]
  refine tendsto_tsum_of_dominated_convergence (bound := fun d : ℕ => (d : ℝ) ^ (-(1 + a)))
    (Real.summable_nat_rpow.mpr (by linarith)) (fun d => ?_) (Eventually.of_forall fun N d => ?_)
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hg]
    · have hlim : Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 ((d : ℝ)⁻¹)) := by
        have h := (tendsto_nat_floor_mul_div_atTop (a := (d : ℝ)⁻¹) (by positivity)).comp
          tendsto_natCast_atTop_atTop
        refine h.congr fun N => ?_
        simp only [Function.comp_apply]
        rw [inv_mul_eq_div, Nat.floor_div_eq_div]
      have h2 := hlim.const_mul ((ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a))
      rw [mul_assoc, rpow_neg_mul_inv_eq hd] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop d] with N hN
      rw [hg]
      dsimp only
      rw [if_pos (Finset.mem_Ioc.mpr ⟨hd, hN⟩)]
      ring
  · have hb0 : 0 ≤ (d : ℝ) ^ (-(1 + a)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
    rw [hg]
    dsimp only
    split_ifs with hd
    · rw [Finset.mem_Ioc] at hd
      have hN : (0 : ℝ) < N := by exact_mod_cast (hd.1.trans_le hd.2)
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd.1
      have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      have hq : ((N / d : ℕ) : ℝ) / N ≤ (d : ℝ)⁻¹ := by
        rw [div_le_iff₀ hN]
        calc ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
          _ = (d : ℝ)⁻¹ * N := by ring
      have hq0 : 0 ≤ ((N / d : ℕ) : ℝ) / N := by positivity
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hd'.le _), abs_of_nonneg hq0,
        ← rpow_neg_mul_inv_eq hd.1]
      calc |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ) ^ (-a) * (((N / d : ℕ) : ℝ) / N)
          ≤ 1 * (d : ℝ) ^ (-a) * (d : ℝ)⁻¹ := by
            gcongr
        _ = _ := by ring
    · simpa using hb0

/-- The Abel kernel `(1 - r) rⁿ / (1 - rⁿ) = rⁿ / ∑_{k<n} rᵏ`. -/
theorem one_sub_mul_pow_div_one_sub_pow {r : ℝ} (hr : r ≠ 1) (n : ℕ) :
    (1 - r) * (r ^ n / (1 - r ^ n)) = r ^ n / ∑ k ∈ Finset.range n, r ^ k := by
  have h := geom_sum_mul r n
  have h1 : (1 - r ^ n) = (1 - r) * ∑ k ∈ Finset.range n, r ^ k := by linarith
  have hr' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  rw [h1, mul_div_assoc']
  rw [mul_div_mul_left _ _ hr']

/-- **Abel limit.**  For `a > 0`, `(1 - r) M_a(r) → ∑ μ(n) n^{-(1+a)}` as `r → 1⁻`. -/
theorem tendsto_one_sub_mul_twistedMobiusLambert {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) * twistedMobiusLambert a r) (𝓝[<] 1)
      (𝓝 (twistedMobiusWittBoundaryIndex a : ℂ)) := by
  set h : ℝ → ℕ → ℝ := fun r n =>
    (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-a) * ((1 - r) * (r ^ n / (1 - r ^ n))) with hh
  have hreal : Tendsto (fun r : ℝ => ∑' n, h r n) (𝓝[<] 1)
      (𝓝 (twistedMobiusWittBoundaryIndex a)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => (n : ℝ) ^ (-(1 + a)))
      (Real.summable_nat_rpow.mpr (by linarith)) (fun n => ?_) ?_
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hh]
      · have hsum_pos : (0 : ℝ) < ∑ k ∈ Finset.range n, (1 : ℝ) ^ k := by
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          exact_mod_cast hn
        have hcont : ContinuousAt (fun r : ℝ => r ^ n / ∑ k ∈ Finset.range n, r ^ k) 1 :=
          (continuousAt_id.pow n).div (continuous_finsetSum _ fun k _ =>
            continuous_pow k).continuousAt hsum_pos.ne'
        have hval : (1 : ℝ) ^ n / ∑ k ∈ Finset.range n, (1 : ℝ) ^ k = (n : ℝ)⁻¹ := by
          simp
        have hlim : Tendsto (fun r : ℝ => (1 - r) * (r ^ n / (1 - r ^ n))) (𝓝[<] 1)
            (𝓝 ((n : ℝ)⁻¹)) := by
          rw [← hval]
          refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact (one_sub_mul_pow_div_one_sub_pow (ne_of_lt hr) n).symm
        have h2 := hlim.const_mul ((ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-a))
        rw [mul_assoc, rpow_neg_mul_inv_eq hn] at h2
        exact h2
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have := Real.rpow_nonneg (le_refl (0 : ℝ)) (-(1 + a))
        simpa [hh] using this
      · have hr0 := hr.1
        have hsum : (n : ℝ) * r ^ n ≤ ∑ k ∈ Finset.range n, r ^ k := by
          have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => r ^ k) (r ^ n)
            (fun k hk => pow_le_pow_of_le_one hr0.le hr.2.le (Finset.mem_range.mp hk).le)
          simpa using this
        have hkernel0 : 0 ≤ r ^ n / ∑ k ∈ Finset.range n, r ^ k := by
          apply div_nonneg (by positivity)
          exact Finset.sum_nonneg fun k _ => by positivity
        have hkernel : r ^ n / ∑ k ∈ Finset.range n, r ^ k ≤ (n : ℝ)⁻¹ := by
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          have hrn : 0 < r ^ n := by positivity
          rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hsum)]
          calc r ^ n = (n : ℝ)⁻¹ * ((n : ℝ) * r ^ n) := by field_simp
            _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, r ^ k := by gcongr
        have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
          have := ArithmeticFunction.abs_moebius_le_one (n := n)
          exact_mod_cast this
        rw [hh]
        dsimp only
        rw [one_sub_mul_pow_div_one_sub_pow (ne_of_lt hr.2) n, Real.norm_eq_abs, abs_mul,
          abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
          abs_of_nonneg hkernel0, ← rpow_neg_mul_inv_eq hn]
        calc |(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ) ^ (-a) *
              (r ^ n / ∑ k ∈ Finset.range n, r ^ k)
            ≤ 1 * (n : ℝ) ^ (-a) * (n : ℝ)⁻¹ := by gcongr
          _ = _ := by ring
  have hcast := (Complex.continuous_ofReal.tendsto _).comp hreal
  refine hcast.congr fun r => ?_
  simp only [Function.comp_apply, hh]
  rw [Complex.ofReal_tsum, twistedMobiusLambert, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [twistedMobiusWeight]
  push_cast
  ring

/-- **Theorem, part 3.**  For `a > 0`: positive Euler-product coefficients, and the Abel limit
`(1 - r) M_a(r) → 1/ζ(1 + a) ∈ (0, 1)`. -/
theorem twistedMobiusLambert_positive_grade_law {a : ℝ} (ha : 0 < a) :
    (∀ m : ℕ, m ≠ 0 → twistedMobiusWittCoefficient a m =
        ∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-a)) ∧ 0 < twistedMobiusWittCoefficient a m) ∧
      Tendsto (fun r : ℝ => (1 - (r : ℂ)) * twistedMobiusLambert a r) (𝓝[<] 1)
        (𝓝 (riemannZeta (((1 + a : ℝ) : ℂ)))⁻¹) ∧
      twistedMobiusWittBoundaryIndex a ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨fun m hm => ⟨twistedMobiusWittCoefficient_eq_primeProduct a hm,
    twistedMobiusWittCoefficient_pos ha hm⟩, ?_, twistedMobiusWittBoundaryIndex_mem_Ioo ha⟩
  rw [← ofReal_twistedMobiusWittBoundaryIndex_eq_inv_riemannZeta ha]
  exact tendsto_one_sub_mul_twistedMobiusLambert ha

/-- The Abel limit read on the coefficient series: `(1 - r) ∑ K_a(m) rᵐ → c_a`. -/
theorem tendsto_one_sub_mul_tsum_twistedMobiusWittCoefficient {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) *
        ∑' m : ℕ, (twistedMobiusWittCoefficient a m : ℂ) * (r : ℂ) ^ m) (𝓝[<] 1)
      (𝓝 (twistedMobiusWittBoundaryIndex a : ℂ)) := by
  refine (tendsto_one_sub_mul_twistedMobiusLambert ha).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with r hr
  have hr' : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hr.1, hr.2⟩
  rw [twistedMobiusLambert_eq_tsum_coefficient ha.le hr']

/-! ## No meromorphic continuation through the cofinal point -/

/-- **Theorem, part 4.**  For `a > 0`, no function meromorphic at `1` agrees with `W_a` on the
part of a neighbourhood of `1` inside the unit disc. -/
theorem twistedMobiusWitt_no_meromorphic_continuation {a : ℝ} (ha : 0 < a) :
    ¬ ∃ W : ℂ → ℂ, MeromorphicAt W 1 ∧
      ∃ U ∈ 𝓝 (1 : ℂ), ∀ z ∈ U, ‖z‖ < 1 → W z = twistedMobiusWitt a z := by
  rintro ⟨W, hW, U, hU, hWU⟩
  obtain ⟨V, hVU, hVo, h1V⟩ := mem_nhds_iff.mp hU
  have hreal : ∀ᶠ r : ℝ in 𝓝[<] 1, (r : ℂ) ∈ V ∧ r ∈ Set.Ioo 0 1 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝 1, (r : ℂ) ∈ V :=
      Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using hVo.mem_nhds h1V)
    have h1' : ∀ᶠ r : ℝ in 𝓝[<] 1, (r : ℂ) ∈ V := nhdsWithin_le_nhds h1
    exact h1'.and (Ioo_mem_nhdsLT (by norm_num))
  have hloc : ∀ᶠ r : ℝ in 𝓝[<] 1, W =ᶠ[𝓝 (r : ℂ)] twistedMobiusWitt a := by
    filter_upwards [hreal] with r hr
    have hopen : IsOpen (V ∩ Metric.ball (0 : ℂ) 1) := hVo.inter Metric.isOpen_ball
    have hmem : (r : ℂ) ∈ V ∩ Metric.ball (0 : ℂ) 1 := by
      refine ⟨hr.1, ?_⟩
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.2.1]
      exact hr.2.2
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz.2
    exact hWU z (hVU hz.1) hz1
  have hne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), W z ≠ 0 := by
    rcases hW.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exfalso
      have h0r := tendsto_ofReal_nhdsWithin_lt_one_nhdsNE.eventually h0
      obtain ⟨r, hr0, hrW⟩ := (h0r.and hloc).exists
      rw [hrW.eq_of_nhds] at hr0
      exact twistedMobiusWitt_ne_zero a r hr0
    · exact h0
  have hlim : Tendsto (fun r : ℝ => (1 - (r : ℂ)) * (-(r : ℂ) * logDeriv W (r : ℂ)))
      (𝓝[<] 1) (𝓝 ((twistedMobiusWittBoundaryIndex a : ℝ) : ℂ)) := by
    refine (tendsto_one_sub_mul_twistedMobiusLambert ha).congr' ?_
    filter_upwards [hloc, hreal] with r hr hr'
    have hr1 : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'.2.1]; exact hr'.2.2
    rw [twistedMobiusLambert_eq_neg_mul_logDeriv ha.le hr1, logDeriv_apply, logDeriv_apply,
      hr.deriv_eq, hr.eq_of_nhds]
  exact no_meromorphic_completion_of_twistedMobiusWittBoundaryIndex ha ⟨W, hW, hne, hlim⟩


end

end GaloisForLFunctions.HTGeometry
