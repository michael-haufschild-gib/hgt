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


end

end GaloisForLFunctions.HTGeometry
