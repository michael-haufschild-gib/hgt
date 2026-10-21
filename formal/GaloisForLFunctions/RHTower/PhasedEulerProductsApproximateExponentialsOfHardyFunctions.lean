import GaloisForLFunctions.RHTower.PecherskyDensityPrimeVectorsHardyDisc
import GaloisForLFunctions.RHTower.AnalyticOnLargerDiscLiesInHardyDisc

/-!
# Phased Euler products approximate the exponential of every Hardy function

With `z₀`, `ρ` as in the Pechersky density lemma (`1/2 ≤ Re z₀`, `2ρ − 2Re z₀ < −1`,
`ρ < 1 − Re z₀`, `2ρ < 5/12`), let `L` be any element of the Hardy space of the disc `|z − z₀| < ρ`, read in
the coordinate `q = (z − z₀)/ρ`.  Then for every `r₁ < 1` and `ε > 0` there are a cutoff `y` and
unimodular phases `ω` with

  `‖exp(L(q)) − ∏_{p ≤ y} (1 − ω_p p^{−(z₀+ρq)})^{−1}‖ < ε`  for all `|q| ≤ r₁`

(`exists_unimodular_eulerProduct_approx_exp`).  The logarithm of the phased Euler product is the
unimodular prime sum `Σ ω_p p^{−z}` plus the remainder `Σ_p (−log(1 − ω_p p^{−z}) − ω_p p^{−z})`,
whose terms are at most `C p^{−2 Re z}` (`norm_eulerLogRemainder_le`).  The remainder of the
primes beyond a cutoff `y₀` is uniformly small; the remainder of the primes up to `y₀`, with their
phases fixed to `1`, is an explicit function analytic on a larger disc, hence an element of the
Hardy space (`hardyDiskOfAnalytic`); the Pechersky lemma with prescribed initial phases
(`exists_unimodular_finite_approx_extend`) then matches the prime sum to `L` minus that element.
-/

open Complex Filter Topology Finset Metric
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## One Euler factor -/

/-- The remainder of the Euler factor logarithm after its linear term. -/
def eulerLogRemainder (ω z : ℂ) (n : ℕ) : ℂ :=
  -Complex.log (1 - ω * (n : ℂ) ^ (-z)) - ω * (n : ℂ) ^ (-z)

theorem norm_phase_cpow_le_rpow {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 1 ≤ n) {z : ℂ} {σ : ℝ}
    (hz : σ ≤ z.re) : ‖ω * (n : ℂ) ^ (-z)‖ ≤ (n : ℝ) ^ (-σ) := by
  rw [norm_mul, hω, one_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem norm_phase_cpow_le {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 2 ≤ n) {z : ℂ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hz : σ ≤ z.re) : ‖ω * (n : ℂ) ^ (-z)‖ ≤ (2 : ℝ) ^ (-σ) :=
  (norm_phase_cpow_le_rpow hω (by omega) hz).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by linarith))

theorem two_rpow_neg_lt_one {σ : ℝ} (hσ : 0 < σ) : (2 : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem norm_phase_cpow_lt_one {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 2 ≤ n) {z : ℂ} {σ : ℝ}
    (hσ : 0 < σ) (hz : σ ≤ z.re) : ‖ω * (n : ℂ) ^ (-z)‖ < 1 :=
  lt_of_le_of_lt (norm_phase_cpow_le hω hn hσ.le hz) (two_rpow_neg_lt_one hσ)

theorem one_sub_phase_cpow_ne_zero_nat {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    {σ : ℝ} (hσ : 0 < σ) (hz : σ ≤ z.re) : 1 - ω * (n : ℂ) ^ (-z) ≠ 0 := by
  intro h
  have h1 := norm_phase_cpow_lt_one hω hn hσ hz
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at h1
  exact lt_irrefl _ h1

theorem one_sub_phase_cpow_mem_slitPlane {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    {σ : ℝ} (hσ : 0 < σ) (hz : σ ≤ z.re) : 1 - ω * (n : ℂ) ^ (-z) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 := norm_phase_cpow_lt_one hω hn hσ hz
  have h2 := Complex.abs_re_le_norm (ω * (n : ℂ) ^ (-z))
  rw [Complex.sub_re, Complex.one_re]
  linarith [(abs_le.mp h2).2]

/-- **The remainder bound**: `‖−log(1 − ω n^{−z}) − ω n^{−z}‖ ≤ (1 − 2^{−σ})⁻¹/2 · n^{−2σ}` for
`σ ≤ Re z`, `σ > 0`, `n ≥ 2`, `|ω| = 1`. -/
theorem norm_eulerLogRemainder_le {ω : ℂ} (hω : ‖ω‖ = 1) {n : ℕ} (hn : 2 ≤ n) {z : ℂ} {σ : ℝ}
    (hσ : 0 < σ) (hz : σ ≤ z.re) :
    ‖eulerLogRemainder ω z n‖ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 * (n : ℝ) ^ (-(2 * σ)) := by
  set w : ℂ := ω * (n : ℂ) ^ (-z) with hw
  have hw1 : ‖w‖ < 1 := norm_phase_cpow_lt_one hω hn hσ hz
  have hw2 : ‖w‖ ≤ (2 : ℝ) ^ (-σ) := norm_phase_cpow_le hω hn hσ.le hz
  have hw3 : ‖w‖ ≤ (n : ℝ) ^ (-σ) := norm_phase_cpow_le_rpow hω (by omega) hz
  have h2lt := two_rpow_neg_lt_one hσ
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Complex.norm_log_one_add_sub_self_le (z := -w) (by rwa [norm_neg])
  rw [norm_neg] at h
  have heq : eulerLogRemainder ω z n = -(Complex.log (1 + -w) - -w) := by
    rw [eulerLogRemainder, ← sub_eq_add_neg, ← hw]
    ring
  rw [heq, norm_neg]
  refine h.trans ?_
  have hsq : ‖w‖ ^ 2 ≤ (n : ℝ) ^ (-(2 * σ)) := by
    calc ‖w‖ ^ 2 ≤ ((n : ℝ) ^ (-σ)) ^ 2 := by gcongr
      _ = (n : ℝ) ^ (-(2 * σ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
          congr 1
          push_cast
          ring
  have hinv : (1 - ‖w‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ (n : ℝ) ^ (-(2 * σ)) * (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 := by
        gcongr
    _ = (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 * (n : ℝ) ^ (-(2 * σ)) := by ring

/-! ## Products, sums, and the exponential -/

/-- A finite product of Euler factors is the exponential of the sum of their principal
logarithms. -/
theorem prod_inv_one_sub_eq_exp_sum {S : Finset ℕ} {w : ℕ → ℂ} (hw : ∀ n ∈ S, 1 - w n ≠ 0) :
    ∏ n ∈ S, (1 - w n)⁻¹ = Complex.exp (∑ n ∈ S, -Complex.log (1 - w n)) := by
  rw [Complex.exp_sum]
  refine prod_congr rfl fun n hn => ?_
  rw [Complex.exp_neg, Complex.exp_log (hw n hn)]

/-- The sum of the Euler-factor logarithms is the linear prime sum plus the remainders. -/
theorem sum_neg_log_eq_sum_add_remainder (S : Finset ℕ) (ω : ℕ → ℂ) (z : ℂ) :
    ∑ n ∈ S, -Complex.log (1 - ω n * (n : ℂ) ^ (-z))
      = ∑ n ∈ S, ω n * (n : ℂ) ^ (-z) + ∑ n ∈ S, eulerLogRemainder (ω n) z n := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [eulerLogRemainder]
  ring

/-- `‖e^B − e^A‖ ≤ 2 e^{‖A‖} ‖B − A‖` when `‖B − A‖ ≤ 1`. -/
theorem norm_cexp_sub_cexp_le_of_norm_sub_le_one {A B : ℂ} (h : ‖B - A‖ ≤ 1) :
    ‖Complex.exp B - Complex.exp A‖ ≤ 2 * Real.exp ‖A‖ * ‖B - A‖ := by
  have heq : Complex.exp B - Complex.exp A = Complex.exp A * (Complex.exp (B - A) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, norm_mul, Complex.norm_exp]
  calc Real.exp A.re * ‖Complex.exp (B - A) - 1‖ ≤ Real.exp ‖A‖ * (2 * ‖B - A‖) := by
        gcongr
        · exact Complex.re_le_norm A
        · exact Complex.norm_exp_sub_one_le h
    _ = 2 * Real.exp ‖A‖ * ‖B - A‖ := by ring

/-- The tail of the remainder majorant beyond a large cutoff is small, uniformly in the upper
limit. -/
theorem exists_remainder_tail_le {σ C δ : ℝ} (hσ : 1 / 2 < σ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (y₀' : ℕ) :
    ∃ y₀ : ℕ, y₀' ≤ y₀ ∧ ∀ N : ℕ,
      ∑ n ∈ Finset.Ico (y₀ + 1) N, C * (n : ℝ) ^ (-(2 * σ)) ≤ δ := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := (tendsto_sum_nat_add fun n : ℕ => (n : ℝ) ^ (-(2 * σ))).eventually_le_const
    (by positivity : (0 : ℝ) < δ / (C + 1))
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp htail
  refine ⟨max y₀' i₀, le_max_left _ _, fun N => ?_⟩
  set y₀ : ℕ := max y₀' i₀ with hy₀
  have hshift : Summable (fun k : ℕ => ((k + (y₀ + 1) : ℕ) : ℝ) ^ (-(2 * σ))) :=
    (summable_nat_add_iff (y₀ + 1)).mpr hg
  have h1 : ∑ n ∈ Finset.Ico (y₀ + 1) N, (n : ℝ) ^ (-(2 * σ))
      ≤ ∑' k : ℕ, ((k + (y₀ + 1) : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq (sum_congr rfl fun k _ => by rw [add_comm])) ?_
    exact hshift.sum_le_tsum _ fun k _ => by positivity
  have h2 : ∑' k : ℕ, ((k + (y₀ + 1) : ℕ) : ℝ) ^ (-(2 * σ)) ≤ δ / (C + 1) :=
    hi₀ (y₀ + 1) (by omega)
  rw [← mul_sum]
  calc C * ∑ n ∈ Finset.Ico (y₀ + 1) N, (n : ℝ) ^ (-(2 * σ)) ≤ C * (δ / (C + 1)) := by
        gcongr
        exact h1.trans h2
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- The Hardy function is bounded on the closed disc of radius `r₁ < 1`. -/
theorem norm_hardyFun_le_of_norm_le (L : HardyDisk) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1)
    {q : ℂ} (hq0 : ‖q‖ ≤ r₁) :
    ‖hardyFun L q‖ ≤ Real.sqrt ((1 - r₁ ^ 2)⁻¹) * ‖L‖ := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hq0 hr₁
  rw [← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq]
  refine (norm_inner_le_norm _ _).trans ?_
  gcongr
  rw [← Real.sqrt_sq (norm_nonneg _), norm_hardyDiskKernel_sq hq]
  refine Real.sqrt_le_sqrt (inv_anti₀ (by nlinarith) ?_)
  nlinarith [norm_nonneg q]

/-! ## The fixed-phase head remainder -/

/-- The remainder of the primes up to `y₀` with all phases equal to one, as a function of the
disc coordinate `q`. -/
def eulerHeadRemainder (z₀ : ℂ) (ρ : ℝ) (y₀ : ℕ) (q : ℂ) : ℂ :=
  ∑ n ∈ (range (y₀ + 1)).filter Nat.Prime, eulerLogRemainder 1 (z₀ + ρ * q) n

/-- On the disc of radius `R`, `Re (z₀ + ρ q) ≥ Re z₀ − ρ R`. -/
theorem re_center_add_le {z₀ : ℂ} {ρ R : ℝ} (hρ : 0 ≤ ρ) {q : ℂ} (hq : ‖q‖ ≤ R) :
    z₀.re - ρ * R ≤ (z₀ + ρ * q).re := by
  rw [Complex.add_re, Complex.re_ofReal_mul]
  have h := Complex.abs_re_le_norm q
  have h2 : -R ≤ q.re := by linarith [(abs_le.mp h).1]
  nlinarith

theorem differentiableOn_eulerHeadRemainder (z₀ : ℂ) {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hpos : ρ * R < z₀.re) (y₀ : ℕ) :
    DifferentiableOn ℂ (eulerHeadRemainder z₀ ρ y₀) (closedBall 0 R) := by
  have hfun : eulerHeadRemainder z₀ ρ y₀ = ∑ n ∈ (range (y₀ + 1)).filter Nat.Prime,
      fun q => eulerLogRemainder 1 (z₀ + ρ * q) n := by
    funext q
    rw [eulerHeadRemainder, Finset.sum_apply]
  rw [hfun]
  refine DifferentiableOn.sum fun n hn => ?_
  have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hexp : DifferentiableOn ℂ (fun q : ℂ => -(z₀ + ρ * q)) (closedBall 0 R) :=
    ((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)).neg
  have hcpow : DifferentiableOn ℂ (fun q : ℂ => (n : ℂ) ^ (-(z₀ + ρ * q))) (closedBall 0 R) :=
    hexp.const_cpow (Or.inl hn0)
  have hlin : DifferentiableOn ℂ (fun q : ℂ => 1 * (n : ℂ) ^ (-(z₀ + ρ * q))) (closedBall 0 R) :=
    (differentiableOn_const _).mul hcpow
  have hlog : DifferentiableOn ℂ (fun q : ℂ => Complex.log (1 - 1 * (n : ℂ) ^ (-(z₀ + ρ * q))))
      (closedBall 0 R) := by
    refine ((differentiableOn_const _).sub hlin).clog fun q hq => ?_
    rw [mem_closedBall, dist_zero_right] at hq
    exact one_sub_phase_cpow_mem_slitPlane (by simp) hn2 (by linarith) (re_center_add_le hρ hq)
  exact hlog.neg.sub hlin

theorem norm_eulerHeadRemainder_le (z₀ : ℂ) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hpos : ρ * R < z₀.re) (y₀ : ℕ)
    {q : ℂ} (hq : ‖q‖ ≤ R) :
    ‖eulerHeadRemainder z₀ ρ y₀ q‖
      ≤ (y₀ + 1 : ℕ) * ((1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2) := by
  have hσ : 0 < z₀.re - ρ * R := by linarith
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2)
    fun n hn => ?_).trans ?_
  · have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc ‖eulerLogRemainder 1 (z₀ + ρ * q) n‖
        ≤ (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2 * (n : ℝ) ^ (-(2 * (z₀.re - ρ * R))) :=
          norm_eulerLogRemainder_le (by simp) hn2 hσ (re_center_add_le hρ hq)
      _ ≤ (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2 * 1 := by
          gcongr
          · have := two_rpow_neg_lt_one hσ
            have h0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ := by
              apply inv_nonneg.mpr
              linarith
            positivity
          · exact Real.rpow_le_one_of_one_le_of_nonpos hn' (by linarith)
      _ = (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2 := mul_one _
  · rw [nsmul_eq_mul]
    have hcard : (((range (y₀ + 1)).filter Nat.Prime).card : ℝ) ≤ (y₀ + 1 : ℕ) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by rw [card_range])
    have hc0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2 := by
      have := two_rpow_neg_lt_one hσ
      have h0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ := inv_nonneg.mpr (by linarith)
      positivity
    exact mul_le_mul_of_nonneg_right hcard hc0

/-! ## The approximation theorem -/

/-- **Phased Euler products approximate the exponential of every Hardy function.**  For `L` in
the Hardy space of the disc `|z − z₀| < ρ` (coordinate `q`), every `r₁ < 1`, `ε > 0` and `y₀'`,
there are `y ≥ y₀'` and unimodular phases `ω` with
`‖exp(L(q)) − ∏_{p ≤ y} (1 − ω_p p^{−(z₀+ρq)})^{−1}‖ < ε` for all `|q| ≤ r₁`. -/
theorem exists_unimodular_eulerProduct_approx_exp (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    (hρ5 : 2 * ρ < 5 / 12)
    (L : HardyDisk) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) (y₀' : ℕ) :
    ∃ y : ℕ, y₀' ≤ y ∧ ∃ ω : ℕ → ℂ, (∀ n, ‖ω n‖ = 1) ∧ ∀ q : ℂ, ‖q‖ ≤ r₁ →
      ‖Complex.exp (hardyFun L q) - ∏ n ∈ (range (y + 1)).filter Nat.Prime,
          (1 - ω n * (n : ℂ) ^ (-(z₀ + ρ * q)))⁻¹‖ < ε := by
  -- the real-part floor on the unit disc and the constants
  set σ₁ : ℝ := z₀.re - ρ with hσ₁
  have hσ₁half : 1 / 2 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁pos : 0 < σ₁ := by linarith
  set K : ℝ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK
  have hKpos : 0 < K := by
    rw [hK]
    apply Real.sqrt_pos.mpr
    apply inv_pos.mpr
    nlinarith
  set M : ℝ := K * ‖L‖ with hM
  set δ : ℝ := min 1 (ε / (4 * Real.exp M)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (4 * Real.exp M) := min_le_right _ _
  set C₁ : ℝ := (1 - (2 : ℝ) ^ (-σ₁))⁻¹ / 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have := two_rpow_neg_lt_one hσ₁pos
    rw [hC₁]
    have h0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ₁))⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  -- the cutoff beyond which the remainder tail is small
  obtain ⟨y₀, hy₀', htail⟩ := exists_remainder_tail_le hσ₁half hC₁0 (by positivity : 0 < δ / 3) y₀'
  -- the head remainder lies in the Hardy space
  set R : ℝ := (1 + z₀.re / ρ) / 2 with hR
  have hR1 : 1 < R := by
    rw [hR]
    have : 1 < z₀.re / ρ := by
      rw [lt_div_iff₀ hρ]
      linarith
    linarith
  have hρR : ρ * R < z₀.re := by
    rw [hR]
    have h1 : ρ * (z₀.re / ρ) = z₀.re := by field_simp
    nlinarith
  have hBcirc : ∀ θ : ℝ, ‖eulerHeadRemainder z₀ ρ y₀ (circleMap 0 R θ)‖
      ≤ (y₀ + 1 : ℕ) * ((1 - (2 : ℝ) ^ (-(z₀.re - ρ * R)))⁻¹ / 2) := fun θ =>
    norm_eulerHeadRemainder_le z₀ hρ.le hρR y₀ (by rw [norm_circleMap_zero, abs_of_pos (by linarith)])
  set R₀v : HardyDisk := hardyDiskOfAnalytic (eulerHeadRemainder z₀ ρ y₀) hR1 hBcirc with hR₀v
  have hR₀fun : ∀ q : ℂ, ‖q‖ < 1 → hardyFun R₀v q = eulerHeadRemainder z₀ ρ y₀ q := fun q hq =>
    hardyFun_hardyDiskOfAnalytic hR1 (differentiableOn_eulerHeadRemainder z₀ hρ.le hρR y₀) hBcirc hq
  -- the Pechersky approximation with the first phases fixed to one
  obtain ⟨N, hN, ω, hω, hωone, hclose⟩ := exists_unimodular_finite_approx_extend
    (primeTerm z₀ hρ.le) (summable_norm_primeTerm_sq z₀ hρ.le hρσ₁)
    (fun _ he M => exists_sum_norm_inner_primeTerm_gt z₀ hρ hσ hρσ₂ hρ5 he M) (L - R₀v)
    (by positivity : (0 : ℝ) < δ / 3 / K) (y₀ + 1) (fun _ => 1) (fun _ => by simp)
  refine ⟨N - 1, by omega, ω, hω, fun q hq => ?_⟩
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1]
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq hr₁
  set z : ℂ := z₀ + ρ * q with hz
  have hzre : σ₁ ≤ z.re := by
    have := re_center_add_le (z₀ := z₀) (R := 1) hρ.le hq1.le
    rw [hσ₁, hz]
    linarith
  -- the Euler product is the exponential of the logarithmic sum
  set S : Finset ℕ := (range N).filter Nat.Prime with hS
  have hprod : ∏ n ∈ S, (1 - ω n * (n : ℂ) ^ (-z))⁻¹
      = Complex.exp (∑ n ∈ S, -Complex.log (1 - ω n * (n : ℂ) ^ (-z))) :=
    prod_inv_one_sub_eq_exp_sum fun n hn =>
      one_sub_phase_cpow_ne_zero_nat (hω n) (mem_filter.mp hn).2.two_le hσ₁pos hzre
  rw [hprod, sum_neg_log_eq_sum_add_remainder]
  -- the linear sum is the Hardy function of the Pechersky sum
  have hlin : ∑ n ∈ S, ω n * (n : ℂ) ^ (-z)
      = hardyFun (∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n) q := by
    rw [← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1, inner_sum, hS, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    rw [inner_smul_right, GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1,
      hardyFun_primeTerm z₀ hρ.le n hq1, mul_ite, mul_zero]
  -- the remainder splits into the fixed head and a small tail
  have hrem : ∑ n ∈ S, eulerLogRemainder (ω n) z n
      = eulerHeadRemainder z₀ ρ y₀ q
        + ∑ n ∈ Finset.Ico (y₀ + 1) N, if n.Prime then eulerLogRemainder (ω n) z n else 0 := by
    rw [hS, sum_filter, ← Finset.sum_range_add_sum_Ico _ hN, eulerHeadRemainder, sum_filter]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [hωone n (mem_range.mp hn)]
  have htailq : ‖∑ n ∈ Finset.Ico (y₀ + 1) N,
      if n.Prime then eulerLogRemainder (ω n) z n else 0‖ ≤ δ / 3 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => ?_).trans (htail N))
    split_ifs with hn
    · exact norm_eulerLogRemainder_le (hω n) hn.two_le hσ₁pos hzre
    · rw [norm_zero]
      positivity
  -- the logarithmic sum is within `δ` of `L(q)`
  have hdiff : ‖hardyFun L q - (∑ n ∈ S, ω n * (n : ℂ) ^ (-z)
      + ∑ n ∈ S, eulerLogRemainder (ω n) z n)‖ ≤ δ := by
    rw [hlin, hrem]
    have hker : hardyFun L q - (hardyFun (∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n) q
        + (eulerHeadRemainder z₀ ρ y₀ q + ∑ n ∈ Finset.Ico (y₀ + 1) N,
          if n.Prime then eulerLogRemainder (ω n) z n else 0))
        = hardyFun (L - R₀v - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n) q
          - ∑ n ∈ Finset.Ico (y₀ + 1) N,
            if n.Prime then eulerLogRemainder (ω n) z n else 0 := by
      rw [← hR₀fun q hq1, ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1,
        ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1,
        ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1,
        ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq1, inner_sub_right, inner_sub_right]
      ring
    rw [hker]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖hardyFun (L - R₀v - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n) q‖ ≤ δ / 3 := by
      have hb := norm_hardyFun_le_of_norm_le (L - R₀v - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n)
        hr₁0 hr₁ hq
      rw [← hK] at hb
      calc _ ≤ K * ‖L - R₀v - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n‖ := hb
        _ ≤ K * (δ / 3 / K) := by gcongr
        _ = δ / 3 := by field_simp
    linarith
  -- the exponential step
  have hML : ‖hardyFun L q‖ ≤ M := by
    rw [hM, hK]
    exact norm_hardyFun_le_of_norm_le L hr₁0 hr₁ hq
  have hexpM : Real.exp ‖hardyFun L q‖ ≤ Real.exp M := Real.exp_le_exp.mpr hML
  rw [norm_sub_rev]
  calc ‖Complex.exp (∑ n ∈ S, ω n * (n : ℂ) ^ (-z) + ∑ n ∈ S, eulerLogRemainder (ω n) z n)
        - Complex.exp (hardyFun L q)‖
      ≤ 2 * Real.exp ‖hardyFun L q‖ * ‖(∑ n ∈ S, ω n * (n : ℂ) ^ (-z)
          + ∑ n ∈ S, eulerLogRemainder (ω n) z n) - hardyFun L q‖ := by
        refine norm_cexp_sub_cexp_le_of_norm_sub_le_one ?_
        rw [norm_sub_rev]
        exact hdiff.trans hδ1
    _ ≤ 2 * Real.exp M * δ := by
        rw [norm_sub_rev]
        gcongr
    _ ≤ 2 * Real.exp M * (ε / (4 * Real.exp M)) := by gcongr
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

end RHTower
