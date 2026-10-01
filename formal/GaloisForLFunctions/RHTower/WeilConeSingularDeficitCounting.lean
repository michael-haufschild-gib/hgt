import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import GaloisForLFunctions.RHTower.WeilFullConeCCMBridge

/-!
# The singular deficit law of the Weil cone (counting form)

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam`.  The **deficit count**

`D(T) = Σ_{0 < γ_q ≤ T} d_q`

sums the deficit weights (`WeilConeSingularDeficitEnvelope`) of the divisor copies of `ξ` whose
ordinates lie in `(0, T]`.  An off-line zero and its reflection `1 − ρ̄` each count `1`, which gives
`2N_off⁺(T)`.  A critical zero counts `(m_ρ − μ_lam({γ}))⁺`, which gives `R⁺(T)`.

**Theorem** (`abs_sub_vonMangoldt_le_of_deficitCount`).  If `D(T)/T ≤ E + η` along arbitrarily
large `T`, for every `η > 0`, then `|lam(m) − Λ(m)| ≤ 4π m E` for every `m ≥ 2`.

**Corollary** (`eq_vonMangoldt_of_deficitCount`, `riemannHypothesis_of_deficitCount`).  A
full-cone producer whose deficit count has lower density zero is `Λ` on `n ≥ 2`, and then RH holds.

**Proof.**
* The envelope law bounds `|w(m)| m^{−σ}` by four times the mean of `ε_σ = Σ_q d_q A_q`.
* Each Poisson term `A_q` has `t`-mass at most `π` (`integral_copyPoisson_le_pi`).  The copies
  with ordinate in `(0, T]` therefore contribute at most `πD(T)`.
* Put `H = √T`.  A copy at distance at least `H` from `t` is dominated by `2σ/(H − 1)` times its
  Poisson term at abscissa `H` (`copyPoisson_le_shift`).  Those terms sum to
  `Re ξ'/ξ(H + it) = O(log T)` (`re_logDeriv_xi_le_log`, via Stirling for `ψ`).
* A copy outside `(0, T]` lies within `H` of `t` only when `t` is within `H` of an end of
  `[8, T]`.  There `ε_σ ≤ Re ξ'/ξ(σ + it) = O(log T)`.
* The total error is `O(σ √T log T) = o(T)`.  Finally let `σ ↓ 1`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## Poisson terms: mass and domination -/

theorem continuous_copyPoisson {σ : ℝ} (hσ : 1 ≤ σ) (q : XiZeroCopy) :
    Continuous fun t => copyPoisson σ t q := by
  obtain ⟨_, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have : 0 < σ - ((q.1 : ℂ)).re := by linarith
  unfold copyPoisson
  exact continuous_const.div (by fun_prop) fun t => by positivity

theorem hasDerivAt_arctan_copy {σ : ℝ} (hσ : 1 ≤ σ) (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (fun t => Real.arctan ((t - ((q.1 : ℂ)).im) / (σ - ((q.1 : ℂ)).re)))
      (copyPoisson σ t q) t := by
  obtain ⟨_, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hc0 : 0 < σ - ((q.1 : ℂ)).re := by linarith
  have h := (((hasDerivAt_id' t).sub_const ((q.1 : ℂ)).im).div_const
    (σ - ((q.1 : ℂ)).re)).arctan
  convert h using 1
  unfold copyPoisson
  field_simp

/-- Each Poisson term has `t`-mass at most `π` on every interval. -/
theorem integral_copyPoisson_le_pi {σ : ℝ} (hσ : 1 ≤ σ) (q : XiZeroCopy) (a b : ℝ) :
    ∫ t in a..b, copyPoisson σ t q ≤ π := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_arctan_copy hσ q t)
    ((continuous_copyPoisson hσ q).intervalIntegrable _ _)]
  have h1 := Real.arctan_lt_pi_div_two ((b - ((q.1 : ℂ)).im) / (σ - ((q.1 : ℂ)).re))
  have h2 := Real.neg_pi_div_two_lt_arctan ((a - ((q.1 : ℂ)).im) / (σ - ((q.1 : ℂ)).re))
  linarith

/-- **Abscissa shift.**  At distance at least `H > 1` from the ordinate,
`A_q^σ(t) ≤ (2σ/(H − 1)) A_q^H(t)`. -/
theorem copyPoisson_le_shift {σ H t : ℝ} (hσ : 1 ≤ σ) (hH : 1 < H) (q : XiZeroCopy)
    (hfar : H ≤ |t - ((q.1 : ℂ)).im|) :
    copyPoisson σ t q ≤ 2 * σ / (H - 1) * copyPoisson H t q := by
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  unfold copyPoisson
  set β := ((q.1 : ℂ)).re
  set x := (t - ((q.1 : ℂ)).im) ^ 2 with hx
  have hHx : H ^ 2 ≤ x := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ H) hfar 2
    rwa [sq_abs] at this
  have ha : 0 < σ - β := by linarith
  have hb1 : H - 1 < H - β := by linarith
  have hb2 : H - β < H := by linarith
  have hx0 : 0 < x := by nlinarith
  have hH1 : 0 < H - 1 := by linarith
  have hb0 : 0 < H - β := by linarith
  calc (σ - β) / ((σ - β) ^ 2 + x) ≤ σ / x := by
        rw [div_le_div_iff₀ (by positivity) hx0]
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ σ) (sq_nonneg (σ - β))
        nlinarith [mul_pos hβ0 hx0]
    _ ≤ 2 * σ / (H - 1) * ((H - β) / ((H - β) ^ 2 + x)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ hx0 (by positivity)]
        have hbx : (H - β) ^ 2 ≤ x := by nlinarith
        have h1 : (H - 1) * ((H - β) ^ 2 + x) ≤ (H - β) * ((H - β) ^ 2 + x) :=
          mul_le_mul_of_nonneg_right hb1.le (by positivity)
        have h2 : (H - β) * ((H - β) ^ 2 + x) ≤ (H - β) * (2 * x) :=
          mul_le_mul_of_nonneg_left (by linarith) hb0.le
        nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith : (0 : ℝ) ≤ σ)]

theorem continuous_tsum_copyPoisson {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun t => ∑' q, copyPoisson σ t q := by
  simpa using continuous_weighted_copyPoisson hσ (c := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl)

/-! ## Growth of `Re ξ'/ξ` on vertical lines -/

/-- The Dirichlet majorant `Σ Λ(n) n^{−σ}`. -/
def vonMangoldtMajorant (σ : ℝ) : ℝ :=
  ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖

theorem vonMangoldtMajorant_nonneg (σ : ℝ) : 0 ≤ vonMangoldtMajorant σ :=
  tsum_nonneg fun _ => norm_nonneg _

theorem norm_LSeries_vonMangoldt_le {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤ vonMangoldtMajorant σ := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have hsum' := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) (by linarith)
  refine (norm_tsum_le_tsum_norm hsum'.norm).trans ?_
  exact hsum'.norm.tsum_le_tsum
    (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n) hsum.norm

/-- **Stirling bound.**  For `1 < σ₀ ≤ σ` and `t ≥ 8`,
`Re ξ'/ξ(σ + it) ≤ ¼ log(σ² + t²) + ½ + 1/σ₀ + 1/(σ₀ − 1) + Σ Λ(n) n^{−σ₀}`. -/
theorem re_logDeriv_xi_le {σ₀ σ t : ℝ} (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ) (ht : 8 ≤ t) :
    (logDeriv xi ((σ : ℂ) + t * I)).re ≤
      Real.log (σ ^ 2 + t ^ 2) / 4 + 1 / 2 + 1 / σ₀ + 1 / (σ₀ - 1) +
        vonMangoldtMajorant σ₀ := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs : 1 < s.re := by rw [hsre]; linarith
  rw [logDeriv_xi_eq_datum hs]
  simp only [zetaArchimedeanDatum, Complex.sub_re, Complex.add_re, Complex.div_ofNat_re,
    Complex.ofReal_re]
  have hdig : (digamma (s / 2)).re ≤ Real.log (σ ^ 2 + t ^ 2) / 2 + 1 := by
    have hs2 : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      rw [hsdef]; push_cast; ring
    rw [hs2]
    have h := re_digamma_vertical_bound_uncond (σ := σ / 2) (t := t / 2) (by linarith)
      (by linarith)
    have hlog : (1 / 2) * Real.log ((σ / 2) ^ 2 + (t / 2) ^ 2) ≤ Real.log (σ ^ 2 + t ^ 2) / 2 := by
      have hpos : 0 < (σ / 2) ^ 2 + (t / 2) ^ 2 := by positivity
      have := Real.log_le_log hpos
        (show (σ / 2) ^ 2 + (t / 2) ^ 2 ≤ σ ^ 2 + t ^ 2 by nlinarith)
      linarith
    have hsmall : 1 / (t / 2) ^ 2 + π / (2 * (t / 2)) ≤ 1 := by
      have h1 : 1 / (t / 2) ^ 2 ≤ 1 / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h2 : π / (2 * (t / 2)) ≤ π / 8 :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
      have := Real.pi_le_four
      linarith
    have := (abs_le.mp h).2
    linarith
  have hnorm : σ ≤ ‖s‖ := by rw [← hsre]; exact (le_abs_self _).trans (Complex.abs_re_le_norm s)
  have h1s : (1 / s).re ≤ 1 / σ₀ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hnorm1 : σ - 1 ≤ ‖s - 1‖ := by
    have : (s - 1).re = σ - 1 := by rw [Complex.sub_re, hsre]; simp
    rw [← this]
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h1s1 : (1 / (s - 1)).re ≤ 1 / (σ₀ - 1) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hL : -(LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤
      vonMangoldtMajorant σ₀ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (norm_LSeries_vonMangoldt_le hσ₀ (by rw [hsre]; exact hσ)))
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem log_sq_add_sq_le {a b T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (hb : 0 < b) (hbT : b ≤ T) :
    Real.log (a ^ 2 + b ^ 2) / 4 ≤ Real.log T / 2 + 1 := by
  have hT : 0 < T := lt_of_lt_of_le hb hbT
  have h1 : a ^ 2 + b ^ 2 ≤ 2 * T ^ 2 := by nlinarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  push_cast at h2
  linarith

/-- The constant of the logarithmic growth bound. -/
def envelopeConst (σ : ℝ) : ℝ := 3 / 2 + 1 / σ + 1 / (σ - 1) + vonMangoldtMajorant σ

theorem re_logDeriv_xi_le_log {σ₀ σ t T : ℝ} (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ) (hσT : σ ≤ T)
    (ht : 8 ≤ t) (htT : t ≤ T) :
    (logDeriv xi ((σ : ℂ) + t * I)).re ≤ Real.log T / 2 + envelopeConst σ₀ := by
  have h1 := re_logDeriv_xi_le hσ₀ hσ ht
  have h2 := log_sq_add_sq_le (a := σ) (b := t) (by linarith) hσT (by linarith) htT
  unfold envelopeConst
  linarith

/-! ## The deficit count -/

/-- The deficit weight of a copy with ordinate in `(0, T]`, and `0` otherwise. -/
def ordinateWindowWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) (q : XiZeroCopy) : ℝ :=
  if 0 < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ T then deficitWeight hW q else 0

/-- **The deficit count** `D(T) = Σ_{0 < γ_q ≤ T} d_q`. -/
def deficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  ∑' q, ordinateWindowWeight hW T q

theorem ordinateWindowWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) (q : XiZeroCopy) :
    0 ≤ ordinateWindowWeight hW T q := by
  unfold ordinateWindowWeight
  split_ifs
  · exact deficitWeight_nonneg hW q
  · exact le_rfl

theorem ordinateWindowWeight_le_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) (q : XiZeroCopy) :
    ordinateWindowWeight hW T q ≤ 1 := by
  unfold ordinateWindowWeight
  split_ifs
  · exact deficitWeight_le_one hW q
  · exact zero_le_one

theorem summable_deficit_mul_copyPoisson {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) (hc1 : ∀ q, c q ≤ 1) :
    Summable fun q => c q * copyPoisson σ t q :=
  (summable_copyPoisson hσ t).of_nonneg_of_le
    (fun q => mul_nonneg (hc0 q) (copyPoisson_pos hσ.le t q).le) fun q => by
      have := mul_le_mul_of_nonneg_right (hc1 q) (copyPoisson_pos hσ.le t q).le
      linarith

theorem deficitEnvelope_le_re_logDeriv_xi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) : deficitEnvelope hW σ t ≤ (logDeriv xi ((σ : ℂ) + t * I)).re := by
  rw [re_logDeriv_xi_eq_tsum_copyPoisson hσ t]
  refine (summable_deficit_mul_copyPoisson hσ t (deficitWeight_nonneg hW)
    (deficitWeight_le_one hW)).tsum_le_tsum (fun q => ?_) (summable_copyPoisson hσ t)
  have := mul_le_mul_of_nonneg_right (deficitWeight_le_one hW q) (copyPoisson_pos hσ.le t q).le
  linarith

/-- **Splitting off the window.**  For `H ≤ t ≤ T − H`,
`ε_σ(t) ≤ Σ_q d_q 1_{(0,T]}(γ_q) A_q^σ(t) + (2σ/(H − 1)) Re ξ'/ξ(H + it)`. -/
theorem deficitEnvelope_le_window {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ H T t : ℝ}
    (hσ : 1 < σ) (hH : 1 < H) (htH : H ≤ t) (htT : t ≤ T - H) :
    deficitEnvelope hW σ t ≤ ∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q +
      2 * σ / (H - 1) * ∑' q, copyPoisson H t q := by
  have hk : 0 ≤ 2 * σ / (H - 1) := div_nonneg (by linarith) (by linarith)
  have hs1 := summable_deficit_mul_copyPoisson hσ t (ordinateWindowWeight_nonneg hW T)
    (ordinateWindowWeight_le_one hW T)
  have hs2 := (summable_copyPoisson hH t).mul_left (2 * σ / (H - 1))
  rw [← tsum_mul_left, ← hs1.tsum_add hs2]
  refine (summable_deficit_mul_copyPoisson hσ t (deficitWeight_nonneg hW)
    (deficitWeight_le_one hW)).tsum_le_tsum (fun q => ?_) (hs1.add hs2)
  have hA := (copyPoisson_pos hσ.le t q).le
  have hAH := (copyPoisson_pos hH.le t q).le
  by_cases hw : 0 < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ T
  · rw [ordinateWindowWeight, if_pos hw]
    have := mul_nonneg hk hAH
    linarith
  · rw [ordinateWindowWeight, if_neg hw, zero_mul, zero_add]
    have hfar : H ≤ |t - ((q.1 : ℂ)).im| := by
      rcases not_and_or.mp hw with h | h
      · push Not at h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · push Not at h
        rw [abs_of_neg (by linarith)]
        linarith
    calc deficitWeight hW q * copyPoisson σ t q ≤ 1 * copyPoisson σ t q :=
          mul_le_mul_of_nonneg_right (deficitWeight_le_one hW q) hA
      _ ≤ _ := by rw [one_mul]; exact copyPoisson_le_shift hσ.le hH q hfar

/-- The window part has total mass at most `πD(T)` on every interval. -/
theorem integral_window_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ T : ℝ} (hσ : 1 < σ)
    (hT : 0 ≤ T) (a b : ℝ) :
    ∫ t in a..b, ∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q ≤ π * deficitCount hW T := by
  have hfin := finite_xiZeroCopy_band (T / 2) (by linarith : (0 : ℝ) ≤ T / 2)
  set S := hfin.toFinset
  have hzero : ∀ q ∉ S, ordinateWindowWeight hW T q = 0 := by
    intro q hq
    rw [ordinateWindowWeight, if_neg]
    intro h
    apply hq
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, abs_le]
    constructor <;> linarith [h.1, h.2]
  have hsum : ∀ t, ∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q =
      ∑ q ∈ S, ordinateWindowWeight hW T q * copyPoisson σ t q :=
    fun t => tsum_eq_sum fun q hq => by rw [hzero q hq, zero_mul]
  have hD : deficitCount hW T = ∑ q ∈ S, ordinateWindowWeight hW T q := tsum_eq_sum fun q hq => hzero q hq
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum (f := fun q t => ordinateWindowWeight hW T q * copyPoisson σ t q)
    fun q _ => ((continuous_copyPoisson hσ.le q).const_mul _).intervalIntegrable _ _,
    hD, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [intervalIntegral.integral_const_mul, mul_comm π]
  exact mul_le_mul_of_nonneg_left (integral_copyPoisson_le_pi hσ.le q a b)
    (ordinateWindowWeight_nonneg hW T q)

/-- **The counting bound.**  For `T ≥ 64` and `σ ≤ √T`,
`∫_8^T ε_σ ≤ πD(T) + (2 + 4σ)√T (½ log T + C_σ)`. -/
theorem integral_deficitEnvelope_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ T : ℝ}
    (hσ : 1 < σ) (hT : 64 ≤ T) (hσT : σ ≤ √T) :
    ∫ t in (8 : ℝ)..T, deficitEnvelope hW σ t ≤
      π * deficitCount hW T + (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ) := by
  set H := √T with hHdef
  have hH8 : 8 ≤ H := by
    rw [hHdef, show (8 : ℝ) = √64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hHsq : H * H = T := Real.mul_self_sqrt (by linarith)
  have h2H : 2 * H ≤ T := by nlinarith
  have hHT : H ≤ T := by nlinarith
  set B := Real.log T / 2 + envelopeConst σ with hB
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ 1 / σ := by positivity
    have h3 : 0 ≤ 1 / (σ - 1) := one_div_nonneg.mpr (by linarith)
    have h4 := vonMangoldtMajorant_nonneg σ
    rw [hB, envelopeConst]
    linarith
  have hcε := continuous_deficitEnvelope hW hσ
  have hi : ∀ a b, IntervalIntegrable (deficitEnvelope hW σ) volume a b :=
    fun a b => hcε.intervalIntegrable a b
  have hP : ∀ t, 8 ≤ t → t ≤ T → deficitEnvelope hW σ t ≤ B := fun t ht htT =>
    (deficitEnvelope_le_re_logDeriv_xi hW hσ t).trans
      (re_logDeriv_xi_le_log hσ le_rfl (by linarith) ht htT)
  have hPH : ∀ t, 8 ≤ t → t ≤ T → ∑' q, copyPoisson H t q ≤ B := fun t ht htT => by
    rw [← re_logDeriv_xi_eq_tsum_copyPoisson (by linarith) t]
    exact re_logDeriv_xi_le_log hσ hσT hHT ht htT
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 8 H) (hi H T),
    ← intervalIntegral.integral_add_adjacent_intervals (hi H (T - H)) (hi (T - H) T)]
  have hend1 : ∫ t in (8 : ℝ)..H, deficitEnvelope hW σ t ≤ H * B := by
    calc _ ≤ ∫ _ in (8 : ℝ)..H, B :=
          intervalIntegral.integral_mono_on hH8 (hi _ _) intervalIntegrable_const
            fun t ht => hP t ht.1 (by linarith [ht.2])
      _ = (H - 8) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ H * B := by nlinarith
  have hend2 : ∫ t in (T - H)..T, deficitEnvelope hW σ t ≤ H * B := by
    calc _ ≤ ∫ _ in (T - H)..T, B :=
          intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const
            fun t ht => hP t (by linarith [ht.1]) ht.2
      _ = H * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hk : 0 ≤ 2 * σ / (H - 1) := div_nonneg (by linarith) (by linarith)
  have hW1 : Continuous fun t => ∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q :=
    continuous_weighted_copyPoisson hσ (ordinateWindowWeight_nonneg hW T) (ordinateWindowWeight_le_one hW T)
  have hP1 : Continuous fun t => ∑' q, copyPoisson H t q := continuous_tsum_copyPoisson (by linarith)
  have hmidP : ∫ t in H..(T - H), ∑' q, copyPoisson H t q ≤ (T - 2 * H) * B := by
    calc _ ≤ ∫ _ in H..(T - H), B :=
          intervalIntegral.integral_mono_on (by linarith) (hP1.intervalIntegrable _ _)
            intervalIntegrable_const fun t ht => hPH t (by linarith [ht.1]) (by linarith [ht.2])
      _ = (T - 2 * H) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hmid : ∫ t in H..(T - H), deficitEnvelope hW σ t ≤
      π * deficitCount hW T + 2 * σ / (H - 1) * ((T - 2 * H) * B) := by
    calc ∫ t in H..(T - H), deficitEnvelope hW σ t
        ≤ ∫ t in H..(T - H), (∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q +
            2 * σ / (H - 1) * ∑' q, copyPoisson H t q) :=
          intervalIntegral.integral_mono_on (by linarith) (hi _ _)
            ((hW1.add (hP1.const_mul _)).intervalIntegrable _ _)
            fun t ht => deficitEnvelope_le_window hW hσ (by linarith) ht.1 ht.2
      _ = (∫ t in H..(T - H), ∑' q, ordinateWindowWeight hW T q * copyPoisson σ t q) +
            2 * σ / (H - 1) * ∫ t in H..(T - H), ∑' q, copyPoisson H t q := by
          rw [intervalIntegral.integral_add (hW1.intervalIntegrable _ _)
            ((hP1.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
      _ ≤ π * deficitCount hW T + 2 * σ / (H - 1) * ((T - 2 * H) * B) :=
          add_le_add (integral_window_le hW hσ (by linarith) _ _)
            (mul_le_mul_of_nonneg_left hmidP hk)
  have hkT : 2 * σ / (H - 1) * T ≤ 4 * σ * H := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hkB : 2 * σ / (H - 1) * ((T - 2 * H) * B) ≤ 4 * σ * H * B := by
    calc 2 * σ / (H - 1) * ((T - 2 * H) * B) ≤ 2 * σ / (H - 1) * (T * B) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hk
      _ = (2 * σ / (H - 1) * T) * B := by ring
      _ ≤ 4 * σ * H * B := mul_le_mul_of_nonneg_right hkT hB0
  have hexp : (2 + 4 * σ) * H * B = 2 * (H * B) + 4 * σ * H * B := by ring
  linarith

/-! ## The counting form of the deficit law -/

theorem tendsto_envelopeError (σ : ℝ) :
    Tendsto (fun T : ℝ => (2 + 4 * σ) * (Real.log T / 2 + envelopeConst σ) / √T) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    Real.tendsto_sqrt_atTop
  have h1 : Tendsto (fun T : ℝ => Real.log T / √T) atTop (𝓝 0) := by
    have := h0.const_mul 2
    rw [mul_zero] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
    simp only [Function.comp, pow_one, one_mul, add_zero]
    rw [Real.log_sqrt hT.le]
    ring
  have h2 : Tendsto (fun T : ℝ => 1 / √T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have := ((h1.div_const 2).add (h2.const_mul (envelopeConst σ))).const_mul (2 + 4 * σ)
  rw [show (2 + 4 * σ) * (0 / 2 + envelopeConst σ * 0) = 0 by ring] at this
  exact this.congr fun T => by ring

/-- **The singular deficit law at abscissa `σ`.**  If `D(T)/T ≤ E + η` along arbitrarily large
`T`, for every `η > 0`, then `|lam(m) − Λ(m)| m^{−σ} ≤ 4πE`. -/
theorem abs_sub_vonMangoldt_mul_rpow_le_of_deficitCount {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ) {E : ℝ}
    (hE : ∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ E + η) {m : ℕ} (hm : 2 ≤ m) :
    |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-σ) ≤ 4 * (π * E) := by
  refine abs_sub_vonMangoldt_le_of_envelope hW hσ (E := π * E) (fun η hη => ?_) hm
  have hev : ∀ᶠ T in atTop, 64 ≤ T ∧ σ ^ 2 ≤ T ∧
      (2 + 4 * σ) * (Real.log T / 2 + envelopeConst σ) / √T ≤ η / 2 :=
    (eventually_ge_atTop 64).and ((eventually_ge_atTop (σ ^ 2)).and
      ((tendsto_envelopeError σ).eventually (ge_mem_nhds (by linarith))))
  refine (hev.and_frequently (hE (η / (2 * π)) (by positivity))).mono fun T hT' => ?_
  obtain ⟨⟨hT, hσT, herr⟩, hD⟩ := hT'
  have hT0 : 0 < T := by linarith
  have hσT' : σ ≤ √T := (Real.le_sqrt (by linarith) hT0.le).mpr hσT
  have hI := integral_deficitEnvelope_le hW hσ hT hσT'
  have hsq : √T * √T = T := Real.mul_self_sqrt hT0.le
  have hsqpos : 0 < √T := Real.sqrt_pos.mpr hT0
  rw [div_le_iff₀ hT0]
  have h1 : π * deficitCount hW T ≤ π * ((E + η / (2 * π)) * T) :=
    mul_le_mul_of_nonneg_left ((div_le_iff₀ hT0).mp hD) Real.pi_pos.le
  have h2 : (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ) ≤ η / 2 * T := by
    have := (div_le_iff₀ hsqpos).mp herr
    calc (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ)
        = (2 + 4 * σ) * (Real.log T / 2 + envelopeConst σ) * √T := by ring
      _ ≤ η / 2 * √T * √T := mul_le_mul_of_nonneg_right this hsqpos.le
      _ = η / 2 * T := by rw [mul_assoc, hsq]
  have h3 : π * ((E + η / (2 * π)) * T) = π * E * T + η / 2 * T := by
    field_simp
  have h4 : (π * E + η) * T = π * E * T + η / 2 * T + η / 2 * T := by ring
  linarith

/-- **The singular deficit law (counting form).**  For a full-cone Weil-positive `lam`: if the
deficit count satisfies `D(T)/T ≤ E + η` along arbitrarily large `T`, for every `η > 0`, then
`|lam(m) − Λ(m)| ≤ 4π m E` for every `m ≥ 2`. -/
theorem abs_sub_vonMangoldt_le_of_deficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {E : ℝ}
    (hE : ∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ E + η) {m : ℕ} (hm : 2 ≤ m) :
    |lam m - ArithmeticFunction.vonMangoldt m| ≤ 4 * π * m * E := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcont : Continuous fun σ : ℝ => |lam m - ArithmeticFunction.vonMangoldt m| *
      (m : ℝ) ^ (-σ) :=
    continuous_const.mul (continuous_const.rpow continuous_neg fun _ => Or.inl hmpos.ne')
  have hlim := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  have hle := le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) =>
    abs_sub_vonMangoldt_mul_rpow_le_of_deficitCount hW hσ hE hm)
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hmpos] at hle
  linarith

/-- **Sparse repair is impossible.**  A full-cone producer whose deficit count has lower density
zero is `Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_deficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (h0 : ∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ η) :
    ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  intro m hm
  have h := abs_sub_vonMangoldt_le_of_deficitCount hW (E := 0)
    (fun η hη => by simpa using h0 η hη) hm
  rw [mul_zero] at h
  have : |lam m - ArithmeticFunction.vonMangoldt m| = 0 := le_antisymm h (abs_nonneg _)
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

/-- **Sparse repair forces RH.**  If some full-cone Weil-positive `lam` has a deficit count of lower
density zero, then RH holds. -/
theorem riemannHypothesis_of_deficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (h0 : ∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ η) : RiemannHypothesis :=
  riemannHypothesis_of_weilPositiveFull_of_ge hW fun n hn =>
    (eq_vonMangoldt_of_deficitCount hW h0 n hn).ge

end RHTower.WeilSpectral

end
