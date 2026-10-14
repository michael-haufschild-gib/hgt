import Mathlib.NumberTheory.AbelSummation
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPNT

/-!
# The logarithmic energy floor of prime weights

Let `c : ℕ → ℝ` be supported on the primes and normalized by the prime number theorem,
`Σ_{k ≤ x} c k ~ x`.  Its logarithmic energy on the critical line is `Σ_{k ≤ T} c(k)²/k`.

**Theorem** (`eventually_half_sub_mul_log_sq_le_sum_sq_div`).  For every `ε > 0`, eventually

`Σ_{k ≤ T} c(k)²/k ≥ (½ − ε) (log T)²`.

The constant `½` is sharp: the von Mangoldt weights satisfy `Σ_{k ≤ T} Λ(k)²/k ≤ (½ + ε)(log T)²`
eventually (`eventually_sum_vonMangoldt_sq_div_le`).  So among weights obeying the prime number
theorem on the primes, `Λ` has asymptotically minimal energy, and the minimal energy
`½ log² T` is the square of the archimedean density `½ log T` of the explicit formula, up to the
factor `2` between `|L|²` and `(Re L)²`.

Proof.
* **Pointwise comparison.**  At a prime `k`, `(c(k) − log k)² ≥ 0` gives
  `c(k)²/k ≥ 2 c(k) log k / k − Λ(k) log k / k`; off the primes both sides are `0` and `−Λ log k/k ≤ 0`.
* **Abel summation** (`sum_mul_eq_sub_integral_mul₁` with `f(t) = log t / t`) turns
  `Σ_{k ≤ T} c(k) log k / k` into `log T · S(T)/T + ∫₂^T (log t − 1)/t · S(t)/t dt`.  With
  `S(t)/t → 1` the integral is `½ log² T + o(log² T)`
  (`eventually_abs_sum_logOver_mul_sub_le`).
* The same asymptotic for `Λ` (prime number theorem) bounds the subtracted term by
  `(½ + o(1)) log² T`, and `2(½) − ½ = ½`.
-/

open Real Filter Topology MeasureTheory ArithmeticFunction Set

noncomputable section

namespace RHTower.PrimeWeightEnergy

/-- The partial sum `S(x) = Σ_{k ≤ x} c k`. -/
def partialSum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k

/-- The Abel weight `log t / t`. -/
def logOver (t : ℝ) : ℝ := Real.log t / t

/-- The main kernel `(log t − 1)/t`, whose primitive is `½ log² t − log t`. -/
def mainKernel (t : ℝ) : ℝ := (Real.log t - 1) / t

theorem hasDerivAt_logOver {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt logOver ((1 - Real.log t) / t ^ 2) t := by
  have h := (Real.hasDerivAt_log ht).div (hasDerivAt_id t) ht
  refine h.congr_deriv ?_
  simp only [id_eq, mul_one]
  field_simp

theorem deriv_logOver {t : ℝ} (ht : t ≠ 0) : deriv logOver t = (1 - Real.log t) / t ^ 2 :=
  (hasDerivAt_logOver ht).deriv

theorem hasDerivAt_mainPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => Real.log u ^ 2 / 2 - Real.log u) (mainKernel t) t := by
  have h1 := Real.hasDerivAt_log ht.ne'
  have h2 := (h1.pow 2).div_const 2
  refine (h2.sub h1).congr_deriv ?_
  rw [mainKernel]
  field_simp
  ring

theorem continuousOn_mainKernel {a b : ℝ} (ha : 0 < a) : ContinuousOn mainKernel (Icc a b) := by
  have hne : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => (ha.trans_le ht.1).ne'
  exact ((Real.continuousOn_log.mono fun t ht => hne t ht).sub continuousOn_const).div
    continuousOn_id hne

theorem mainKernel_nonneg {t : ℝ} (ht : 3 ≤ t) : 0 ≤ mainKernel t := by
  have h1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans ht
  exact div_nonneg (by linarith) (by linarith)

theorem integral_mainKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, mainKernel t =
      (Real.log b ^ 2 / 2 - Real.log b) - (Real.log a ^ 2 / 2 - Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_mainPrimitive (ha.trans_le hx.1)
  · exact (continuousOn_mainKernel ha).intervalIntegrable_of_Icc hab

/-- **Abel's formula** for the weight `log t / t`. -/
theorem sum_logOver_mul_eq {c : ℕ → ℝ} (hc0 : c 0 = 0) (hc1 : c 1 = 0) {T : ℝ} (hT : 2 ≤ T) :
    ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, logOver k * c k =
      logOver T * partialSum c T + ∫ t in (2 : ℝ)..T, mainKernel t * (partialSum c t / t) := by
  have hint : IntegrableOn (deriv logOver) (Icc 2 T) := by
    have hc : ContinuousOn (fun t => (1 - Real.log t) / t ^ 2) (Icc 2 T) := by
      have hne : ∀ t ∈ Icc (2 : ℝ) T, t ≠ 0 := fun t ht => by linarith [ht.1]
      exact (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht => hne t ht)).div
        (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (hne t ht)
    refine (hc.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    rw [deriv_logOver (by linarith [ht.1] : t ≠ 0)]
  have h := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 T
    (fun t ht => (hasDerivAt_logOver (by linarith [ht.1] : t ≠ 0)).differentiableAt) hint
  rw [h, intervalIntegral.integral_of_le hT, sub_eq_add_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  simp only [partialSum, mainKernel]
  rw [deriv_logOver ht0]
  field_simp
  ring

/-- The Abel integrand is interval integrable on every `[a, b] ⊂ [2, ∞)`. -/
theorem intervalIntegrable_mainKernel_mul (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => mainKernel t * (partialSum c t / t)) volume a b := by
  have hg : IntegrableOn (fun t => mainKernel t / t) (Icc a b) := by
    have hne : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
    exact ((continuousOn_mainKernel (by linarith)).div continuousOn_id hne).integrableOn_Icc
  have h := integrableOn_mul_sum_Icc c (m := 0) (by linarith : (0 : ℝ) ≤ a) hg
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [partialSum]
  ring

theorem intervalIntegrable_mainKernel {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable mainKernel volume a b :=
  (continuousOn_mainKernel (by linarith)).intervalIntegrable_of_Icc hab

/-- **Abel asymptotic.**  If `S(x)/x → 1` then `Σ_{k ≤ T} c(k) log k / k = ½ log² T + o(log² T)`. -/
theorem eventually_abs_sum_logOver_mul_sub_le {c : ℕ → ℝ} (hc0 : c 0 = 0) (hc1 : c 1 = 0)
    (hS : Tendsto (fun x => partialSum c x / x) atTop (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      |∑ k ∈ Finset.Icc 0 ⌊T⌋₊, logOver k * c k - Real.log T ^ 2 / 2| ≤ ε * Real.log T ^ 2 := by
  have hev : ∀ᶠ x in atTop, |partialSum c x / x - 1| ≤ ε / 2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hS) (ε / 2) (by linarith)] with x hx
    rw [Real.dist_eq] at hx
    exact hx.le
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp hev
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = max t₁ 3 := ⟨_, rfl⟩
  have ht₀3 : 3 ≤ t₀ := by rw [ht₀]; exact le_max_right _ _
  have he : ∀ t, t₀ ≤ t → |partialSum c t / t - 1| ≤ ε / 2 := fun t ht =>
    ht₁ t ((le_max_left _ _).trans (ht₀ ▸ ht))
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ,
      C₀ = |∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t| := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = Real.log 2 ^ 2 / 2 - Real.log 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 + ε / 2 + |K₀| + C₀ + ε / 4 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB, hC₀]; positivity
  filter_upwards [eventually_ge_atTop t₀,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (4 * B / (3 * ε)))] with T hT hlogT
  have hT2 : (2 : ℝ) ≤ T := by linarith
  set L := Real.log T with hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlogT
  have hLM : 4 * B / (3 * ε) ≤ L := (le_max_right _ _).trans hlogT
  -- Abel and splitting of the integral
  have habel := sum_logOver_mul_eq hc0 hc1 hT2
  have hI : ∫ t in (2 : ℝ)..T, mainKernel t * (partialSum c t / t) =
      (∫ t in (2 : ℝ)..T, mainKernel t) +
        ((∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t) +
          ∫ t in t₀..T, mainKernel t * (partialSum c t / t) - mainKernel t) := by
    have h1 := intervalIntegral.integral_sub (intervalIntegrable_mainKernel_mul c le_rfl hT2)
      (intervalIntegrable_mainKernel le_rfl hT2)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_mainKernel_mul c le_rfl (by linarith : (2 : ℝ) ≤ t₀)).sub
        (intervalIntegrable_mainKernel le_rfl (by linarith : (2 : ℝ) ≤ t₀)))
      ((intervalIntegrable_mainKernel_mul c (by linarith) hT).sub
        (intervalIntegrable_mainKernel (by linarith) hT))
    linarith
  have hmain : ∫ t in (2 : ℝ)..T, mainKernel t = (L ^ 2 / 2 - L) - K₀ := by
    rw [integral_mainKernel (by norm_num) hT2, hK₀]
  -- the tail
  have htail : |∫ t in t₀..T, mainKernel t * (partialSum c t / t) - mainKernel t| ≤
      ε / 2 * (L ^ 2 / 2 + 1 / 2) := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le hT
      (f := fun t => mainKernel t * (partialSum c t / t) - mainKernel t)
      (g := fun t => ε / 2 * mainKernel t)
      (Eventually.of_forall fun t ht => by
        have hmk := mainKernel_nonneg (ht₀3.trans ht.1.le)
        have h1 := he t ht.1.le
        rw [Real.norm_eq_abs, show mainKernel t * (partialSum c t / t) - mainKernel t =
          mainKernel t * (partialSum c t / t - 1) by ring, abs_mul, abs_of_nonneg hmk]
        nlinarith)
      ((intervalIntegrable_mainKernel (by linarith) hT).const_mul _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_mainKernel (by linarith) hT] at hle
    refine hle.trans ?_
    have hu := sq_nonneg (Real.log t₀ - 1)
    have hL0 : 0 ≤ L := by linarith
    nlinarith
  -- the boundary term
  have hbd : |logOver T * partialSum c T| ≤ L * (1 + ε / 2) := by
    have hT0 : T ≠ 0 := by linarith
    have h1 := he T hT
    rw [show logOver T * partialSum c T = L * (partialSum c T / T) by
      rw [logOver, hL]; field_simp, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := abs_sub_abs_le_abs_sub (partialSum c T / T) 1
    rw [abs_one] at this
    linarith
  -- assembly
  have hkey : ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, logOver k * c k - L ^ 2 / 2 =
      logOver T * partialSum c T - L - K₀ +
        ((∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t) +
          ∫ t in t₀..T, mainKernel t * (partialSum c t / t) - mainKernel t) := by
    rw [habel, hI, hmain]
    ring
  rw [hkey]
  have hfirst : |∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t| ≤ C₀ :=
    hC₀.ge
  have hsplit := abs_add_three (logOver T * partialSum c T - L - K₀)
    (∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t)
    (∫ t in t₀..T, mainKernel t * (partialSum c t / t) - mainKernel t)
  have hfront : |logOver T * partialSum c T - L - K₀| ≤ L * (1 + ε / 2) + L + |K₀| := by
    have := abs_sub (logOver T * partialSum c T - L) K₀
    have := abs_sub (logOver T * partialSum c T) L
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)] at this
    linarith
  have hBL : B * L ≤ 3 * ε / 4 * L ^ 2 := by
    have h4 : B ≤ 3 * ε / 4 * L := by
      rw [div_le_iff₀ (by positivity)] at hLM
      linarith
    nlinarith
  rw [← add_assoc]
  calc |logOver T * partialSum c T - L - K₀ +
        (∫ t in (2 : ℝ)..t₀, mainKernel t * (partialSum c t / t) - mainKernel t) +
          ∫ t in t₀..T, mainKernel t * (partialSum c t / t) - mainKernel t|
      ≤ (L * (1 + ε / 2) + L + |K₀|) + C₀ + ε / 2 * (L ^ 2 / 2 + 1 / 2) := by
        linarith
    _ ≤ ε * L ^ 2 := by
        have hK0 : 0 ≤ |K₀| := abs_nonneg _
        have hC0 : 0 ≤ C₀ := by rw [hC₀]; exact abs_nonneg _
        rw [hB] at hBL
        nlinarith

/-- The prime number theorem in partial-sum form: `Σ_{k ≤ x} Λ(k) / x → 1`. -/
theorem tendsto_partialSum_vonMangoldt_div :
    Tendsto (fun x => partialSum (fun k => Λ k) x / x) atTop (𝓝 1) := by
  refine RHTower.Sieve.tendsto_sum_vonMangoldt_div.congr fun x => ?_
  simp only [partialSum]
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]

theorem logOver_mul_vonMangoldt_nonneg (k : ℕ) : 0 ≤ logOver k * Λ k :=
  mul_nonneg (div_nonneg (Real.log_natCast_nonneg k) (Nat.cast_nonneg k)) vonMangoldt_nonneg

/-- **The logarithmic energy floor.**  Weights supported on the primes and normalized by the prime
number theorem have energy `Σ_{k ≤ T} c(k)²/k ≥ (½ − ε) log² T` for all large `T`. -/
theorem eventually_half_sub_mul_log_sq_le_sum_sq_div {c : ℕ → ℝ}
    (hc : ∀ k, ¬ k.Prime → c k = 0)
    (hS : Tendsto (fun x => partialSum c x / x) atTop (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (1 / 2 - ε) * Real.log T ^ 2 ≤ ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, c k ^ 2 / k := by
  have hc0 : c 0 = 0 := hc 0 Nat.not_prime_zero
  have hc1 : c 1 = 0 := hc 1 Nat.not_prime_one
  have hΛ0 : (fun k => Λ k) 0 = 0 := by simp
  have hΛ1 : (fun k => Λ k) 1 = 0 := by simp
  filter_upwards [eventually_abs_sum_logOver_mul_sub_le hc0 hc1 hS (ε := ε / 3) (by linarith),
    eventually_abs_sum_logOver_mul_sub_le hΛ0 hΛ1 tendsto_partialSum_vonMangoldt_div
      (ε := ε / 3) (by linarith)] with T h1 h2
  have hpt : ∀ k ∈ Finset.Icc 0 ⌊T⌋₊,
      2 * (logOver k * c k) - logOver k * Λ k ≤ c k ^ 2 / k := by
    intro k _
    by_cases hk : k.Prime
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
      rw [vonMangoldt_apply_prime hk, logOver]
      have hsq : 0 ≤ (c k - Real.log k) ^ 2 / k := div_nonneg (sq_nonneg _) hk0.le
      have e : c k ^ 2 / k - (2 * (Real.log k / k * c k) - Real.log k / k * Real.log k) =
          (c k - Real.log k) ^ 2 / k := by
        field_simp
        ring
      linarith
    · rw [hc k hk]
      have := logOver_mul_vonMangoldt_nonneg k
      simp only [mul_zero, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_div]
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h2).2
  have hL := sq_nonneg (Real.log T)
  linarith

/-- **Sharpness.**  The von Mangoldt weights have energy `Σ_{k ≤ T} Λ(k)²/k ≤ (½ + ε) log² T` for
all large `T`. -/
theorem eventually_sum_vonMangoldt_sq_div_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, Λ k ^ 2 / k ≤ (1 / 2 + ε) * Real.log T ^ 2 := by
  have hΛ0 : (fun k => Λ k) 0 = 0 := by simp
  have hΛ1 : (fun k => Λ k) 1 = 0 := by simp
  filter_upwards [eventually_abs_sum_logOver_mul_sub_le hΛ0 hΛ1
    tendsto_partialSum_vonMangoldt_div hε] with T h
  have hpt : ∀ k ∈ Finset.Icc 0 ⌊T⌋₊, Λ k ^ 2 / k ≤ logOver k * Λ k := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [logOver]
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hle : Λ k ≤ Real.log k := vonMangoldt_le_log
      have hnn : 0 ≤ Λ k := vonMangoldt_nonneg
      rw [logOver, div_mul_eq_mul_div, sq]
      exact div_le_div_of_nonneg_right (by nlinarith) hk0.le
  have hsum := Finset.sum_le_sum hpt
  have a2 := (abs_le.mp h).2
  linarith

/-- The Chebyshev weights `θ(k) = log k` on primes, `0` elsewhere. -/
def thetaWeight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

/-- **Stability of the energy floor.**  For prime weights normalized by the prime number theorem,
the energy distance to the Chebyshev weights is controlled by the energy excess over `½ log² T`:
eventually `Σ_{k ≤ T} (c(k) − θ(k))²/k ≤ Σ_{k ≤ T} c(k)²/k − (½ − ε) log² T`.  Hence weights of
asymptotically minimal energy are asymptotically the Chebyshev weights: `Λ` is the unique energy
minimizer up to `o(log² T)` in the energy metric. -/
theorem eventually_sum_sub_thetaWeight_sq_div_le {c : ℕ → ℝ}
    (hc : ∀ k, ¬ k.Prime → c k = 0)
    (hS : Tendsto (fun x => partialSum c x / x) atTop (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, (c k - thetaWeight k) ^ 2 / k ≤
      ∑ k ∈ Finset.Icc 0 ⌊T⌋₊, c k ^ 2 / k - (1 / 2 - ε) * Real.log T ^ 2 := by
  have hc0 : c 0 = 0 := hc 0 Nat.not_prime_zero
  have hc1 : c 1 = 0 := hc 1 Nat.not_prime_one
  have hΛ0 : (fun k => Λ k) 0 = 0 := by simp
  have hΛ1 : (fun k => Λ k) 1 = 0 := by simp
  filter_upwards [eventually_abs_sum_logOver_mul_sub_le hc0 hc1 hS (ε := ε / 3) (by linarith),
    eventually_abs_sum_logOver_mul_sub_le hΛ0 hΛ1 tendsto_partialSum_vonMangoldt_div
      (ε := ε / 3) (by linarith)] with T h1 h2
  have hpt : ∀ k ∈ Finset.Icc 0 ⌊T⌋₊,
      (c k - thetaWeight k) ^ 2 / k ≤ c k ^ 2 / k - 2 * (logOver k * c k) + logOver k * Λ k := by
    intro k _
    by_cases hk : k.Prime
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.pos
      rw [thetaWeight, if_pos hk, vonMangoldt_apply_prime hk, logOver]
      apply le_of_eq
      field_simp
      ring
    · rw [thetaWeight, if_neg hk, hc k hk]
      have := logOver_mul_vonMangoldt_nonneg k
      simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
        mul_zero]
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h2).2
  linarith

end RHTower.PrimeWeightEnergy
