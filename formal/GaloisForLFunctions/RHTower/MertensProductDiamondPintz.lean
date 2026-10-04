import GaloisForLFunctions.RHTower.MertensErrorLittlewoodOmega
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# The Diamond–Pintz theorem: oscillation of Mertens' product

Let `N = ⌊x⌋` and `P(x) = -log ∏_{p ≤ x}(1 - 1/p) = Σ_{p ≤ N} Σ_{k ≥ 1} 1/(k p^k)`.  The prime-power
sum `A(x) = Σ_{n ≤ x} Λ(n)/(n log n)` is the part with `p^k ≤ N`, so

```text
P(x) - A(x) = Σ_{p ≤ N} Σ_{k > K_p} 1/(k p^k),     K_p = ⌊log_p N⌋,
```

and each inner tail is at most `2/((K_p + 1) p^{K_p + 1}) ≤ min(2 log p/(x log x), 1/p²)`.
Splitting
at `p = √x`, Chebyshev's bound `θ(y) ≤ y log 4` and Abel summation give

```text
0 ≤ P(x) - A(x) ≤ 8 log 4/(√x log x)        (x ≥ 4).
```

With `mertensError_omega_pm_littlewood` this proves the theorem of Diamond and Pintz:
`P(x) - log log x - γ = Ω±(logloglog x/(√x log x))`; in particular
`∏_{p ≤ x}(1 - 1/p)^{-1} - e^γ log x` changes sign infinitely often.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Regrouping `A` by primes -/

/-- `A(x) = Σ_{p ≤ N} Σ_{k=1}^{K_p} 1/(k p^k)`. -/
theorem mertensPowerSum_eq_sum_primes (x : ℝ) :
    mertensPowerSum x = ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
  set N := ⌊x⌋₊ with hN
  rw [show (∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime,
      ∑ k ∈ Finset.Icc 1 (Nat.log p N), 1 / ((k : ℝ) * (p : ℝ) ^ k))
      = ∑ a ∈ ((Finset.Icc 0 N).filter Nat.Prime).sigma (fun p => Finset.Icc 1 (Nat.log p N)),
          1 / ((a.2 : ℝ) * (a.1 : ℝ) ^ a.2) from
      (Finset.sum_sigma ((Finset.Icc 0 N).filter Nat.Prime) (fun p => Finset.Icc 1 (Nat.log p N))
        (fun a => 1 / ((a.2 : ℝ) * (a.1 : ℝ) ^ a.2))).symm]
  unfold mertensPowerSum
  rw [← hN]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.1 ^ a.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ ha _
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨⟨_, hpN⟩, hp⟩, hk1, hkK⟩ := ha
    have hN0 : N ≠ 0 := by have := hp.two_le; omega
    simp only [Finset.mem_Icc]
    refine ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
    exact le_trans (Nat.pow_le_pow_right hp.pos hkK) (Nat.pow_log_le_self p hN0)
  · rintro ⟨p, k⟩ ha _ ⟨q, j⟩ hb _ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at ha hb
    dsimp only at h
    obtain ⟨hpq, hkj⟩ := Nat.Prime.pow_inj' ha.1.2 hb.1.2 (show k ≠ 0 by omega)
      (show j ≠ 0 by omega) h
    subst hpq; subst hkj; rfl
  · intro n hn hg
    simp only [Finset.mem_Icc] at hn
    have hΛ : vonMangoldt n ≠ 0 := by
      intro h0; apply hg; simp [eulerLogCoeffReal, h0]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpk : p ≤ p ^ k := Nat.le_self_pow hk.ne' p
    refine ⟨⟨p, k⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨Nat.zero_le _, le_trans hpk hn.2⟩, hp⟩, hk, Nat.le_log_of_pow_le hp.one_lt hn.2⟩
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
  · rintro ⟨p, k⟩ ha _
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨_, hp⟩, hk1, _⟩ := ha
    have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    simp only [eulerLogCoeffReal]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
    field_simp

/-! ## The tail of `-log(1 - 1/p)` -/

theorem sum_Icc_one_inv_mul_pow_eq (p : ℕ) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * (p : ℝ) ^ k)
      = ∑ n ∈ Finset.range K, (1 / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    congr 1
    push_cast
    rw [one_div_pow]
    field_simp

/-- `0 ≤ -log(1 - 1/p) - Σ_{k ≤ K} 1/(k p^k) ≤ 2/((K + 1) p^{K + 1})`. -/
theorem log_one_sub_inv_tail_mem {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    0 ≤ -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * (p : ℝ) ^ k) ∧
      -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * (p : ℝ) ^ k)
        ≤ 2 / (((K : ℝ) + 1) * (p : ℝ) ^ (K + 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; linarith
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one habs
  set a : ℕ → ℝ := fun n => r ^ (n + 1) / ((n : ℝ) + 1) with ha
  have hsplit := hS.summable.sum_add_tsum_nat_add K
  rw [hS.tsum_eq] at hsplit
  rw [sum_Icc_one_inv_mul_pow_eq, ← hr]
  have htail : -Real.log (1 - r) - ∑ n ∈ Finset.range K, a n = ∑' n : ℕ, a (n + K) := by
    linarith
  rw [htail]
  have hsumm : Summable fun n : ℕ => a (n + K) := (summable_nat_add_iff K).mpr hS.summable
  constructor
  · exact tsum_nonneg fun n => by rw [ha]; positivity
  · have hgeo : Summable fun n : ℕ => r ^ (K + 1) / ((K : ℝ) + 1) * r ^ n :=
      (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
    have hle : ∀ n : ℕ, a (n + K) ≤ r ^ (K + 1) / ((K : ℝ) + 1) * r ^ n := by
      intro n
      rw [ha]
      simp only
      have h1 : ((K : ℝ) + 1) ≤ ((n + K : ℕ) : ℝ) + 1 := by
        push_cast; linarith [n.cast_nonneg (α := ℝ)]
      have h2 : r ^ (n + K + 1) = r ^ (K + 1) * r ^ n := by ring
      rw [h2, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
    calc ∑' n : ℕ, a (n + K) ≤ ∑' n : ℕ, r ^ (K + 1) / ((K : ℝ) + 1) * r ^ n :=
          hsumm.tsum_le_tsum hle hgeo
      _ = r ^ (K + 1) / ((K : ℝ) + 1) * (1 - r)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
      _ ≤ r ^ (K + 1) / ((K : ℝ) + 1) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      _ = 2 / (((K : ℝ) + 1) * (p : ℝ) ^ (K + 1)) := by
          rw [hr, one_div_pow]; field_simp

/-- The prime tail `t_p = -log(1 - 1/p) - Σ_{k ≤ K_p} 1/(k p^k)`. -/
def mertensPrimeTail (N p : ℕ) : ℝ :=
  -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 (Nat.log p N), 1 / ((k : ℝ) * (p : ℝ) ^ k)

/-- For `p ≤ N = ⌊x⌋`: `0 ≤ t_p`, `t_p ≤ 2 log p/(x log x)` and `t_p ≤ 1/p²`. -/
theorem mertensPrimeTail_bounds {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : p.Prime) (hpN : p ≤ ⌊x⌋₊) :
    0 ≤ mertensPrimeTail ⌊x⌋₊ p ∧
      mertensPrimeTail ⌊x⌋₊ p ≤ 2 * Real.log p / (x * Real.log x) ∧
      mertensPrimeTail ⌊x⌋₊ p ≤ 1 / (p : ℝ) ^ 2 := by
  set N := ⌊x⌋₊ with hN
  set K := Nat.log p N with hK
  obtain ⟨h0, h1⟩ := log_one_sub_inv_tail_mem hp.two_le K
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hK1 : 1 ≤ K := Nat.log_pos hp.one_lt hpN
  -- `p^{K+1} > x`
  have hpow : x < (p : ℝ) ^ (K + 1) := by
    have h := Nat.lt_pow_succ_log_self hp.one_lt N
    have h' : ((N + 1 : ℕ) : ℝ) ≤ ((p ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith [Nat.lt_floor_add_one x]
  have hpow0 : 0 < (p : ℝ) ^ (K + 1) := by positivity
  have hKlog : Real.log x / Real.log p ≤ (K : ℝ) + 1 := by
    rw [div_le_iff₀ hlp]
    have := Real.log_lt_log hx0 hpow
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  refine ⟨h0, ?_, ?_⟩
  · refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : Real.log x ≤ ((K : ℝ) + 1) * Real.log p := by
      rwa [div_le_iff₀ hlp] at hKlog
    have h3 : x * Real.log x ≤ (p : ℝ) ^ (K + 1) * (((K : ℝ) + 1) * Real.log p) :=
      mul_le_mul hpow.le h2 hlx.le hpow0.le
    nlinarith
  · refine h1.trans ?_
    have hK2 : (2 : ℝ) ≤ (K : ℝ) + 1 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
      linarith
    have hpp : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (K + 1) :=
      pow_le_pow_right₀ hp1.le (by omega)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (p : ℝ)]

/-! ## Summing the tails -/

/-- **Abel summation for `Σ log p/p²`.**  `Σ_{y < p ≤ x} log p/p² ≤ 3 log 4/y` for `1 ≤ y ≤ x`. -/
theorem sum_Ioc_prime_log_div_sq_le {y x : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, 1 / (n : ℝ) ^ 2 * (if n.Prime then Real.log n else 0)
      ≤ 3 * Real.log 4 / y := by
  have hy0 : 0 < y := by linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : ∀ t ∈ Icc y x, HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-(2 / t ^ 3)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have h := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht0)
    simp only [one_div]
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => -(2 / t ^ 3)) (Icc y x) :=
    (continuousOn_const.div (continuousOn_pow 3) fun t (ht : t ∈ Icc y x) =>
      pow_ne_zero 3 (ne_of_gt (show (0 : ℝ) < t by linarith [ht.1]))).neg
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / t ^ 2) (Icc y x) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (c := fun n => if n.Prime then Real.log n else 0)
    (f := fun t : ℝ => 1 / t ^ 2) hy0.le hyx (fun t ht => (hd t ht).differentiableAt) hint
  have hθ : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0)
      = Chebyshev.theta t := fun t => by rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at h
  rw [h]
  -- the integral term
  have hI : -∫ t in Ioc y x, deriv (fun t : ℝ => 1 / t ^ 2) t * Chebyshev.theta t
      ≤ 2 * Real.log 4 / y := by
    have hcongr : ∫ t in Ioc y x, deriv (fun t : ℝ => 1 / t ^ 2) t * Chebyshev.theta t
        = -∫ t in y..x, 2 / t ^ 3 * Chebyshev.theta t := by
      rw [intervalIntegral.integral_of_le hyx, ← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
      ring
    rw [hcongr, neg_neg]
    have hc3 : ContinuousOn (fun t : ℝ => 2 / t ^ 3) (uIcc y x) := by
      rw [uIcc_of_le hyx]
      exact continuousOn_const.div (continuousOn_id.pow 3) fun t ht => pow_ne_zero 3 (ne_of_gt (by
        linarith [ht.1]))
    have hc2 : ContinuousOn (fun t : ℝ => 2 * Real.log 4 / t ^ 2) (uIcc y x) := by
      rw [uIcc_of_le hyx]
      exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (ne_of_gt (by
        linarith [ht.1]))
    have hmono : ∫ t in y..x, 2 / t ^ 3 * Chebyshev.theta t
        ≤ ∫ t in y..x, 2 * Real.log 4 / t ^ 2 := by
      refine intervalIntegral.integral_mono_on hyx
        ((Chebyshev.theta_mono.intervalIntegrable).continuousOn_mul hc3)
        hc2.intervalIntegrable fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hθt := Chebyshev.theta_le_log4_mul_x ht0.le
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * Chebyshev.theta t * t ^ 2 ≤ 2 * (Real.log 4 * t) * t ^ 2 := by
        have := Chebyshev.theta_nonneg t
        nlinarith [sq_nonneg t]
      nlinarith
    have hFTC : ∫ t in y..x, 2 * Real.log 4 / t ^ 2 = 2 * Real.log 4 * (1 / y - 1 / x) := by
      have hd2 : ∀ t ∈ uIcc y x, HasDerivAt (fun t : ℝ => -(2 * Real.log 4 / t))
          (2 * Real.log 4 / t ^ 2) t := by
        intro t ht
        rw [uIcc_of_le hyx] at ht
        have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
        have h := ((hasDerivAt_id t).inv ht0).const_mul (2 * Real.log 4) |>.neg
        refine h.congr_deriv ?_
        simp only [id]
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hc2.intervalIntegrable]
      ring
    rw [hFTC] at hmono
    have hx0 : 0 < x := by linarith
    have : 2 * Real.log 4 * (1 / y - 1 / x) ≤ 2 * Real.log 4 / y := by
      have h1x : 0 < 1 / x := by positivity
      rw [mul_sub, mul_one_div]
      linarith [mul_pos (by positivity : (0 : ℝ) < 2 * Real.log 4) h1x]
    linarith
  have hx0 : 0 < x := by linarith
  have hθx : 1 / x ^ 2 * Chebyshev.theta x ≤ Real.log 4 / y := by
    have h1 := Chebyshev.theta_le_log4_mul_x hx0.le
    calc 1 / x ^ 2 * Chebyshev.theta x ≤ 1 / x ^ 2 * (Real.log 4 * x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.log 4 / x := by field_simp
      _ ≤ Real.log 4 / y := div_le_div_of_nonneg_left hl4.le hy0 hyx
  have hθy : 0 ≤ 1 / y ^ 2 * Chebyshev.theta y :=
    mul_nonneg (by positivity) (Chebyshev.theta_nonneg y)
  have e : 3 * Real.log 4 / y = Real.log 4 / y + 2 * Real.log 4 / y := by ring
  linarith


/-- **The prime-tail sum.**  `Σ_{p ≤ N} t_p ≤ 8 log 4/(√x log x)` for `x ≥ 4`. -/
theorem sum_mertensPrimeTail_le {x : ℝ} (hx : 4 ≤ x) :
    ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, mertensPrimeTail ⌊x⌋₊ p
      ≤ 8 * Real.log 4 / (Real.sqrt x * Real.log x) := by
  set N := ⌊x⌋₊ with hN
  set S := (Finset.Icc 0 N).filter Nat.Prime with hS
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 2 ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hsxx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hmem : ∀ p ∈ S, p.Prime ∧ p ≤ N := fun p hp => by
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hp; exact ⟨hp.2, hp.1.2⟩
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x)]
  -- small primes
  have hsmall : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x), mertensPrimeTail N p
      ≤ 2 * Real.log 4 / (Real.sqrt x * Real.log x) := by
    have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x), mertensPrimeTail N p
        ≤ ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x),
          2 / (x * Real.log x) * Real.log p := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpS := (Finset.mem_filter.mp hp).1
      obtain ⟨hpr, hpN⟩ := hmem p hpS
      have := (mertensPrimeTail_bounds (by linarith) hpr hpN).2.1
      rw [show 2 / (x * Real.log x) * Real.log p = 2 * Real.log p / (x * Real.log x) by ring]
      exact this
    have h2 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x), Real.log (p : ℝ)
        ≤ Chebyshev.theta (Real.sqrt x) := by
      rw [Chebyshev.theta_eq_sum_Icc]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ =>
        Real.log_natCast_nonneg p)
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨Nat.zero_le _, Nat.le_floor hp.2⟩, hp.1.2⟩
    have h3 := Chebyshev.theta_le_log4_mul_x hsx0.le
    rw [← Finset.mul_sum] at h1
    calc _ ≤ 2 / (x * Real.log x) * ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt x),
          Real.log (p : ℝ) := h1
      _ ≤ 2 / (x * Real.log x) * (Real.log 4 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = 2 * Real.log 4 * Real.sqrt x / (x * Real.log x) := by ring
      _ = 2 * Real.log 4 * Real.sqrt x / (Real.sqrt x * Real.sqrt x * Real.log x) := by
          rw [Real.mul_self_sqrt hx0.le]
      _ = 2 * Real.log 4 / (Real.sqrt x * Real.log x) := by field_simp
  -- large primes
  have hlarge : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt x), mertensPrimeTail N p
      ≤ 6 * Real.log 4 / (Real.sqrt x * Real.log x) := by
    set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 * (if n.Prime then Real.log n else 0) with hg
    have h1 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt x), mertensPrimeTail N p
        ≤ ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt x), 2 / Real.log x * g p := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpS, hpx⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpr, hpN⟩ := hmem p hpS
      have ht := (mertensPrimeTail_bounds (by linarith) hpr hpN).2.2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      have hpx' : Real.sqrt x < p := not_le.mp hpx
      have hlog : Real.log x ≤ 2 * Real.log p := by
        have h := Real.log_lt_log hsx0 hpx'
        rw [Real.log_sqrt hx0.le] at h
        linarith
      rw [hg]
      simp only [if_pos hpr]
      refine ht.trans ?_
      rw [show 2 / Real.log x * (1 / (p : ℝ) ^ 2 * Real.log p)
        = (2 * Real.log p / Real.log x) * (1 / (p : ℝ) ^ 2) by ring]
      have hge : 1 ≤ 2 * Real.log p / Real.log x := by rw [le_div_iff₀ hlx]; linarith
      have hpos : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
      nlinarith
    have hgnn : ∀ n, 0 ≤ g n := fun n => by
      simp only [hg]
      split_ifs
      · exact mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
      · simp
    have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt x), g p
        ≤ ∑ n ∈ Finset.Ioc ⌊Real.sqrt x⌋₊ N, g n := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun n _ _ => hgnn n)
      obtain ⟨hpS, hpx⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, hpN⟩ := hmem p hpS
      have hpx' : Real.sqrt x < p := not_le.mp hpx
      simp only [Finset.mem_Ioc]
      refine ⟨?_, hpN⟩
      have := Nat.floor_le hsx0.le
      exact_mod_cast (lt_of_le_of_lt this hpx')
    have h3 := sum_Ioc_prime_log_div_sq_le (by linarith : (1 : ℝ) ≤ Real.sqrt x) hsxx
    rw [← Finset.mul_sum] at h1
    calc _ ≤ 2 / Real.log x * ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt x), g p := h1
      _ ≤ 2 / Real.log x * (3 * Real.log 4 / Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = 6 * Real.log 4 / (Real.sqrt x * Real.log x) := by field_simp; ring
  have e : 8 * Real.log 4 / (Real.sqrt x * Real.log x)
      = 2 * Real.log 4 / (Real.sqrt x * Real.log x)
        + 6 * Real.log 4 / (Real.sqrt x * Real.log x) := by ring
  linarith

/-! ## The product -/

/-- The Mertens product error `P(x) - log log x - γ`, `P(x) = -log ∏_{p ≤ x}(1 - 1/p)`. -/
def mertensProductError (x : ℝ) : ℝ :=
  -Real.log (mertensPrimeProduct ⌊x⌋₊) - Real.log (Real.log x) - Real.eulerMascheroniConstant

theorem neg_log_mertensPrimeProduct_eq (N : ℕ) :
    -Real.log (mertensPrimeProduct N)
      = ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, -Real.log (1 - 1 / (p : ℝ)) := by
  have hpos : ∀ n ∈ Finset.Icc 0 N, (if n.Prime then 1 - ((n : ℝ))⁻¹ else 1) ≠ 0 := by
    intro n _
    by_cases hp : n.Prime
    · rw [if_pos hp]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      have : ((n : ℝ))⁻¹ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) this
      linarith
    · rw [if_neg hp]; norm_num
  rw [mertensPrimeProduct, Real.log_prod hpos, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, one_div]
  · rw [if_neg hp, if_neg hp]; simp

/-- **Product versus prime powers.**  `0 ≤ P(x) - A(x) ≤ 8 log 4/(√x log x)` for `x ≥ 4`. -/
theorem mertensProductError_sub_mem {x : ℝ} (hx : 4 ≤ x) :
    0 ≤ mertensProductError x - mertensError x ∧
      mertensProductError x - mertensError x ≤ 8 * Real.log 4 / (Real.sqrt x * Real.log x) := by
  have heq : mertensProductError x - mertensError x
      = ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, mertensPrimeTail ⌊x⌋₊ p := by
    unfold mertensProductError mertensError mertensPrimeTail
    rw [neg_log_mertensPrimeProduct_eq, mertensPowerSum_eq_sum_primes, Finset.sum_sub_distrib]
    ring
  rw [heq]
  refine ⟨Finset.sum_nonneg fun p hp => ?_, sum_mertensPrimeTail_le hx⟩
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  exact (mertensPrimeTail_bounds (by linarith) hp.2 hp.1.2).1

/-- **Diamond–Pintz, upper side.**  `P(x) - log log x - γ > (c/28) logloglog x/(√x log x)` for
arbitrarily large `x`, `c = 1/(70π³)`. -/
theorem frequently_littlewood_lt_mertensProductError :
    ∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.log (Real.log (Real.log x))
      / (Real.sqrt x * Real.log x) < mertensProductError x :=
  (frequently_littlewood_lt_mertensError.and_eventually (eventually_ge_atTop (4 : ℝ))).mono
    fun x ⟨h, hx⟩ => by linarith [(mertensProductError_sub_mem hx).1]

/-- **Diamond–Pintz, lower side.**  `P(x) - log log x - γ < -(c/56) logloglog x/(√x log x)` for
arbitrarily large `x`. -/
theorem frequently_mertensProductError_lt_neg_littlewood :
    ∃ᶠ x : ℝ in atTop, mertensProductError x
      < -(littlewoodConst / 56 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) := by
  have hc0 := littlewoodConst_pos
  refine (frequently_mertensError_lt_neg_littlewood.and_eventually
    ((eventually_ge_atTop (4 : ℝ)).and (tendsto_logLogLog_atTop.eventually_ge_atTop
      (448 * Real.log 4 / littlewoodConst)))).mono fun x ⟨h, hx, hL⟩ => ?_
  have hx0 : 0 < x := by linarith
  have hD : 0 < Real.sqrt x * Real.log x :=
    mul_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos (by linarith))
  have h2 := (mertensProductError_sub_mem hx).2
  have hL' : 8 * Real.log 4 ≤ littlewoodConst / 56 * Real.log (Real.log (Real.log x)) := by
    rw [div_le_iff₀ hc0] at hL; linarith
  have hsplit : -(littlewoodConst / 28 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) + 8 * Real.log 4 / (Real.sqrt x * Real.log x)
      ≤ -(littlewoodConst / 56 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) := by
    rw [← neg_div, ← neg_div, ← add_div, div_le_div_iff_of_pos_right hD]
    linarith
  linarith

/-- **The Diamond–Pintz theorem.**  `P(x) - log log x - γ = Ω±(logloglog x/(√x log x))`. -/
theorem mertensProductError_omega_pm_littlewood :
    (∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.log (Real.log (Real.log x))
      / (Real.sqrt x * Real.log x) < mertensProductError x) ∧
    ∃ᶠ x : ℝ in atTop, mertensProductError x
      < -(littlewoodConst / 56 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) :=
  ⟨frequently_littlewood_lt_mertensProductError, frequently_mertensProductError_lt_neg_littlewood⟩

theorem mertensProductError_pos_iff {x : ℝ} (hx : 1 < x) :
    0 < mertensProductError x
      ↔ Real.exp Real.eulerMascheroniConstant * Real.log x < (mertensPrimeProduct ⌊x⌋₊)⁻¹ := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hP := mertensPrimeProduct_pos ⌊x⌋₊
  have hR : 0 < Real.exp Real.eulerMascheroniConstant * Real.log x := by positivity
  rw [← Real.log_lt_log_iff hR (inv_pos.mpr hP), Real.log_inv, Real.log_mul
    (Real.exp_pos _).ne' hlx.ne', Real.log_exp, mertensProductError]
  constructor <;> intro h <;> linarith

theorem mertensProductError_neg_iff {x : ℝ} (hx : 1 < x) :
    mertensProductError x < 0
      ↔ (mertensPrimeProduct ⌊x⌋₊)⁻¹ < Real.exp Real.eulerMascheroniConstant * Real.log x := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hP := mertensPrimeProduct_pos ⌊x⌋₊
  have hR : 0 < Real.exp Real.eulerMascheroniConstant * Real.log x := by positivity
  rw [← Real.log_lt_log_iff (inv_pos.mpr hP) hR, Real.log_inv, Real.log_mul
    (Real.exp_pos _).ne' hlx.ne', Real.log_exp, mertensProductError]
  constructor <;> intro h <;> linarith

/-- **Mertens' product crosses `e^γ log x` infinitely often in both directions.** -/
theorem mertensProduct_inv_sub_exp_gamma_log_sign_changes :
    (∃ᶠ x : ℝ in atTop,
      Real.exp Real.eulerMascheroniConstant * Real.log x < (mertensPrimeProduct ⌊x⌋₊)⁻¹) ∧
    ∃ᶠ x : ℝ in atTop,
      (mertensPrimeProduct ⌊x⌋₊)⁻¹ < Real.exp Real.eulerMascheroniConstant * Real.log x := by
  have hc0 := littlewoodConst_pos
  have hev : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 0 ≤ littlewoodConst / 56
      * Real.log (Real.log (Real.log x)) / (Real.sqrt x * Real.log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), tendsto_logLogLog_atTop.eventually_ge_atTop 0]
      with x hx hL
    refine ⟨hx, div_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg x)
      (Real.log_pos hx).le)⟩
  constructor
  · refine (frequently_littlewood_lt_mertensProductError.and_eventually hev).mono
      fun x ⟨h, hx1, h0⟩ => (mertensProductError_pos_iff hx1).mp ?_
    have : 0 ≤ littlewoodConst / 28 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x) := by
      have e : littlewoodConst / 28 * Real.log (Real.log (Real.log x))
          / (Real.sqrt x * Real.log x)
          = 2 * (littlewoodConst / 56 * Real.log (Real.log (Real.log x))
            / (Real.sqrt x * Real.log x)) := by ring
      rw [e]; linarith
    linarith
  · refine (frequently_mertensProductError_lt_neg_littlewood.and_eventually hev).mono
      fun x ⟨h, hx1, h0⟩ => (mertensProductError_neg_iff hx1).mp (by linarith)

end

end RHTower
