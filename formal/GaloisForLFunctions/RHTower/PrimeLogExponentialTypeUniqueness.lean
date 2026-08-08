import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity
import Mathlib.NumberTheory.Chebyshev

/-!
# Prime logarithms are a uniqueness set at finite exponential type

A nonzero entire function of finite exponential type has only linearly many zeros in growing
discs.  If it vanished at every prime logarithm, the disc of radius `O(t)` would instead contain
at least `π(exp t)` zeros.  Chebyshev's explicit lower bound makes that count exponentially larger
than the Jensen bound, a contradiction.

This is classical `[BRIDGE]` infrastructure.  Its role is to mark the topology transition in the
archimedean sampling problem: prime samples are maximally blind on `C₀`, but injective on every
finite-type Paley--Wiener carrier.  The theorem proves uniqueness, not a bounded sampling inverse.
-/

open Complex Metric Set Filter Topology
open scoped Nat.Prime

namespace RHTower

/-- If every prime logarithm is a zero, the analytic divisor count in the ball containing the
prime logarithms below `log n` is at least `π(n)`. -/
theorem primeCounting_le_sum_divisor_of_primeLog_zeros
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → f (Real.log p) = 0)
    {n : ℕ} (hn : 2 ≤ n) :
    (n.primeCounting : ℤ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor f
        (closedBall c (1 + ‖c‖ + Real.log n))) u := by
  let z : ℕ → ℂ := fun p => Real.log p
  have hinj : Set.InjOn z n.primesLE := by
    intro p hp q hq hpq
    have hpPrime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hqPrime : q.Prime := (Nat.mem_primesLE.mp hq).2
    have hlog : Real.log p = Real.log q := by
      exact Complex.ofReal_injective hpq
    have hpexp := congrArg Real.exp hlog
    rw [Real.exp_log (by exact_mod_cast hpPrime.pos),
      Real.exp_log (by exact_mod_cast hqPrime.pos)] at hpexp
    exact_mod_cast hpexp
  have hball : ∀ p ∈ n.primesLE, z p ∈ closedBall c (1 + ‖c‖ + Real.log n) := by
    intro p hp
    have hple : p ≤ n := (Nat.mem_primesLE.mp hp).1
    have hpPrime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hn0 : (0 : ℝ) < n := by positivity
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
    have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlogle : Real.log p ≤ Real.log n :=
      Real.log_le_log hp0 (by exact_mod_cast hple)
    rw [mem_closedBall, dist_eq]
    calc
      ‖z p - c‖ ≤ ‖z p‖ + ‖c‖ := norm_sub_le _ _
      _ = Real.log p + ‖c‖ := by
        change ‖((Real.log (p : ℝ) : ℝ) : ℂ)‖ + ‖c‖ = _
        rw [Complex.norm_real, Real.norm_of_nonneg hlogp0]
      _ ≤ 1 + ‖c‖ + Real.log n := by linarith
  have hzero : ∀ p ∈ n.primesLE, f (z p) = 0 := by
    intro p hp
    exact hprime p (Nat.mem_primesLE.mp hp).2
  simpa [Nat.primesLE_card_eq_primeCounting] using
    card_le_sum_divisor_of_finite_zeros hf hfc n.primesLE z hinj hball hzero

/-- Chebyshev's prime-count lower bound eventually exceeds any prescribed linear zero-count
envelope when measured in the prime-logarithmic radius. -/
theorem exists_chebyshev_primeLog_count_gt_linear (K : ℝ) (hK : 0 < K) (c : ℂ) :
    ∃ t : ℝ, 1 ≤ t ∧ Real.log 2 < t ∧
      K * (2 + ‖c‖ + t) <
        ((Real.exp t - 1) * Real.log 2 - Real.log (Real.exp t + 2)) / t := by
  let B : ℝ := K * (3 + ‖c‖) + 1 + Real.log 3 + Real.log 2
  let D : ℝ := B / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := div_pos hB hlog2
  have htend := Real.tendsto_exp_div_pow_atTop 2
  have hevent : ∀ᶠ t : ℝ in atTop, D + 1 ≤ Real.exp t / t ^ 2 :=
    (tendsto_atTop.1 htend (D + 1))
  have hall : ∀ᶠ t : ℝ in atTop,
      D + 1 ≤ Real.exp t / t ^ 2 ∧ 1 ≤ t ∧ Real.log 2 < t := by
    filter_upwards [hevent, eventually_ge_atTop (1 : ℝ),
      eventually_gt_atTop (Real.log 2)] with t hratio ht1 htlog2
    exact ⟨hratio, ht1, htlog2⟩
  obtain ⟨t, hratio, ht1, htlog2⟩ := hall.exists
  refine ⟨t, ht1, htlog2, ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hexp1 : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
  have hlogBound : Real.log (Real.exp t + 2) ≤ t + Real.log 3 := by
    calc
      Real.log (Real.exp t + 2) ≤ Real.log (3 * Real.exp t) := by
        apply Real.log_le_log
        · positivity
        · nlinarith
      _ = Real.log 3 + Real.log (Real.exp t) := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero t)]
      _ = t + Real.log 3 := by rw [Real.log_exp]; ring
  have hgeom : t * (2 + ‖c‖ + t) ≤ (3 + ‖c‖) * t ^ 2 := by
    have ht_sq : t ≤ t ^ 2 := by nlinarith
    have hnorm : ‖c‖ * t ≤ ‖c‖ * t ^ 2 :=
      mul_le_mul_of_nonneg_left ht_sq (norm_nonneg c)
    nlinarith
  have hsmall : t + Real.log 3 + Real.log 2 ≤
      (1 + Real.log 3 + Real.log 2) * t ^ 2 := by
    nlinarith [sq_nonneg (t - 1)]
  have hexpDom : B * t ^ 2 < Real.exp t * Real.log 2 := by
    have hratio' : D < Real.exp t / t ^ 2 := lt_of_lt_of_le (lt_add_one D) hratio
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
    have hmul : D * t ^ 2 < Real.exp t := (lt_div_iff₀ ht2).mp hratio'
    have hBD : B = D * Real.log 2 := by
      dsimp [D]
      field_simp
    calc
      B * t ^ 2 = (D * t ^ 2) * Real.log 2 := by rw [hBD]; ring
      _ < Real.exp t * Real.log 2 := mul_lt_mul_of_pos_right hmul hlog2
  rw [lt_div_iff₀ ht0]
  dsimp [B] at hexpDom
  nlinarith

/-- **Prime-log uniqueness at finite exponential type.** An entire function satisfying a global
finite-exponential-type bound and vanishing at every prime logarithm is identically zero. -/
theorem eq_zero_of_exponentialType_of_primeLog_zeros
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (hprime : ∀ p : ℕ, p.Prime → f (Real.log p) = 0) :
    f = 0 := by
  funext c
  by_contra hfc
  obtain ⟨K, hK, hzeroCount⟩ :=
    exponentialType_zeroCount_linear hf hfc hA hC hgrow
  obtain ⟨t, ht1, htlog2, hdom⟩ :=
    exists_chebyshev_primeLog_count_gt_linear K hK c
  let n : ℕ := ⌊Real.exp t⌋₊
  have hexp2 : (2 : ℝ) < Real.exp t := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num)]
      _ < Real.exp t := Real.exp_lt_exp.mpr htlog2
  have hn : 2 ≤ n := by
    apply Nat.le_floor
    exact hexp2.le
  have hn0 : (0 : ℝ) < n := by positivity
  have hnexp : (n : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hlogn : Real.log n ≤ t := by
    exact (Real.log_le_iff_le_exp hn0).2 hnexp
  have hprimeLower :
      ((Real.exp t - 1) * Real.log 2 - Real.log (Real.exp t + 2)) / t ≤
        (n.primeCounting : ℝ) := by
    have h := Chebyshev.pi_ge' (x := Real.exp t) (by linarith [Real.exp_pos t])
    simpa [n, Real.log_exp] using h
  let r : ℝ := 1 + ‖c‖ + Real.log n
  have hr : 1 ≤ r := by
    have hlogn0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    dsimp [r]
    linarith [norm_nonneg c]
  have hdivLowerInt := primeCounting_le_sum_divisor_of_primeLog_zeros
    hf hfc hprime hn
  have hdivLower : (n.primeCounting : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) := by
    exact_mod_cast hdivLowerInt
  have hdivUpper :
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤
        K * (1 + r) := hzeroCount r hr
  have hKmono : K * (1 + r) ≤ K * (2 + ‖c‖ + t) := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    dsimp [r]
    linarith
  linarith

end RHTower
