import GaloisForLFunctions.RHTower.WeilPositivityCramerRandomPrimes

/-!
# Random log-rough prime systems are almost surely not Weil-positive

This extends the Cramér-model theorem to random models that exclude integers with small prime
factors, such as Granville's refinement of Cramér's model.

**Hypothesis.** `X_n ∈ [0,1]` are pairwise independent on the squarefree integers, and
`E X_n ≥ c / log n` for every squarefree `n ≥ 3` whose prime factors all exceed `log n`.

**Theorem** (`ae_not_weilPositiveFull_of_rough_random`).  Almost surely, no weights agreeing with
`X_n log n` on the squarefree integers are full-cone Weil-positive for the archimedean datum of `ζ`.

**Granville's model.**  Integers `n ∈ (x, 2x]` coprime to `Q = ∏_{p ≤ A} p`, with `A ≤ log x`, are
kept with probability `(Q/φ(Q))/log n ≥ 1/log n`, independently.  An integer whose prime factors
all exceed `log n` is coprime to `Q`, so the hypothesis holds with `c = 1`.

**Proof.**  The resonator is `1_{m ∣ N}` with `N = ∏_{p ∈ S} p`, where `S` is a set of
`⌊b²/(3 log b)⌋` primes in `(b², b³]`.  Such primes exist for large `b` by Chebyshev's bounds.
* `log N ≤ b²`, and every prime factor of a divisor exceeds `b²`, so every divisor is log-rough.
* The divisor law gives `2 S_N ≤ (log N + C₀) 2^{|S|}`.
* `E S_N ≥ c 2^{|S|}(Q_S - 2)` and `Var S_N ≤ (log N)² 4^{|S|} Q_S`, where
  `Q_S = ∏_{p ∈ S}(1 + p^{-1/2}/2) ≥ exp(|S| b^{-3/2}/4) ≥ b⁶`.
* Chebyshev's inequality at one large `b` and a countable union over integer `C₀` conclude.
-/

open Finset Filter MeasureTheory ProbabilityTheory

namespace RHTower
namespace RoughRandomPrimes

open PrimorialResonance CramerModel

/-! ## Resonance sums over an arbitrary modulus -/

variable {Ω : Type*}

/-- The coefficient `log n · n^{-1/2} · d(N/n)`. -/
noncomputable def coefN (N n : ℕ) : ℝ := Real.log n / Real.sqrt n * ((N / n).divisors.card : ℝ)

/-- `S_N = ∑_{n ∣ N, n ≥ 2} log n · n^{-1/2} d(N/n) X_n`. -/
noncomputable def sumN (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ N.divisors with 2 ≤ n, coefN N n * X n ω

theorem coefN_nonneg (N n : ℕ) : 0 ≤ coefN N n := by
  unfold coefN
  have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  positivity

theorem exists_sumN_le_of_weilPositiveFull (X : ℕ → Ω → ℝ) {ω : Ω} {lam : ℕ → ℝ}
    (hlam : ∀ n, Squarefree n → lam n = Real.log n * X n ω) (hW : WeilPositiveFull lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → Squarefree N →
      2 * sumN X N ω ≤ (Real.log N + C₀) * N.divisors.card := by
  obtain ⟨C₀, hC⟩ := weil_divisor_resonance_bound (weilPositive_of_weilPositiveFull hW)
  refine ⟨C₀, fun N hN hsq => ?_⟩
  have h := hC N hN
  convert h using 3
  unfold sumN
  refine sum_congr rfl fun n hn => ?_
  have hsqn : Squarefree n := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hn).1)
  rw [hlam n hsqn]
  unfold coefN
  ring

section Probability

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_sumN_ge (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1) {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : N ≠ 0)
    (hmean : ∀ n ∈ N.divisors, 3 ≤ n → c / Real.log n ≤ ∫ ω, X n ω ∂P) :
    c * (resonanceMass (1 / 2) N - 2 * N.divisors.card) ≤ ∫ ω, sumN X N ω ∂P := by
  have hint : ∫ ω, sumN X N ω ∂P =
      ∑ n ∈ N.divisors with 2 ≤ n, coefN N n * ∫ ω, X n ω ∂P := by
    unfold sumN
    rw [integral_finsetSum _ fun n _ => (integrable_of_unit (hm n) (hb n)).const_mul _]
    exact sum_congr rfl fun n _ => integral_const_mul _ _
  rw [hint]
  have hsub : N.divisors.filter (fun n => 3 ≤ n) ⊆ N.divisors.filter (fun n => 2 ≤ n) := by
    intro m hm'; simp only [mem_filter] at hm' ⊢; exact ⟨hm'.1, by omega⟩
  have hE0 : ∀ n, 0 ≤ ∫ ω, X n ω ∂P := fun n => integral_nonneg fun ω => (hb n ω).1
  calc c * (resonanceMass (1 / 2) N - 2 * N.divisors.card)
      ≤ c * ∑ n ∈ N.divisors with 3 ≤ n,
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((N / n).divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_left (resonanceMass_le_sum_three_le _ (by norm_num) hN) hc
    _ = ∑ n ∈ N.divisors with 3 ≤ n, coefN N n * (c / Real.log n) := by
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        obtain ⟨-, h3⟩ := mem_filter.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        have hs : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
          rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]; exact (one_div _).symm
        unfold coefN
        rw [hs]
        field_simp
    _ ≤ ∑ n ∈ N.divisors with 3 ≤ n, coefN N n * ∫ ω, X n ω ∂P := by
        refine sum_le_sum fun n hn => ?_
        obtain ⟨hd, h3⟩ := mem_filter.mp hn
        exact mul_le_mul_of_nonneg_left (hmean n hd h3) (coefN_nonneg N n)
    _ ≤ ∑ n ∈ N.divisors with 2 ≤ n, coefN N n * ∫ ω, X n ω ∂P :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg (coefN_nonneg N n) (hE0 n)

theorem coefN_sq_le {N n : ℕ} (hN : N ≠ 0) (hn : n ∈ N.divisors) :
    coefN N n ^ 2 ≤ Real.log N ^ 2 * N.divisors.card *
      ((n : ℝ) ^ (-(1 : ℝ)) * ((N / n).divisors.card : ℝ)) := by
  have hd := Nat.dvd_of_mem_divisors hn
  have hn1 : 1 ≤ n := Nat.pos_of_mem_divisors hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log hn0 (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd)
  have hτ := card_divisors_div_le hN hd
  have hτ0 : (0 : ℝ) ≤ ((N / n).divisors.card : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hinv : (n : ℝ) ^ (-(1 : ℝ)) = 1 / n := by rw [Real.rpow_neg_one, one_div]
  have h1 : Real.log n ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hl0 hlN 2
  have h2 : ((N / n).divisors.card : ℝ) ^ 2 ≤
      (N.divisors.card : ℝ) * ((N / n).divisors.card : ℝ) := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hτ hτ0
  have hlhs : coefN N n ^ 2 = Real.log n ^ 2 * ((N / n).divisors.card : ℝ) ^ 2 / n := by
    unfold coefN
    rw [mul_pow, div_pow, hs]
    ring
  rw [hlhs, hinv, div_le_iff₀ hn0]
  calc Real.log n ^ 2 * ((N / n).divisors.card : ℝ) ^ 2
      ≤ Real.log N ^ 2 * ((N.divisors.card : ℝ) * ((N / n).divisors.card : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.log N ^ 2 * (N.divisors.card : ℝ) * (1 / n * ((N / n).divisors.card : ℝ)) * n := by
        field_simp

theorem variance_sumN_le (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {N : ℕ}
    (hN : N ≠ 0) (hsq : Squarefree N) :
    Var[sumN X N; P] ≤ Real.log N ^ 2 * N.divisors.card * resonanceMass 1 N := by
  set D := N.divisors.filter (fun n => 2 ≤ n)
  have hfun : sumN X N = ∑ n ∈ D, fun ω => coefN N n * X n ω := by
    funext ω; unfold sumN; rw [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum (fun n _ => memLp_two_of_unit (hm n) (hb n) _)
    (fun i hi j hj hij => (hind i j hij
      (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hi).1))
      (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hj).1))
      ).comp (measurable_const_mul _) (measurable_const_mul _))]
  have hterm : ∀ n ∈ D, Var[fun ω => coefN N n * X n ω; P] ≤ coefN N n ^ 2 := fun n _ => by
    rw [variance_const_mul]
    calc coefN N n ^ 2 * Var[X n; P] ≤ coefN N n ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (variance_le_one_of_unit (hm n) (hb n)) (sq_nonneg _)
      _ = coefN N n ^ 2 := mul_one _
  refine (sum_le_sum hterm).trans ?_
  have hDsub : D ⊆ N.divisors := filter_subset _ _
  calc ∑ n ∈ D, coefN N n ^ 2
      ≤ ∑ n ∈ D, Real.log N ^ 2 * N.divisors.card *
          ((n : ℝ) ^ (-(1 : ℝ)) * ((N / n).divisors.card : ℝ)) :=
        sum_le_sum fun n hn => coefN_sq_le hN (hDsub hn)
    _ ≤ ∑ n ∈ N.divisors, Real.log N ^ 2 * N.divisors.card *
          ((n : ℝ) ^ (-(1 : ℝ)) * ((N / n).divisors.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hDsub fun n _ _ => by
          have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 : ℝ))
          positivity
    _ = Real.log N ^ 2 * N.divisors.card * resonanceMass 1 N := by
        rw [← mul_sum, resonanceMass_apply]

theorem memLp_sumN (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1) (N : ℕ) : MemLp (sumN X N) 2 P := by
  have hfun : sumN X N = ∑ n ∈ N.divisors.filter (fun n => 2 ≤ n),
      fun ω => coefN N n * X n ω := by
    funext ω; unfold sumN; rw [Finset.sum_apply]
  rw [hfun]
  exact memLp_finsetSum' _ fun n _ => memLp_two_of_unit (hm n) (hb n) _

/-- **Chebyshev step for one modulus.**  If `N ≥ 1` is squarefree with `d(N) = 2^k`,
`M_{1/2}(N) = 2^k Q`, `M_1(N) ≤ 2^k Q`, `log N ≤ y`, `y³ ≤ Q`, and `y` exceeds the thresholds,
then the Weil event at `N` has probability at most `ε`. -/
theorem measure_sumN_le_le (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ} (hc : 0 < c)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) {N k : ℕ} {Q y : ℝ} (hN : N ≠ 0) (hsq : Squarefree N)
    (hmean : ∀ n ∈ N.divisors, 3 ≤ n → c / Real.log n ≤ ∫ ω, X n ω ∂P)
    (hτ : ((N.divisors.card : ℕ) : ℝ) = 2 ^ k)
    (hM : resonanceMass (1 / 2) N = 2 ^ k * Q) (hM1 : resonanceMass 1 N ≤ 2 ^ k * Q)
    (hlog : Real.log N ≤ y) (hcube : y ^ 3 ≤ Q) (hy0 : 4 ≤ y)
    (hyA : (1 + |K| + 2 * c) / c ≤ y) (hyB : 16 * 1 ^ 2 / (c ^ 2 * ε) ≤ y) :
    P {ω | 2 * sumN X N ω ≤ (Real.log N + K) * N.divisors.card} ≤ ENNReal.ofReal ε := by
  have hq : (0 : ℝ) < 2 ^ k := by positivity
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg _
  have hQ4 : 4 ≤ Q := by
    have : (4 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy0 3
    linarith
  have hE := integral_sumN_ge X hm hb hc.le hN hmean (P := P)
  rw [hM, hτ] at hE
  have hE' : c * 2 ^ k * (Q - 2) ≤ ∫ ω, sumN X N ω ∂P := by linarith
  have hlog1 : Real.log N ≤ y * 1 := by linarith
  have hKy := weil_bound_le_mean_aux (L := 1) (logN := Real.log N) (K := K) hc (by linarith)
    hyA hcube hlog1
  have hEpos : 0 < ∫ ω, sumN X N ω ∂P := by
    have : 0 < c * 2 ^ k * (Q - 2) := by
      have : 0 < Q - 2 := by linarith
      positivity
    linarith
  have hsub : {ω | 2 * sumN X N ω ≤ (Real.log N + K) * N.divisors.card} ⊆
      {ω | (∫ ω, sumN X N ω ∂P) / 2 ≤ |sumN X N ω - ∫ ω, sumN X N ω ∂P|} := by
    intro ω h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [hτ] at h
    have h2 : 2 * sumN X N ω ≤ ∫ ω, sumN X N ω ∂P := by
      calc 2 * sumN X N ω ≤ (Real.log N + K) * 2 ^ k := h
        _ ≤ c * (Q - 2) * 2 ^ k := mul_le_mul_of_nonneg_right hKy hq.le
        _ ≤ ∫ ω, sumN X N ω ∂P := by linarith
    rw [abs_sub_comm, le_abs]
    left; linarith
  have hV := variance_sumN_le X hm hb hind hN hsq (P := P)
  rw [hτ] at hV
  have hV' : Var[sumN X N; P] ≤ Real.log N ^ 2 * 2 ^ k * (2 ^ k * Q) :=
    hV.trans (mul_le_mul_of_nonneg_left hM1 (by positivity))
  have hratio := variance_ratio_aux (L := 1) (logN := Real.log N) hc hε hq (by linarith) hV' hE'
    hQ4 hcube hyB hlogN0 hlog1
  have hcheb := meas_ge_le_variance_div_sq (memLp_sumN X hm hb N (P := P)) (half_pos hEpos)
  refine (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [div_le_iff₀ (by positivity)]
  exact hratio

end Probability

/-! ## Moduli built from prime sets -/

theorem squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hS p hp).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

theorem resonanceMass_prod_primes (a : ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    resonanceMass a (∏ p ∈ S, p) = ∏ p ∈ S, (2 + (p : ℝ) ^ (-a)) := by
  rw [(isMultiplicative_resonanceMass a).map_prod_of_prime _ hS]
  exact prod_congr rfl fun p hp => resonanceMass_prime a (hS p hp)

theorem card_divisors_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (((∏ p ∈ S, p).divisors.card : ℕ) : ℝ) = 2 ^ S.card := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_prod_of_prime S hS
  rw [ArithmeticFunction.sigma_zero_apply] at h
  rw [h, ← prod_const]
  push_cast
  refine prod_congr rfl fun q hq => ?_
  rw [ArithmeticFunction.sigma_zero_apply, (hS q hq).divisors,
    card_pair (Ne.symm (hS q hq).one_lt.ne')]
  norm_num

/-- `Q_S = ∏_{p ∈ S} (1 + p^{-1/2}/2)`. -/
noncomputable def setProduct (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2)

theorem prod_two_add_eq_set (S : Finset ℕ) (x : ℕ → ℝ) :
    ∏ p ∈ S, (2 + x p) = 2 ^ S.card * ∏ p ∈ S, (1 + x p / 2) := by
  rw [← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun _ _ => by ring

theorem resonanceMass_half_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    resonanceMass (1 / 2) (∏ p ∈ S, p) = 2 ^ S.card * setProduct S := by
  rw [resonanceMass_prod_primes _ hS, prod_two_add_eq_set]; rfl

theorem resonanceMass_one_prod_primes_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    resonanceMass 1 (∏ p ∈ S, p) ≤ 2 ^ S.card * setProduct S := by
  rw [resonanceMass_prod_primes _ hS, prod_two_add_eq_set, setProduct]
  refine mul_le_mul_of_nonneg_left (prod_le_prod (fun p _ => ?_) fun p hp => ?_) (by positivity)
  · have := Real.rpow_nonneg (Nat.cast_nonneg p) (-1 : ℝ); linarith
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    have : (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
    linarith

/-- If every prime of `S` lies in `[1, Y]`, then `Q_S ≥ exp(|S| Y^{-1/2}/4)`. -/
theorem exp_le_setProduct {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {Y : ℝ}
    (hY : ∀ p ∈ S, (p : ℝ) ≤ Y) :
    Real.exp (S.card * Y ^ (-(1 / 2 : ℝ)) / 4) ≤ setProduct S := by
  have hstep : ∀ p ∈ S, Real.exp (Y ^ (-(1 / 2 : ℝ)) / 4) ≤ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hle : Y ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hp0 (hY p hp) (by norm_num)
    have hp' : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
    have hY0 : 0 ≤ Y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [hY p hp]) _
    have h := exp_half_le_one_add (x := Y ^ (-(1 / 2 : ℝ)) / 2) (by linarith) (by linarith)
    calc Real.exp (Y ^ (-(1 / 2 : ℝ)) / 4) = Real.exp (Y ^ (-(1 / 2 : ℝ)) / 2 / 2) := by ring_nf
      _ ≤ 1 + Y ^ (-(1 / 2 : ℝ)) / 2 := h
      _ ≤ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by linarith
  calc Real.exp (S.card * Y ^ (-(1 / 2 : ℝ)) / 4)
      = ∏ _p ∈ S, Real.exp (Y ^ (-(1 / 2 : ℝ)) / 4) := by
        rw [prod_const, ← Real.exp_nat_mul]; ring_nf
    _ ≤ setProduct S := prod_le_prod (fun _ _ => (Real.exp_pos _).le) hstep

/-! ## Primes in `(b², b³]` -/

/-- The primes in `(b², b³]`. -/
noncomputable def window (b : ℕ) : Finset ℕ := (b ^ 3).primesLE.filter (fun p => b ^ 2 < p)

theorem mem_window {b p : ℕ} (hp : p ∈ window b) : p.Prime ∧ b ^ 2 < p ∧ p ≤ b ^ 3 := by
  obtain ⟨h1, h2⟩ := mem_filter.mp hp
  exact ⟨Nat.prime_of_mem_primesLE h1, h2, Nat.le_of_mem_primesLE h1⟩

theorem sum_log_window (b : ℕ) :
    ∑ p ∈ window b, Real.log p = Chebyshev.theta (b ^ 3 : ℕ) - Chebyshev.theta (b ^ 2 : ℕ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsplit := sum_filter_add_sum_filter_not ((b ^ 3).primesLE) (fun p => b ^ 2 < p)
    (fun p => Real.log p)
  have hlow : (b ^ 3).primesLE.filter (fun p => ¬ b ^ 2 < p) = (b ^ 2).primesLE := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE, not_lt]
    constructor
    · rintro ⟨⟨_, hp⟩, h⟩; exact ⟨h, hp⟩
    · rintro ⟨h, hp⟩
      refine ⟨⟨h.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero ?_) (by norm_num)), hp⟩, h⟩
      rintro rfl; simp at h; exact hp.ne_zero (by omega)
  rw [hlow] at hsplit
  unfold window
  linarith

theorem sum_log_window_le (b : ℕ) :
    ∑ p ∈ window b, Real.log p ≤ (window b).card * (3 * Real.log b) := by
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hpr, -, hp3⟩ := mem_window hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  calc Real.log p ≤ Real.log ((b : ℝ) ^ 3) :=
        Real.log_le_log hp0 (by exact_mod_cast hp3)
    _ = 3 * Real.log b := by rw [Real.log_pow]; norm_num

/-- Chebyshev's bounds give `∑_{b² < p ≤ b³} log p ≥ b²` for all large `b`. -/
theorem eventually_sum_log_window_ge :
    ∀ᶠ b : ℕ in atTop, ((b : ℝ) ^ 2) ≤ ∑ p ∈ window b, Real.log p := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log (x ^ 3 + 1) ≤ Real.log 2 / 4 * x ^ 3 :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).eventually
      (eventually_log_add_one_le (show 0 < Real.log 2 / 4 by positivity))
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ Real.log 2 / 24 * x ^ (3 / 2 : ℝ) :=
    eventually_log_le_mul_rpow (by norm_num) (by positivity)
  have hK : ∀ᶠ x : ℝ in atTop, 4 * (Real.log 4 + 1) / Real.log 2 ≤ x := eventually_ge_atTop _
  have hev := (h1.and (h2.and (hK.and (eventually_ge_atTop (1 : ℝ)))))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev] with b hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  rw [sum_log_window]
  have hθ := Chebyshev.theta_ge (b ^ 3)
  have hθ2 : Chebyshev.theta ((b ^ 2 : ℕ) : ℝ) ≤ Real.log 4 * (b ^ 2 : ℕ) :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  push_cast at hθ hθ2 ⊢
  have hx0 : (0 : ℝ) < b := by linarith
  have hsq : Real.sqrt ((b : ℝ) ^ 3) = (b : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hlog3 : Real.log ((b : ℝ) ^ 3) = 3 * Real.log b := by rw [Real.log_pow]; norm_num
  rw [hsq, hlog3] at hθ
  have hpow : (b : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (3 / 2 : ℝ) = (b : ℝ) ^ 3 := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp0 : 0 ≤ (b : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hmid : 2 * (b : ℝ) ^ (3 / 2 : ℝ) * (3 * Real.log b) ≤ Real.log 2 / 4 * (b : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 6 * (b : ℝ) ^ (3 / 2 : ℝ) by positivity)
    calc 2 * (b : ℝ) ^ (3 / 2 : ℝ) * (3 * Real.log b) = 6 * (b : ℝ) ^ (3 / 2 : ℝ) * Real.log b := by
          ring
      _ ≤ 6 * (b : ℝ) ^ (3 / 2 : ℝ) * (Real.log 2 / 24 * (b : ℝ) ^ (3 / 2 : ℝ)) := this
      _ = Real.log 2 / 4 * ((b : ℝ) ^ (3 / 2 : ℝ) * (b : ℝ) ^ (3 / 2 : ℝ)) := by ring
      _ = Real.log 2 / 4 * (b : ℝ) ^ 3 := by rw [hpow]
  have hquad : ((b : ℝ) ^ 2) * (Real.log 4 + 1) ≤ Real.log 2 / 4 * (b : ℝ) ^ 3 := by
    have h' : 4 * (Real.log 4 + 1) ≤ Real.log 2 * b := by
      rw [div_le_iff₀ hl2] at hb3; linarith
    have := mul_le_mul_of_nonneg_left h' (sq_nonneg (b : ℝ))
    nlinarith
  nlinarith

theorem eventually_card_window_ge :
    ∀ᶠ b : ℕ in atTop, (b : ℝ) ^ 2 / (3 * Real.log b) ≤ (window b).card := by
  filter_upwards [eventually_sum_log_window_ge, eventually_ge_atTop 2] with b hb hb2
  have hl : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  rw [div_le_iff₀ (by positivity)]
  have := sum_log_window_le b
  linarith

/-- The number of primes used at scale `b`. -/
noncomputable def primeCount (b : ℕ) : ℕ := ⌊(b : ℝ) ^ 2 / (3 * Real.log b)⌋₊

theorem eventually_six_log_le :
    ∀ᶠ b : ℕ in atTop, 6 * Real.log b ≤
      (primeCount b : ℝ) * ((b : ℝ) ^ 3) ^ (-(1 / 2 : ℝ)) / 4 := by
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ 1 / 144 * x ^ (1 / 2 : ℝ) :=
    eventually_log_sq_le (by norm_num) (by norm_num)
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ 1 / 6 * x ^ (2 : ℝ) :=
    eventually_log_le_mul_rpow (by norm_num) (by norm_num)
  have hev := h1.and (h2.and (eventually_ge_atTop (3 : ℝ)))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev] with b hb
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hx0 : (0 : ℝ) < b := by linarith
  have hl : 0 < Real.log b := Real.log_pos (by linarith)
  have hfl : (b : ℝ) ^ 2 / (3 * Real.log b) - 1 ≤ primeCount b := by
    have := Nat.lt_floor_add_one ((b : ℝ) ^ 2 / (3 * Real.log b))
    unfold primeCount; linarith
  have h32 : ((b : ℝ) ^ 3) ^ (1 / 2 : ℝ) = (b : ℝ) ^ (1 / 2 : ℝ) * b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show ((3 : ℕ) : ℝ) * (1 / 2) = 1 / 2 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hpow : ((b : ℝ) ^ 3) ^ (-(1 / 2 : ℝ)) = 1 / ((b : ℝ) ^ (1 / 2 : ℝ) * b) := by
    rw [Real.rpow_neg (by positivity), h32, inv_eq_one_div]
  have hs0 : 0 < (b : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hss : (b : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) = b := by
    rw [← Real.rpow_add hx0]; norm_num
  have hb2' : Real.log b ≤ 1 / 6 * (b : ℝ) ^ 2 := by
    have h := hb2
    rwa [Real.rpow_two] at h
  -- target: 24 log b · b^{3/2} ≤ b²/(3 log b) − 1
  have hmain : 24 * Real.log b * ((b : ℝ) ^ (1 / 2 : ℝ) * b) ≤
      (b : ℝ) ^ 2 / (3 * Real.log b) - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    have hA : 72 * Real.log b ^ 2 * ((b : ℝ) ^ (1 / 2 : ℝ) * b) ≤ (b : ℝ) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ 72 * ((b : ℝ) ^ (1 / 2 : ℝ) * b) by
        positivity)
      calc 72 * Real.log b ^ 2 * ((b : ℝ) ^ (1 / 2 : ℝ) * b)
          = Real.log b ^ 2 * (72 * ((b : ℝ) ^ (1 / 2 : ℝ) * b)) := by ring
        _ ≤ 1 / 144 * (b : ℝ) ^ (1 / 2 : ℝ) * (72 * ((b : ℝ) ^ (1 / 2 : ℝ) * b)) := this
        _ = ((b : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ)) * b / 2 := by ring
        _ = (b : ℝ) ^ 2 / 2 := by rw [hss]; ring
    have hexp : (24 * Real.log b * ((b : ℝ) ^ (1 / 2 : ℝ) * b) + 1) * (3 * Real.log b) =
        72 * Real.log b ^ 2 * ((b : ℝ) ^ (1 / 2 : ℝ) * b) + 3 * Real.log b := by ring
    rw [hexp]
    have h3 : 3 * Real.log b ≤ (b : ℝ) ^ 2 / 2 := by
      calc 3 * Real.log b ≤ 3 * (1 / 6 * (b : ℝ) ^ 2) := by gcongr
        _ = (b : ℝ) ^ 2 / 2 := by ring
    exact (add_le_add hA h3).trans (le_of_eq (by ring))
  have hK0 : (0 : ℝ) ≤ primeCount b := Nat.cast_nonneg _
  have hden : 0 < (b : ℝ) ^ (1 / 2 : ℝ) * b := by positivity
  have hfin := hmain.trans hfl
  rw [hpow, show (primeCount b : ℝ) * (1 / ((b : ℝ) ^ (1 / 2 : ℝ) * b)) / 4 =
      (primeCount b : ℝ) / (4 * ((b : ℝ) ^ (1 / 2 : ℝ) * b)) by field_simp,
    le_div_iff₀ (by positivity)]
  linarith

/-- A prime dividing a product of primes is one of them. -/
theorem mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ ∏ p ∈ S, p) : q ∈ S := by
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hd
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hS p hp)).mp hqp]

section Main

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **For a fixed constant `K`, the Weil resonance bound at every product of primes is a null
event.** -/
theorem measure_forall_sumN_le_eq_zero (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ} (hc : 0 < c)
    (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → (∀ q, q.Prime → q ∣ n → Real.log n < q) →
      c / Real.log n ≤ ∫ ω, X n ω ∂P) (K : ℝ) :
    P {ω | ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      2 * sumN X (∏ p ∈ S, p) ω ≤
        (Real.log (∏ p ∈ S, p : ℕ) + K) * (∏ p ∈ S, p).divisors.card} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
  have hεr : (0 : ℝ) < ε := hε
  set A : ℝ := (1 + |K| + 2 * c) / c with hAdef
  set B : ℝ := 16 * 1 ^ 2 / (c ^ 2 * ε) with hBdef
  obtain ⟨b, hcard, hsix, hbig, hb3⟩ := (eventually_card_window_ge.and
    (eventually_six_log_le.and ((eventually_ge_atTop ⌈A + B + 4⌉₊).and
      (eventually_ge_atTop 3)))).exists
  have hceil : A + B + 4 ≤ (b : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hbig)
  have hbr : (3 : ℝ) ≤ b := by exact_mod_cast hb3
  have hl : 0 < Real.log b := Real.log_pos (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hb_le_sq : (b : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  -- choose the primes
  have hKle : primeCount b ≤ (window b).card := by
    have h := Nat.floor_le_of_le (n := (window b).card) hcard
    exact h
  obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hKle
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (mem_window (hSsub hp)).1
  set N := ∏ p ∈ S, p with hNdef
  have hN : N ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hsq : Squarefree N := squarefree_prod_primes hS
  -- log N ≤ b²
  have hlogN : Real.log N ≤ (b : ℝ) ^ 2 := by
    rw [hNdef, Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (hS p hp).ne_zero)]
    calc ∑ p ∈ S, Real.log (p : ℝ) ≤ ∑ _p ∈ S, 3 * Real.log b := by
          refine sum_le_sum fun p hp => ?_
          obtain ⟨hpr, -, hp3⟩ := mem_window (hSsub hp)
          calc Real.log (p : ℝ) ≤ Real.log ((b : ℝ) ^ 3) :=
                Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast hp3)
            _ = 3 * Real.log b := by rw [Real.log_pow]; norm_num
      _ = (primeCount b : ℝ) * (3 * Real.log b) := by rw [sum_const, hScard, nsmul_eq_mul]
      _ ≤ (b : ℝ) ^ 2 := by
          have := Nat.floor_le (show 0 ≤ (b : ℝ) ^ 2 / (3 * Real.log b) by positivity)
          unfold primeCount
          rw [le_div_iff₀ (by positivity)] at this
          linarith
  -- the product is at least b⁶
  have hQ : ((b : ℝ) ^ 2) ^ 3 ≤ setProduct S := by
    have hY : ∀ p ∈ S, (p : ℝ) ≤ (b : ℝ) ^ 3 := fun p hp => by
      exact_mod_cast (mem_window (hSsub hp)).2.2
    refine le_trans ?_ (exp_le_setProduct hS hY)
    rw [hScard]
    calc ((b : ℝ) ^ 2) ^ 3 = Real.exp (6 * Real.log b) := by
          rw [show (6 : ℝ) * Real.log b = Real.log ((b : ℝ) ^ 6) by rw [Real.log_pow]; norm_num,
            Real.exp_log (by positivity)]; ring
      _ ≤ Real.exp ((primeCount b : ℝ) * ((b : ℝ) ^ 3) ^ (-(1 / 2 : ℝ)) / 4) :=
          Real.exp_le_exp.mpr hsix
  -- the mean hypothesis on the divisors of N
  have hmeanN : ∀ n ∈ N.divisors, 3 ≤ n → c / Real.log n ≤ ∫ ω, X n ω ∂P := by
    intro n hn h3
    have hdn := Nat.dvd_of_mem_divisors hn
    refine hmean n h3 (hsq.squarefree_of_dvd hdn) fun q hq hqn => ?_
    have hqS := mem_of_prime_dvd_prod hS hq (hqn.trans hdn)
    have hq2 : (b : ℝ) ^ 2 < q := by exact_mod_cast (mem_window (hSsub hqS)).2.1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogn : Real.log n ≤ Real.log N :=
      Real.log_le_log hn0 (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdn)
    linarith
  have hsubset : {ω | ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      2 * sumN X (∏ p ∈ S, p) ω ≤
        (Real.log (∏ p ∈ S, p : ℕ) + K) * (∏ p ∈ S, p).divisors.card} ⊆
      {ω | 2 * sumN X N ω ≤ (Real.log N + K) * N.divisors.card} := fun ω hω => hω S hS
  refine (measure_mono hsubset).trans ?_
  have t1 : (4 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  have t2 : (1 + |K| + 2 * c) / c ≤ (b : ℝ) ^ 2 := by rw [← hAdef]; linarith
  have t3 : 16 * 1 ^ 2 / (c ^ 2 * (ε : ℝ)) ≤ (b : ℝ) ^ 2 := by rw [← hBdef]; linarith
  exact measure_sumN_le_le X hm hb hind hc K hεr hN hsq hmeanN
    (card_divisors_prod_primes hS) (resonanceMass_half_prod_primes hS)
    (resonanceMass_one_prod_primes_le hS) hlogN hQ t1 t2 t3

/-- **Random log-rough prime systems are almost surely not Weil-positive.**  Let `X_n ∈ [0,1]` be
pairwise independent on the squarefree integers with `E X_n ≥ c / log n` for every squarefree
`n ≥ 3` whose prime factors all exceed `log n`.  Then almost surely no weights agreeing with
`X_n log n` on the squarefree integers are full-cone Weil-positive.  This covers Granville's
refinement of Cramér's model: integers coprime to the primes `≤ A(n)`, `A(n) ≤ log n`, are kept
with probability `(Q/φ(Q))/log n ≥ 1/log n`. -/
theorem ae_not_weilPositiveFull_of_rough_random (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, 0 ≤ X n ω ∧ X n ω ≤ 1)
    (hind : ∀ i j, i ≠ j → Squarefree i → Squarefree j → X i ⟂ᵢ[P] X j) {c : ℝ} (hc : 0 < c)
    (hmean : ∀ n : ℕ, 3 ≤ n → Squarefree n → (∀ q, q.Prime → q ∣ n → Real.log n < q) →
      c / Real.log n ≤ ∫ ω, X n ω ∂P)
    (lam : Ω → ℕ → ℝ) (hlam : ∀ ω n, Squarefree n → lam ω n = Real.log n * X n ω) :
    ∀ᵐ ω ∂P, ¬ WeilPositiveFull (lam ω) := by
  rw [ae_iff]
  simp only [not_not]
  have hsub : {ω | WeilPositiveFull (lam ω)} ⊆
      ⋃ K : ℕ, {ω | ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        2 * sumN X (∏ p ∈ S, p) ω ≤
          (Real.log (∏ p ∈ S, p : ℕ) + K) * (∏ p ∈ S, p).divisors.card} := by
    intro ω hω
    obtain ⟨C₀, hC⟩ := exists_sumN_le_of_weilPositiveFull X (hlam ω) hω
    obtain ⟨K, hK⟩ := exists_nat_ge C₀
    refine Set.mem_iUnion.mpr ⟨K, fun S hS => ?_⟩
    have hN1 : 1 ≤ ∏ p ∈ S, p :=
      Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero)
    exact (hC _ hN1 (squarefree_prod_primes hS)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  exact measure_mono_null hsub (measure_iUnion_null fun K =>
    measure_forall_sumN_le_eq_zero X hm hb hind hc hmean K)

end Main

end RoughRandomPrimes


end RHTower
