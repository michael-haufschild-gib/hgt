import Zeta23.ThmE.PPChi
import Zeta23.Chebyshev

/-!
# Coprime Chebyshev–Mertens sums, uniformly in the modulus

Removing the prime powers that share a factor with `q` from `Σ_{n ≤ x} Λ(n)²/n` costs
`Σ_{p | q} Σ_{k ≥ 1} log²p/p^k ≤ 2 Σ_{p | q} log²p/p`, and

`Σ_{p | q} log²p/p ≤ K log²(log q + 8)`                       (`sum_primeFactors_log_sq_div_le`)

with an absolute `K`: the primes `p ≤ Y = log q + 8` contribute at most `Σ_{n ≤ Y} Λ(n)²/n ≪ log²Y`, and the
at most `log q/log 2` primes `p > Y` contribute at most `log²Y/Y` each, because `log²x/x` decreases on
`[e², ∞)`.  Consequently the weighted coprime sum of Alpöge–Furman's prime-side diagonal satisfies

`(L − 2w)³/6 − (B + K' log²(log q + 8)) L² ≤ Σ_{n ≤ X, (n,q) = 1} Λ(n)²/n · g(log n) ≤ L³/6 + (B + K' log²(log q + 8)) L²`

(`sumA2gCoprime_upper_uniform`, `sumA2gCoprime_lower_uniform`): the error is `o(L³)` for every modulus
`q ≤ T^A`, unlike the `(1 + log q)²` loss of the crude bound.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- `log²x/x` decreases on `[e², ∞)`. -/
theorem log_sq_div_antitoneOn : AntitoneOn (fun x : ℝ => Real.log x ^ 2 / x) (Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 2) hy
  have h := Real.log_div_sqrt_antitoneOn hx hy hxy
  have hy1 : 1 ≤ y := le_trans (by linarith [Real.add_one_le_exp 2]) (show Real.exp 2 ≤ y from hy)
  have hpos : 0 ≤ Real.log y / Real.sqrt y := div_nonneg (Real.log_nonneg hy1) (Real.sqrt_nonneg _)
  have e : ∀ z : ℝ, 0 < z → Real.log z ^ 2 / z = (Real.log z / Real.sqrt z) ^ 2 := by
    intro z hz; rw [div_pow, Real.sq_sqrt hz.le]
  simp only
  rw [e y hy0, e x hx0]
  exact pow_le_pow_left₀ hpos h 2

/-- `ω(q) log 2 ≤ log q`. -/
theorem card_primeFactors_mul_log_two_le (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have h3 : (2:ℝ) ^ q.primeFactors.card ≤ q := by exact_mod_cast h1.trans h2
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

theorem two_le_exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith [Real.exp_pos 1]

/-- **`Σ_{p | q} log²p/p ≤ K log²(log q + 8)`.** -/
theorem sum_primeFactors_log_sq_div_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q →
      ∑ p ∈ q.primeFactors, Real.log p ^ 2 / p ≤ K * Real.log (Real.log q + 8) ^ 2 := by
  classical
  obtain ⟨Ca, hCa⟩ := Cheb.chebyshevMertens.cheb2a
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨1 / 2 + 1 / Real.log 2 + |Ca|, by positivity, fun q hq => ?_⟩
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  set Y : ℝ := Real.log q + 8 with hY
  have hY8 : 8 ≤ Y := by rw [hY]; linarith
  have hYe : Real.exp 2 ≤ Y := two_le_exp_two_le_eight.trans hY8
  have hlogY : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hterm0 : ∀ p ∈ q.primeFactors, 0 ≤ Real.log p ^ 2 / p := fun p _ => by positivity
  rw [← Finset.sum_filter_add_sum_filter_not q.primeFactors (fun p : ℕ => (p : ℝ) ≤ Y)]
  -- small primes
  have hsmall : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), Real.log p ^ 2 / p
      ≤ Real.log Y ^ 2 / 2 + |Ca| * Real.log Y := by
    have hsub : q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y) ⊆ Finset.Ioc 0 ⌊Y⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      rw [Finset.mem_Ioc]
      exact ⟨hpp.pos, Nat.le_floor hp.2⟩
    have heq : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), Real.log p ^ 2 / p
        = ∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), (Λ p : ℝ) ^ 2 / p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp.1)]
    rw [heq]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => a2_nonneg n).trans ?_
    have h := hCa Y (by linarith)
    have := (abs_le.mp h).2
    have hCa' : Ca * Real.log Y ≤ |Ca| * Real.log Y :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  -- large primes
  have hlarge : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), Real.log p ^ 2 / p
      ≤ Real.log Y ^ 2 / Real.log 2 := by
    have hbd : ∀ p ∈ q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y),
        Real.log p ^ 2 / p ≤ Real.log Y ^ 2 / Y := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpY : Y ≤ (p : ℝ) := (not_le.mp hp.2).le
      exact log_sq_div_antitoneOn (show Real.exp 2 ≤ Y from hYe)
        (show Real.exp 2 ≤ (p : ℝ) from hYe.trans hpY) hpY
    refine (Finset.sum_le_card_nsmul _ _ _ hbd).trans ?_
    rw [nsmul_eq_mul]
    have hcard : ((q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y)).card : ℝ)
        ≤ Real.log q / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      refine le_trans ?_ (card_primeFactors_mul_log_two_le q hq)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hlog2.le
    have hY0 : 0 < Y := by linarith
    calc ((q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y)).card : ℝ) * (Real.log Y ^ 2 / Y)
        ≤ Real.log q / Real.log 2 * (Real.log Y ^ 2 / Y) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ Y / Real.log 2 * (Real.log Y ^ 2 / Y) := by
          gcongr; rw [hY]; linarith
      _ = Real.log Y ^ 2 / Real.log 2 := by field_simp
  have hfin : Real.log Y ^ 2 / 2 + |Ca| * Real.log Y + Real.log Y ^ 2 / Real.log 2
      ≤ (1 / 2 + 1 / Real.log 2 + |Ca|) * Real.log Y ^ 2 := by
    have h1 : |Ca| * Real.log Y ≤ |Ca| * Real.log Y ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have e : (1 / 2 + 1 / Real.log 2 + |Ca|) * Real.log Y ^ 2
        = Real.log Y ^ 2 / 2 + Real.log Y ^ 2 / Real.log 2 + |Ca| * Real.log Y ^ 2 := by ring
    linarith
  linarith

/-- **The removed prime powers.**  For a weight `0 ≤ w ≤ W` on the window,
`Σ_{n ≤ x, (n,q) > 1} Λ(n)²/n · w(n) ≤ 2 W Σ_{p | q} log²p/p`. -/
theorem removed_le_sharp (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (w : ℕ → ℝ) (W : ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ W) (hW : 0 ≤ W) :
    ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℝ) ^ 2 / n * w n
      ≤ 2 * W * ∑ p ∈ q.primeFactors, Real.log p ^ 2 / p := by
  classical
  have hq0 : 0 < q := hq
  set f : ℕ → ℝ := fun n => (Λ n : ℝ) ^ 2 / n * w n with hf
  have hf0 : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ f n := by
    intro n hn
    have := (hw n hn).1
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    positivity
  set U : ℕ → Finset ℕ :=
    fun p => (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ∃ k, 0 < k ∧ n = p ^ k) with hU
  have hsub : ((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q)).filter (fun n => f n ≠ 0)
      ⊆ q.primeFactors.biUnion U := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnT, hne⟩ := hn
    rw [Finset.mem_filter] at hnT
    obtain ⟨hnIoc, hncop⟩ := hnT
    have hΛ : Λ n ≠ 0 := by
      intro h0
      apply hne
      rw [hf]
      simp [h0]
    obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ
    have hp' : p.Prime := hp.nat_prime
    have hpq : p ∣ q := by
      by_contra hnd
      exact hncop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp').2 hnd))
    rw [Finset.mem_biUnion]
    exact ⟨p, Nat.mem_primeFactors.2 ⟨hp', hpq, hq0.ne'⟩,
      by rw [hU]; exact Finset.mem_filter.2 ⟨hnIoc, ⟨k, hk, rfl⟩⟩⟩
  have hdisj : ∀ p₁ ∈ q.primeFactors, ∀ p₂ ∈ q.primeFactors, p₁ ≠ p₂ →
      Disjoint (U p₁) (U p₂) := by
    intro p₁ h₁ p₂ h₂ hne
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    rw [hU, Finset.mem_filter] at hn₁ hn₂
    obtain ⟨-, k₁, hk₁, rfl⟩ := hn₁
    obtain ⟨-, k₂, hk₂, he⟩ := hn₂
    have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors h₁
    have hp₂ : p₂.Prime := Nat.prime_of_mem_primeFactors h₂
    apply hne
    have hdvd : p₂ ∣ p₁ ^ k₁ := he ▸ dvd_pow_self p₂ hk₂.ne'
    exact ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).1 (Nat.Prime.dvd_of_dvd_pow hp₂ hdvd)).symm
  have hfiber : ∀ p ∈ q.primeFactors, ∑ n ∈ U p, f n ≤ 2 * W * (Real.log p ^ 2 / p) := by
    intro p hpmem
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hp2 : 2 ≤ p := hp'.two_le
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp'.pos
    set Kp := (Finset.Icc 1 ⌊x⌋₊).filter (fun k => p ^ k ∈ Finset.Ioc 0 ⌊x⌋₊) with hKp
    have hUeq : U p = Kp.image (fun k => p ^ k) := by
      ext n
      rw [hU, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hnIoc, k, hk, rfl⟩
        refine ⟨k, ?_, rfl⟩
        rw [hKp, Finset.mem_filter, Finset.mem_Icc]
        have hkx : k ≤ ⌊x⌋₊ := by
          have h1 : k < 2 ^ k := Nat.lt_two_pow_self
          have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
          have h3 : p ^ k ≤ ⌊x⌋₊ := (Finset.mem_Ioc.1 hnIoc).2
          omega
        exact ⟨⟨hk, hkx⟩, hnIoc⟩
      · rintro ⟨k, hk, rfl⟩
        rw [hKp, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨hk.2, k, hk.1.1, rfl⟩
    have hinj : Set.InjOn (fun k => p ^ k) ↑Kp :=
      fun a _ b _ hab => Nat.pow_right_injective hp2 hab
    rw [hUeq, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    have hterm : ∀ k ∈ Kp, f (p ^ k) ≤ 2 * W * (Real.log p ^ 2 / p) * ((1:ℝ)/2) ^ k := by
      intro k hkmem
      rw [hKp, Finset.mem_filter, Finset.mem_Icc] at hkmem
      obtain ⟨⟨hk1, -⟩, hIoc⟩ := hkmem
      have hΛpk : (Λ (p ^ k) : ℝ) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hp']
      have hwk := hw (p ^ k) hIoc
      -- p^k ≥ p · 2^(k-1)
      have hpk : (p : ℝ) * 2 ^ k ≤ 2 * (p : ℝ) ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h2j : (2:ℝ) ^ j ≤ (p : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp2) j
        rw [pow_succ, pow_succ]
        nlinarith [pow_pos hp0 j]
      have hpk0 : (0:ℝ) < (p:ℝ) ^ k := by positivity
      rw [hf]
      have e1 : ((Λ (p ^ k) : ℝ)) ^ 2 = Real.log p ^ 2 := by rw [hΛpk]
      push_cast
      rw [e1]
      have hl0 : 0 ≤ Real.log p ^ 2 := sq_nonneg _
      calc Real.log p ^ 2 / ((p:ℝ) ^ k) * w (p ^ k)
          ≤ Real.log p ^ 2 / ((p:ℝ) ^ k) * W :=
            mul_le_mul_of_nonneg_left hwk.2 (by positivity)
        _ ≤ Real.log p ^ 2 * (2 / ((p:ℝ) * 2 ^ k)) * W := by
            apply mul_le_mul_of_nonneg_right _ hW
            rw [div_eq_mul_one_div]
            apply mul_le_mul_of_nonneg_left _ hl0
            rw [div_le_div_iff₀ hpk0 (by positivity)]
            linarith
        _ = 2 * W * (Real.log p ^ 2 / p) * ((1:ℝ)/2) ^ k := by
            rw [div_pow, one_pow]; field_simp
    have hgeom : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((1:ℝ)/2) ^ k ≤ 1 := by
      have h : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, ((1:ℝ)/2) ^ k ≤ 1 - ((1:ℝ)/2) ^ N := by
        intro N
        induction N with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
          have h2 : ((1:ℝ)/2) ^ (n+1) = ((1:ℝ)/2) ^ n * (1/2) := by ring
          rw [h2]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]
      have := h ⌊x⌋₊
      have : (0:ℝ) ≤ ((1:ℝ)/2) ^ ⌊x⌋₊ := by positivity
      linarith
    have hc0 : 0 ≤ 2 * W * (Real.log p ^ 2 / p) := by positivity
    calc ∑ k ∈ Kp, f (p ^ k) ≤ ∑ k ∈ Kp, 2 * W * (Real.log p ^ 2 / p) * ((1:ℝ)/2) ^ k :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, 2 * W * (Real.log p ^ 2 / p) * ((1:ℝ)/2) ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (by rw [hKp]; exact Finset.filter_subset _ _)
          intro k _ _
          positivity
      _ = 2 * W * (Real.log p ^ 2 / p) * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((1:ℝ)/2) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ 2 * W * (Real.log p ^ 2 / p) * 1 := mul_le_mul_of_nonneg_left hgeom hc0
      _ = 2 * W * (Real.log p ^ 2 / p) := mul_one _
  calc ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), f n
      = ∑ n ∈ ((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q)).filter
          (fun n => f n ≠ 0), f n := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ q.primeFactors.biUnion U, f n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        apply hf0
        rw [Finset.mem_biUnion] at hn
        obtain ⟨p, -, hp⟩ := hn
        rw [hU] at hp
        exact (Finset.mem_filter.1 hp).1
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ U p, f n := Finset.sum_biUnion hdisj
    _ ≤ ∑ p ∈ q.primeFactors, 2 * W * (Real.log p ^ 2 / p) := Finset.sum_le_sum hfiber
    _ = 2 * W * ∑ p ∈ q.primeFactors, Real.log p ^ 2 / p := by rw [Finset.mul_sum]

/-- **The coprime second Chebyshev–Mertens sum, uniformly in the modulus.** -/
theorem coprime_cheb2b_uniform :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
        ≤ (B + K * Real.log (Real.log q + 8) ^ 2) * Real.log x ^ 2 := by
  classical
  obtain ⟨Cb, hCb⟩ := Cheb.chebyshevMertens.cheb2b
  obtain ⟨K₀, hK₀, hK₀b⟩ := sum_primeFactors_log_sq_div_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨|Cb|, 2 * K₀ / Real.log 2, abs_nonneg _, by positivity, fun q hq x hx => ?_⟩
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlx0 : 0 ≤ Real.log x := by linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊)
    (fun n => Nat.Coprime n q) (fun n => (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n))
  have hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ Real.log x - Real.log n ∧ Real.log x - Real.log n ≤ Real.log x := by
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
    have hnx : (n:ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le (by linarith))
    exact ⟨by linarith [Real.log_le_log (by linarith) hnx], by linarith [Real.log_nonneg hn1]⟩
  have hrem := removed_le_sharp q hq x (fun n => Real.log x - Real.log n) (Real.log x) hw hlx0
  have hrem0 : 0 ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
      (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) :=
    Finset.sum_nonneg fun n hn => mul_nonneg (a2_nonneg n) (hw n (Finset.mem_filter.1 hn).1).1
  have hS := hK₀b q hq
  have hall := hCb x hx
  set R := ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
      (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) with hR
  have hRle : R ≤ 2 * K₀ / Real.log 2 * Real.log (Real.log q + 8) ^ 2 * Real.log x ^ 2 := by
    refine hrem.trans ?_
    have h1 : 2 * Real.log x * ∑ p ∈ q.primeFactors, Real.log p ^ 2 / p
        ≤ 2 * Real.log x * (K₀ * Real.log (Real.log q + 8) ^ 2) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h2 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; nlinarith
    have h3 : 0 ≤ K₀ * Real.log (Real.log q + 8) ^ 2 := by positivity
    calc 2 * Real.log x * ∑ p ∈ q.primeFactors, Real.log p ^ 2 / p
        ≤ 2 * Real.log x * (K₀ * Real.log (Real.log q + 8) ^ 2) := h1
      _ ≤ 2 * (Real.log x ^ 2 / Real.log 2) * (K₀ * Real.log (Real.log q + 8) ^ 2) := by gcongr
      _ = 2 * K₀ / Real.log 2 * Real.log (Real.log q + 8) ^ 2 * Real.log x ^ 2 := by ring
  have hCbx : Cb * Real.log x ^ 2 ≤ |Cb| * Real.log x ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  rw [abs_le] at hall ⊢
  constructor <;> nlinarith [hall.1, hall.2]

section Sandwich

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- **Upper half of the coprime sandwich, uniformly in the modulus.** -/
theorem sumA2gCoprime_upper_uniform :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ (p : Setting) (F : LocalFun),
      LocalHypsCore cϱ p F →
        sumA2gCoprime q p.X F.g ≤ p.L ^ 3 / 6 + (B + K * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2 := by
  obtain ⟨B, K, hB, hK, hC⟩ := coprime_cheb2b_uniform
  refine ⟨B, K, hB, hK, fun q hq p F hF => ?_⟩
  have hX1 : (1:ℝ) ≤ p.X := by linarith [hF.two_le_X]
  have h1 : sumA2gCoprime q p.X F.g
      ≤ ∑ n ∈ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (p.L - Real.log n) := by
    unfold sumA2gCoprime
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n ∈ primeRange p.X := (Finset.mem_filter.mp hn).1
    refine mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
    calc F.g (Real.log n) ≤ F.Aphi (Real.log n) := hF.g_le_Aphi _
      _ ≤ max (p.L - |Real.log n|) 0 := hF.Aphi_le _
      _ = p.L - Real.log n := by
          rw [abs_of_nonneg (log_nonneg_of_mem_primeRange hn'), max_eq_left]
          have := log_le_of_mem_primeRange hX1 hn'
          rw [p.log_X] at this; linarith
  have h2 := hC q hq p.X hF.two_le_X
  rw [p.log_X] at h2
  have h3 := (abs_le.mp h2).2
  linarith

/-- **Lower half of the coprime sandwich, uniformly in the modulus.** -/
theorem sumA2gCoprime_lower_uniform :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ (p : Setting) (F : LocalFun),
      LocalHyps cϱ p F →
        (p.L - 2 * p.w) ^ 3 / 6 - (B + K * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2
          ≤ sumA2gCoprime q p.X F.g := by
  obtain ⟨B, K, hB, hK, hC⟩ := coprime_cheb2b_uniform
  refine ⟨B, K, hB, hK, fun q hq p F hF => ?_⟩
  set L' := p.L - 2 * p.w with hL'
  set x' := Real.exp L' with hx'
  have hL'pos : 6 ≤ L' := by have := hF.w_le; have := hF.eight_le_L; rw [hL']; linarith
  have hL'le : L' ≤ p.L := by rw [hL']; linarith [hF.one_le_w]
  have hx'2 : 2 ≤ x' := by linarith [Real.add_one_le_exp L']
  have hx'X : x' ≤ p.X := Real.exp_le_exp.mpr hL'le
  have hlogx' : Real.log x' = L' := Real.log_exp _
  have hsub : (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q)
      ⊆ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q) :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hx'X))
  have h1 : ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
      (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n) ≤ sumA2gCoprime q p.X F.g := by
    unfold sumA2gCoprime
    calc ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n)
        ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
          have hn' : n ∈ primeRange x' := (Finset.mem_filter.mp hn).1
          calc Real.log x' - Real.log n ≤ max (p.L - 2 * p.w - |Real.log n|) 0 := by
                rw [hlogx', abs_of_nonneg (log_nonneg_of_mem_primeRange hn'), hL']
                exact le_max_left _ _
            _ ≤ F.g (Real.log n) := hF.g_lower _
      _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n _ _
          have : 0 ≤ F.g (Real.log n) := le_trans (le_max_right _ _) (hF.g_lower _)
          exact mul_nonneg (a2_nonneg n) this
  have h2 := hC q hq x' hx'2
  rw [hlogx'] at h2
  have h3 := (abs_le.mp h2).1
  have hBK : 0 ≤ B + K * Real.log (Real.log q + 8) ^ 2 := by positivity
  have hCmax : (B + K * Real.log (Real.log q + 8) ^ 2) * L' ^ 2
      ≤ (B + K * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hL'le 2) hBK
  rw [hlogx'] at h1
  linarith

end Sandwich

end RHTower
