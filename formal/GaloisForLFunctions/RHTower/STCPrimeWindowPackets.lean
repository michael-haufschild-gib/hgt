import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Prime packets in shrinking multiplicative windows

The relative prime-gap consequence `prime_between` of the prime number theorem gives, for every
`η > 0`, a prime in `(x, (1+η)x)` for all large `x`.  Iterating it produces arbitrarily long
increasing prime chains whose consecutive ratios stay below `1+η`, and prime pairs or triples
whose ratios approach any prescribed values `exp d > 1`.  These are the only prime-distribution
inputs of the STC route cards (ordered-rank growth, vanishing normalized calibration, prime-only
flat-completion rigidity, commutator ghost).
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- An infinite increasing chain of primes above `N`, with consecutive ratios below `1+η`. -/
theorem exists_prime_chain {η : ℝ} (hη : 0 < η) (N : ℝ) :
    ∃ p : ℕ → ℕ, (∀ i, (p i).Prime) ∧ N < p 0 ∧
      ∀ i, p i < p (i + 1) ∧ (p (i + 1) : ℝ) < (1 + η) * p i := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (prime_between hη)
  obtain ⟨p₀, hp₀, hp₀X, -⟩ := hX (max X N) (le_max_left X N)
  classical
  let next : ℕ → ℕ := fun m =>
    if h : X ≤ (m : ℝ) then Classical.choose (hX m h) else m
  have next_spec : ∀ m : ℕ, X ≤ (m : ℝ) →
      (next m).Prime ∧ (m : ℝ) < next m ∧ (next m : ℝ) < (1 + η) * m := by
    intro m hm
    simp only [next, dif_pos hm]
    exact Classical.choose_spec (hX m hm)
  let p : ℕ → ℕ := fun i => next^[i] p₀
  have hsucc : ∀ i, p (i + 1) = next (p i) := fun i =>
    Function.iterate_succ_apply' next i p₀
  have hge : ∀ i, X ≤ (p i : ℝ) ∧ (p i).Prime := by
    intro i
    induction i with
    | zero => exact ⟨(le_max_left X N).trans hp₀X.le, hp₀⟩
    | succ i ih =>
      obtain ⟨hpr, hlt, -⟩ := next_spec (p i) ih.1
      rw [hsucc]
      exact ⟨ih.1.trans hlt.le, hpr⟩
  refine ⟨p, fun i => (hge i).2, (le_max_right X N).trans_lt hp₀X, fun i => ?_⟩
  obtain ⟨-, hlt, hup⟩ := next_spec (p i) (hge i).1
  rw [hsucc]
  exact ⟨by exact_mod_cast hlt, hup⟩

/-- Along a chain with consecutive ratios below `1+η`, the `i`-th term is below `(1+η)^i`
times the first. -/
theorem prime_chain_le_pow {η : ℝ} (hη : 0 < η) {p : ℕ → ℕ}
    (hstep : ∀ i, (p (i + 1) : ℝ) < (1 + η) * p i) (i : ℕ) :
    (p i : ℝ) ≤ (1 + η) ^ i * p 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc (p (i + 1) : ℝ) ≤ (1 + η) * p i := (hstep i).le
      _ ≤ (1 + η) * ((1 + η) ^ i * p 0) := by gcongr
      _ = (1 + η) ^ (i + 1) * p 0 := by ring

/-- **Prime packets.** For every `ε > 0`, length `n` and threshold `N`, there is a strictly
increasing prime sequence starting above `N` whose first `n+1` terms all lie in
`[p 0, (1+ε) p 0)`. -/
theorem exists_prime_packet {ε : ℝ} (hε : 0 < ε) (n : ℕ) (N : ℝ) :
    ∃ p : ℕ → ℕ, StrictMono p ∧ (∀ i, (p i).Prime) ∧ N < p 0 ∧
      ∀ i ≤ n, (p i : ℝ) < (1 + ε) * p 0 := by
  set η : ℝ := Real.log (1 + ε) / (n + 1) with hηdef
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hη : 0 < η := div_pos hlog (by positivity)
  obtain ⟨p, hprime, hN, hstep⟩ := exists_prime_chain hη N
  have hmono : StrictMono p := strictMono_nat_of_lt_succ fun i => (hstep i).1
  refine ⟨p, hmono, hprime, hN, fun i hi => ?_⟩
  have hp0 : (0 : ℝ) < p 0 := by exact_mod_cast (hprime 0).pos
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · nlinarith
  · have hle := prime_chain_le_pow hη (fun j => (hstep j).2) i
    have hlt : (p i : ℝ) < (1 + η) ^ i * p 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc (p (j + 1) : ℝ) < (1 + η) * p j := (hstep j).2
        _ ≤ (1 + η) * ((1 + η) ^ j * p 0) := by
          gcongr
          exact prime_chain_le_pow hη (fun k => (hstep k).2) j
        _ = (1 + η) ^ (j + 1) * p 0 := by ring
    have hpow : (1 + η) ^ i ≤ 1 + ε := by
      calc (1 + η) ^ i ≤ Real.exp η ^ i := by
            gcongr
            linarith [Real.add_one_le_exp η]
        _ = Real.exp (i * η) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((n + 1) * η) := by
            gcongr
            exact_mod_cast (show i ≤ n + 1 by omega)
        _ = 1 + ε := by
            rw [hηdef, mul_div_cancel₀ _ (by positivity : ((n : ℝ) + 1) ≠ 0),
              Real.exp_log (by linarith)]
    calc (p i : ℝ) < (1 + η) ^ i * p 0 := hlt
      _ ≤ (1 + ε) * p 0 := by gcongr

/-- Arbitrarily large pairs of distinct primes with ratio arbitrarily close to one. -/
theorem exists_prime_pair_ratio_lt {ε : ℝ} (hε : 0 < ε) (N : ℝ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧ (q : ℝ) < (1 + ε) * p := by
  obtain ⟨p, hmono, hprime, hN, hwin⟩ := exists_prime_packet hε 1 N
  exact ⟨p 0, p 1, hprime 0, hprime 1, hN, hmono (by norm_num), hwin 1 le_rfl⟩

/-- For fixed `c > 1`, every multiplicative window `(c m, (1+ε) c m)` above a threshold
contains a prime. -/
theorem exists_prime_ratio_window {c ε : ℝ} (hc : 1 ≤ c) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ m : ℝ, X ≤ m →
      ∃ q : ℕ, q.Prime ∧ c * m < q ∧ (q : ℝ) < (1 + ε) * (c * m) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (prime_between hε)
  refine ⟨max X 0, fun m hm => hX (c * m) ?_⟩
  have hm0 : 0 ≤ m := (le_max_right X 0).trans hm
  have hXm : X ≤ m := (le_max_left X 0).trans hm
  nlinarith

/-- **Cofinal prime triples with prescribed log gaps.** For `d, e > 0` there are primes
`p_k < q_k < r_k` with `p_k → ∞`, `log q_k - log p_k → d` and `log r_k - log q_k → e`. -/
theorem exists_prime_triples_logGap {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    ∃ p q r : ℕ → ℕ, (∀ k, (p k).Prime ∧ (q k).Prime ∧ (r k).Prime) ∧
      (∀ k, p k < q k ∧ q k < r k) ∧
      Tendsto (fun k => (p k : ℝ)) atTop atTop ∧
      Tendsto (fun k => Real.log (q k) - Real.log (p k)) atTop (𝓝 d) ∧
      Tendsto (fun k => Real.log (r k) - Real.log (q k)) atTop (𝓝 e) := by
  classical
  have hcd : 1 ≤ Real.exp d := Real.one_le_exp hd.le
  have hce : 1 ≤ Real.exp e := Real.one_le_exp he.le
  have hwin : ∀ k : ℕ, ∃ X : ℝ, ∀ m : ℝ, X ≤ m →
      (∃ q : ℕ, q.Prime ∧ Real.exp d * m < q ∧
        (q : ℝ) < (1 + 1 / (k + 1)) * (Real.exp d * m)) ∧
      (∃ q : ℕ, q.Prime ∧ Real.exp e * m < q ∧
        (q : ℝ) < (1 + 1 / (k + 1)) * (Real.exp e * m)) := by
    intro k
    have hk : (0 : ℝ) < 1 / (k + 1) := by positivity
    obtain ⟨X₁, h₁⟩ := exists_prime_ratio_window hcd hk
    obtain ⟨X₂, h₂⟩ := exists_prime_ratio_window hce hk
    exact ⟨max X₁ X₂, fun m hm =>
      ⟨h₁ m ((le_max_left _ _).trans hm), h₂ m ((le_max_right _ _).trans hm)⟩⟩
  choose X hX using hwin
  -- first prime above `max (X k) k`
  have hfirst : ∀ k : ℕ, ∃ p : ℕ, p.Prime ∧ max (X k) k < p := by
    intro k
    obtain ⟨p, hp, hlt⟩ := Nat.exists_infinite_primes (⌈max (X k) k⌉₊ + 1)
    refine ⟨p, hlt, ?_⟩
    have : (⌈max (X k) (k : ℝ)⌉₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp
    linarith [Nat.le_ceil (max (X k) (k : ℝ))]
  choose p hpprime hpbig using hfirst
  have hpX : ∀ k, X k ≤ (p k : ℝ) := fun k => (le_max_left _ _).trans (hpbig k).le
  have hq : ∀ k, ∃ q : ℕ, q.Prime ∧ Real.exp d * p k < q ∧
      (q : ℝ) < (1 + 1 / (k + 1)) * (Real.exp d * p k) := fun k => ((hX k) _ (hpX k)).1
  choose q hqprime hqlo hqhi using hq
  have hp0 : ∀ k, (0 : ℝ) < p k := fun k => by exact_mod_cast (hpprime k).pos
  have hqp : ∀ k, (p k : ℝ) < q k := fun k => by
    have := hqlo k; nlinarith [hp0 k, Real.one_lt_exp_iff.mpr hd]
  have hqX : ∀ k, X k ≤ (q k : ℝ) := fun k => (hpX k).trans (hqp k).le
  have hr : ∀ k, ∃ r : ℕ, r.Prime ∧ Real.exp e * q k < r ∧
      (r : ℝ) < (1 + 1 / (k + 1)) * (Real.exp e * q k) := fun k => ((hX k) _ (hqX k)).2
  choose r hrprime hrlo hrhi using hr
  have hq0 : ∀ k, (0 : ℝ) < q k := fun k => (hp0 k).trans (hqp k)
  have hrq : ∀ k, (q k : ℝ) < r k := fun k => by
    have := hrlo k; nlinarith [hq0 k, Real.one_lt_exp_iff.mpr he]
  -- ratio limits
  have hshrink : Tendsto (fun k : ℕ => Real.log (1 + 1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp h1
    simp only [Function.comp_def, add_zero, Real.log_one] at h2
    exact h2
  have hgap : ∀ (c : ℝ) (m n : ℕ → ℕ), (∀ k, (0 : ℝ) < m k) →
      (∀ k, Real.exp c * m k < n k) →
      (∀ k, (n k : ℝ) < (1 + 1 / (k + 1)) * (Real.exp c * m k)) →
      Tendsto (fun k => Real.log (n k) - Real.log (m k)) atTop (𝓝 c) := by
    intro c m n hm hlo hhi
    have hlo' : ∀ k, c ≤ Real.log (n k) - Real.log (m k) := by
      intro k
      have hpos : 0 < Real.exp c * m k := mul_pos (Real.exp_pos c) (hm k)
      have := Real.log_le_log hpos (hlo k).le
      rw [Real.log_mul (Real.exp_pos c).ne' (hm k).ne', Real.log_exp] at this
      linarith
    have hhi' : ∀ k, Real.log (n k) - Real.log (m k) ≤
        c + Real.log (1 + 1 / ((k : ℝ) + 1)) := by
      intro k
      have hpos : 0 < (n k : ℝ) := (mul_pos (Real.exp_pos c) (hm k)).trans (hlo k)
      have := Real.log_le_log hpos (hhi k).le
      rw [Real.log_mul (by positivity) (mul_pos (Real.exp_pos c) (hm k)).ne',
        Real.log_mul (Real.exp_pos c).ne' (hm k).ne', Real.log_exp] at this
      linarith
    have hup : Tendsto (fun k : ℕ => c + Real.log (1 + 1 / ((k : ℝ) + 1))) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.add hshrink
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo' hhi'
  refine ⟨p, q, r, fun k => ⟨hpprime k, hqprime k, hrprime k⟩,
    fun k => ⟨by exact_mod_cast hqp k, by exact_mod_cast hrq k⟩, ?_,
    hgap d p q hp0 hqlo hqhi, hgap e q r hq0 hrlo hrhi⟩
  refine tendsto_atTop_mono (fun k => ((le_max_right _ _).trans (hpbig k).le)) ?_
  exact tendsto_natCast_atTop_atTop

end

end RHTower
