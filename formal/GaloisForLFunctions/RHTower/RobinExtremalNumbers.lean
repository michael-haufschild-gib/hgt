import GaloisForLFunctions.RHTower.RobinInequalityKFree

/-!
# Extremal numbers for Robin's inequality

For `ε > 0` and a prime `p` put `Q_p(ε) = 1 + (1 - 1/p)/(p^ε - 1)` and let `a_p(ε)` be the largest
`k` with `p^k ≤ Q_p(ε)`.  The local weight `w_p(a) = log((1 - p^{-(a+1)})/(1 - 1/p)) - ε a log p`
increases from `a` to `a + 1` exactly when `p^{a+1} ≤ Q_p(ε)`, so `a_p(ε)` maximizes it.  Hence the
extremal number `N = ∏_{p ≤ B} p^{a_p(ε)}` (with `a_p(ε) = 0` beyond `B`) maximizes
`σ(m)/m^{1+ε}`:
`log(σ(n)/n) - ε log n ≤ log(σ(N)/N) - ε log N` for every `n ≥ 1`.
-/

open Filter Topology
open ArithmeticFunction (sigma isMultiplicative_sigma sigma_one_apply_prime_pow)

namespace RHTower

noncomputable section

/-- The threshold `Q_p(ε) = 1 + (1 - 1/p)/(p^ε - 1)`. -/
def robinThreshold (ε : ℝ) (p : ℕ) : ℝ := 1 + (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1)

/-- The extremal exponent `a_p(ε)`: the largest `k` with `p^k ≤ Q_p(ε)`. -/
def robinExponent (ε : ℝ) (p : ℕ) : ℕ := Nat.log p ⌊robinThreshold ε p⌋₊

/-- The local factor `σ(p^a)/p^a = (1 - p^{-(a+1)})/(1 - 1/p)`. -/
def robinLocal (p a : ℕ) : ℝ := (1 - (1 / (p : ℝ)) ^ (a + 1)) / (1 - 1 / (p : ℝ))

/-- The local weight `w_p(a) = log(σ(p^a)/p^a) - ε a log p`. -/
def robinWeight (ε : ℝ) (p a : ℕ) : ℝ := Real.log (robinLocal p a) - ε * a * Real.log p

theorem robinLocal_pos {p : ℕ} (hp : p.Prime) (a : ℕ) : 0 < robinLocal p a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hq0 : 0 < 1 / (p : ℝ) := by positivity
  have h1 : (1 / (p : ℝ)) ^ (a + 1) < 1 := pow_lt_one₀ hq0.le hq (Nat.succ_ne_zero a)
  unfold robinLocal
  exact div_pos (by linarith) (by linarith)

theorem robinWeight_zero (ε : ℝ) {p : ℕ} (hp : p.Prime) : robinWeight ε p 0 = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h : 1 - 1 / (p : ℝ) ≠ 0 := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  rw [robinWeight, robinLocal, zero_add, pow_one, div_self h, Real.log_one]
  simp

theorem one_le_robinThreshold {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    1 ≤ robinThreshold ε p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpe : 1 < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have : 0 ≤ (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1) := by
    refine div_nonneg ?_ (by linarith)
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  unfold robinThreshold; linarith

/-- `k ≤ a_p(ε) ⟺ p^k ≤ Q_p(ε)`. -/
theorem le_robinExponent_iff {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    k ≤ robinExponent ε p ↔ ((p : ℝ) ^ k ≤ robinThreshold ε p) := by
  have hQ := one_le_robinThreshold hε hp
  have hfl : ⌊robinThreshold ε p⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊robinThreshold ε p⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
    omega
  rw [robinExponent, Nat.le_log_iff_pow_le hp.one_lt hfl, Nat.le_floor_iff (by linarith)]
  push_cast
  rfl

/-- **The step criterion.**  `w_p(a + 1) ≥ w_p(a) ⟺ p^{a+1} ≤ Q_p(ε)`. -/
theorem robinWeight_le_succ_iff {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    robinWeight ε p a ≤ robinWeight ε p (a + 1) ↔ (p : ℝ) ^ (a + 1) ≤ robinThreshold ε p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpe : 1 < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hpe' : (p : ℝ) ^ ε - 1 ≠ 0 := by linarith
  set t := (1 / (p : ℝ)) ^ (a + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := pow_lt_one₀ (by positivity) (by rw [div_lt_one hp0]; exact hp1)
    (Nat.succ_ne_zero a)
  have hloc : robinLocal p (a + 1) / robinLocal p a = (1 - t / p) / (1 - t) := by
    unfold robinLocal
    rw [show a + 1 + 1 = (a + 1) + 1 by ring, pow_succ, ← ht]
    have h1t : 1 - t ≠ 0 := by linarith
    field_simp
  have hlocpos := robinLocal_pos hp a
  have hlocpos' := robinLocal_pos hp (a + 1)
  have hdiff : robinWeight ε p (a + 1) - robinWeight ε p a
      = Real.log ((1 - t / p) / (1 - t)) - Real.log ((p : ℝ) ^ ε) := by
    unfold robinWeight
    rw [← hloc, Real.log_div hlocpos'.ne' hlocpos.ne', Real.log_rpow hp0]
    push_cast; ring
  have hr0 : 0 < (1 - t / p) / (1 - t) := by
    have : t / p < 1 := by rw [div_lt_one hp0]; linarith
    exact div_pos (by linarith) (by linarith)
  have hpow : (p : ℝ) ^ (a + 1) = 1 / t := by rw [ht, one_div_pow, one_div_one_div]
  have hQ : robinThreshold ε p = ((p : ℝ) ^ ε - 1 / p) / ((p : ℝ) ^ ε - 1) := by
    unfold robinThreshold
    field_simp
    ring
  have h1 : robinWeight ε p a ≤ robinWeight ε p (a + 1)
      ↔ (p : ℝ) ^ ε ≤ (1 - t / p) / (1 - t) := by
    rw [← sub_nonneg, hdiff, sub_nonneg, Real.log_le_log_iff (by positivity) hr0]
  have h2 : (p : ℝ) ^ ε ≤ (1 - t / p) / (1 - t) ↔ (p : ℝ) ^ ε - 1 ≤ t * ((p : ℝ) ^ ε - 1 / p) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (p : ℝ) ^ ε * (1 - t) - (1 - t / p)
        = ((p : ℝ) ^ ε - 1) - t * ((p : ℝ) ^ ε - 1 / p) := by ring
    constructor <;> intro h <;> linarith
  have h3 : (p : ℝ) ^ ε - 1 ≤ t * ((p : ℝ) ^ ε - 1 / p)
      ↔ 1 / t ≤ ((p : ℝ) ^ ε - 1 / p) / ((p : ℝ) ^ ε - 1) := by
    rw [div_le_div_iff₀ ht0 (by linarith)]
    constructor <;> intro h <;> linarith
  rw [h1, h2, h3, hpow, hQ]

/-- **`a_p(ε)` maximizes the local weight.** -/
theorem robinWeight_le_robinExponent {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    robinWeight ε p a ≤ robinWeight ε p (robinExponent ε p) := by
  set m := robinExponent ε p with hm
  have hup : ∀ d k : ℕ, k + d = m → robinWeight ε p k ≤ robinWeight ε p m := by
    intro d
    induction d with
    | zero => intro k hk; rw [add_zero] at hk; rw [hk]
    | succ d ih =>
      intro k hk
      have h1 := ih (k + 1) (by omega)
      have h2 : robinWeight ε p k ≤ robinWeight ε p (k + 1) :=
        (robinWeight_le_succ_iff hε hp k).mpr ((le_robinExponent_iff hε hp (k + 1)).mp (by omega))
      linarith
  have hdown : ∀ d : ℕ, robinWeight ε p (m + d) ≤ robinWeight ε p m := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : ¬ robinWeight ε p (m + d) ≤ robinWeight ε p (m + d + 1) := by
        rw [robinWeight_le_succ_iff hε hp, ← le_robinExponent_iff hε hp]
        omega
      push Not at h2
      rw [← add_assoc]
      linarith
  rcases le_or_gt a m with h | h
  · exact hup (m - a) a (by omega)
  · have := hdown (a - m)
    rwa [show m + (a - m) = a by omega] at this

theorem robinWeight_robinExponent_nonneg {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 ≤ robinWeight ε p (robinExponent ε p) := by
  have := robinWeight_le_robinExponent hε hp 0
  rwa [robinWeight_zero ε hp] at this

/-- The extremal number `N = ∏_{p ≤ B} p^{a_p(ε)}`. -/
def robinExtremal (ε : ℝ) (B : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 0 B).filter Nat.Prime, p ^ robinExponent ε p

theorem robinExtremal_pos (ε : ℝ) (B : ℕ) : 0 < robinExtremal ε B :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.mp hp).2.pos _

/-- `σ(N)/N = ∏_{p ≤ B} σ(p^{a_p})/p^{a_p}`. -/
theorem sigma_div_robinExtremal (ε : ℝ) (B : ℕ) :
    ((sigma 1 (robinExtremal ε B) : ℕ) : ℝ) / (robinExtremal ε B : ℝ)
      = ∏ p ∈ (Finset.Icc 0 B).filter Nat.Prime, robinLocal p (robinExponent ε p) := by
  have hmul : ((sigma 1 (robinExtremal ε B) : ℕ) : ℝ)
      = ∏ p ∈ (Finset.Icc 0 B).filter Nat.Prime, ((sigma 1 (p ^ robinExponent ε p) : ℕ) : ℝ) := by
    rw [robinExtremal, isMultiplicative_sigma.map_prod (fun p => p ^ robinExponent ε p) _ ?_]
    · push_cast; rfl
    · intro p hp q hq hpq
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hq).2).mpr hpq)
  have hN : ((robinExtremal ε B : ℕ) : ℝ)
      = ∏ p ∈ (Finset.Icc 0 B).filter Nat.Prime, (p : ℝ) ^ robinExponent ε p := by
    rw [robinExtremal]; push_cast; rfl
  rw [hmul, hN, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact sigma_prime_pow_div (Finset.mem_filter.mp hp).2

/-- `log N = Σ_{p ≤ B} a_p log p`. -/
theorem log_robinExtremal (ε : ℝ) (B : ℕ) :
    Real.log (robinExtremal ε B : ℝ)
      = ∑ p ∈ (Finset.Icc 0 B).filter Nat.Prime, (robinExponent ε p : ℝ) * Real.log p := by
  rw [robinExtremal]
  push_cast
  rw [Real.log_prod (fun p hp =>
    (pow_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) _).ne')]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_pow]

/-- `log(σ(N)/N) - ε log N = Σ_{p ≤ B} w_p(a_p(ε))`. -/
theorem log_sigma_div_sub_robinExtremal (ε : ℝ) (B : ℕ) :
    Real.log ((sigma 1 (robinExtremal ε B) : ℝ) / (robinExtremal ε B : ℝ))
        - ε * Real.log (robinExtremal ε B : ℝ)
      = ∑ p ∈ (Finset.Icc 0 B).filter Nat.Prime, robinWeight ε p (robinExponent ε p) := by
  rw [sigma_div_robinExtremal, log_robinExtremal,
    Real.log_prod (fun p hp => (robinLocal_pos (Finset.mem_filter.mp hp).2 _).ne'),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [robinWeight]
  ring

/-- `log(σ(n)/n) - ε log n = Σ_{p ∣ n} w_p(v_p(n))`. -/
theorem log_sigma_div_sub_eq_sum {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    Real.log ((sigma 1 n : ℝ) / (n : ℝ)) - ε * Real.log (n : ℝ)
      = ∑ p ∈ n.primeFactors, robinWeight ε p (n.factorization p) := by
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    have hn' := Nat.prod_factorization_pow_eq_self hn
    unfold Finsupp.prod at hn'
    rw [Nat.support_factorization] at hn'
    conv_lhs => rw [← hn']
    push_cast; rfl
  have hprod : ∏ p ∈ n.primeFactors, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p)
      = ∏ p ∈ n.primeFactors, robinLocal p (n.factorization p) := rfl
  rw [sigma_div_eq_prod hn, hprod, Real.log_prod (fun p hp =>
    (robinLocal_pos (Nat.prime_of_mem_primeFactors hp) _).ne'), hnR,
    Real.log_prod (fun p hp => (pow_pos (by exact_mod_cast
      (Nat.prime_of_mem_primeFactors hp).pos) _).ne'), Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_pow, robinWeight, robinLocal]
  ring

/-- **The Lagrangian inequality.**  If `a_p(ε) = 0` for all primes `p > B`, the extremal number
`N = ∏_{p ≤ B} p^{a_p(ε)}` satisfies `log(σ(n)/n) - ε log n ≤ log(σ(N)/N) - ε log N` for all
`n ≥ 1`. -/
theorem log_sigma_div_sub_le_robinExtremal {ε : ℝ} (hε : 0 < ε) {B : ℕ}
    (hB : ∀ p : ℕ, p.Prime → B < p → robinExponent ε p = 0) {n : ℕ} (hn : n ≠ 0) :
    Real.log ((sigma 1 n : ℝ) / (n : ℝ)) - ε * Real.log (n : ℝ)
      ≤ Real.log ((sigma 1 (robinExtremal ε B) : ℝ) / (robinExtremal ε B : ℝ))
        - ε * Real.log (robinExtremal ε B : ℝ) := by
  rw [log_sigma_div_sub_eq_sum hn, log_sigma_div_sub_robinExtremal]
  set f : ℕ → ℝ := fun p => robinWeight ε p (robinExponent ε p) with hf
  calc ∑ p ∈ n.primeFactors, robinWeight ε p (n.factorization p)
      ≤ ∑ p ∈ n.primeFactors, f p := Finset.sum_le_sum fun p hp =>
        robinWeight_le_robinExponent hε (Nat.prime_of_mem_primeFactors hp) _
    _ = ∑ p ∈ n.primeFactors.filter (fun q => q ≤ B), f p := by
        rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ B) f,
          add_eq_left]
        refine Finset.sum_eq_zero fun p hp => ?_
        simp only [Finset.mem_filter, not_le] at hp
        have hpp := Nat.prime_of_mem_primeFactors hp.1
        simp only [hf, hB p hpp hp.2, robinWeight_zero ε hpp]
    _ ≤ ∑ p ∈ (Finset.Icc 0 B).filter Nat.Prime, f p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ =>
          robinWeight_robinExponent_nonneg hε (Finset.mem_filter.mp hp).2
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨Nat.zero_le _, hp.2⟩, Nat.prime_of_mem_primeFactors hp.1⟩

end

end RHTower
