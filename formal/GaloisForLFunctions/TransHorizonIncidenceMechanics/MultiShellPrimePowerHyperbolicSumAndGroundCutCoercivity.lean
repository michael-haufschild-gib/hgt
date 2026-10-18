import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalPrimeChainHyperbolicCoercivityAndClockStepBound

/-!
# Pillar XXIX: Multi-Shell Prime-Power Hyperbolic Factorization and Universal Ground-Cut Multi-Prime Coercivity (`MultiShellPrimePowerHyperbolicSumAndGroundCutCoercivity`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Global prime-chain variance factorization `divisor_cut_eq_chainVariance` (`RHTower.CHMDPrimeChainVariance`);
  - Single-step valuation-clock lower bound `chainVariance_offlineRadialEnvelope_ge_clock_step` (`GlobalPrimeChainHyperbolicCoercivityAndClockStepBound`).
- **What existing results left unresolved (Track B Step 3 for Uncharted Obstacle 2):**
  In `GlobalPrimeChainHyperbolicCoercivityAndClockStepBound`, the valuation-clock lower bound was proved for a single prime factor $p \in N.\text{primeFactors}$ and the first excited step $b \to p \cdot b$. Two natural questions remained:
  1. How does an arbitrary higher prime-power shell $p^r \cdot b \in N.\text{divisors}$ ($r \ge 1$) contribute across a cut $\log b < u < \log(p^r \cdot b)$?
  2. Can we bound `chainVariance N u (offlineRadialEnvelope β)` and the global functional-equation excess from below by summing over **all** prime factors $p \in N.\text{primeFactors}$ simultaneously at a universal cut $u$?
- **New content in this module (`Candidate new theorem` & `Corollary`):**
  1. **Multi-Shell Prime-Power Radial Factorization (`offlineRadialEnvelope_pow_mul_eq`, `offlineRadialEnvelope_pow_mul_sub_sq_eq`, `chainVariance_offlineRadialEnvelope_ge_prime_pow_shell`):**
     For any prime $p$, base $b \in N.\text{divisors}$ with $\operatorname{ordCompl}_p(b) = b$, and shell exponent $r \ge 1$ with $p^r \cdot b \in N.\text{divisors}$, $\operatorname{ordCompl}_p(p^r \cdot b) = b$ and:
     $$\bigl(r_\beta(b) - r_\beta(p^r \cdot b)\bigr)^2 = r_\beta(b)^2 \bigl(e^{\beta r \log p} - 1\bigr)^2,$$
     yielding the multi-shell lower bound $\log p \cdot r_\beta(b)^2 (e^{\beta r \log p} - 1)^2 \le \operatorname{chainVariance}(N, u, r_\beta)$ whenever $\log b < u < \log(p^r \cdot b)$.
  2. **Universal Ground-Cut Multi-Prime Coercivity (`chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut`, `globalOfflineChainVariance_symmetrized_sub_critical_ge_sum_primeFactors`):**
     At any ground cut $u \in (0, \log 2)$, for **every** $N \in \mathbb{N}$ (with no hypotheses on $N$) and **every** prime factor $p \in N.\text{primeFactors}$, the unit divisor $b = 1$ lies in $\operatorname{chainLeft}(N, p, 1, u)$ and $p$ lies in $\operatorname{chainRight}(N, p, 1, u)$ because $\log 1 = 0 < u < \log 2 \le \log p$. Summing over all $p \in N.\text{primeFactors}$ simultaneously gives the unconditional multi-prime lower bounds:
     $$\sum_{p \in N.\text{primeFactors}} \log p \cdot \bigl(e^{\beta \log p} - 1\bigr)^2 \le \operatorname{chainVariance}(N, u, r_\beta),$$
     $$\sum_{p \in N.\text{primeFactors}} \frac{\log p}{2}\Bigl(\bigl(e^{\beta \log p} - 1\bigr)^2 + \bigl(e^{-\beta \log p} - 1\bigr)^2\Bigr) \le
       \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
         \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
       \operatorname{globalCriticalChainVariance}(N, u, \theta).$$
-/

open Set Finset
open RHTower.CHMDPrimeChain
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Multi-Shell Prime-Power Radial Factorization (`p^r * b`) -/

/-- Along any prime `p` and exponent `r : ℕ`, multiplying a base `b` satisfying `ordCompl[p] b = b`
by `p ^ r` preserves `ordCompl[p] (p ^ r * b) = b`. -/
theorem ordCompl_prime_pow_mul_eq_of_ordCompl_eq {p b : ℕ} (hp : p.Prime) (r : ℕ)
    (hb : ordCompl[p] b = b) :
    ordCompl[p] (p ^ r * b) = b := by
  have hchain : ordCompl[p] b = ordCompl[p] (p ^ r * b) :=
    same_chain_of_pow_mul hp (by ring : p ^ r * b = b * p ^ r)
  exact hchain.symm.trans hb

/-- `r`-th excited shell membership in `chainRight`: if `p` is prime, `p ^ r * b ∈ N.divisors`,
`ordCompl[p] b = b`, and `u < Real.log (p ^ r * b)`, then `p ^ r * b ∈ chainRight N p b u`. -/
theorem mem_chainRight_prime_pow_mul {N p b r : ℕ} {u : ℝ}
    (hp : p.Prime) (hprbN : p ^ r * b ∈ N.divisors) (hb_compl : ordCompl[p] b = b)
    (hlog : u < Real.log ((p ^ r * b : ℕ) : ℝ)) :
    p ^ r * b ∈ chainRight N p b u := by
  unfold chainRight
  exact Finset.mem_filter.mpr
    ⟨hprbN, ordCompl_prime_pow_mul_eq_of_ordCompl_eq hp r hb_compl, hlog⟩

/-- **Multi-Shell Multiplicative Law for `offlineRadialEnvelope`
(`offlineRadialEnvelope_pow_mul_eq`):**
For every $\beta \in \mathbb{R}$, $p > 0$, $b > 0$, and $r \in \mathbb{N}$:
$$r_\beta(p^r \cdot b) = r_\beta(b) \cdot e^{\beta (r : \mathbb{R}) \log p}.$$ -/
theorem offlineRadialEnvelope_pow_mul_eq (β : ℝ) {p b : ℕ} (hp : 0 < p) (hb : 0 < b) (r : ℕ) :
    offlineRadialEnvelope β (p ^ r * b) =
      offlineRadialEnvelope β b * Real.exp (β * (r : ℝ) * Real.log (p : ℝ)) := by
  unfold offlineRadialEnvelope
  have hp_real : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hpr_real : ((p ^ r : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero r hp_real
  have hb_real : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [Nat.cast_mul, Real.log_mul hpr_real hb_real, Nat.cast_pow, Real.log_pow, ← Real.exp_add]
  congr 1
  ring

/-- **Multi-Shell Squared Jump Formula for `offlineRadialEnvelope`
(`offlineRadialEnvelope_pow_mul_sub_sq_eq`):**
For every $\beta \in \mathbb{R}$, $p > 0$, $b > 0$, and $r \in \mathbb{N}$:
$$\bigl(r_\beta(b) - r_\beta(p^r \cdot b)\bigr)^2 =
  r_\beta(b)^2 \bigl(e^{\beta (r : \mathbb{R}) \log p} - 1\bigr)^2.$$ -/
theorem offlineRadialEnvelope_pow_mul_sub_sq_eq (β : ℝ) {p b : ℕ}
    (hp : 0 < p) (hb : 0 < b) (r : ℕ) :
    (offlineRadialEnvelope β b - offlineRadialEnvelope β (p ^ r * b)) ^ (2 : ℕ) =
      offlineRadialEnvelope β b ^ (2 : ℕ) *
        (Real.exp (β * (r : ℝ) * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) := by
  rw [offlineRadialEnvelope_pow_mul_eq β hp hb r]
  ring

/-- **Multi-Shell Lower Bound on Single-Chain `varianceEnergy`
(`varianceEnergy_offlineRadialEnvelope_ge_prime_pow_shell`):**
Whenever $p$ is prime, $b \in N.\text{divisors}$, $p^r \cdot b \in N.\text{divisors}$,
$\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p^r \cdot b)$:
$$r_\beta(b)^2 \bigl(e^{\beta (r : \mathbb{R}) \log p} - 1\bigr)^2 \le
  \operatorname{varianceEnergy}\bigl(\operatorname{chainLeft}(N, p, b, u),\,
    \operatorname{chainRight}(N, p, b, u),\, r_\beta\bigr).$$ -/
theorem varianceEnergy_offlineRadialEnvelope_ge_prime_pow_shell {N p b r : ℕ} {u : ℝ} (β : ℝ)
    (hp : p.Prime) (hbN : b ∈ N.divisors) (hprbN : p ^ r * b ∈ N.divisors)
    (hb_compl : ordCompl[p] b = b)
    (hu_left : Real.log (b : ℝ) < u) (hu_right : u < Real.log ((p ^ r * b : ℕ) : ℝ)) :
    offlineRadialEnvelope β b ^ (2 : ℕ) *
        (Real.exp (β * (r : ℝ) * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) ≤
      varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) := by
  have hmb : b ∈ chainLeft N p b u := mem_chainLeft_base hbN hb_compl hu_left
  have hkprb : p ^ r * b ∈ chainRight N p b u :=
    mem_chainRight_prime_pow_mul hp hprbN hb_compl hu_right
  have hb_pos : 0 < b := Nat.pos_of_mem_divisors hbN
  rw [← offlineRadialEnvelope_pow_mul_sub_sq_eq β hp.pos hb_pos r, ← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have hle_inner : (offlineRadialEnvelope β b - offlineRadialEnvelope β (p ^ r * b)) ^ (2 : ℕ) ≤
      ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun k => (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun k _ => sq_nonneg _) hkprb
  have hle_outer : (∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ)) ≤
      ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun m => ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hmb
  linarith

/-- **Multi-Shell Lower Bound on Global `chainVariance`
(`chainVariance_offlineRadialEnvelope_ge_prime_pow_shell`):**
Whenever $p \in N.\text{primeFactors}$, $b \in N.\text{divisors}$, $p^r \cdot b \in N.\text{divisors}$,
$\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p^r \cdot b)$:
$$\log p \cdot r_\beta(b)^2 \bigl(e^{\beta (r : \mathbb{R}) \log p} - 1\bigr)^2 \le
  \operatorname{chainVariance}(N, u, r_\beta).$$ -/
theorem chainVariance_offlineRadialEnvelope_ge_prime_pow_shell {N p b r : ℕ} {u : ℝ} (β : ℝ)
    (hpN : p ∈ N.primeFactors) (hbN : b ∈ N.divisors) (hprbN : p ^ r * b ∈ N.divisors)
    (hb_compl : ordCompl[p] b = b)
    (hu_left : Real.log (b : ℝ) < u) (hu_right : u < Real.log ((p ^ r * b : ℕ) : ℝ)) :
    Real.log (p : ℝ) *
        (offlineRadialEnvelope β b ^ (2 : ℕ) *
          (Real.exp (β * (r : ℝ) * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) ≤
      chainVariance N u (offlineRadialEnvelope β) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hstep := varianceEnergy_offlineRadialEnvelope_ge_prime_pow_shell
    β hp hbN hprbN hb_compl hu_left hu_right
  have hle_b : varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) ≤
      ∑ d ∈ N.divisors,
        varianceEnergy (chainLeft N p d u) (chainRight N p d u) (offlineRadialEnvelope β) :=
    Finset.single_le_sum
      (f := fun d => varianceEnergy (chainLeft N p d u) (chainRight N p d u)
        (offlineRadialEnvelope β))
      (fun d _ => varianceEnergy_nonneg _ _ _) hbN
  have hle_p : Real.log (p : ℝ) *
        (∑ d ∈ N.divisors,
          varianceEnergy (chainLeft N p d u) (chainRight N p d u) (offlineRadialEnvelope β)) ≤
      chainVariance N u (offlineRadialEnvelope β) := by
    unfold chainVariance
    exact Finset.single_le_sum
      (f := fun q : ℕ => Real.log (q : ℝ) * ∑ d ∈ N.divisors,
        varianceEnergy (chainLeft N q d u) (chainRight N q d u) (offlineRadialEnvelope β))
      (fun q hq => mul_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt.le))
        (Finset.sum_nonneg fun d _ => varianceEnergy_nonneg _ _ _)) hpN
  exact (mul_le_mul_of_nonneg_left (hstep.trans hle_b) hlog_nonneg).trans hle_p

/-! ## §2. Universal Ground-Cut Multi-Prime Coercivity ($u \in (0, \log 2)$) -/

/-- At `m = 1`, `offlineRadialEnvelope β 1 = 1` for every `β : ℝ`. -/
theorem offlineRadialEnvelope_one (β : ℝ) :
    offlineRadialEnvelope β 1 = 1 := by
  simp [offlineRadialEnvelope]

/-- On any ground cut `0 < u < Real.log 2`, for every prime factor `p ∈ N.primeFactors`, the unit
base `b = 1` chain has `varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u) (offlineRadialEnvelope β) ≥ (exp (β * log p) - 1)^2`. -/
theorem varianceEnergy_ground_cut_ge_prime_step {N p : ℕ} {u : ℝ} (β : ℝ)
    (hpN : p ∈ N.primeFactors) (hu0 : 0 < u) (hu2 : u < Real.log 2) :
    (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) ≤
      varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u) (offlineRadialEnvelope β) := by
  obtain ⟨hp_prime, hp_dvd, hN0⟩ := Nat.mem_primeFactors.mp hpN
  have h1N : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr hN0
  have hp1N : p * 1 ∈ N.divisors := by
    rw [mul_one]
    exact Nat.mem_divisors.mpr ⟨hp_dvd, hN0⟩
  have h1_compl : ordCompl[p] 1 = 1 := by simp
  have hu_left : Real.log ((1 : ℕ) : ℝ) < u := by simpa using hu0
  have hu_right : u < Real.log ((p * 1 : ℕ) : ℝ) := by
    rw [mul_one]
    have hlog2_le : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp_prime.two_le)
    linarith
  have hstep := varianceEnergy_offlineRadialEnvelope_ge_clock_step
    β hp_prime h1N hp1N h1_compl hu_left hu_right
  simpa [offlineRadialEnvelope_one] using hstep

/-- **Universal Ground-Cut Multi-Prime Lower Bound on `chainVariance`
(`chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut`):**
For **every** $N \in \mathbb{N}$ (with no hypotheses on $N$), every ground cut
$u \in (0, \log 2)$, and every displacement $\beta \in \mathbb{R}$:
$$\sum_{p \in N.\text{primeFactors}} \log p \cdot \bigl(e^{\beta \log p} - 1\bigr)^2 \le
  \operatorname{chainVariance}(N, u, r_\beta).$$ -/
theorem chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut
    (N : ℕ) {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.log 2) (β : ℝ) :
    (∑ p ∈ N.primeFactors,
        Real.log (p : ℝ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) ≤
      chainVariance N u (offlineRadialEnvelope β) := by
  unfold chainVariance
  refine Finset.sum_le_sum fun p hpN => ?_
  obtain ⟨hp_prime, _, hN0⟩ := Nat.mem_primeFactors.mp hpN
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
  have h1N : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr hN0
  have hstep := varianceEnergy_ground_cut_ge_prime_step β hpN hu0 hu2
  have hle_b : varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u) (offlineRadialEnvelope β) ≤
      ∑ b ∈ N.divisors,
        varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) :=
    Finset.single_le_sum
      (f := fun b => varianceEnergy (chainLeft N p b u) (chainRight N p b u)
        (offlineRadialEnvelope β))
      (fun b _ => varianceEnergy_nonneg _ _ _) h1N
  exact mul_le_mul_of_nonneg_left (hstep.trans hle_b) hlog_nonneg

/-- **Universal Ground-Cut Multi-Prime Lower Bound on the Global Off-Line Excess
(`globalOfflineChainVariance_symmetrized_sub_critical_ge_sum_primeFactors`):**
For **every** $N \in \mathbb{N}$, every ground cut $u \in (0, \log 2)$, every displacement
$\beta \in \mathbb{R}$, and every phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\sum_{p \in N.\text{primeFactors}}
    \frac{\log p}{2}\Bigl(\bigl(e^{\beta \log p} - 1\bigr)^2 +
      \bigl(e^{-\beta \log p} - 1\bigr)^2\Bigr) \le
  \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
    \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
  \operatorname{globalCriticalChainVariance}(N, u, \theta).$$ -/
theorem globalOfflineChainVariance_symmetrized_sub_critical_ge_sum_primeFactors
    (N : ℕ) {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.log 2) (β : ℝ) (θ : ℕ → ℝ) :
    (∑ p ∈ N.primeFactors,
        (Real.log (p : ℝ) / 2) *
          ((Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) +
            (Real.exp (-β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ))) ≤
      (1 / 2 : ℝ) *
        (globalOfflineChainVariance N u β θ + globalOfflineChainVariance N u (-β) θ) -
        globalCriticalChainVariance N u θ := by
  have hdom := globalCriticalChainVariance_le_symmetrized_offline N u β θ
  have hpos := chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut N hu0 hu2 β
  have hneg := chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut N hu0 hu2 (-β)
  have hsum_eq :
      (∑ p ∈ N.primeFactors,
        (Real.log (p : ℝ) / 2) *
          ((Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) +
            (Real.exp (-β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ))) =
      (1 / 2 : ℝ) *
        ((∑ p ∈ N.primeFactors,
            Real.log (p : ℝ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) +
          (∑ p ∈ N.primeFactors,
            Real.log (p : ℝ) * (Real.exp (-β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
