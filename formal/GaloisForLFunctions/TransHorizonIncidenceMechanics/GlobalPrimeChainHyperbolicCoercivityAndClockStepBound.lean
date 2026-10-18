import GaloisForLFunctions.TransHorizonIncidenceMechanics.OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence

/-!
# Pillar XXVII: Global Prime-Chain Hyperbolic Coercivity and Explicit Valuation-Clock Step Lower Bound (`GlobalPrimeChainHyperbolicCoercivityAndClockStepBound`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Global prime-chain variance factorization `divisor_cut_eq_chainVariance` and `chainVariance_zero_iff` (`RHTower.CHMDPrimeChainVariance`);
  - Local single-chain off-line hyperbolic excess `varianceEnergy_symmetrized_offline_sub_critical_eq` (`OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence`).
- **What existing results left unresolved (Track B Step 2 for Uncharted Obstacle 2):**
  In `OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence`, the off-line hyperbolic excess over the critical line was established on a single bipartite chain cut $(L, R)$. To connect directly to the global von Mangoldt divisor-cut energy `CHMDPrimeChain.chainVariance N u` and obtain a quantitative lower bound in terms of the prime step $\tau = \log p$ and off-line displacement $\beta = \operatorname{Re}(\rho) - 1/2$, we must:
  1. Lift the functional-equation $(+\beta, -\beta)$ hyperbolic excess identity to the full global sum over $p \in N.\text{primeFactors}$ and $b \in N.\text{divisors}$ weighted by $\log p$;
  2. Evaluate the radial jump across a single $p$-adic valuation-clock step $b \to p \cdot b$ as $r_\beta(b)^2 (e^{\beta \log p} - 1)^2$ and prove the quantitative lower bound on `chainVariance N u (offlineRadialEnvelope β)` and on the global off-line excess.
- **New content in this module (`Candidate new theorem` & `Corollary`):**
  1. **Global Two-Channel `chainVariance` Hyperbolic Decomposition (`globalOfflineChainVariance_symmetrized_sub_critical_eq`, `globalCriticalChainVariance_le_symmetrized_offline`):**
     For every $N \in \mathbb{N}$, cut $u \in \mathbb{R}$, displacement $\beta \in \mathbb{R}$, and phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
     $$\frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
       \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
       \operatorname{globalCriticalChainVariance}(N, u, \theta) =
       \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
         \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr) +
       \operatorname{globalHyperbolicPhaseAmplification}(N, u, \beta, \theta) \ge
       \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
         \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr) \ge 0.$$
  2. **Exact Valuation-Clock Step Factorization (`offlineRadialEnvelope_prime_mul_eq`, `offlineRadialEnvelope_prime_mul_sub_sq_eq`):**
     For any prime $p$ and base divisor $b \in N.\text{divisors}$, the radial envelope across the elementary $p$-adic step $b \to p \cdot b$ satisfies $r_\beta(p \cdot b) = r_\beta(b) e^{\beta \log p}$ and:
     $$\bigl(r_\beta(b) - r_\beta(p \cdot b)\bigr)^2 = r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2.$$
  3. **Quantitative Valuation-Clock Step Lower Bound on `chainVariance` and Global Off-Line Excess (`varianceEnergy_offlineRadialEnvelope_ge_clock_step`, `chainVariance_offlineRadialEnvelope_ge_clock_step`, `globalOfflineChainVariance_symmetrized_sub_critical_ge_clock_step`):**
     Whenever $p \in N.\text{primeFactors}$, $b \in N.\text{divisors}$, $p \cdot b \in N.\text{divisors}$, $\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p \cdot b)$, the global radial `chainVariance` and the global functional-equation off-line excess satisfy the explicit quantitative lower bounds:
     $$\log p \cdot r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2 \le \operatorname{chainVariance}(N, u, r_\beta),$$
     $$\frac{\log p}{2}\Bigl(r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2 +
       r_{-\beta}(b)^2 \bigl(e^{-\beta \log p} - 1\bigr)^2\Bigr) \le
       \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
         \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
       \operatorname{globalCriticalChainVariance}(N, u, \theta),$$
     which is strictly positive ($> 0$) for every $\beta \ne 0$ (`clock_step_lower_bound_pos`).
-/

open Set Finset
open RHTower.CHMDPrimeChain
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Global Two-Channel `chainVariance` Lift & Hyperbolic Coercivity -/

/-- Global two-channel prime-chain variance for a polar profile `(r cos θ, r sin θ)` at cut `u`. -/
def globalPolarChainVariance (N : ℕ) (u : ℝ) (r θ : ℕ → ℝ) : ℝ :=
  chainVariance N u (polarCosChannel r θ) + chainVariance N u (polarSinChannel r θ)

/-- Global two-channel prime-chain variance on the critical line (`r ≡ 1`, `β = 0`). -/
def globalCriticalChainVariance (N : ℕ) (u : ℝ) (θ : ℕ → ℝ) : ℝ :=
  chainVariance N u (criticalCosChannel θ) + chainVariance N u (criticalSinChannel θ)

/-- Global two-channel prime-chain variance for an off-line spectral parameter with displacement `β`. -/
def globalOfflineChainVariance (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) : ℝ :=
  globalPolarChainVariance N u (offlineRadialEnvelope β) θ

/-- Global hyperbolic-phase amplification summed over all prime chains `(p, b)` of `N` at cut `u`. -/
def globalHyperbolicPhaseAmplification (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) : ℝ :=
  ∑ p ∈ N.primeFactors, Real.log p *
    ∑ b ∈ N.divisors,
      offlineHyperbolicPhaseAmplification (chainLeft N p b u) (chainRight N p b u) β θ

/-- Chainwise expansion of `globalPolarChainVariance`. -/
theorem globalPolarChainVariance_eq_sum (N : ℕ) (u : ℝ) (r θ : ℕ → ℝ) :
    globalPolarChainVariance N u r θ =
      ∑ p ∈ N.primeFactors, Real.log p *
        ∑ b ∈ N.divisors,
          polarTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) r θ := by
  unfold globalPolarChainVariance chainVariance polarTwoChannelVariance
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]

/-- Chainwise expansion of `globalCriticalChainVariance`. -/
theorem globalCriticalChainVariance_eq_sum (N : ℕ) (u : ℝ) (θ : ℕ → ℝ) :
    globalCriticalChainVariance N u θ =
      ∑ p ∈ N.primeFactors, Real.log p *
        ∑ b ∈ N.divisors,
          criticalTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) θ := by
  unfold globalCriticalChainVariance chainVariance criticalTwoChannelVariance
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]

/-- Chainwise expansion of `globalOfflineChainVariance`. -/
theorem globalOfflineChainVariance_eq_sum (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) :
    globalOfflineChainVariance N u β θ =
      ∑ p ∈ N.primeFactors, Real.log p *
        ∑ b ∈ N.divisors,
          offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) β θ := by
  unfold globalOfflineChainVariance offlineTwoChannelVariance
  exact globalPolarChainVariance_eq_sum N u (offlineRadialEnvelope β) θ

/-- At `β = 0`, `globalOfflineChainVariance` equals `globalCriticalChainVariance`. -/
theorem globalOfflineChainVariance_zero_eq_critical (N : ℕ) (u : ℝ) (θ : ℕ → ℝ) :
    globalOfflineChainVariance N u 0 θ = globalCriticalChainVariance N u θ := by
  rw [globalOfflineChainVariance_eq_sum, globalCriticalChainVariance_eq_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  exact offlineTwoChannelVariance_zero_eq_critical (chainLeft N p b u) (chainRight N p b u) θ

/-- Non-negativity of `globalHyperbolicPhaseAmplification`. -/
theorem globalHyperbolicPhaseAmplification_nonneg (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) :
    0 ≤ globalHyperbolicPhaseAmplification N u β θ := by
  unfold globalHyperbolicPhaseAmplification
  refine Finset.sum_nonneg fun p hp => ?_
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  exact mul_nonneg hlog (Finset.sum_nonneg fun b _ =>
    offlineHyperbolicPhaseAmplification_nonneg (chainLeft N p b u) (chainRight N p b u) β θ)

/-- **Global Off-Line Hyperbolic `chainVariance` Decomposition
(`globalOfflineChainVariance_symmetrized_sub_critical_eq`):**
For every $N \in \mathbb{N}$, cut $u \in \mathbb{R}$, off-line displacement $\beta \in \mathbb{R}$,
and phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
    \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
  \operatorname{globalCriticalChainVariance}(N, u, \theta) =
  \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
    \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr) +
  \operatorname{globalHyperbolicPhaseAmplification}(N, u, \beta, \theta).$$ -/
theorem globalOfflineChainVariance_symmetrized_sub_critical_eq
    (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) :
    (1 / 2 : ℝ) *
        (globalOfflineChainVariance N u β θ + globalOfflineChainVariance N u (-β) θ) -
        globalCriticalChainVariance N u θ =
      (1 / 2 : ℝ) *
        (chainVariance N u (offlineRadialEnvelope β) +
          chainVariance N u (offlineRadialEnvelope (-β))) +
        globalHyperbolicPhaseAmplification N u β θ := by
  rw [globalOfflineChainVariance_eq_sum N u β θ,
    globalOfflineChainVariance_eq_sum N u (-β) θ,
    globalCriticalChainVariance_eq_sum N u θ]
  unfold chainVariance globalHyperbolicPhaseAmplification
  have hchain : ∀ p ∈ N.primeFactors,
      (1 / 2 : ℝ) *
          (Real.log p * ∑ b ∈ N.divisors,
              offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) β θ +
            Real.log p * ∑ b ∈ N.divisors,
              offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) (-β) θ) -
          Real.log p * ∑ b ∈ N.divisors,
            criticalTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) θ =
        (1 / 2 : ℝ) *
          (Real.log p * ∑ b ∈ N.divisors,
              varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) +
            Real.log p * ∑ b ∈ N.divisors,
              varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope (-β))) +
          Real.log p * ∑ b ∈ N.divisors,
            offlineHyperbolicPhaseAmplification (chainLeft N p b u) (chainRight N p b u) β θ := by
    intro p _
    have hinner :
        (∑ b ∈ N.divisors,
          ((1 / 2 : ℝ) *
            (offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) β θ +
              offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) (-β) θ) -
            criticalTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) θ)) =
        ∑ b ∈ N.divisors,
          ((1 / 2 : ℝ) *
            (varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) +
              varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope (-β))) +
            offlineHyperbolicPhaseAmplification (chainLeft N p b u) (chainRight N p b u) β θ) :=
      Finset.sum_congr rfl fun b _ =>
        varianceEnergy_symmetrized_offline_sub_critical_eq
          (chainLeft N p b u) (chainRight N p b u) β θ
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hinner
    linear_combination Real.log (p : ℝ) * hinner
  have hsum := Finset.sum_congr rfl hchain
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

/-- **Universal Global Off-Line Hyperbolic Dominance Over Critical-Line Variance
(`globalCriticalChainVariance_le_symmetrized_offline`):**
For every $N \in \mathbb{N}$, cut $u \in \mathbb{R}$, off-line displacement $\beta \in \mathbb{R}$,
and phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{globalCriticalChainVariance}(N, u, \theta) +
  \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
    \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr) \le
  \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
    \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr).$$ -/
theorem globalCriticalChainVariance_le_symmetrized_offline
    (N : ℕ) (u β : ℝ) (θ : ℕ → ℝ) :
    globalCriticalChainVariance N u θ +
        (1 / 2 : ℝ) *
          (chainVariance N u (offlineRadialEnvelope β) +
            chainVariance N u (offlineRadialEnvelope (-β))) ≤
      (1 / 2 : ℝ) *
        (globalOfflineChainVariance N u β θ + globalOfflineChainVariance N u (-β) θ) := by
  have hid := globalOfflineChainVariance_symmetrized_sub_critical_eq N u β θ
  have hamp := globalHyperbolicPhaseAmplification_nonneg N u β θ
  linarith

/-! ## §2. Explicit Valuation-Clock Step Membership & Quantitative Lower Bound -/

/-- Along any prime `p`, multiplying a base `b` satisfying `ordCompl[p] b = b` by `p` preserves
`ordCompl[p] (p * b) = b`. -/
theorem ordCompl_prime_mul_eq_of_ordCompl_eq {p b : ℕ} (hp : p.Prime)
    (hb : ordCompl[p] b = b) :
    ordCompl[p] (p * b) = b := by
  have hchain : ordCompl[p] b = ordCompl[p] (p * b) :=
    same_chain_of_pow_mul hp (by ring : p * b = b * p ^ 1)
  exact hchain.symm.trans hb

/-- Ground-state membership in `chainLeft`: if `b ∈ N.divisors`, `ordCompl[p] b = b`, and
`Real.log b < u`, then `b ∈ chainLeft N p b u`. -/
theorem mem_chainLeft_base {N p b : ℕ} {u : ℝ}
    (hbN : b ∈ N.divisors) (hb_compl : ordCompl[p] b = b) (hlog : Real.log (b : ℝ) < u) :
    b ∈ chainLeft N p b u := by
  unfold chainLeft
  exact Finset.mem_filter.mpr ⟨hbN, hb_compl, hlog⟩

/-- First-excited-state membership in `chainRight`: if `p` is prime, `p * b ∈ N.divisors`,
`ordCompl[p] b = b`, and `u < Real.log (p * b)`, then `p * b ∈ chainRight N p b u`. -/
theorem mem_chainRight_prime_mul {N p b : ℕ} {u : ℝ}
    (hp : p.Prime) (hpbN : p * b ∈ N.divisors) (hb_compl : ordCompl[p] b = b)
    (hlog : u < Real.log ((p * b : ℕ) : ℝ)) :
    p * b ∈ chainRight N p b u := by
  unfold chainRight
  exact Finset.mem_filter.mpr ⟨hpbN, ordCompl_prime_mul_eq_of_ordCompl_eq hp hb_compl, hlog⟩

/-- **Multiplicative Step Law for `offlineRadialEnvelope` (`offlineRadialEnvelope_prime_mul_eq`):**
For every $\beta \in \mathbb{R}$, $p > 0$, and $b > 0$:
$$r_\beta(p \cdot b) = r_\beta(b) \cdot e^{\beta \log p}.$$ -/
theorem offlineRadialEnvelope_prime_mul_eq (β : ℝ) {p b : ℕ} (hp : 0 < p) (hb : 0 < b) :
    offlineRadialEnvelope β (p * b) =
      offlineRadialEnvelope β b * Real.exp (β * Real.log (p : ℝ)) := by
  unfold offlineRadialEnvelope
  have hp_real : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hb_real : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [Nat.cast_mul, Real.log_mul hp_real hb_real, ← Real.exp_add]
  congr 1
  ring

/-- **Exact Valuation-Clock Step Squared Jump Formula
(`offlineRadialEnvelope_prime_mul_sub_sq_eq`):**
For every $\beta \in \mathbb{R}$, $p > 0$, and $b > 0$:
$$\bigl(r_\beta(b) - r_\beta(p \cdot b)\bigr)^2 =
  r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2.$$ -/
theorem offlineRadialEnvelope_prime_mul_sub_sq_eq (β : ℝ) {p b : ℕ} (hp : 0 < p) (hb : 0 < b) :
    (offlineRadialEnvelope β b - offlineRadialEnvelope β (p * b)) ^ (2 : ℕ) =
      offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) := by
  rw [offlineRadialEnvelope_prime_mul_eq β hp hb]
  ring

/-- **Strict Positivity of the Valuation-Clock Step Factor (`clock_step_lower_bound_pos`):**
For every prime $p$, $b \in \mathbb{N}$, and off-line displacement $\beta \ne 0$:
$$0 < \log p \cdot r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2.$$ -/
theorem clock_step_lower_bound_pos {p : ℕ} (hp : p.Prime) (b : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    0 < Real.log (p : ℝ) *
      (offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) := by
  have hlog_pos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr_pos : 0 < offlineRadialEnvelope β b ^ (2 : ℕ) :=
     pow_pos (offlineRadialEnvelope_pos β b) 2
  have hexp_ne : Real.exp (β * Real.log (p : ℝ)) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, Real.exp_eq_one_iff]
    exact mul_ne_zero hβ hlog_pos.ne'
  have hsq_pos : 0 < (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hexp_ne
  positivity

/-- **Quantitative Valuation-Clock Step Lower Bound on Single-Chain `varianceEnergy`
(`varianceEnergy_offlineRadialEnvelope_ge_clock_step`):**
Whenever $p$ is prime, $b \in N.\text{divisors}$, $p \cdot b \in N.\text{divisors}$,
$\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p \cdot b)$, the radial chain variance
satisfies:
$$r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2 \le
  \operatorname{varianceEnergy}\bigl(\operatorname{chainLeft}(N, p, b, u),\,
    \operatorname{chainRight}(N, p, b, u),\, r_\beta\bigr).$$ -/
theorem varianceEnergy_offlineRadialEnvelope_ge_clock_step {N p b : ℕ} {u : ℝ} (β : ℝ)
    (hp : p.Prime) (hbN : b ∈ N.divisors) (hpbN : p * b ∈ N.divisors)
    (hb_compl : ordCompl[p] b = b)
    (hu_left : Real.log (b : ℝ) < u) (hu_right : u < Real.log ((p * b : ℕ) : ℝ)) :
    offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) ≤
      varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) := by
  have hmb : b ∈ chainLeft N p b u := mem_chainLeft_base hbN hb_compl hu_left
  have hkpb : p * b ∈ chainRight N p b u := mem_chainRight_prime_mul hp hpbN hb_compl hu_right
  have hb_pos : 0 < b := Nat.pos_of_mem_divisors hbN
  rw [← offlineRadialEnvelope_prime_mul_sub_sq_eq β hp.pos hb_pos, ← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have hle_inner : (offlineRadialEnvelope β b - offlineRadialEnvelope β (p * b)) ^ (2 : ℕ) ≤
      ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun k => (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun k _ => sq_nonneg _) hkpb
  have hle_outer : (∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ)) ≤
      ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun m => ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hmb
  linarith

/-- **Quantitative Valuation-Clock Step Lower Bound on Global `chainVariance`
(`chainVariance_offlineRadialEnvelope_ge_clock_step`):**
Whenever $p \in N.\text{primeFactors}$, $b \in N.\text{divisors}$, $p \cdot b \in N.\text{divisors}$,
$\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p \cdot b)$, the global radial
`chainVariance` satisfies:
$$\log p \cdot r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2 \le
  \operatorname{chainVariance}(N, u, r_\beta).$$ -/
theorem chainVariance_offlineRadialEnvelope_ge_clock_step {N p b : ℕ} {u : ℝ} (β : ℝ)
    (hpN : p ∈ N.primeFactors) (hbN : b ∈ N.divisors) (hpbN : p * b ∈ N.divisors)
    (hb_compl : ordCompl[p] b = b)
    (hu_left : Real.log (b : ℝ) < u) (hu_right : u < Real.log ((p * b : ℕ) : ℝ)) :
    Real.log (p : ℝ) *
        (offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) ≤
      chainVariance N u (offlineRadialEnvelope β) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hstep := varianceEnergy_offlineRadialEnvelope_ge_clock_step
    β hp hbN hpbN hb_compl hu_left hu_right
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
  have hmul : Real.log (p : ℝ) *
      (offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) ≤
      Real.log (p : ℝ) *
        ∑ d ∈ N.divisors,
          varianceEnergy (chainLeft N p d u) (chainRight N p d u) (offlineRadialEnvelope β) :=
    mul_le_mul_of_nonneg_left (hstep.trans hle_b) hlog_nonneg
  exact hmul.trans hle_p

/-- **Quantitative Valuation-Clock Step Lower Bound on the Global Off-Line Excess
(`globalOfflineChainVariance_symmetrized_sub_critical_ge_clock_step`):**
Whenever $p \in N.\text{primeFactors}$, $b \in N.\text{divisors}$, $p \cdot b \in N.\text{divisors}$,
$\operatorname{ordCompl}_p(b) = b$, and $\log b < u < \log(p \cdot b)$, for **every** displacement
$\beta \in \mathbb{R}$ and phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\frac{\log p}{2}\Bigl(r_\beta(b)^2 \bigl(e^{\beta \log p} - 1\bigr)^2 +
    r_{-\beta}(b)^2 \bigl(e^{-\beta \log p} - 1\bigr)^2\Bigr) \le
  \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
    \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
  \operatorname{globalCriticalChainVariance}(N, u, \theta).$$ -/
theorem globalOfflineChainVariance_symmetrized_sub_critical_ge_clock_step
    {N p b : ℕ} {u : ℝ} (β : ℝ) (θ : ℕ → ℝ)
    (hpN : p ∈ N.primeFactors) (hbN : b ∈ N.divisors) (hpbN : p * b ∈ N.divisors)
    (hb_compl : ordCompl[p] b = b)
    (hu_left : Real.log (b : ℝ) < u) (hu_right : u < Real.log ((p * b : ℕ) : ℝ)) :
    (Real.log (p : ℝ) / 2) *
        (offlineRadialEnvelope β b ^ (2 : ℕ) * (Real.exp (β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ) +
          offlineRadialEnvelope (-β) b ^ (2 : ℕ) *
            (Real.exp (-β * Real.log (p : ℝ)) - 1) ^ (2 : ℕ)) ≤
      (1 / 2 : ℝ) *
        (globalOfflineChainVariance N u β θ + globalOfflineChainVariance N u (-β) θ) -
        globalCriticalChainVariance N u θ := by
  have hdom := globalCriticalChainVariance_le_symmetrized_offline N u β θ
  have hpos := chainVariance_offlineRadialEnvelope_ge_clock_step
    β hpN hbN hpbN hb_compl hu_left hu_right
  have hneg := chainVariance_offlineRadialEnvelope_ge_clock_step
    (-β) hpN hbN hpbN hb_compl hu_left hu_right
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
