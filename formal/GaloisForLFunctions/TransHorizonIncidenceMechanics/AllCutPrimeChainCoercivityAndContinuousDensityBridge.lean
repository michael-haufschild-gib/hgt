import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiShellPrimePowerHyperbolicSumAndGroundCutCoercivity
import GaloisForLFunctions.RHTower.CHMDPrimeChainSourceFactorization

/-!
# All-Cut Prime-Chain Coercivity, Quadratic Hyperbolic Floor, and Continuous CHMD Density Bridge

This module advances **Steps 1 and 2** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`):

1. **Universal Symmetrized Hyperbolic Convexity Floor & Quadratic $\beta^2 (\log p)^3$ Coercivity**:
   - Proves the elementary convexity inequality $(e^x - 1)^2 + (e^{-x} - 1)^2 \ge x^2$ for all
     $x \in \mathbb{R}$ (`exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq`).
   - Combines both $(+\beta)$ and $(-\beta)$ radial branches in
     `globalOfflineChainVariance_symmetrized_sub_critical_eq` to establish the explicit quadratic
     coercivity floor
     $$\frac{1}{2}\beta^2 \sum_{p \in N.\text{primeFactors}} (\log p)^3
       \le \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
         \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr)$$
     at every ground cut $u \in (0, \log 2)$ (`globalOfflineChainVariance_symmetrized_sub_critical_ge_quadratic_cubic_log`).

2. **Multi-Shell Valuation Summation & All-Cut Straddling $p$-Rough Bases**:
   - Sums the prime-power radial jumps $(r_\beta(b) - r_\beta(p^r \cdot b))^2 = r_\beta(b)^2 (e^{\beta r \log p} - 1)^2$
     simultaneously over any finite set of active valuation shells $S \subseteq \mathbb{N}$ along a
     fixed prime chain (`varianceEnergy_offlineRadialEnvelope_ge_sum_shells`), and over any subset
     of $p$-coprime chain bases $B \subseteq N.\text{divisors}$ straddling an arbitrary cut $u > 0$
     (`chainVariance_offlineRadialEnvelope_ge_sum_straddling_bases`).

3. **Continuous Logarithmic Pullback to `CHMDPrimeChainSource.chainDensity` and `density`**:
   - Evaluates the continuous CHMD crossing functionals `CHMDPrimeChainSource.chainDensity` and
     `CHMDPrimeChainSource.density` (`m ↦ v(u - log m)`) on the continuous off-line wave pair
     $v_{\beta,\gamma}^{\cos}(x) = e^{-\beta x}\cos(\gamma x)$ and
     $v_{\beta,\gamma}^{\sin}(x) = -e^{-\beta x}\sin(\gamma x)$.
   - Proves the exact continuous-to-discrete factorization
     $$\operatorname{continuousOfflineTwoChannelDensity}(N, \beta, \gamma, u)
       = e^{-2\beta u}\,\operatorname{fiber}(N, u)\,
         \operatorname{globalOfflineChainVariance}(N, u, \beta, \theta_{\gamma, u}),$$
     yielding pointwise non-negativity and explicit ground-cut lower bounds for the cut-normalized
     symmetrized CHMD crossing density (`continuousOfflineTwoChannelDensity_symmetrized_sub_critical_eq`).
-/

open Finset Real
open RHTower.CHMDPrimeChain RHTower.CHMDPrimeChainSource
open RHTower.CHMDPrimeCuts RHTower.PhiDivisorEnergy

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Hyperbolic Convexity Floor & Quadratic $\beta^2 (\log p)^3$ Coercivity -/

/-- **Universal Symmetrized Exponential-Minus-One Quadratic Floor
(`exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq`):**
For every $x \in \mathbb{R}$, $x^2 \le (e^x - 1)^2 + (e^{-x} - 1)^2$.
(Classification: Known elementary convexity consequence of $1 + x \le e^x$.) -/
theorem exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq (x : ℝ) :
    x ^ (2 : ℕ) ≤ (Real.exp x - 1) ^ (2 : ℕ) + (Real.exp (-x) - 1) ^ (2 : ℕ) := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h2 : 0 ≤ (Real.exp (-x) - 1) ^ (2 : ℕ) := sq_nonneg _
    have hsq : x ^ (2 : ℕ) ≤ (Real.exp x - 1) ^ (2 : ℕ) := by
      nlinarith [mul_le_mul h1 h1 hx (by linarith)]
    linarith
  · have h1 : -x ≤ Real.exp (-x) - 1 := by linarith [Real.add_one_le_exp (-x)]
    have h2 : 0 ≤ (Real.exp x - 1) ^ (2 : ℕ) := sq_nonneg _
    have hsq : x ^ (2 : ℕ) ≤ (Real.exp (-x) - 1) ^ (2 : ℕ) := by
      nlinarith [mul_le_mul h1 h1 (by linarith) (by linarith)]
    linarith

/-- At the ground chain base $b = 1$, the symmetrized prime-power shell jump
$\frac{1}{2}((r_\beta(1) - r_\beta(p^r))^2 + (r_{-\beta}(1) - r_{-\beta}(p^r))^2)$ dominates
$\frac{1}{2} \beta^2 r^2 (\log p)^2$.
(Classification: Corollary.) -/
theorem symmetrized_ground_prime_pow_shell_jump_ge_quadratic (β : ℝ) {p : ℕ} (hp : 0 < p) (r : ℕ) :
    (1 / 2 : ℝ) * (β * (r : ℝ) * Real.log p) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) *
        ((offlineRadialEnvelope β 1 - offlineRadialEnvelope β (p ^ r)) ^ (2 : ℕ) +
          (offlineRadialEnvelope (-β) 1 - offlineRadialEnvelope (-β) (p ^ r)) ^ (2 : ℕ)) := by
  have hpos := offlineRadialEnvelope_pow_mul_sub_sq_eq β hp (by omega : 0 < 1) r
  have hneg := offlineRadialEnvelope_pow_mul_sub_sq_eq (-β) hp (by omega : 0 < 1) r
  simp only [mul_one, offlineRadialEnvelope_one, one_pow, one_mul, neg_mul] at hpos hneg ⊢
  rw [hpos, hneg]
  have hexp := exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq (β * (r : ℝ) * Real.log p)
  linarith

/-- For any prime factor $p \in N.\text{primeFactors}$ and ground cut $u \in (0, \log 2)$, the
symmetrized $(+\beta, -\beta)$ variance energy on the $b = 1$ ground chain dominates
$\frac{1}{2} \beta^2 (\log p)^2$.
(Classification: New formulation.) -/
theorem symmetrized_ground_varianceEnergy_ge_quadratic (N : ℕ) {p : ℕ}
    (hpN : p ∈ N.primeFactors) {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.log 2) (β : ℝ) :
    (1 / 2 : ℝ) * (β * Real.log p) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) *
        (varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u) (offlineRadialEnvelope β) +
          varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u) (offlineRadialEnvelope (-β))) := by
  have h1 := varianceEnergy_ground_cut_ge_prime_step β hpN hu0 hu2
  have h2 := varianceEnergy_ground_cut_ge_prime_step (-β) hpN hu0 hu2
  rw [neg_mul] at h2
  have hexp := exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq (β * Real.log p)
  linarith

/-- **Quadratic $\beta^2 (\log p)^3$ Ground-Cut Coercivity Floor
(`symmetrized_chainVariance_ge_quadratic_cubic_log`):**
For every $N \in \mathbb{N}$, ground cut $u \in (0, \log 2)$, and off-line displacement
$\beta \in \mathbb{R}$:
$$\frac{1}{2}\beta^2 \sum_{p \in N.\text{primeFactors}} (\log p)^3
  \le \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
    \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr).$$
(Classification: Candidate new theorem.) -/
theorem symmetrized_chainVariance_ge_quadratic_cubic_log (N : ℕ) {u : ℝ}
    (hu0 : 0 < u) (hu2 : u < Real.log 2) (β : ℝ) :
    (1 / 2 : ℝ) * β ^ (2 : ℕ) * (∑ p ∈ N.primeFactors, Real.log p ^ (3 : ℕ)) ≤
      (1 / 2 : ℝ) *
        (chainVariance N u (offlineRadialEnvelope β) +
          chainVariance N u (offlineRadialEnvelope (-β))) := by
  have h1 := chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut N hu0 hu2 β
  have h2 := chainVariance_offlineRadialEnvelope_ge_sum_primeFactors_of_ground_cut N hu0 hu2 (-β)
  have hsum :
      (1 / 2 : ℝ) * β ^ (2 : ℕ) * (∑ p ∈ N.primeFactors, Real.log p ^ (3 : ℕ)) ≤
        (1 / 2 : ℝ) *
          ((∑ p ∈ N.primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ)) +
            (∑ p ∈ N.primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    have hexp := exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq (β * Real.log p)
    rw [← neg_mul] at hexp
    have hmul := mul_le_mul_of_nonneg_left hexp hlog
    nlinarith
  linarith

/-- **Global Off-Line `chainVariance` Quadratic Coercivity Theorem
(`globalOfflineChainVariance_symmetrized_sub_critical_ge_quadratic_cubic_log`):**
For every $N \in \mathbb{N}$, ground cut $u \in (0, \log 2)$, off-line displacement $\beta \in \mathbb{R}$,
and phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\frac{1}{2}\beta^2 \sum_{p \in N.\text{primeFactors}} (\log p)^3
  \le \frac{1}{2}\Bigl(\operatorname{globalOfflineChainVariance}(N, u, \beta, \theta) +
    \operatorname{globalOfflineChainVariance}(N, u, -\beta, \theta)\Bigr) -
      \operatorname{globalCriticalChainVariance}(N, u, \theta).$$
(Classification: Candidate new theorem.) -/
theorem globalOfflineChainVariance_symmetrized_sub_critical_ge_quadratic_cubic_log
    (N : ℕ) {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.log 2) (β : ℝ) (θ : ℕ → ℝ) :
    (1 / 2 : ℝ) * β ^ (2 : ℕ) * (∑ p ∈ N.primeFactors, Real.log p ^ (3 : ℕ)) ≤
      (1 / 2 : ℝ) *
          (globalOfflineChainVariance N u β θ + globalOfflineChainVariance N u (-β) θ) -
        globalCriticalChainVariance N u θ := by
  rw [globalOfflineChainVariance_symmetrized_sub_critical_eq]
  have h1 := symmetrized_chainVariance_ge_quadratic_cubic_log N hu0 hu2 β
  have h2 := globalHyperbolicPhaseAmplification_nonneg N u β θ
  linarith

/-! ## §2. Multi-Shell Valuation Summation & All-Cut Straddling $p$-Rough Bases -/

/-- Injectivity of the prime-power shell map $r \mapsto p^r \cdot b$ for $p \ge 2$ and $b \ge 1$.
(Classification: Known.) -/
theorem pow_mul_right_injective_of_prime {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    Function.Injective (fun r : ℕ => p ^ r * b) := by
  intro r₁ r₂ h
  have hpow : p ^ r₁ = p ^ r₂ := Nat.eq_of_mul_eq_mul_right hb h
  exact (Nat.pow_right_injective hp.two_le) hpow

/-- **Simultaneous Multi-Shell Prime-Power Lower Bound Along a Single Chain
(`varianceEnergy_offlineRadialEnvelope_ge_sum_shells`):**
For any prime $p$, $p$-coprime base $b \in N.\text{divisors}$ (`ordCompl[p] b = b`), cut $u > \log b$,
and finite set of exponents $S \subseteq \mathbb{N}$ such that every $r \in S$ satisfies
$p^r \cdot b \in N.\text{divisors}$ and $u < \log(p^r \cdot b)$,
`varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β)`
dominates the sum over all shells $r \in S$:
$$\sum_{r \in S} r_\beta(b)^2 (e^{\beta r \log p} - 1)^2
  \le \operatorname{varianceEnergy}(\operatorname{chainLeft}(N, p, b, u),
    \operatorname{chainRight}(N, p, b, u), r_\beta).$$
(Classification: Candidate new theorem.) -/
theorem varianceEnergy_offlineRadialEnvelope_ge_sum_shells {N p b : ℕ}
    (hp : p.Prime) (hbN : b ∈ N.divisors) (hb_compl : ordCompl[p] b = b)
    {u : ℝ} (hu_left : Real.log (b : ℝ) < u)
    (S : Finset ℕ) (hS : ∀ r ∈ S, p ^ r * b ∈ N.divisors ∧ u < Real.log ((p ^ r * b : ℕ) : ℝ))
    (β : ℝ) :
    (∑ r ∈ S, offlineRadialEnvelope β b ^ (2 : ℕ) *
        (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ)) ≤
      varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) := by
  have hb_pos : 0 < b := Nat.pos_of_mem_divisors hbN
  have hb_left : b ∈ chainLeft N p b u := mem_chainLeft_base hbN hb_compl hu_left
  have himg_sub : S.image (fun r => p ^ r * b) ⊆ chainRight N p b u := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
    obtain ⟨hpr_div, hu_prb⟩ := hS r hr
    exact mem_chainRight_prime_pow_mul hp hpr_div hb_compl hu_prb
  rw [← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have h1 :
      (∑ k ∈ chainRight N p b u,
          (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ)) ≤
        ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
          (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun m => ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hb_left
  have h2 :
      (∑ k ∈ S.image (fun r => p ^ r * b),
          (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ)) ≤
        ∑ k ∈ chainRight N p b u,
          (offlineRadialEnvelope β b - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => sq_nonneg _)
  rw [Finset.sum_image (fun r₁ _ r₂ _ h => pow_mul_right_injective_of_prime hp hb_pos h)] at h2
  have h3 :
      (∑ r ∈ S, (offlineRadialEnvelope β b - offlineRadialEnvelope β (p ^ r * b)) ^ (2 : ℕ)) =
        ∑ r ∈ S, offlineRadialEnvelope β b ^ (2 : ℕ) *
          (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    exact offlineRadialEnvelope_pow_mul_sub_sq_eq β hp.pos hb_pos r
  linarith

/-- **All-Cut Straddling $p$-Rough Base Coercivity Bound
(`chainVariance_offlineRadialEnvelope_ge_sum_straddling_bases`):**
For any prime factor $p \in N.\text{primeFactors}$, valuation shell $r \in \mathbb{N}$, cut $u \in \mathbb{R}$,
and subset $B \subseteq N.\text{divisors}$ of $p$-coprime chain bases straddling the cut
($\forall b \in B,\; \operatorname{ordCompl}_p(b) = b \land p^r \cdot b \in N.\text{divisors} \land \log b < u < \log(p^r \cdot b)$):
$$\log p \cdot (e^{\beta r \log p} - 1)^2 \sum_{b \in B} r_\beta(b)^2
  \le \operatorname{chainVariance}(N, u, r_\beta).$$
(Classification: Candidate new theorem.) -/
theorem chainVariance_offlineRadialEnvelope_ge_sum_straddling_bases (N : ℕ) {p : ℕ} (r : ℕ)
    (hpN : p ∈ N.primeFactors) (u : ℝ)
    (B : Finset ℕ) (hB_sub : B ⊆ N.divisors)
    (hB : ∀ b ∈ B, ordCompl[p] b = b ∧ p ^ r * b ∈ N.divisors ∧
      Real.log (b : ℝ) < u ∧ u < Real.log ((p ^ r * b : ℕ) : ℝ))
    (β : ℝ) :
    Real.log p * (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ) *
        (∑ b ∈ B, offlineRadialEnvelope β b ^ (2 : ℕ)) ≤
      chainVariance N u (offlineRadialEnvelope β) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  unfold chainVariance
  have hp_le :
      Real.log p * ∑ b ∈ N.divisors,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) ≤
        ∑ q ∈ N.primeFactors, Real.log q * ∑ b ∈ N.divisors,
          varianceEnergy (chainLeft N q b u) (chainRight N q b u) (offlineRadialEnvelope β) := by
    refine Finset.single_le_sum
      (f := fun q : ℕ => Real.log (q : ℝ) * ∑ b ∈ N.divisors,
        varianceEnergy (chainLeft N q b u) (chainRight N q b u) (offlineRadialEnvelope β))
      (fun q hq => ?_) hpN
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le))
      (Finset.sum_nonneg fun b _ => varianceEnergy_nonneg _ _ _)
  have hb_sub :
      (∑ b ∈ B,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β)) ≤
        ∑ b ∈ N.divisors,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) :=
    Finset.sum_le_sum_of_subset_of_nonneg hB_sub (fun _ _ _ => varianceEnergy_nonneg _ _ _)
  have hb_term :
      (∑ b ∈ B, offlineRadialEnvelope β b ^ (2 : ℕ) *
          (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ)) ≤
        ∑ b ∈ B,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) := by
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨hb_compl, hprb_div, hub, hu_prb⟩ := hB b hb
    exact varianceEnergy_offlineRadialEnvelope_ge_prime_pow_shell
      β hp (hB_sub hb) hprb_div hb_compl hub hu_prb
  have hmul :
      Real.log p * (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ) *
          (∑ b ∈ B, offlineRadialEnvelope β b ^ (2 : ℕ)) =
        Real.log p * ∑ b ∈ B, offlineRadialEnvelope β b ^ (2 : ℕ) *
          (Real.exp (β * (r : ℝ) * Real.log p) - 1) ^ (2 : ℕ) := by
    rw [← Finset.sum_mul]
    ring
  linarith [mul_le_mul_of_nonneg_left (hb_term.trans hb_sub) hlog]

/-! ## §3. Continuous Logarithmic Pullback to `CHMDPrimeChainSource.chainDensity` and `density` -/

/-- Continuous off-line cosine wave $v_{\beta,\gamma}^{\cos}(x) = e^{-\beta x}\cos(\gamma x)$ on $\mathbb{R}$. -/
def continuousOfflineCosWave (β γ x : ℝ) : ℝ :=
  Real.exp (-β * x) * Real.cos (γ * x)

/-- Continuous off-line sine wave $v_{\beta,\gamma}^{\sin}(x) = -e^{-\beta x}\sin(\gamma x)$ on $\mathbb{R}$. -/
def continuousOfflineSinWave (β γ x : ℝ) : ℝ :=
  -Real.exp (-β * x) * Real.sin (γ * x)

/-- At every cut $u \in \mathbb{R}$ and integer $m \in \mathbb{N}$, the shifted continuous cosine
wave $v_{\beta,\gamma}^{\cos}(u - \log m)$ factors into $e^{-\beta u}$ times the discrete polar
cosine channel `polarCosChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m`.
(Classification: New formulation.) -/
theorem continuousOfflineCosWave_shift_eq (β γ u : ℝ) (m : ℕ) :
    continuousOfflineCosWave β γ (u - Real.log m) =
      Real.exp (-β * u) *
        polarCosChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
  unfold continuousOfflineCosWave polarCosChannel offlineRadialEnvelope
  have hexp : Real.exp (-β * (u - Real.log m)) =
      Real.exp (-β * u) * Real.exp (β * Real.log m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcos : Real.cos (γ * (u - Real.log m)) = Real.cos (γ * Real.log m - γ * u) := by
    rw [← Real.cos_neg]
    congr 1
    ring
  rw [hexp, hcos, mul_assoc]

/-- At every cut $u \in \mathbb{R}$ and integer $m \in \mathbb{N}$, the shifted continuous sine
wave $v_{\beta,\gamma}^{\sin}(u - \log m)$ factors into $e^{-\beta u}$ times the discrete polar
sine channel `polarSinChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m`.
(Classification: New formulation.) -/
theorem continuousOfflineSinWave_shift_eq (β γ u : ℝ) (m : ℕ) :
    continuousOfflineSinWave β γ (u - Real.log m) =
      Real.exp (-β * u) *
        polarSinChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
  unfold continuousOfflineSinWave polarSinChannel offlineRadialEnvelope
  have hexp : Real.exp (-β * (u - Real.log m)) =
      Real.exp (-β * u) * Real.exp (β * Real.log m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsin : -Real.sin (γ * (u - Real.log m)) = Real.sin (γ * Real.log m - γ * u) := by
    rw [← Real.sin_neg]
    congr 1
    ring
  calc
    -Real.exp (-β * (u - Real.log m)) * Real.sin (γ * (u - Real.log m))
        = Real.exp (-β * (u - Real.log m)) * (-Real.sin (γ * (u - Real.log m))) := by ring
    _ = Real.exp (-β * u) * (Real.exp (β * Real.log m) * Real.sin (γ * Real.log m - γ * u)) := by
        rw [hexp, hsin, mul_assoc]

/-- Scaling law for `CHMDPrimeChain.varianceEnergy`: multiplying the sequence by a constant $c$
multiplies `varianceEnergy` by $c^2$.
(Classification: Known.) -/
theorem varianceEnergy_const_mul (L R : Finset ℕ) (c : ℝ) (a : ℕ → ℝ) :
    varianceEnergy L R (fun m => c * a m) = c ^ (2 : ℕ) * varianceEnergy L R a := by
  simp only [← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Scaling law for `CHMDPrimeChain.chainVariance`: multiplying the sequence by a constant $c$
multiplies `chainVariance` by $c^2$.
(Classification: Known.) -/
theorem chainVariance_const_mul (N : ℕ) (u c : ℝ) (a : ℕ → ℝ) :
    chainVariance N u (fun m => c * a m) = c ^ (2 : ℕ) * chainVariance N u a := by
  unfold chainVariance
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hb :
      (∑ b ∈ N.divisors,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) (fun m => c * a m)) =
        c ^ (2 : ℕ) * ∑ b ∈ N.divisors,
          varianceEnergy (chainLeft N p b u) (chainRight N p b u) a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => varianceEnergy_const_mul _ _ c a
  rw [hb]
  ring

/-- Continuous two-channel CHMD `chainDensity` at `(N, p, b)` and cut $u$:
sum of `CHMDPrimeChainSource.chainDensity` on the continuous cosine and sine off-line waves. -/
def continuousOfflineTwoChannelChainDensity (N p b : ℕ) (β γ u : ℝ) : ℝ :=
  chainDensity N p b (continuousOfflineCosWave β γ) u +
    chainDensity N p b (continuousOfflineSinWave β γ) u

/-- Continuous two-channel CHMD `density` at product index $N$ and cut $u$:
sum of `CHMDPrimeChainSource.density` on the continuous cosine and sine off-line waves. -/
def continuousOfflineTwoChannelDensity (N : ℕ) (β γ u : ℝ) : ℝ :=
  density N (continuousOfflineCosWave β γ) u +
    density N (continuousOfflineSinWave β γ) u

/-- **Exact Pullback of Continuous `chainDensity` to Discrete `offlineTwoChannelVariance`
(`continuousOfflineTwoChannelChainDensity_eq`):**
At every $(N, p, b)$ and cut $u \in \mathbb{R}$,
$$\operatorname{continuousOfflineTwoChannelChainDensity}(N, p, b, \beta, \gamma, u)
  = e^{-2\beta u}\,\log p \cdot \operatorname{fiber}(N, u)\,
    \operatorname{offlineTwoChannelVariance}(\operatorname{chainLeft}(N, p, b, u),
      \operatorname{chainRight}(N, p, b, u), \beta, \theta_{\gamma, u}).$$
(Classification: New formulation.) -/
theorem continuousOfflineTwoChannelChainDensity_eq (N p b : ℕ) (β γ u : ℝ) :
    continuousOfflineTwoChannelChainDensity N p b β γ u =
      Real.exp (-2 * β * u) * Real.log p * fiber N u *
        offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) β
          (fun k => γ * Real.log k - γ * u) := by
  unfold continuousOfflineTwoChannelChainDensity chainDensity
    offlineTwoChannelVariance polarTwoChannelVariance
  have hcos : (fun m : ℕ => continuousOfflineCosWave β γ (u - Real.log m)) =
      fun m : ℕ => Real.exp (-β * u) *
        polarCosChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
    funext m
    exact continuousOfflineCosWave_shift_eq β γ u m
  have hsin : (fun m : ℕ => continuousOfflineSinWave β γ (u - Real.log m)) =
      fun m : ℕ => Real.exp (-β * u) *
        polarSinChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
    funext m
    exact continuousOfflineSinWave_shift_eq β γ u m
  have hexp : Real.exp (-β * u) ^ (2 : ℕ) = Real.exp (-2 * β * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hcos, hsin, varianceEnergy_const_mul, varianceEnergy_const_mul, hexp]
  ring

/-- **Exact Pullback of Continuous `density` to Discrete `globalOfflineChainVariance`
(`continuousOfflineTwoChannelDensity_eq`):**
At every product index $N$ and cut $u \in \mathbb{R}$,
$$\operatorname{continuousOfflineTwoChannelDensity}(N, \beta, \gamma, u)
  = e^{-2\beta u}\,\operatorname{fiber}(N, u)\,
    \operatorname{globalOfflineChainVariance}(N, u, \beta, \theta_{\gamma, u}).$$
(Classification: New formulation.) -/
theorem continuousOfflineTwoChannelDensity_eq (N : ℕ) (β γ u : ℝ) :
    continuousOfflineTwoChannelDensity N β γ u =
      Real.exp (-2 * β * u) * fiber N u *
        globalOfflineChainVariance N u β (fun k => γ * Real.log k - γ * u) := by
  unfold continuousOfflineTwoChannelDensity density globalOfflineChainVariance globalPolarChainVariance
  have hcos : (fun m : ℕ => continuousOfflineCosWave β γ (u - Real.log m)) =
      fun m : ℕ => Real.exp (-β * u) *
        polarCosChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
    funext m
    exact continuousOfflineCosWave_shift_eq β γ u m
  have hsin : (fun m : ℕ => continuousOfflineSinWave β γ (u - Real.log m)) =
      fun m : ℕ => Real.exp (-β * u) *
        polarSinChannel (offlineRadialEnvelope β) (fun k => γ * Real.log k - γ * u) m := by
    funext m
    exact continuousOfflineSinWave_shift_eq β γ u m
  have hexp : Real.exp (-β * u) ^ (2 : ℕ) = Real.exp (-2 * β * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hcos, hsin, chainVariance_const_mul, chainVariance_const_mul, hexp]
  ring

/-- **Continuous CHMD Crossing Density Hyperbolic Excess Law
(`continuousOfflineTwoChannelDensity_symmetrized_sub_critical_eq`):**
For every product index $N \in \mathbb{N}$, off-line displacement $\beta \in \mathbb{R}$, ordinate
$\gamma \in \mathbb{R}$, and cut $u \in \mathbb{R}$, the cut-normalized functional-equation pair of
continuous CHMD crossing densities exceeds the critical-line ($\beta = 0$) crossing density by:
$$\frac{1}{2}\Bigl(e^{2\beta u}\operatorname{continuousOfflineTwoChannelDensity}(N, \beta, \gamma, u) +
    e^{-2\beta u}\operatorname{continuousOfflineTwoChannelDensity}(N, -\beta, \gamma, u)\Bigr) -
  \operatorname{continuousOfflineTwoChannelDensity}(N, 0, \gamma, u)
  = \operatorname{fiber}(N, u) \cdot \left(
    \frac{1}{2}\Bigl(\operatorname{chainVariance}(N, u, r_\beta) +
      \operatorname{chainVariance}(N, u, r_{-\beta})\Bigr) +
    \operatorname{globalHyperbolicPhaseAmplification}(N, u, \beta, \theta_{\gamma, u})\right).$$
(Classification: Candidate new theorem.) -/
theorem continuousOfflineTwoChannelDensity_symmetrized_sub_critical_eq
    (N : ℕ) (β γ u : ℝ) :
    (1 / 2 : ℝ) *
        (Real.exp (2 * β * u) * continuousOfflineTwoChannelDensity N β γ u +
          Real.exp (-2 * β * u) * continuousOfflineTwoChannelDensity N (-β) γ u) -
        continuousOfflineTwoChannelDensity N 0 γ u =
      fiber N u *
        ((1 / 2 : ℝ) *
          (chainVariance N u (offlineRadialEnvelope β) +
            chainVariance N u (offlineRadialEnvelope (-β))) +
          globalHyperbolicPhaseAmplification N u β (fun k => γ * Real.log k - γ * u)) := by
  rw [continuousOfflineTwoChannelDensity_eq N β γ u,
    continuousOfflineTwoChannelDensity_eq N (-β) γ u,
    continuousOfflineTwoChannelDensity_eq N 0 γ u]
  have h1 : Real.exp (2 * β * u) * Real.exp (-2 * β * u) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h2 : Real.exp (-2 * β * u) * Real.exp (-2 * (-β) * u) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h3 : Real.exp (-2 * (0 : ℝ) * u) = 1 := by
    ring_nf
    exact Real.exp_zero
  have h0 : globalOfflineChainVariance N u 0 (fun k => γ * Real.log k - γ * u) =
      globalCriticalChainVariance N u (fun k => γ * Real.log k - γ * u) :=
    globalOfflineChainVariance_zero_eq_critical N u _
  have hsym := globalOfflineChainVariance_symmetrized_sub_critical_eq N u β
    (fun k => γ * Real.log k - γ * u)
  linear_combination
    (1 / 2 : ℝ) * globalOfflineChainVariance N u β (fun k => γ * Real.log k - γ * u) *
      fiber N u * h1 +
    (1 / 2 : ℝ) * globalOfflineChainVariance N u (-β) (fun k => γ * Real.log k - γ * u) *
      fiber N u * h2 -
    globalOfflineChainVariance N u 0 (fun k => γ * Real.log k - γ * u) * fiber N u * h3 -
    fiber N u * h0 +
    fiber N u * hsym

/-- **Ground-Cut Coercivity of the Continuous CHMD Crossing Density
(`continuousOfflineTwoChannelDensity_symmetrized_sub_critical_ge_quadratic`):**
For every positive product index $N \ge 2$ and ground cut $u \in (0, \log 2)$, the cut-normalized
symmetrized continuous CHMD crossing density exceeds the critical-line crossing density by at least
$$\frac{1}{2}\,\operatorname{fiber}(N, u)\,\beta^2 \sum_{p \in N.\text{primeFactors}} (\log p)^3.$$
(Classification: Candidate new theorem.) -/
theorem continuousOfflineTwoChannelDensity_symmetrized_sub_critical_ge_quadratic
    {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.log 2) (β γ : ℝ) :
    (1 / 2 : ℝ) * fiber N u * β ^ (2 : ℕ) *
        (∑ p ∈ N.primeFactors, Real.log p ^ (3 : ℕ)) ≤
      (1 / 2 : ℝ) *
          (Real.exp (2 * β * u) * continuousOfflineTwoChannelDensity N β γ u +
            Real.exp (-2 * β * u) * continuousOfflineTwoChannelDensity N (-β) γ u) -
        continuousOfflineTwoChannelDensity N 0 γ u := by
  rw [continuousOfflineTwoChannelDensity_symmetrized_sub_critical_eq]
  have huN : u < Real.log N := hu2.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hf_pos : 0 ≤ fiber N u :=
    (fiber_pos_on_central (by omega) hu0.le huN.le).le
  have hquad := symmetrized_chainVariance_ge_quadratic_cubic_log N hu0 hu2 β
  have hamp := globalHyperbolicPhaseAmplification_nonneg N u β (fun k => γ * Real.log k - γ * u)
  have hsum :
      (1 / 2 : ℝ) * β ^ (2 : ℕ) * (∑ p ∈ N.primeFactors, Real.log p ^ (3 : ℕ)) ≤
        (1 / 2 : ℝ) *
          (chainVariance N u (offlineRadialEnvelope β) +
            chainVariance N u (offlineRadialEnvelope (-β))) +
          globalHyperbolicPhaseAmplification N u β (fun k => γ * Real.log k - γ * u) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hf_pos
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
