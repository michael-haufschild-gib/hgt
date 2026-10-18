import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance

/-!
# Pillar XXV: Off-Line Hyperbolic Prime-Chain Excess, Polar-Phase Factorization, and Second-Order Chain Recurrence (`OffLineHyperbolicPrimeChainExcessAndCardinalRecurrence`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Complete bipartite prime-chain variance decomposition `bipartiteEnergy L R a = varianceEnergy L R a` (`RHTower.CHMDPrimeChainVariance`);
  - Functional-equation pairing of zeros $\rho = 1/2 + \beta + i\alpha \leftrightarrow 1 - \bar{\rho} = 1/2 - \beta + i\alpha$ ($\beta = \operatorname{Re}(\rho) - 1/2$);
  - Polar decomposition of two-channel oscillations $(r \cos \theta, r \sin \theta)$.
- **What existing theories leave unresolved (Uncharted Obstacle 2, Walls 9 & 13 in `hard-obstacles-summary-1810.md`):**
  In `CHMD`, Beurling–Deny contraction $v \mapsto |v|$ loses the factor of $2$ between Perron–Frobenius ($\mu < 1$) and the RH threshold ($\mu \le 1/2$), while linear explicit-formula arguments fail against the fake-weight countermodel $\zeta(s-a)\zeta(s+a)$ (Wall 9). A genuine prime-chain mechanism must show how the $p$-adic prime-chain variance `CHMDPrimeChain.varianceEnergy` distinguishes an **off-line spectral pair** ($\beta \ne 0$, radial envelope $m^{\pm \beta} = e^{\pm \beta \log m}$) from a **critical-line unitary mode** ($\beta = 0$, unit envelope $r(m) \equiv 1$).
- **New content in this module (`Candidate new theorem`):**
  1. **Exact Polar-Phase Edge Factorization (`polar_two_channel_jump_eq`, `offlineChain_two_channel_jump_eq`):**
     For any radial amplitude $r : \mathbb{N} \to \mathbb{R}$ and phase $\theta : \mathbb{N} \to \mathbb{R}$, the two-channel squared jump between nodes $m$ and $k$ factors into the pure radial jump $(r(m) - r(k))^2$ plus $r(m)r(k)$ times the unitary critical-line phase jump:
     $$\bigl(r(m)\cos\theta(m) - r(k)\cos\theta(k)\bigr)^2 + \bigl(r(m)\sin\theta(m) - r(k)\sin\theta(k)\bigr)^2 =
       \bigl(r(m) - r(k)\bigr)^2 + r(m) r(k) \Bigl(\bigl(\cos\theta(m) - \cos\theta(k)\bigr)^2 + \bigl(\sin\theta(m) - \sin\theta(k)\bigr)^2\Bigr).$$
  2. **Exact Functional-Equation Pair $(+\beta, -\beta)$ Hyperbolic Excess Over the Critical Line ($\beta = 0$) (`symmetrized_offline_jump_sub_critical_eq`, `varianceEnergy_symmetrized_offline_sub_critical_eq`, `varianceEnergy_critical_le_symmetrized_offline`):**
     For any off-line displacement $\beta \in \mathbb{R}$, let $r_\beta(m) = e^{\beta \log m}$ and $r_{-\beta}(m) = e^{-\beta \log m}$ be the functional-equation pair, and let $\beta = 0$ ($r_0 \equiv 1$) be the critical-line baseline. On **every** prime chain $(N, p, b, u)$, the functional-equation-averaged `varianceEnergy` exceeds the critical-line `varianceEnergy` by the **pure radial hyperbolic chain variance** plus a **non-negative hyperbolic-phase amplification term**:
     $$\frac{1}{2}\Bigl(\mathcal{V}_{L,R}(\beta, \theta) + \mathcal{V}_{L,R}(-\beta, \theta)\Bigr) - \mathcal{V}_{L,R}(0, \theta) =
       \frac{1}{2}\Bigl(\operatorname{varianceEnergy}(L, R, r_\beta) + \operatorname{varianceEnergy}(L, R, r_{-\beta})\Bigr) +
         \mathcal{A}_{L,R}(\beta, \theta) \ge
       \frac{1}{2}\Bigl(\operatorname{varianceEnergy}(L, R, r_\beta) + \operatorname{varianceEnergy}(L, R, r_{-\beta})\Bigr) \ge 0.$$
  3. **Strict Off-Line Hyperbolic Penalty (`strict_pos_symmetrized_offline_excess_of_mem_cut`):**
     Whenever $\beta \ne 0$ and the prime-chain cut is non-empty ($m \in \operatorname{chainLeft}(N, p, b, u)$, $k \in \operatorname{chainRight}(N, p, b, u)$), $\log m < u < \log k$ forces $e^{\beta \log m} \ne e^{\beta \log k}$, so the off-line hyperbolic excess over the critical-line baseline is **strictly positive ($> 0$)** for every phase $\theta$ (even when the phase difference $\theta(m) - \theta(k) \in 2\pi\mathbb{Z}$ makes the critical-line variance vanish!).
  4. **Exact Second-Order Prime-Chain Difference Recurrence (`offlineChainCos_step_recurrence`, `offlineChainSin_step_recurrence`):**
     Along any $p$-adic chain step $\tau = \log p$, the off-line chain wave $\Phi_{\alpha, \beta}(\theta_0, r) = e^{\beta r \tau}\cos(\theta_0 + \alpha r \tau)$ satisfies the exact constant-coefficient second-order recurrence
     $$\Phi_{\alpha, \beta}(\theta_0, r + 1) - 2 e^{\beta \tau}\cos(\alpha \tau)\,\Phi_{\alpha, \beta}(\theta_0, r) + e^{2\beta \tau}\,\Phi_{\alpha, \beta}(\theta_0, r - 1) = 0.$$
-/

open Set Finset
open RHTower.CHMDPrimeChain
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Polar-Phase Factorization of Two-Channel Chain Jumps -/

/-- Cosine channel of a polar arithmetic profile with radial envelope `r` and phase `θ`. -/
def polarCosChannel (r θ : ℕ → ℝ) (m : ℕ) : ℝ :=
  r m * Real.cos (θ m)

/-- Sine channel of a polar arithmetic profile with radial envelope `r` and phase `θ`. -/
def polarSinChannel (r θ : ℕ → ℝ) (m : ℕ) : ℝ :=
  r m * Real.sin (θ m)

/-- Unitary cosine channel on the critical line (`r ≡ 1`, `β = 0`). -/
def criticalCosChannel (θ : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.cos (θ m)

/-- Unitary sine channel on the critical line (`r ≡ 1`, `β = 0`). -/
def criticalSinChannel (θ : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.sin (θ m)

/-- Two-channel prime-chain `varianceEnergy` of a polar profile `(r cos θ, r sin θ)` across a
bipartite cut `(L, R)`. -/
def polarTwoChannelVariance (L R : Finset ℕ) (r θ : ℕ → ℝ) : ℝ :=
  varianceEnergy L R (polarCosChannel r θ) + varianceEnergy L R (polarSinChannel r θ)

/-- Two-channel prime-chain `varianceEnergy` on the critical line (`r ≡ 1`, `β = 0`). -/
def criticalTwoChannelVariance (L R : Finset ℕ) (θ : ℕ → ℝ) : ℝ :=
  varianceEnergy L R (criticalCosChannel θ) + varianceEnergy L R (criticalSinChannel θ)

/-- **Algebraic Polar-Phase Edge Factorization (`polar_two_channel_jump_algebraic`):**
For any real numbers $a, b, c_1, s_1, c_2, s_2$ satisfying $c_1^2 + s_1^2 = 1$ and
$c_2^2 + s_2^2 = 1$:
$$(a c_1 - b c_2)^2 + (a s_1 - b s_2)^2 =
  (a - b)^2 + a b \bigl((c_1 - c_2)^2 + (s_1 - s_2)^2\bigr).$$ -/
theorem polar_two_channel_jump_algebraic {a b c₁ s₁ c₂ s₂ : ℝ}
    (h₁ : c₁ ^ (2 : ℕ) + s₁ ^ (2 : ℕ) = 1) (h₂ : c₂ ^ (2 : ℕ) + s₂ ^ (2 : ℕ) = 1) :
    (a * c₁ - b * c₂) ^ (2 : ℕ) + (a * s₁ - b * s₂) ^ (2 : ℕ) =
      (a - b) ^ (2 : ℕ) + a * b * ((c₁ - c₂) ^ (2 : ℕ) + (s₁ - s₂) ^ (2 : ℕ)) := by
  linear_combination (a ^ (2 : ℕ) - a * b) * h₁ + (b ^ (2 : ℕ) - a * b) * h₂

/-- **Pointwise Polar-Phase Edge Factorization (`polar_two_channel_jump_eq`):**
For every radial envelope $r : \mathbb{N} \to \mathbb{R}$, phase $\theta : \mathbb{N} \to \mathbb{R}$,
and nodes $m, k \in \mathbb{N}$:
$$\bigl(r(m)\cos\theta(m) - r(k)\cos\theta(k)\bigr)^2 +
  \bigl(r(m)\sin\theta(m) - r(k)\sin\theta(k)\bigr)^2 =
  \bigl(r(m) - r(k)\bigr)^2 +
    r(m) r(k) \Bigl(\bigl(\cos\theta(m) - \cos\theta(k)\bigr)^2 +
      \bigl(\sin\theta(m) - \sin\theta(k)\bigr)^2\Bigr).$$ -/
theorem polar_two_channel_jump_eq (r θ : ℕ → ℝ) (m k : ℕ) :
    (polarCosChannel r θ m - polarCosChannel r θ k) ^ (2 : ℕ) +
        (polarSinChannel r θ m - polarSinChannel r θ k) ^ (2 : ℕ) =
      (r m - r k) ^ (2 : ℕ) +
        r m * r k *
          ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
            (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ)) := by
  unfold polarCosChannel polarSinChannel criticalCosChannel criticalSinChannel
  exact polar_two_channel_jump_algebraic (Real.cos_sq_add_sin_sq (θ m))
    (Real.cos_sq_add_sin_sq (θ k))

/-- **Critical-Line Unitary Phase Jump Formula (`critical_two_channel_jump_eq_two_sub_two_cos`):**
On the critical line ($r \equiv 1$), the two-channel squared jump depends only on the phase
difference $\theta(m) - \theta(k)$:
$$\bigl(\cos\theta(m) - \cos\theta(k)\bigr)^2 + \bigl(\sin\theta(m) - \sin\theta(k)\bigr)^2 =
  2\bigl(1 - \cos(\theta(m) - \theta(k))\bigr).$$ -/
theorem critical_two_channel_jump_eq_two_sub_two_cos (θ : ℕ → ℝ) (m k : ℕ) :
    (criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
        (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ) =
      2 * (1 - Real.cos (θ m - θ k)) := by
  unfold criticalCosChannel criticalSinChannel
  have h₁ := Real.cos_sq_add_sin_sq (θ m)
  have h₂ := Real.cos_sq_add_sin_sq (θ k)
  rw [Real.cos_sub]
  linear_combination h₁ + h₂

/-! ## §2. Off-Line Functional-Equation Pair $(+\beta, -\beta)$ vs. Critical-Line Baseline ($\beta = 0$) -/

/-- Off-line radial envelope $r_\beta(m) = \exp(\beta \log m)$ associated with real-part displacement
$\beta = \operatorname{Re}(\rho) - 1/2$. -/
def offlineRadialEnvelope (β : ℝ) (m : ℕ) : ℝ :=
  Real.exp (β * Real.log m)

/-- At $\beta = 0$ (on the critical line), `offlineRadialEnvelope 0 m = 1` for all $m \in \mathbb{N}$. -/
theorem offlineRadialEnvelope_zero (m : ℕ) :
    offlineRadialEnvelope 0 m = 1 := by
  simp [offlineRadialEnvelope]

/-- Pointwise positivity of `offlineRadialEnvelope β m`. -/
theorem offlineRadialEnvelope_pos (β : ℝ) (m : ℕ) :
    0 < offlineRadialEnvelope β m :=
  Real.exp_pos _

/-- Functional-equation reciprocity of the radial envelopes:
`offlineRadialEnvelope β m * offlineRadialEnvelope (-β) m = 1`. -/
theorem offlineRadialEnvelope_mul_neg (β : ℝ) (m : ℕ) :
    offlineRadialEnvelope β m * offlineRadialEnvelope (-β) m = 1 := by
  unfold offlineRadialEnvelope
  rw [← Real.exp_add]
  have h0 : β * Real.log (m : ℝ) + -β * Real.log (m : ℝ) = 0 := by ring
  rw [h0, Real.exp_zero]

/-- Two-channel prime-chain `varianceEnergy` for an off-line spectral parameter with displacement
$\beta \in \mathbb{R}$ and phase profile $\theta : \mathbb{N} \to \mathbb{R}$. -/
def offlineTwoChannelVariance (L R : Finset ℕ) (β : ℝ) (θ : ℕ → ℝ) : ℝ :=
  polarTwoChannelVariance L R (offlineRadialEnvelope β) θ

/-- At $\beta = 0$, `offlineTwoChannelVariance` coincides identically with the critical-line
unitary variance `criticalTwoChannelVariance`. -/
theorem offlineTwoChannelVariance_zero_eq_critical (L R : Finset ℕ) (θ : ℕ → ℝ) :
    offlineTwoChannelVariance L R 0 θ = criticalTwoChannelVariance L R θ := by
  unfold offlineTwoChannelVariance polarTwoChannelVariance criticalTwoChannelVariance
  have hcos : polarCosChannel (offlineRadialEnvelope 0) θ = criticalCosChannel θ := by
    ext m; simp [polarCosChannel, criticalCosChannel, offlineRadialEnvelope_zero]
  have hsin : polarSinChannel (offlineRadialEnvelope 0) θ = criticalSinChannel θ := by
    ext m; simp [polarSinChannel, criticalSinChannel, offlineRadialEnvelope_zero]
  rw [hcos, hsin]

/-- Hyperbolic-phase amplification term across a bipartite prime-chain cut `(L, R)`:
$$\mathcal{A}_{L,R}(\beta, \theta) :=
  \sum_{m \in L} \sum_{k \in R}
    \frac{1}{2}\Bigl(e^{\beta(\log m + \log k)/2} - e^{-\beta(\log m + \log k)/2}\Bigr)^2
      \Bigl(\bigl(\cos\theta(m) - \cos\theta(k)\bigr)^2 + \bigl(\sin\theta(m) - \sin\theta(k)\bigr)^2\Bigr).$$ -/
def offlineHyperbolicPhaseAmplification (L R : Finset ℕ) (β : ℝ) (θ : ℕ → ℝ) : ℝ :=
  ∑ m ∈ L, ∑ k ∈ R,
    ((1 / 2 : ℝ) *
      (Real.exp (β * (Real.log m + Real.log k) / 2) -
        Real.exp (-(β * (Real.log m + Real.log k) / 2))) ^ (2 : ℕ)) *
      ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
        (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ))

/-- Non-negativity of the hyperbolic-phase amplification term `offlineHyperbolicPhaseAmplification`. -/
theorem offlineHyperbolicPhaseAmplification_nonneg (L R : Finset ℕ) (β : ℝ) (θ : ℕ → ℝ) :
    0 ≤ offlineHyperbolicPhaseAmplification L R β θ := by
  unfold offlineHyperbolicPhaseAmplification
  refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ => ?_
  positivity

/-- Identity for the hyperbolic multiplier:
`(exp x + exp (-x)) / 2 - 1 = (1 / 2) * (exp (x / 2) - exp (-(x / 2))) ^ 2`. -/
theorem exp_add_exp_neg_div_two_sub_one (x : ℝ) :
    (Real.exp x + Real.exp (-x)) / 2 - 1 =
      (1 / 2 : ℝ) * (Real.exp (x / 2) - Real.exp (-(x / 2))) ^ (2 : ℕ) := by
  have h1 : Real.exp (x / 2) ^ (2 : ℕ) = Real.exp x := by
    rw [sq, ← Real.exp_add, add_halves]
  have h2 : Real.exp (-(x / 2)) ^ (2 : ℕ) = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination -(1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2 + h3

/-- **Pointwise Symmetrized Off-Line Jump Excess Identity (`symmetrized_offline_jump_sub_critical_eq`):**
For every off-line displacement $\beta \in \mathbb{R}$, phase profile $\theta : \mathbb{N} \to \mathbb{R}$,
and nodes $m, k \in \mathbb{N}$, the functional-equation average of the $(+\beta)$ and $(-\beta)$
two-channel jumps minus the critical-line ($\beta = 0$) jump decomposes into the sum of squares:
$$\frac{1}{2}\Bigl(\Delta E_{+\beta}(m, k) + \Delta E_{-\beta}(m, k)\Bigr) - \Delta E_0(m, k) =
  \frac{\bigl(r_\beta(m) - r_\beta(k)\bigr)^2 + \bigl(r_{-\beta}(m) - r_{-\beta}(k)\bigr)^2}{2} +
    \frac{1}{2}\Bigl(e^{\beta(\log m + \log k)/2} - e^{-\beta(\log m + \log k)/2}\Bigr)^2 \Delta E_0(m, k).$$ -/
theorem symmetrized_offline_jump_sub_critical_eq (β : ℝ) (θ : ℕ → ℝ) (m k : ℕ) :
    (1 / 2 : ℝ) *
        (((polarCosChannel (offlineRadialEnvelope β) θ m -
            polarCosChannel (offlineRadialEnvelope β) θ k) ^ (2 : ℕ) +
          (polarSinChannel (offlineRadialEnvelope β) θ m -
            polarSinChannel (offlineRadialEnvelope β) θ k) ^ (2 : ℕ)) +
         ((polarCosChannel (offlineRadialEnvelope (-β)) θ m -
            polarCosChannel (offlineRadialEnvelope (-β)) θ k) ^ (2 : ℕ) +
          (polarSinChannel (offlineRadialEnvelope (-β)) θ m -
            polarSinChannel (offlineRadialEnvelope (-β)) θ k) ^ (2 : ℕ))) -
        ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
          (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ)) =
      (1 / 2 : ℝ) *
        ((offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) +
          (offlineRadialEnvelope (-β) m - offlineRadialEnvelope (-β) k) ^ (2 : ℕ)) +
      ((1 / 2 : ℝ) *
        (Real.exp (β * (Real.log m + Real.log k) / 2) -
          Real.exp (-(β * (Real.log m + Real.log k) / 2))) ^ (2 : ℕ)) *
        ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
          (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ)) := by
  rw [polar_two_channel_jump_eq (offlineRadialEnvelope β) θ m k,
    polar_two_channel_jump_eq (offlineRadialEnvelope (-β)) θ m k]
  have hprod_pos : offlineRadialEnvelope β m * offlineRadialEnvelope β k =
      Real.exp (β * (Real.log m + Real.log k)) := by
    unfold offlineRadialEnvelope
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod_neg : offlineRadialEnvelope (-β) m * offlineRadialEnvelope (-β) k =
      Real.exp (-(β * (Real.log m + Real.log k))) := by
    unfold offlineRadialEnvelope
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp := exp_add_exp_neg_div_two_sub_one (β * (Real.log m + Real.log k))
  rw [hprod_pos, hprod_neg, ← hexp]
  ring

/-- **Exact Off-Line Hyperbolic Prime-Chain Variance Decomposition
(`varianceEnergy_symmetrized_offline_sub_critical_eq`):**
For every bipartite prime-chain cut `(L, R)`, off-line displacement $\beta \in \mathbb{R}$, and
phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\frac{1}{2}\Bigl(\operatorname{offlineTwoChannelVariance}(L, R, \beta, \theta) +
    \operatorname{offlineTwoChannelVariance}(L, R, -\beta, \theta)\Bigr) -
  \operatorname{criticalTwoChannelVariance}(L, R, \theta) =
  \frac{1}{2}\Bigl(\operatorname{varianceEnergy}(L, R, r_\beta) +
    \operatorname{varianceEnergy}(L, R, r_{-\beta})\Bigr) +
  \operatorname{offlineHyperbolicPhaseAmplification}(L, R, \beta, \theta).$$ -/
theorem varianceEnergy_symmetrized_offline_sub_critical_eq
    (L R : Finset ℕ) (β : ℝ) (θ : ℕ → ℝ) :
    (1 / 2 : ℝ) *
        (offlineTwoChannelVariance L R β θ + offlineTwoChannelVariance L R (-β) θ) -
        criticalTwoChannelVariance L R θ =
      (1 / 2 : ℝ) *
        (varianceEnergy L R (offlineRadialEnvelope β) +
          varianceEnergy L R (offlineRadialEnvelope (-β))) +
        offlineHyperbolicPhaseAmplification L R β θ := by
  unfold offlineTwoChannelVariance polarTwoChannelVariance criticalTwoChannelVariance
    offlineHyperbolicPhaseAmplification
  simp only [← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have hsum :
      (∑ m ∈ L, ∑ k ∈ R,
        ((1 / 2 : ℝ) *
          (((polarCosChannel (offlineRadialEnvelope β) θ m -
              polarCosChannel (offlineRadialEnvelope β) θ k) ^ (2 : ℕ) +
            (polarSinChannel (offlineRadialEnvelope β) θ m -
              polarSinChannel (offlineRadialEnvelope β) θ k) ^ (2 : ℕ)) +
           ((polarCosChannel (offlineRadialEnvelope (-β)) θ m -
              polarCosChannel (offlineRadialEnvelope (-β)) θ k) ^ (2 : ℕ) +
            (polarSinChannel (offlineRadialEnvelope (-β)) θ m -
              polarSinChannel (offlineRadialEnvelope (-β)) θ k) ^ (2 : ℕ))) -
          ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
            (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ)))) =
      ∑ m ∈ L, ∑ k ∈ R,
        ((1 / 2 : ℝ) *
          ((offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) +
            (offlineRadialEnvelope (-β) m - offlineRadialEnvelope (-β) k) ^ (2 : ℕ)) +
        ((1 / 2 : ℝ) *
          (Real.exp (β * (Real.log m + Real.log k) / 2) -
            Real.exp (-(β * (Real.log m + Real.log k) / 2))) ^ (2 : ℕ)) *
          ((criticalCosChannel θ m - criticalCosChannel θ k) ^ (2 : ℕ) +
            (criticalSinChannel θ m - criticalSinChannel θ k) ^ (2 : ℕ))) :=
    Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun k _ => symmetrized_offline_jump_sub_critical_eq β θ m k
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

/-- **Universal Off-Line Hyperbolic Dominance Over the Critical-Line Unitary Baseline
(`varianceEnergy_critical_le_symmetrized_offline`):**
For every prime-chain cut `(L, R)`, displacement $\beta \in \mathbb{R}$, and phase profile
$\theta : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{criticalTwoChannelVariance}(L, R, \theta) +
  \frac{1}{2}\Bigl(\operatorname{varianceEnergy}(L, R, r_\beta) +
    \operatorname{varianceEnergy}(L, R, r_{-\beta})\Bigr) \le
  \frac{1}{2}\Bigl(\operatorname{offlineTwoChannelVariance}(L, R, \beta, \theta) +
    \operatorname{offlineTwoChannelVariance}(L, R, -\beta, \theta)\Bigr).$$ -/
theorem varianceEnergy_critical_le_symmetrized_offline
    (L R : Finset ℕ) (β : ℝ) (θ : ℕ → ℝ) :
    criticalTwoChannelVariance L R θ +
        (1 / 2 : ℝ) *
          (varianceEnergy L R (offlineRadialEnvelope β) +
            varianceEnergy L R (offlineRadialEnvelope (-β))) ≤
      (1 / 2 : ℝ) *
        (offlineTwoChannelVariance L R β θ + offlineTwoChannelVariance L R (-β) θ) := by
  have hid := varianceEnergy_symmetrized_offline_sub_critical_eq L R β θ
  have hamp := offlineHyperbolicPhaseAmplification_nonneg L R β θ
  linarith

/-! ## §3. Strict Off-Line Hyperbolic Penalty on Every Active Prime-Chain Cut ($\beta \ne 0$) -/

/-- Whenever $\beta \ne 0$ and $\log m < \log k$, the off-line radial envelope separates $m$ and $k$:
$(r_\beta(m) - r_\beta(k))^2 > 0$. -/
theorem offlineRadialEnvelope_sub_sq_pos_of_log_lt {β : ℝ} (hβ : β ≠ 0)
    {m k : ℕ} (hlog : Real.log (m : ℝ) < Real.log (k : ℝ)) :
    0 < (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) := by
  have hne : offlineRadialEnvelope β m ≠ offlineRadialEnvelope β k := by
    unfold offlineRadialEnvelope
    intro heq
    have hinj := Real.exp_injective heq
    have hdiff : β * (Real.log (k : ℝ) - Real.log (m : ℝ)) = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with hβ0 | hlog0
    · exact hβ hβ0
    · linarith
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)

/-- **Strict Positivity of Radial Prime-Chain `varianceEnergy` for Off-Line Modes
(`varianceEnergy_offlineRadialEnvelope_pos_of_mem_cut`):**
For every off-line displacement $\beta \ne 0$ and every prime-chain cut
$(L, R) = (\operatorname{chainLeft}(N, p, b, u), \operatorname{chainRight}(N, p, b, u))$
containing at least one left node $m_0 \in L$ and one right node $k_0 \in R$:
$$0 < \operatorname{varianceEnergy}\bigl(\operatorname{chainLeft}(N, p, b, u),\,
  \operatorname{chainRight}(N, p, b, u),\, r_\beta\bigr).$$ -/
theorem varianceEnergy_offlineRadialEnvelope_pos_of_mem_cut {N p b : ℕ} {u β : ℝ}
    (hβ : β ≠ 0) {m₀ k₀ : ℕ}
    (hm₀ : m₀ ∈ chainLeft N p b u) (hk₀ : k₀ ∈ chainRight N p b u) :
    0 < varianceEnergy (chainLeft N p b u) (chainRight N p b u) (offlineRadialEnvelope β) := by
  rw [← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have hlog : Real.log (m₀ : ℝ) < Real.log (k₀ : ℝ) := by
    unfold chainLeft at hm₀
    unfold chainRight at hk₀
    simp only [Finset.mem_filter] at hm₀ hk₀
    linarith [hm₀.2.2, hk₀.2.2]
  have hpos_term : 0 < (offlineRadialEnvelope β m₀ - offlineRadialEnvelope β k₀) ^ (2 : ℕ) :=
    offlineRadialEnvelope_sub_sq_pos_of_log_lt hβ hlog
  have hle_inner : (offlineRadialEnvelope β m₀ - offlineRadialEnvelope β k₀) ^ (2 : ℕ) ≤
      ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m₀ - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun k => (offlineRadialEnvelope β m₀ - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun k _ => sq_nonneg _) hk₀
  have hle_outer : (∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m₀ - offlineRadialEnvelope β k) ^ (2 : ℕ)) ≤
      ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun m => ∑ k ∈ chainRight N p b u,
        (offlineRadialEnvelope β m - offlineRadialEnvelope β k) ^ (2 : ℕ))
      (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hm₀
  linarith

/-- **Strict Off-Line Hyperbolic Excess Over the Critical-Line Baseline
(`strict_pos_symmetrized_offline_excess_of_mem_cut`):**
Whenever $\beta \ne 0$ and the prime-chain cut $(L, R) = (\operatorname{chainLeft}(N, p, b, u), \operatorname{chainRight}(N, p, b, u))$
is non-empty ($m_0 \in L, k_0 \in R$), for **every** phase profile $\theta : \mathbb{N} \to \mathbb{R}$:
$$\operatorname{criticalTwoChannelVariance}(L, R, \theta) <
  \frac{1}{2}\Bigl(\operatorname{offlineTwoChannelVariance}(L, R, \beta, \theta) +
    \operatorname{offlineTwoChannelVariance}(L, R, -\beta, \theta)\Bigr).$$ -/
theorem strict_pos_symmetrized_offline_excess_of_mem_cut {N p b : ℕ} {u β : ℝ}
    (hβ : β ≠ 0) (θ : ℕ → ℝ) {m₀ k₀ : ℕ}
    (hm₀ : m₀ ∈ chainLeft N p b u) (hk₀ : k₀ ∈ chainRight N p b u) :
    criticalTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) θ <
      (1 / 2 : ℝ) *
        (offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) β θ +
          offlineTwoChannelVariance (chainLeft N p b u) (chainRight N p b u) (-β) θ) := by
  have hdom := varianceEnergy_critical_le_symmetrized_offline
    (chainLeft N p b u) (chainRight N p b u) β θ
  have hpos₁ := varianceEnergy_offlineRadialEnvelope_pos_of_mem_cut hβ hm₀ hk₀
  have hpos₂ : 0 ≤ varianceEnergy (chainLeft N p b u) (chainRight N p b u)
      (offlineRadialEnvelope (-β)) := varianceEnergy_nonneg _ _ _
  linarith

/-! ## §4. Exact Second-Order Prime-Chain Difference Recurrence (Cardinal Commutator Law) -/

/-- Continuous off-line chain wave cosine component $\Phi_{\alpha, \beta}(\theta_0, t) = e^{\beta t} \cos(\theta_0 + \alpha t)$. -/
def offlineChainWaveCos (α β θ₀ t : ℝ) : ℝ :=
  Real.exp (β * t) * Real.cos (θ₀ + α * t)

/-- Continuous off-line chain wave sine component $\Psi_{\alpha, \beta}(\theta_0, t) = e^{\beta t} \sin(\theta_0 + \alpha t)$. -/
def offlineChainWaveSin (α β θ₀ t : ℝ) : ℝ :=
  Real.exp (β * t) * Real.sin (θ₀ + α * t)

/-- **Exact Second-Order Prime-Chain Difference Recurrence for `offlineChainWaveCos`
(`offlineChainWaveCos_step_recurrence`):**
Along any arithmetic progression of logarithmic positions $t - \tau, t, t + \tau$ (such as
consecutive powers $p^{r-1} b, p^r b, p^{r+1} b$ along a $p$-adic chain with $\tau = \log p$),
`offlineChainWaveCos α β θ₀` satisfies the exact constant-coefficient second-order recurrence:
$$\Phi_{\alpha, \beta}(\theta_0, t + \tau) -
  2 e^{\beta \tau} \cos(\alpha \tau)\,\Phi_{\alpha, \beta}(\theta_0, t) +
  e^{2\beta \tau}\,\Phi_{\alpha, \beta}(\theta_0, t - \tau) = 0.$$ -/
theorem offlineChainWaveCos_step_recurrence (α β θ₀ t τ : ℝ) :
    offlineChainWaveCos α β θ₀ (t + τ) -
      2 * Real.exp (β * τ) * Real.cos (α * τ) * offlineChainWaveCos α β θ₀ t +
      Real.exp (2 * β * τ) * offlineChainWaveCos α β θ₀ (t - τ) = 0 := by
  unfold offlineChainWaveCos
  have hexp_add : Real.exp (β * (t + τ)) = Real.exp (β * t) * Real.exp (β * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_sub : Real.exp (2 * β * τ) * Real.exp (β * (t - τ)) =
      Real.exp (β * t) * Real.exp (β * τ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcos_add : Real.cos (θ₀ + α * (t + τ)) =
      Real.cos (θ₀ + α * t) * Real.cos (α * τ) -
        Real.sin (θ₀ + α * t) * Real.sin (α * τ) := by
    rw [show θ₀ + α * (t + τ) = (θ₀ + α * t) + α * τ by ring, Real.cos_add]
  have hcos_sub : Real.cos (θ₀ + α * (t - τ)) =
      Real.cos (θ₀ + α * t) * Real.cos (α * τ) +
        Real.sin (θ₀ + α * t) * Real.sin (α * τ) := by
    rw [show θ₀ + α * (t - τ) = (θ₀ + α * t) - α * τ by ring, Real.cos_sub]
  rw [hexp_add, ← mul_assoc (Real.exp (2 * β * τ)), hexp_sub, hcos_add, hcos_sub]
  ring

/-- **Exact Second-Order Prime-Chain Difference Recurrence for `offlineChainWaveSin`
(`offlineChainWaveSin_step_recurrence`):**
Along any logarithmic step $\tau$, `offlineChainWaveSin α β θ₀` satisfies the identical
second-order recurrence:
$$\Psi_{\alpha, \beta}(\theta_0, t + \tau) -
  2 e^{\beta \tau} \cos(\alpha \tau)\,\Psi_{\alpha, \beta}(\theta_0, t) +
  e^{2\beta \tau}\,\Psi_{\alpha, \beta}(\theta_0, t - \tau) = 0.$$ -/
theorem offlineChainWaveSin_step_recurrence (α β θ₀ t τ : ℝ) :
    offlineChainWaveSin α β θ₀ (t + τ) -
      2 * Real.exp (β * τ) * Real.cos (α * τ) * offlineChainWaveSin α β θ₀ t +
      Real.exp (2 * β * τ) * offlineChainWaveSin α β θ₀ (t - τ) = 0 := by
  unfold offlineChainWaveSin
  have hexp_add : Real.exp (β * (t + τ)) = Real.exp (β * t) * Real.exp (β * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_sub : Real.exp (2 * β * τ) * Real.exp (β * (t - τ)) =
      Real.exp (β * t) * Real.exp (β * τ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsin_add : Real.sin (θ₀ + α * (t + τ)) =
      Real.sin (θ₀ + α * t) * Real.cos (α * τ) +
        Real.cos (θ₀ + α * t) * Real.sin (α * τ) := by
    rw [show θ₀ + α * (t + τ) = (θ₀ + α * t) + α * τ by ring, Real.sin_add]
  have hsin_sub : Real.sin (θ₀ + α * (t - τ)) =
      Real.sin (θ₀ + α * t) * Real.cos (α * τ) -
        Real.cos (θ₀ + α * t) * Real.sin (α * τ) := by
    rw [show θ₀ + α * (t - τ) = (θ₀ + α * t) - α * τ by ring, Real.sin_sub]
  rw [hexp_add, ← mul_assoc (Real.exp (2 * β * τ)), hexp_sub, hsin_add, hsin_sub]
  ring

/-- **Phase-Invariant Single-Step Casimir / Wronskian Identity Along a Prime Chain
(`offlineChainWave_step_casimir_eq`):**
For every $\alpha, \beta, \theta_0, t, \tau \in \mathbb{R}$, the two-channel squared step from $t$
to $t + \tau$ is completely independent of the base phase $\theta_0$ and factors as:
$$\bigl(\Phi_{\alpha, \beta}(\theta_0, t + \tau) - \Phi_{\alpha, \beta}(\theta_0, t)\bigr)^2 +
  \bigl(\Psi_{\alpha, \beta}(\theta_0, t + \tau) - \Psi_{\alpha, \beta}(\theta_0, t)\bigr)^2 =
  e^{2\beta t} \Bigl(\bigl(e^{\beta \tau} - 1\bigr)^2 + 2 e^{\beta \tau}\bigl(1 - \cos(\alpha \tau)\bigr)\Bigr).$$ -/
theorem offlineChainWave_step_casimir_eq (α β θ₀ t τ : ℝ) :
    (offlineChainWaveCos α β θ₀ (t + τ) - offlineChainWaveCos α β θ₀ t) ^ (2 : ℕ) +
        (offlineChainWaveSin α β θ₀ (t + τ) - offlineChainWaveSin α β θ₀ t) ^ (2 : ℕ) =
      Real.exp (β * t) ^ (2 : ℕ) *
        ((Real.exp (β * τ) - 1) ^ (2 : ℕ) +
          2 * Real.exp (β * τ) * (1 - Real.cos (α * τ))) := by
  unfold offlineChainWaveCos offlineChainWaveSin
  have hexp_add : Real.exp (β * (t + τ)) = Real.exp (β * t) * Real.exp (β * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₁ := Real.cos_sq_add_sin_sq (θ₀ + α * (t + τ))
  have h₂ := Real.cos_sq_add_sin_sq (θ₀ + α * t)
  have hsub : Real.cos (α * τ) =
      Real.cos (θ₀ + α * (t + τ)) * Real.cos (θ₀ + α * t) +
        Real.sin (θ₀ + α * (t + τ)) * Real.sin (θ₀ + α * t) := by
    rw [show α * τ = (θ₀ + α * (t + τ)) - (θ₀ + α * t) by ring, Real.cos_sub]
  rw [hexp_add, hsub]
  linear_combination
    (Real.exp (β * t) * Real.exp (β * τ)) ^ (2 : ℕ) * h₁ +
      Real.exp (β * t) ^ (2 : ℕ) * h₂

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
