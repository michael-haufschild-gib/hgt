import GaloisForLFunctions.TransHorizonIncidenceMechanics.AllCutPrimeChainCoercivityAndContinuousDensityBridge

/-!
# Compactly Windowed Off-Line Prime-Chain Integrals and Two-Point Ground-Cut Coercivity

This module advances **Steps 1 and 2** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`) from pointwise logarithmic cut
densities to compactly supported test profiles (`HasCompactSupport`) and their integrated prime-chain
variances `CHMDPrimeChainSource.chainIntegral` and `primeCrossing`:

1. **Windowed Continuous Off-Line Wave Pair (`windowedOfflineCosWave`, `windowedOfflineSinWave`, `windowedOfflineRadialWave`)**:
   - Multiplies the continuous off-line waves $v_{\beta,\gamma}^{\cos}(x) = e^{-\beta x}\cos(\gamma x)$,
     $v_{\beta,\gamma}^{\sin}(x) = -e^{-\beta x}\sin(\gamma x)$, and the radial profile
     $v_{\beta,0}(x) = e^{-\beta x}$ by a continuous compactly supported window $w : \mathbb{R} \to \mathbb{R}$.
   - Establishes continuity, compact support, and unconditional summability of `chainIntegral` to
     `∑' d : ℕ, primeCrossing` via `CHMDPrimeChainSource.complete_chain_hasSum`.

2. **Universal Non-Negative Window Phase Dominance (`windowed_offline_two_channel_jump_eq`, `windowed_chainDensity_two_channel_ge_radial`, `windowed_chainIntegral_two_channel_ge_radial`)**:
   - Proves that for **any** window $w : \mathbb{R} \to \mathbb{R}$, the two-channel jump of
     $(v_{\beta,\gamma,w}^{\cos}, v_{\beta,\gamma,w}^{\sin})$ across $(m, k)$ equals the radial jump
     $(v_{\beta,0,w}(u - \log m) - v_{\beta,0,w}(u - \log k))^2$ plus the phase interaction
     $v_{\beta,0,w}(u - \log m) v_{\beta,0,w}(u - \log k) \Delta\Phi_{\theta_{\gamma,u}}(m, k)$.
   - Whenever $w \ge 0$ on $\mathbb{R}$, $v_{\beta,0,w} \ge 0$ everywhere, so the two-channel
     `chainDensity`, `density`, and `chainIntegral` dominate the pure radial windowed functionals
     pointwise and in integral, without requiring $w$ to be locally constant.

3. **Two-Point Plateau Ground-Cut Coercivity (`windowed_varianceEnergy_ground_cut_ge_prime_step`, `windowed_density_ground_cut_ge_sum_primeFactors`, `windowed_two_channel_density_symmetrized_ground_cut_ge_quadratic`)**:
   - Because `bipartiteEnergy` is a sum of squares over $(m, k) \in L \times R$, the ground-step
     lower bound at $(m, k) = (1, p)$ on $u \in (0, \log 2)$ requires $w$ to equal $1$ **only at the
     two evaluation points** $u$ and $u - \log p$ (`w u = 1` and `w (u - Real.log p) = 1`),
     delivering the full $e^{-2\beta u}(e^{\beta \log p} - 1)^2$ and quadratic $\beta^2 (\log p)^3$
     lower bounds for compactly supported profiles.
-/

open Finset Real MeasureTheory Set
open RHTower.CHMDPrimeChain RHTower.CHMDPrimeChainSource
open RHTower.CHMDPrimeCuts RHTower.PhiDivisorEnergy
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Windowed Continuous Off-Line Wave Pair & Compact-Support Summability -/

/-- Windowed continuous off-line cosine wave
$v_{\beta,\gamma,w}^{\cos}(x) = w(x) e^{-\beta x}\cos(\gamma x)$. -/
def windowedOfflineCosWave (w : ℝ → ℝ) (β γ x : ℝ) : ℝ :=
  w x * continuousOfflineCosWave β γ x

/-- Windowed continuous off-line sine wave
$v_{\beta,\gamma,w}^{\sin}(x) = -w(x) e^{-\beta x}\sin(\gamma x)$. -/
def windowedOfflineSinWave (w : ℝ → ℝ) (β γ x : ℝ) : ℝ :=
  w x * continuousOfflineSinWave β γ x

/-- Windowed continuous radial off-line wave
$v_{\beta,0,w}(x) = w(x) e^{-\beta x}$. -/
def windowedOfflineRadialWave (w : ℝ → ℝ) (β x : ℝ) : ℝ :=
  w x * Real.exp (-β * x)

/-- Continuity of `windowedOfflineCosWave w β γ` for continuous `w`.
(Classification: Known.) -/
theorem continuous_windowedOfflineCosWave {w : ℝ → ℝ} (hw : Continuous w) (β γ : ℝ) :
    Continuous (windowedOfflineCosWave w β γ) := by
  unfold windowedOfflineCosWave continuousOfflineCosWave
  fun_prop

/-- Continuity of `windowedOfflineSinWave w β γ` for continuous `w`.
(Classification: Known.) -/
theorem continuous_windowedOfflineSinWave {w : ℝ → ℝ} (hw : Continuous w) (β γ : ℝ) :
    Continuous (windowedOfflineSinWave w β γ) := by
  unfold windowedOfflineSinWave continuousOfflineSinWave
  fun_prop

/-- Continuity of `windowedOfflineRadialWave w β` for continuous `w`.
(Classification: Known.) -/
theorem continuous_windowedOfflineRadialWave {w : ℝ → ℝ} (hw : Continuous w) (β : ℝ) :
    Continuous (windowedOfflineRadialWave w β) := by
  unfold windowedOfflineRadialWave
  fun_prop

/-- Compact support of `windowedOfflineCosWave w β γ` when `HasCompactSupport w`.
(Classification: Known.) -/
theorem hasCompactSupport_windowedOfflineCosWave {w : ℝ → ℝ} (hwc : HasCompactSupport w)
    (β γ : ℝ) :
    HasCompactSupport (windowedOfflineCosWave w β γ) :=
  hwc.mul_right

/-- Compact support of `windowedOfflineSinWave w β γ` when `HasCompactSupport w`.
(Classification: Known.) -/
theorem hasCompactSupport_windowedOfflineSinWave {w : ℝ → ℝ} (hwc : HasCompactSupport w)
    (β γ : ℝ) :
    HasCompactSupport (windowedOfflineSinWave w β γ) :=
  hwc.mul_right

/-- Compact support of `windowedOfflineRadialWave w β` when `HasCompactSupport w`.
(Classification: Known.) -/
theorem hasCompactSupport_windowedOfflineRadialWave {w : ℝ → ℝ} (hwc : HasCompactSupport w)
    (β : ℝ) :
    HasCompactSupport (windowedOfflineRadialWave w β) :=
  hwc.mul_right

/-- Unconditional prime-chain summation for `windowedOfflineCosWave`, `windowedOfflineSinWave`,
and `windowedOfflineRadialWave`.
(Classification: Corollary of `CHMDPrimeChainSource.complete_chain_hasSum`.) -/
theorem windowedOfflineWaves_complete_chain_hasSum {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (β γ : ℝ) :
    HasSum (chainIntegral (windowedOfflineCosWave w β γ))
        (∑' d : ℕ, primeCrossing (windowedOfflineCosWave w β γ) d) ∧
      HasSum (chainIntegral (windowedOfflineSinWave w β γ))
        (∑' d : ℕ, primeCrossing (windowedOfflineSinWave w β γ) d) ∧
      HasSum (chainIntegral (windowedOfflineRadialWave w β))
        (∑' d : ℕ, primeCrossing (windowedOfflineRadialWave w β) d) :=
  ⟨complete_chain_hasSum (continuous_windowedOfflineCosWave hw β γ)
      (hasCompactSupport_windowedOfflineCosWave hwc β γ),
   complete_chain_hasSum (continuous_windowedOfflineSinWave hw β γ)
      (hasCompactSupport_windowedOfflineSinWave hwc β γ),
   complete_chain_hasSum (continuous_windowedOfflineRadialWave hw β)
      (hasCompactSupport_windowedOfflineRadialWave hwc β)⟩

/-! ## §2. Universal Non-Negative Window Phase Dominance -/

/-- Polar-channel representation of the windowed cosine wave at shift $u - \log m$:
`windowedOfflineCosWave w β γ (u - log m) = windowedOfflineRadialWave w β (u - log m) * cos (continuousPhaseProfile γ u m)`. -/
theorem windowedOfflineCosWave_sub_log_eq (w : ℝ → ℝ) (β γ u : ℝ) (m : ℕ) :
    windowedOfflineCosWave w β γ (u - Real.log m) =
      polarCosChannel (fun k : ℕ => windowedOfflineRadialWave w β (u - Real.log k))
        (continuousPhaseProfile γ u) m := by
  unfold windowedOfflineCosWave continuousOfflineCosWave polarCosChannel
    windowedOfflineRadialWave continuousPhaseProfile
  rw [Real.cos_neg]
  ring

/-- Polar-channel representation of the windowed sine wave at shift $u - \log m$:
`windowedOfflineSinWave w β γ (u - log m) = windowedOfflineRadialWave w β (u - log m) * sin (continuousPhaseProfile γ u m)`. -/
theorem windowedOfflineSinWave_sub_log_eq (w : ℝ → ℝ) (β γ u : ℝ) (m : ℕ) :
    windowedOfflineSinWave w β γ (u - Real.log m) =
      polarSinChannel (fun k : ℕ => windowedOfflineRadialWave w β (u - Real.log k))
        (continuousPhaseProfile γ u) m := by
  unfold windowedOfflineSinWave continuousOfflineSinWave polarSinChannel
    windowedOfflineRadialWave continuousPhaseProfile
  rw [Real.sin_neg]
  ring

/-- **Pointwise Windowed Two-Channel Jump Decomposition (`windowed_offline_two_channel_jump_eq`):**
For any window $w : \mathbb{R} \to \mathbb{R}$, parameters $\beta, \gamma, u \in \mathbb{R}$, and
divisors $m, k \in \mathbb{N}$:
$$\bigl(v_{\beta,\gamma,w}^{\cos}(u - \log m) - v_{\beta,\gamma,w}^{\cos}(u - \log k)\bigr)^2 +
  \bigl(v_{\beta,\gamma,w}^{\sin}(u - \log m) - v_{\beta,\gamma,w}^{\sin}(u - \log k)\bigr)^2$$
$$= \bigl(v_{\beta,0,w}(u - \log m) - v_{\beta,0,w}(u - \log k)\bigr)^2 +
  v_{\beta,0,w}(u - \log m)\,v_{\beta,0,w}(u - \log k)\,
    \Bigl(\bigl(\cos\theta_{\gamma,u}(m) - \cos\theta_{\gamma,u}(k)\bigr)^2 +
      \bigl(\sin\theta_{\gamma,u}(m) - \sin\theta_{\gamma,u}(k)\bigr)^2\Bigr).$$
(Classification: New formulation.) -/
theorem windowed_offline_two_channel_jump_eq (w : ℝ → ℝ) (β γ u : ℝ) (m k : ℕ) :
    (windowedOfflineCosWave w β γ (u - Real.log m) -
        windowedOfflineCosWave w β γ (u - Real.log k)) ^ (2 : ℕ) +
      (windowedOfflineSinWave w β γ (u - Real.log m) -
        windowedOfflineSinWave w β γ (u - Real.log k)) ^ (2 : ℕ) =
      (windowedOfflineRadialWave w β (u - Real.log m) -
        windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ) +
      windowedOfflineRadialWave w β (u - Real.log m) *
        windowedOfflineRadialWave w β (u - Real.log k) *
        ((criticalCosChannel (continuousPhaseProfile γ u) m -
            criticalCosChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ) +
          (criticalSinChannel (continuousPhaseProfile γ u) m -
            criticalSinChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ)) := by
  rw [windowedOfflineCosWave_sub_log_eq, windowedOfflineCosWave_sub_log_eq,
    windowedOfflineSinWave_sub_log_eq, windowedOfflineSinWave_sub_log_eq]
  exact polar_two_channel_jump_eq
    (fun j : ℕ => windowedOfflineRadialWave w β (u - Real.log j))
    (continuousPhaseProfile γ u) m k

/-- Whenever $w$ is non-negative (`∀ x, 0 ≤ w x`), `windowedOfflineRadialWave w β x ≥ 0` for all $x$. -/
theorem windowedOfflineRadialWave_nonneg {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) (β x : ℝ) :
    0 ≤ windowedOfflineRadialWave w β x :=
  mul_nonneg (hw x) (Real.exp_pos _).le

/-- **Universal Non-Negative Window Two-Channel `varianceEnergy` Dominance
(`windowed_varianceEnergy_two_channel_ge_radial`):**
For every non-negative window $w : \mathbb{R} \to \mathbb{R}$ (`∀ x, 0 ≤ w x`), finite sets
$L, R \subseteq \mathbb{N}$, and parameters $\beta, \gamma, u \in \mathbb{R}$:
$$\operatorname{varianceEnergy}(L, R, \text{fun } m \mapsto v_{\beta,0,w}(u - \log m)) \le
  \operatorname{varianceEnergy}(L, R, \text{fun } m \mapsto v_{\beta,\gamma,w}^{\cos}(u - \log m)) +
    \operatorname{varianceEnergy}(L, R, \text{fun } m \mapsto v_{\beta,\gamma,w}^{\sin}(u - \log m)).$$
(Classification: Candidate new theorem.) -/
theorem windowed_varianceEnergy_two_channel_ge_radial {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (L R : Finset ℕ) (β γ u : ℝ) :
    varianceEnergy L R (fun m : ℕ => windowedOfflineRadialWave w β (u - Real.log m)) ≤
      varianceEnergy L R (fun m : ℕ => windowedOfflineCosWave w β γ (u - Real.log m)) +
        varianceEnergy L R (fun m : ℕ => windowedOfflineSinWave w β γ (u - Real.log m)) := by
  rw [← bipartiteEnergy_eq_variance, ← bipartiteEnergy_eq_variance, ← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [windowed_offline_two_channel_jump_eq]
  have h1 := windowedOfflineRadialWave_nonneg hw β (u - Real.log m)
  have h2 := windowedOfflineRadialWave_nonneg hw β (u - Real.log k)
  have h3 : 0 ≤ (criticalCosChannel (continuousPhaseProfile γ u) m -
      criticalCosChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ) +
    (criticalSinChannel (continuousPhaseProfile γ u) m -
      criticalSinChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ) :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hprod : 0 ≤ windowedOfflineRadialWave w β (u - Real.log m) *
      windowedOfflineRadialWave w β (u - Real.log k) *
      ((criticalCosChannel (continuousPhaseProfile γ u) m -
          criticalCosChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ) +
        (criticalSinChannel (continuousPhaseProfile γ u) m -
          criticalSinChannel (continuousPhaseProfile γ u) k) ^ (2 : ℕ)) :=
    mul_nonneg (mul_nonneg h1 h2) h3
  linarith

/-- **Pointwise `chainDensity` Dominance for Non-Negative Windows
(`windowed_chainDensity_two_channel_ge_radial`):**
For every non-negative window $w : \mathbb{R} \to \mathbb{R}$, positive product index $N : \mathbb{N}_+$,
prime factor $p \in N.\text{primeFactors}$, base $b \in \mathbb{N}$, and parameters $\beta, \gamma, u \in \mathbb{R}$:
$$\operatorname{chainDensity}(N, p, b, v_{\beta,0,w}, u) \le
  \operatorname{chainDensity}(N, p, b, v_{\beta,\gamma,w}^{\cos}, u) +
    \operatorname{chainDensity}(N, p, b, v_{\beta,\gamma,w}^{\sin}, u).$$
(Classification: Corollary.) -/
theorem windowed_chainDensity_two_channel_ge_radial {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (N : ℕ+) {p : ℕ} (hp : p ∈ (N : ℕ).primeFactors) (b : ℕ) (β γ u : ℝ) :
    chainDensity N p b (windowedOfflineRadialWave w β) u ≤
      chainDensity N p b (windowedOfflineCosWave w β γ) u +
        chainDensity N p b (windowedOfflineSinWave w β γ) u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) (Real.log (N : ℕ))
  · unfold chainDensity
    rw [← mul_add]
    have hcoeff : 0 ≤ Real.log p * fiber (N : ℕ) u :=
      mul_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
        (fiber_pos_on_central N.pos hu.1.le hu.2.le).le
    exact mul_le_mul_of_nonneg_left
      (windowed_varianceEnergy_two_channel_ge_radial hw
        (chainLeft N p b u) (chainRight N p b u) β γ u)
      hcoeff
  · simp only [chainDensity, chainVariance_term_zero_outside _ _ _ _ _ hu, mul_zero, add_zero, le_rfl]

/-- **Pointwise `density` Dominance for Non-Negative Windows
(`windowed_density_two_channel_ge_radial`):**
For every non-negative window $w : \mathbb{R} \to \mathbb{R}$, positive product index $N : \mathbb{N}_+$,
and parameters $\beta, \gamma, u \in \mathbb{R}$:
$$\operatorname{density}(N, v_{\beta,0,w}, u) \le
  \operatorname{density}(N, v_{\beta,\gamma,w}^{\cos}, u) +
    \operatorname{density}(N, v_{\beta,\gamma,w}^{\sin}, u).$$
(Classification: Corollary.) -/
theorem windowed_density_two_channel_ge_radial {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (N : ℕ+) (β γ u : ℝ) :
    density (N : ℕ) (windowedOfflineRadialWave w β) u ≤
      density (N : ℕ) (windowedOfflineCosWave w β γ) u +
        density (N : ℕ) (windowedOfflineSinWave w β γ) u := by
  rw [density_eq_sum_chains, density_eq_sum_chains, density_eq_sum_chains, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  exact windowed_chainDensity_two_channel_ge_radial hw N hp b β γ u

/-- **Integrated `chainIntegral` Dominance for Compactly Supported Non-Negative Windows
(`windowed_chainIntegral_two_channel_ge_radial`):**
For every continuous compactly supported non-negative window $w : \mathbb{R} \to \mathbb{R}$,
chain index $q : \text{ChainIndex}$, and parameters $\beta, \gamma \in \mathbb{R}$:
$$\operatorname{chainIntegral}(v_{\beta,0,w}, q) \le
  \operatorname{chainIntegral}(v_{\beta,\gamma,w}^{\cos}, q) +
    \operatorname{chainIntegral}(v_{\beta,\gamma,w}^{\sin}, q).$$
(Classification: Candidate new theorem.) -/
theorem windowed_chainIntegral_two_channel_ge_radial {w : ℝ → ℝ}
    (hw_cont : Continuous w) (hwc : HasCompactSupport w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (q : ChainIndex) (β γ : ℝ) :
    chainIntegral (windowedOfflineRadialWave w β) q ≤
      chainIntegral (windowedOfflineCosWave w β γ) q +
        chainIntegral (windowedOfflineSinWave w β γ) q := by
  unfold chainIntegral
  have hint_rad := integrable_chainDensity q.1 q.2.1.property q.2.2.property
    (continuous_windowedOfflineRadialWave hw_cont β)
    (hasCompactSupport_windowedOfflineRadialWave hwc β)
  have hint_cos := integrable_chainDensity q.1 q.2.1.property q.2.2.property
    (continuous_windowedOfflineCosWave hw_cont β γ)
    (hasCompactSupport_windowedOfflineCosWave hwc β γ)
  have hint_sin := integrable_chainDensity q.1 q.2.1.property q.2.2.property
    (continuous_windowedOfflineSinWave hw_cont β γ)
    (hasCompactSupport_windowedOfflineSinWave hwc β γ)
  rw [← integral_add hint_cos hint_sin]
  refine integral_mono hint_rad (hint_cos.add hint_sin) fun u => ?_
  exact windowed_chainDensity_two_channel_ge_radial hw_nonneg q.1 q.2.1.property q.2.2.val β γ u

/-! ## §3. Two-Point Plateau Ground-Cut Coercivity for Compactly Supported Profiles -/

/-- Exact evaluation of the ground-step jump $(1 \to p)$ of `windowedOfflineRadialWave w β`
whenever $w(u) = 1$ and $w(u - \log p) = 1$:
$$\bigl(v_{\beta,0,w}(u - \log 1) - v_{\beta,0,w}(u - \log p)\bigr)^2
  = e^{-2\beta u}\bigl(e^{\beta \log p} - 1\bigr)^2.$$
(Classification: New formulation.) -/
theorem windowedOfflineRadialWave_ground_step_sq_eq {w : ℝ → ℝ} {u : ℝ} {p : ℕ}
    (hw1 : w u = 1) (hwp : w (u - Real.log p) = 1) (β : ℝ) :
    (windowedOfflineRadialWave w β (u - Real.log (1 : ℕ)) -
        windowedOfflineRadialWave w β (u - Real.log p)) ^ (2 : ℕ) =
      Real.exp (-2 * β * u) * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ) := by
  unfold windowedOfflineRadialWave
  simp only [Nat.cast_one, Real.log_one, sub_zero, hw1, hwp, one_mul]
  have h1 : -β * (u - Real.log p) = -β * u + β * Real.log p := by ring
  have h2 : Real.exp (-β * u) ^ (2 : ℕ) = Real.exp (-2 * β * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h1, Real.exp_add]
  linear_combination (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ) * h2

/-- **Two-Point Ground-Cut Lower Bound on Windowed `varianceEnergy`
(`windowed_varianceEnergy_ground_cut_ge_prime_step`):**
For any window $w : \mathbb{R} \to \mathbb{R}$, ground cut $u \in (0, \log 2)$, and prime factor
$p \in N.\text{primeFactors}$ such that $w(u) = 1$ and $w(u - \log p) = 1$:
$$e^{-2\beta u}\bigl(e^{\beta \log p} - 1\bigr)^2 \le
  \operatorname{varianceEnergy}\bigl(\operatorname{chainLeft}(N, p, 1, u),
    \operatorname{chainRight}(N, p, 1, u), \text{fun } m \mapsto v_{\beta,0,w}(u - \log m)\bigr).$$
(Classification: Candidate new theorem.) -/
theorem windowed_varianceEnergy_ground_cut_ge_prime_step {w : ℝ → ℝ} {N p : ℕ} {u : ℝ}
    (hpN : p ∈ N.primeFactors) (hu0 : 0 < u) (hu2 : u < Real.log 2)
    (hw1 : w u = 1) (hwp : w (u - Real.log p) = 1) (β : ℝ) :
    Real.exp (-2 * β * u) * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ) ≤
      varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u)
        (fun m : ℕ => windowedOfflineRadialWave w β (u - Real.log m)) := by
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
  have hm1 : 1 ∈ chainLeft N p 1 u := mem_chainLeft_base h1N h1_compl hu_left
  have hkp : p ∈ chainRight N p 1 u := by
    simpa only [mul_one] using mem_chainRight_prime_mul hp_prime hp1N h1_compl hu_right
  rw [← windowedOfflineRadialWave_ground_step_sq_eq hw1 hwp β, ← bipartiteEnergy_eq_variance]
  unfold bipartiteEnergy
  have hle_inner :
      (windowedOfflineRadialWave w β (u - Real.log (1 : ℕ)) -
          windowedOfflineRadialWave w β (u - Real.log p)) ^ (2 : ℕ) ≤
        ∑ k ∈ chainRight N p 1 u,
          (windowedOfflineRadialWave w β (u - Real.log (1 : ℕ)) -
            windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun k : ℕ => (windowedOfflineRadialWave w β (u - Real.log (1 : ℕ)) -
        windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ))
      (fun k _ => sq_nonneg _) hkp
  have hle_outer :
      (∑ k ∈ chainRight N p 1 u,
          (windowedOfflineRadialWave w β (u - Real.log (1 : ℕ)) -
            windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ)) ≤
        ∑ m ∈ chainLeft N p 1 u, ∑ k ∈ chainRight N p 1 u,
          (windowedOfflineRadialWave w β (u - Real.log m) -
            windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun m : ℕ => ∑ k ∈ chainRight N p 1 u,
        (windowedOfflineRadialWave w β (u - Real.log m) -
          windowedOfflineRadialWave w β (u - Real.log k)) ^ (2 : ℕ))
      (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hm1
  linarith

/-- **Ground-Cut Multi-Prime Lower Bound for Compactly Windowed Radial Density
(`windowed_density_ground_cut_ge_sum_primeFactors`):**
For any window $w : \mathbb{R} \to \mathbb{R}$, ground cut $u \in (0, \log 2)$, and $N \in \mathbb{N}$
such that $w(u) = 1$ and $w(u - \log p) = 1$ for all $p \in N.\text{primeFactors}$:
$$e^{-2\beta u}\,\operatorname{fiber}(N, u)
    \sum_{p \in N.\text{primeFactors}} \log p \cdot \bigl(e^{\beta \log p} - 1\bigr)^2 \le
  \operatorname{density}(N, v_{\beta,0,w}, u).$$
(Classification: Candidate new theorem.) -/
theorem windowed_density_ground_cut_ge_sum_primeFactors {w : ℝ → ℝ} (N : ℕ) {u : ℝ}
    (hu0 : 0 < u) (hu2 : u < Real.log 2)
    (hw1 : w u = 1) (hwp : ∀ p ∈ N.primeFactors, w (u - Real.log p) = 1) (β : ℝ) :
    Real.exp (-2 * β * u) * fiber N u *
        (∑ p ∈ N.primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ)) ≤
      density N (windowedOfflineRadialWave w β) u := by
  rcases N.eq_zero_or_pos with rfl | hN_pos
  · simp [density, chainVariance]
  · unfold density chainVariance
    have hfib : 0 ≤ fiber N u := by
      by_cases huN : u ≤ Real.log N
      · exact (fiber_pos_on_central hN_pos hu0.le huN).le
      · push Not at huN
        have hN1 : N = 1 := by
          have hlog : Real.log (N : ℝ) < Real.log 2 := huN.trans hu2
          have hlt2 : (N : ℝ) < 2 :=
            (Real.log_lt_log_iff (by exact_mod_cast hN_pos) (by norm_num)).mp hlog
          have hlt2_nat : N < 2 := by exact_mod_cast hlt2
          omega
        subst hN1
        simp [fiber, cuspTerm]
    rw [mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hfib
    refine Finset.sum_le_sum fun p hpN => ?_
    obtain ⟨hp_prime, _, hN0⟩ := Nat.mem_primeFactors.mp hpN
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    have h1N : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr hN0
    have hstep := windowed_varianceEnergy_ground_cut_ge_prime_step
      hpN hu0 hu2 hw1 (hwp p hpN) β
    have hle_b :
        varianceEnergy (chainLeft N p 1 u) (chainRight N p 1 u)
            (fun m : ℕ => windowedOfflineRadialWave w β (u - Real.log m)) ≤
          ∑ b ∈ N.divisors,
            varianceEnergy (chainLeft N p b u) (chainRight N p b u)
              (fun m : ℕ => windowedOfflineRadialWave w β (u - Real.log m)) :=
      Finset.single_le_sum
        (f := fun b : ℕ => varianceEnergy (chainLeft N p b u) (chainRight N p b u)
          (fun m : ℕ => windowedOfflineRadialWave w β (u - Real.log m)))
        (fun b _ => varianceEnergy_nonneg _ _ _) h1N
    have hmul := mul_le_mul_of_nonneg_left (hstep.trans hle_b) hlog
    linarith

/-- **Quadratic $\beta^2 (\log p)^3$ Coercivity for Symmetrized Windowed Two-Channel Density
(`windowed_two_channel_density_symmetrized_ground_cut_ge_quadratic`):**
For any non-negative window $w : \mathbb{R} \to \mathbb{R}$ (`∀ x, 0 ≤ w x`), positive product index
$N : \mathbb{N}_+$, and ground cut $u \in (0, \log 2)$ such that $w(u) = 1$ and $w(u - \log p) = 1$
for all $p \in N.\text{primeFactors}$:
$$\frac{1}{2}\beta^2\,\operatorname{fiber}(N, u)\sum_{p \in N.\text{primeFactors}} (\log p)^3 \le
  \frac{1}{2}\Bigl(
    e^{2\beta u}\bigl(\operatorname{density}(N, v_{\beta,\gamma,w}^{\cos}, u) +
      \operatorname{density}(N, v_{\beta,\gamma,w}^{\sin}, u)\bigr) +
    e^{-2\beta u}\bigl(\operatorname{density}(N, v_{-\beta,\gamma,w}^{\cos}, u) +
      \operatorname{density}(N, v_{-\beta,\gamma,w}^{\sin}, u)\bigr)\Bigr).$$
(Classification: Candidate new theorem.) -/
theorem windowed_two_channel_density_symmetrized_ground_cut_ge_quadratic
    {w : ℝ → ℝ} (hw_nonneg : ∀ x, 0 ≤ w x) (N : ℕ+) {u : ℝ}
    (hu0 : 0 < u) (hu2 : u < Real.log 2)
    (hw1 : w u = 1) (hwp : ∀ p ∈ (N : ℕ).primeFactors, w (u - Real.log p) = 1)
    (β γ : ℝ) :
    (1 / 2 : ℝ) * β ^ (2 : ℕ) * fiber (N : ℕ) u *
        (∑ p ∈ (N : ℕ).primeFactors, Real.log p ^ (3 : ℕ)) ≤
      (1 / 2 : ℝ) *
        (Real.exp (2 * β * u) *
            (density (N : ℕ) (windowedOfflineCosWave w β γ) u +
              density (N : ℕ) (windowedOfflineSinWave w β γ) u) +
          Real.exp (-2 * β * u) *
            (density (N : ℕ) (windowedOfflineCosWave w (-β) γ) u +
              density (N : ℕ) (windowedOfflineSinWave w (-β) γ) u)) := by
  have hdom_pos := windowed_density_two_channel_ge_radial hw_nonneg N β γ u
  have hdom_neg := windowed_density_two_channel_ge_radial hw_nonneg N (-β) γ u
  have hrad_pos := windowed_density_ground_cut_ge_sum_primeFactors (N : ℕ) hu0 hu2 hw1 hwp β
  have hrad_neg := windowed_density_ground_cut_ge_sum_primeFactors (N : ℕ) hu0 hu2 hw1 hwp (-β)
  have hexp_pos : 0 < Real.exp (2 * β * u) := Real.exp_pos _
  have hexp_neg : 0 < Real.exp (-2 * β * u) := Real.exp_pos _
  have hcancel_pos : Real.exp (2 * β * u) * Real.exp (-2 * β * u) = 1 := by
    rw [← Real.exp_add]
    have h0 : 2 * β * u + -2 * β * u = 0 := by ring
    rw [h0, Real.exp_zero]
  have hcancel_neg : Real.exp (-2 * β * u) * Real.exp (-2 * (-β) * u) = 1 := by
    rw [← Real.exp_add]
    have h0 : -2 * β * u + -2 * (-β) * u = 0 := by ring
    rw [h0, Real.exp_zero]
  have h1 :
      fiber (N : ℕ) u *
          (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ)) ≤
        Real.exp (2 * β * u) *
          (density (N : ℕ) (windowedOfflineCosWave w β γ) u +
            density (N : ℕ) (windowedOfflineSinWave w β γ) u) := by
    have hm := mul_le_mul_of_nonneg_left (hrad_pos.trans hdom_pos) hexp_pos.le
    calc fiber (N : ℕ) u *
          (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ))
        = (Real.exp (2 * β * u) * Real.exp (-2 * β * u)) * fiber (N : ℕ) u *
            (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ)) := by
          rw [hcancel_pos, one_mul]
      _ = Real.exp (2 * β * u) *
            (Real.exp (-2 * β * u) * fiber (N : ℕ) u *
              (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ))) := by
          ring
      _ ≤ Real.exp (2 * β * u) *
            (density (N : ℕ) (windowedOfflineCosWave w β γ) u +
              density (N : ℕ) (windowedOfflineSinWave w β γ) u) := hm
  have h2 :
      fiber (N : ℕ) u *
          (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ)) ≤
        Real.exp (-2 * β * u) *
          (density (N : ℕ) (windowedOfflineCosWave w (-β) γ) u +
            density (N : ℕ) (windowedOfflineSinWave w (-β) γ) u) := by
    have hm := mul_le_mul_of_nonneg_left (hrad_neg.trans hdom_neg) hexp_neg.le
    calc fiber (N : ℕ) u *
          (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ))
        = (Real.exp (-2 * β * u) * Real.exp (-2 * (-β) * u)) * fiber (N : ℕ) u *
            (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ)) := by
          rw [hcancel_neg, one_mul]
      _ = Real.exp (-2 * β * u) *
            (Real.exp (-2 * (-β) * u) * fiber (N : ℕ) u *
              (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ))) := by
          ring
      _ ≤ Real.exp (-2 * β * u) *
            (density (N : ℕ) (windowedOfflineCosWave w (-β) γ) u +
              density (N : ℕ) (windowedOfflineSinWave w (-β) γ) u) := hm
  have hfib_nonneg : 0 ≤ fiber (N : ℕ) u := by
    by_cases huN : u ≤ Real.log (N : ℕ)
    · exact (fiber_pos_on_central N.pos hu0.le huN).le
    · push Not at huN
      have hN1 : (N : ℕ) = 1 := by
        have hlog : Real.log (N : ℝ) < Real.log 2 := huN.trans hu2
        have hlt2 : (N : ℝ) < 2 :=
          (Real.log_lt_log_iff (by exact_mod_cast N.pos) (by norm_num)).mp hlog
        have hlt2_nat : (N : ℕ) < 2 := by exact_mod_cast hlt2
        have hpos : 0 < (N : ℕ) := N.pos
        omega
      rw [hN1]
      simp [fiber, cuspTerm]
  have hquad :
      β ^ (2 : ℕ) * (∑ p ∈ (N : ℕ).primeFactors, Real.log p ^ (3 : ℕ)) ≤
        (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (β * Real.log p) - 1) ^ (2 : ℕ)) +
          (∑ p ∈ (N : ℕ).primeFactors, Real.log p * (Real.exp (-β * Real.log p) - 1) ^ (2 : ℕ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    have hexp := exp_sub_one_sq_add_exp_neg_sub_one_sq_ge_sq (β * Real.log p)
    rw [← neg_mul] at hexp
    have hmul := mul_le_mul_of_nonneg_left hexp hlog
    nlinarith
  have hfib_quad := mul_le_mul_of_nonneg_left hquad hfib_nonneg
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
