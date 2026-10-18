import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeClockWaveletTensorAndPhaseRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DownwardBuchstabL2TelescopeAndSawtoothCoupling
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThirdBandCompositeStepAndLinearL2EnergyBounds
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification

/-!
# Composite Clock-Wavelet Tensor, Downward Buchstab $L^2$ Telescope, and Short-Window Iso-State Bridge

This module bridges three further families of unconditional theorems from
`TransHorizonIncidenceMechanics` directly into `BezoutValuationIncidence` (independent of Wall 1):

1. **Composite Valuation-Clock Wavelet Tensor & Adjacent Valuation-Shell Phase Recovery:**
   - Cross-coprime moduli and lags factor both `sieveLagMultiplier` and `ramanujanLagCoefficient`
     as exact multiplicative tensors (`sieveLagMultiplier_mul_split`, `ramanujanLagCoefficient_mul_split`),
     and mixed four-lag differences factor into two-direction wavelet products
     (`sieveLagMultiplier_mixed_difference`, `clockTensorMultiplier_prime_powers`).
   - For any prime $p$, shell $a \ge 1$, and nonzero composite modulus $q \ne 0$, evaluating the
     composite clock wavelet at the canonical transverse visibility clock
     $L = \operatorname{lagVisibilityClock}(\operatorname{ordCompl}_p(q))$ isolates the adjacent
     valuation shells $v_p(q) \in \{a, a + 1\}$ with exact dipole cancellation and opposite calibrated
     amplitudes $+p^a$ and $-p^a$ (`bvi_composite_clock_wavelet_tensor_and_shell_recovery`).

2. **Downward Buchstab $L^2$ Energy Telescope, Báez-Duarte Sawtooth Coupling, and Three-Band Linear Bounds:**
   - At every prime horizon step $p = N + 1$, the $L^2$ prefix energy increment
     $\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c)$ couples directly to BVI's
     `sievePrefixDiscrepancy N (M / (N + 1)) c` (`sieveL2PrefixEnergy_prime_horizon_sub_eq_discrepancy`)
     and satisfies the universal scale-halving subadditivity inequality
     $$\mathcal{E}_N(M; c) \le \mathcal{E}_{N+1}(M; c) + \mathcal{E}_N\bigl(\lfloor M / (N + 1) \rfloor; c\bigr).$$
   - Across the first three trans-horizon bands $3 \le N \le M < 4(N + 1)$, the Möbius $L^2$ energy
     $\mathcal{E}_N(M; \mu)$ satisfies an exact $(2, 3)$-adic closed form together with the explicit
     linear upper bounds $1 + (M - N)$, $1 + 2(M - N)$, and $1 + 3(M - N)$
     (`bvi_buchstab_l2_sawtooth_step_and_three_band_energy`).

3. **Short-Window Shifted Correlation Defect & Necessary-and-Sufficient Iso-State Classification:**
   - On any short window $[M_0 + 1, M_0 + M]$ ($M \ll L_N$), the renormalized correlation defect
     $\widetilde{\mathcal{D}}_N(M_0, M; c)$ equals the increment of the Selberg LCM and Bézout CRT
     sawtooth remainders minus $M \cdot \operatorname{sieveSuccessorReserve}(N, c)$, and is
     non-positive for all weights $c$ (resp. all squarefree-supported weights $c$) **if and only if**
     the window endpoints share the same multiplicative observation state
     $\sigma_N(M_0 + M + 1) = \sigma_N(M_0 + 1)$ (resp. radical state
     $\operatorname{rad}_N(M_0 + M + 1) = \operatorname{rad}_N(M_0 + 1)$)
     (`bvi_short_window_defect_iso_state_classification`).
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
## §1. Composite Valuation-Clock Wavelet Tensor and Adjacent Shell Phase Recovery
-/

/-- **Composite Clock-Wavelet Tensor Factorization and Adjacent Valuation-Shell Recovery
(`bvi_composite_clock_wavelet_tensor_and_shell_recovery`):**
1. For coprime moduli $q_1, q_2$ and cross-coprime lags $h_1, h_2$, both `sieveLagMultiplier` and
   `ramanujanLagCoefficient` factor multiplicatively:
   $$\lambda_{q_1 q_2}(h_1 h_2) = \lambda_{q_1}(h_1)\,\lambda_{q_2}(h_2), \qquad
     c_{q_1 q_2}(h_1 h_2) = c_{q_1}(h_1)\,c_{q_2}(h_2).$$
2. For any prime $p$, shell $a \ge 1$, and nonzero integer $q \ne 0$, the calibrated composite
   Ramanujan clock wavelet at the transverse visibility clock
   $L = \operatorname{lagVisibilityClock}(\operatorname{ordCompl}_p(q))$ equals $+p^a$ on shell
   $v_p(q) = a$, $-p^a$ on shell $v_p(q) = a + 1$, and $0$ on all other shells.
3. For any two distinct primes $p \ne r$ and shells $a, c \ge 1$, the two-dimensional tensor
   wavelet `clockTensorMultiplier p r a c (p^b * r^d)` is nonzero if and only if
   $(b, d) \in \{a, a + 1\} \times \{c, c + 1\}$. -/
theorem bvi_composite_clock_wavelet_tensor_and_shell_recovery :
    (∀ {q₁ q₂ h₁ h₂ : ℕ}, q₁.Coprime q₂ → q₁.Coprime h₂ → q₂.Coprime h₁ →
      sieveLagMultiplier (q₁ * q₂) (h₁ * h₂) =
        sieveLagMultiplier q₁ h₁ * sieveLagMultiplier q₂ h₂ ∧
      ramanujanLagCoefficient (q₁ * q₂) (h₁ * h₂) =
        ramanujanLagCoefficient q₁ h₁ * ramanujanLagCoefficient q₂ h₂) ∧
    (∀ {p a q : ℕ}, p.Prime → 1 ≤ a → q ≠ 0 →
      compositeClockWaveletRamanujan p a q (lagVisibilityClock (ordCompl[p] q)) /
          ramanujanLagCoefficient (ordCompl[p] q) (lagVisibilityClock (ordCompl[p] q)) =
        if q.factorization p = a then ((p ^ a : ℕ) : ℝ)
        else if q.factorization p = a + 1 then -((p ^ a : ℕ) : ℝ) else 0) ∧
    (∀ {p r a b c d : ℕ}, p.Prime → r.Prime → p ≠ r → 1 ≤ a → 1 ≤ c →
      (clockTensorMultiplier p r a c (p ^ b * r ^ d) ≠ 0 ↔
        (b = a ∨ b = a + 1) ∧ (d = c ∨ d = c + 1))) :=
  ⟨fun hq h₁₂ h₂₁ =>
    ⟨sieveLagMultiplier_mul_split hq h₁₂ h₂₁,
      ramanujanLagCoefficient_mul_split hq h₁₂ h₂₁⟩,
    fun hp ha hq => compositeClockWaveletRamanujan_valuation_phase_recovery hp ha hq,
    fun hp hr hpr ha hc => clockTensorMultiplier_prime_powers_ne_zero_iff hp hr hpr ha hc⟩

/-!
## §2. Downward Buchstab $L^2$ Energy Telescope, Sawtooth Step Law, and Three-Band Bounds
-/

/-- **Downward Buchstab $L^2$ Sawtooth Step Law, Scale-Halving Subadditivity, and Three-Band Bounds
(`bvi_buchstab_l2_sawtooth_step_and_three_band_energy`):**
1. At every prime horizon step $p = N + 1$, for all $M \in \mathbb{N}$ and $c : \mathbb{N} \to \mathbb{R}$,
   the $L^2$ prefix energy step is given in terms of BVI's `sievePrefixDiscrepancy` by
   $$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
     \left\lfloor \frac{M}{N + 1} \right\rfloor \bigl(c(N + 1)^2 + 2 c(N + 1)\mathcal{H}_N(c)\bigr) +
       2 c(N + 1)\operatorname{sievePrefixDiscrepancy}\bigl(N, \lfloor M / (N + 1) \rfloor, c\bigr),$$
   and satisfies the universal scale-halving subadditivity inequality
   $$\mathcal{E}_N(M; c) \le \mathcal{E}_{N+1}(M; c) + \mathcal{E}_N\bigl(\lfloor M / (N + 1) \rfloor; c\bigr).$$
2. For the Möbius weight `moebiusReal`, the trans-horizon $L^2$ prefix energy $\mathcal{E}_N(M; \mu)$
   satisfies the explicit linear bounds across the first three bands:
   - $\mathcal{E}_N(M; \mu) \le 1 + (M - N)$ for $1 \le N \le M < 2(N + 1)$,
   - $\mathcal{E}_N(M; \mu) \le 1 + 2(M - N)$ for $2 \le N \le M < 3(N + 1)$, and
   - $\mathcal{E}_N(M; \mu) \le 1 + 3(M - N)$ for $3 \le N \le M < 4(N + 1)$. -/
theorem bvi_buchstab_l2_sawtooth_step_and_three_band_energy :
    (∀ {N : ℕ}, (N + 1).Prime → ∀ (M : ℕ) (c : ℕ → ℝ),
      sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
        ((M / (N + 1) : ℕ) : ℝ) *
            (c (N + 1) ^ (2 : ℕ) + 2 * c (N + 1) * finiteHarmonicSum N c) +
          2 * c (N + 1) * sievePrefixDiscrepancy N (M / (N + 1)) c ∧
      sieveL2PrefixEnergy N M c ≤
        sieveL2PrefixEnergy (N + 1) M c + sieveL2PrefixEnergy N (M / (N + 1)) c) ∧
    (∀ {N M : ℕ}, 1 ≤ N → N ≤ M → M < 2 * (N + 1) →
      sieveL2PrefixEnergy N M moebiusReal ≤ 1 + ((M - N : ℕ) : ℝ)) ∧
    (∀ {N M : ℕ}, 2 ≤ N → N ≤ M → M < 3 * (N + 1) →
      sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 2 * ((M - N : ℕ) : ℝ)) ∧
    (∀ {N M : ℕ}, 3 ≤ N → N ≤ M → M < 4 * (N + 1) →
      sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 3 * ((M - N : ℕ) : ℝ)) :=
  ⟨fun hp M c =>
    ⟨sieveL2PrefixEnergy_prime_horizon_sub_eq_discrepancy hp M c,
      sieveL2PrefixEnergy_le_prime_succ_add_div hp M c⟩,
    fun hN1 hNM hM2 => sieveL2PrefixEnergy_moebiusReal_first_octave_le hN1 hNM hM2,
    fun hN2 hNM hM3 => sieveL2PrefixEnergy_moebiusReal_two_band_le hN2 hNM hM3,
    fun hN3 hNM hM4 => sieveL2PrefixEnergy_moebiusReal_three_band_le hN3 hNM hM4⟩

/-!
## §3. Short-Window Shifted Correlation Defect and Iso-State Classification
-/

/-- **Short-Window Remainder Polarization and Iso-State / Iso-Radical Classification
(`bvi_short_window_defect_iso_state_classification`):**
For every cutoff $N$, starting offset $M_0$, and window length $M$:
1. The short-window renormalized defect $\widetilde{\mathcal{D}}_N(M_0, M; c)$ satisfies both the
   classical remainder-increment identity and the Dirichlet polarization identity:
   $$\widetilde{\mathcal{D}}_N(M_0, M; c) =
     \Delta R_{\mathrm{LCM}}(N, M_0, M; c) + \Delta R_{\mathrm{CRT}}(N, M_0, M; c)
       - M \cdot \operatorname{sieveSuccessorReserve}(N, c),$$
   $$2\,\widetilde{\mathcal{D}}_N(M_0, M; c) =
     -\operatorname{shortWindowDirichletEnergy}(N, M_0, M, c) +
       s_{N,c}(M_0 + M + 1)^2 - s_{N,c}(M_0 + 1)^2.$$
2. $\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0$ holds for **every** weight $c : \mathbb{N} \to \mathbb{R}$
   **if and only if** $\operatorname{horizonObservationState}(N, M_0 + M + 1) =
   \operatorname{horizonObservationState}(N, M_0 + 1)$.
3. $\widetilde{\mathcal{D}}_N(M_0, M; c) \le 0$ holds for **every** squarefree-supported weight $c$
   **if and only if** $\operatorname{horizonRadicalState}(N, M_0 + M + 1) =
   \operatorname{horizonRadicalState}(N, M_0 + 1)$. -/
theorem bvi_short_window_defect_iso_state_classification (N M₀ M : ℕ) :
    (∀ c : ℕ → ℝ,
      shortWindowRenormalizedDefect N M₀ M c =
        (signedLcmFractDefect N (M₀ + M) c - signedLcmFractDefect N M₀ c) +
          (bezoutSawtoothRemainderForm (M₀ + M) N c - bezoutSawtoothRemainderForm M₀ N c) -
          (M : ℝ) * sieveSuccessorReserve N c ∧
      2 * shortWindowRenormalizedDefect N M₀ M c =
        -shortWindowDirichletEnergy N M₀ M c +
          sieveSeq N c (M₀ + M + 1) ^ (2 : ℕ) - sieveSeq N c (M₀ + 1) ^ (2 : ℕ)) ∧
    ((∀ c : ℕ → ℝ, shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonObservationState N (M₀ + M + 1) = horizonObservationState N (M₀ + 1)) ∧
    ((∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        shortWindowRenormalizedDefect N M₀ M c ≤ 0) ↔
      horizonRadicalState N (M₀ + M + 1) = horizonRadicalState N (M₀ + 1)) :=
  ⟨fun c =>
    ⟨shortWindowRenormalizedDefect_eq_classical_remainders_sub_reserve N M₀ M c,
      two_mul_shortWindowRenormalizedDefect_eq N M₀ M c⟩,
    forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq N M₀ M,
    forall_squarefree_shortWindowRenormalizedDefect_nonpos_iff_radicalState_eq N M₀ M⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
