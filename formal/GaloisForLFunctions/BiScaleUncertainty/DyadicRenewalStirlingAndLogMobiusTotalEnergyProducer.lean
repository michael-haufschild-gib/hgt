import GaloisForLFunctions.BiScaleUncertainty.SawtoothPhaseCancellationAndBandSpectralProducer
import GaloisForLFunctions.BiScaleUncertainty.DyadicRenewalChain
import GaloisForLFunctions.BiScaleUncertainty.LocalToGlobalTailStabilityAndWitnessIndicatorPairing
import GaloisForLFunctions.BiScaleUncertainty.SelbergSieveTailQuadraticFormAndTruncatedDivisorGram

/-!
# Pillar XXXV: Closed-Form Log-Möbius Total Energy Producer, Dyadic Renewal Stirling Sandwich & Selberg Sieve Tail Producer Bounds

This module integrates our explicit Chebyshev, Stirling, and Möbius-log producers into three
parallel structural developments (`WitnessGermOriginMassAndJointTailHeadSynthesis`,
`DyadicRenewalChain`, and `SelbergSieveTailQuadraticFormAndTruncatedDivisorGram`), replacing
every remaining unestimated tail integral, dyadic block input, and $\ell^1$ sieve remainder with
100% unconditional closed-form producer bounds:

1. **Closed-Form Total Energy Producer Bound on `logMobiusFermiErrorEnergy N` & Dual Witness Pairing (§1):**
   In `WitnessGermOriginMassAndJointTailHeadSynthesis` and `ChebyshevHeadAndShearCellProducer`,
   the normalized Chebyshev head of `logMobiusFermiErrorEnergy N` was bounded by
   $(\log 4 + 4)^2 N / (\log N)^2$, while the small-$t$ origin tail
   $\int_0^{1/(N+1)} \|h(t) - \operatorname{logMobiusFermiApprox}(N, t)\|^2\,dt$ remained unestimated.
   Here we prove that every coefficient of `logMobiusFermiApprox N` ($N \ge 2$, $1 \le d \le N$)
   satisfies $|\mu(d) \log(N/d) / \log N| \le 1$, giving the pointwise bound
   $\|\operatorname{logMobiusFermiApprox}(N, t)\| \le 3N$, the closed-form small-$t$ tail bound
   $$\int_0^{1/(N+1)} \bigl\|h(t) - \operatorname{logMobiusFermiApprox}(N, t)\bigr\|^2\,dt
     \;\le\; \frac{(1 + 3N)^2}{N + 1},$$
   the **first complete closed-form total energy producer bound** (both tail and head!):
   $$\operatorname{logMobiusFermiErrorEnergy}(N)
     \;\le\; \frac{(1 + 3N)^2}{N + 1} + \frac{(\log 4 + 4)^2 N}{(\log N)^2},$$
   and the unconditional global witness pairing bound against any `w : L2FermiWitness`.

2. **Two-Sided Stirling Producer Sandwich & Geometric Schur Bounds for `DyadicRenewalChain` (§2):**
   In `DyadicRenewalChain`, the dyadic block input at step $h = \log 2$ is
   `chainInput (Real.log 2) k = (√2)^{-(k+1)} ((ψ(2^{k+1}) - ψ(2^k)) - 2^k - log 2)`.
   Connecting `Chebyshev.psi (2^k)` to `RHTower.chebyshevPsi (2^k)` via
   `chebyshev_psi_natCast_eq_chebyshevPsi` and bounding the dyadic increment by the
   Stirling-controlled alternating producer `chebyshevAlternatingProducer (2^k)` yields the
   unconditional two-sided producer sandwich on `chainInput (Real.log 2) k`, the prime-free
   envelope `dyadicRenewalStirlingInputProducer k`, and explicit Schur bounds on the chain state
   energy $\sum_{k < K} \operatorname{chainState}(N, \log 2, k)^2$ and causal response window energy
   $\int_0^{K\log 2} R_N(t)^2\,dt$.

3. **Explicit Möbius & Von Mangoldt Producer Specializations of the Selberg $\Lambda^2$-Sieve Tail (§3):**
   Specializing `SelbergSieveTailQuadraticFormAndTruncatedDivisorGram` to the raw Möbius weight
   $\mu(d)$ and the von Mangoldt divisor weight $-\mu(d)\log d$ bounds the $\ell^1$ remainder by
   $N^2$ and $(\operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N)^2$ respectively, while
   identifying the exact bulk head energy on $1 \le k \le N$ with $\sum_{k=1}^N \Lambda(k)^2$.
-/

open Complex MeasureTheory Set Filter Topology Finset
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry
open RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped BigOperators CompactlySupported Real ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Closed-Form Total Energy Producer Bound on `logMobiusFermiErrorEnergy N` & Dual Witness Pairing -/

/-- For every `N ≥ 2` and `d ∈ Finset.Icc 1 N`, the log-smoothed Möbius coefficient satisfies
`‖((μ(d) * log(N / d) / log N : ℝ) : ℂ)‖ ≤ 1`. -/
theorem norm_logMobiusFermiApprox_coeff_le_one {N d : ℕ} (hN : 2 ≤ N)
    (hd : d ∈ Finset.Icc 1 N) :
    ‖((((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ)‖ ≤ 1 := by
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt_one
  have hdiv_ge_one : (1 : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
    (one_le_div hd_pos).mpr (by exact_mod_cast hdN)
  have hdiv_le_N : (N : ℝ) / (d : ℝ) ≤ (N : ℝ) :=
    div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hd1)
  have hlog_nonneg : 0 ≤ Real.log ((N : ℝ) / (d : ℝ)) := Real.log_nonneg hdiv_ge_one
  have hlog_le : Real.log ((N : ℝ) / (d : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) hdiv_le_N
  have hratio_nonneg : 0 ≤ Real.log ((N : ℝ) / (d : ℝ)) / Real.log (N : ℝ) :=
    div_nonneg hlog_nonneg hlogN_pos.le
  have hratio_le_one : Real.log ((N : ℝ) / (d : ℝ)) / Real.log (N : ℝ) ≤ 1 :=
    (div_le_one hlogN_pos).mpr hlog_le
  have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [Complex.norm_real, Real.norm_eq_abs, mul_div_assoc, abs_mul,
    abs_of_nonneg hratio_nonneg]
  nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]

/-- **Pointwise Linear Bound on `logMobiusFermiApprox N t`:**
For every `N ≥ 2` and `t : ℝ`,
$$\|\operatorname{logMobiusFermiApprox}(N, t)\| \;\le\; 3N.$$ -/
theorem norm_logMobiusFermiApprox_le_three_mul {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖logMobiusFermiApprox N t‖ ≤ 3 * (N : ℝ) := by
  have h1 := norm_logMobiusFermiApprox_le N t
  have h2 :
      (∑ d ∈ Finset.Icc 1 N,
        ‖((((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ)‖ * 3) ≤
      ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) * 3 := by
    refine Finset.sum_le_sum fun d hd => ?_
    exact mul_le_mul_of_nonneg_right (norm_logMobiusFermiApprox_coeff_le_one hN hd) (by positivity)
  rw [Finset.sum_const, Nat.card_Icc, show N + 1 - 1 = N by omega, nsmul_eq_mul] at h2
  linarith

/-- **Pointwise Quadratic Bound on `‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2`:**
For every `N ≥ 2` and `t : ℝ`,
$$\|\operatorname{dyadicHaar}(t) - \operatorname{logMobiusFermiApprox}(N, t)\|^2
  \;\le\; (1 + 3N)^2.$$ -/
theorem normSq_dyadicHaar_sub_logMobiusFermiApprox_le {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2 ≤ (1 + 3 * (N : ℝ)) ^ 2 := by
  have htri : ‖dyadicHaar t - logMobiusFermiApprox N t‖ ≤ 1 + 3 * (N : ℝ) := by
    calc ‖dyadicHaar t - logMobiusFermiApprox N t‖
        ≤ ‖dyadicHaar t‖ + ‖logMobiusFermiApprox N t‖ := norm_sub_le _ _
      _ = 1 + ‖logMobiusFermiApprox N t‖ := by rw [norm_dyadicHaar]
      _ ≤ 1 + 3 * (N : ℝ) := add_le_add le_rfl (norm_logMobiusFermiApprox_le_three_mul hN t)
  exact pow_le_pow_left₀ (norm_nonneg _) htri 2

/-- **Unconditional Closed-Form Producer Bound on the Small-`t` Tail of `logMobiusFermiErrorEnergy N`:**
For every `N ≥ 2`, the small-$t$ tail integral over `(0, 1 / (N + 1)]` is bounded in closed form by
`(1 + 3N)² / (N + 1)`:
$$\int_0^{1/(N+1)} \bigl\|\operatorname{dyadicHaar}(t) - \operatorname{logMobiusFermiApprox}(N, t)\bigr\|^2\,dt
  \;\le\; \frac{(1 + 3N)^2}{N + 1}.$$ -/
theorem integral_normSq_dyadicHaar_sub_logMobiusFermiApprox_tail_le {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) ≤
    (1 + 3 * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) := by
  set S : Set ℝ := Ioc (0 : ℝ) (1 / ((N : ℝ) + 1))
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint : IntegrableOn (fun t => ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) S :=
    (integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N).mono_set (Ioc_subset_Ioc le_rfl hc1)
  have hconst : IntegrableOn (fun _ : ℝ => (1 + 3 * (N : ℝ)) ^ 2) S :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hle := setIntegral_mono_on hint hconst measurableSet_Ioc fun t _ =>
    normSq_dyadicHaar_sub_logMobiusFermiApprox_le hN t
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), sub_zero, smul_eq_mul] at hle
  calc (∫ t in S, ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2)
      ≤ 1 / ((N : ℝ) + 1) * (1 + 3 * (N : ℝ)) ^ 2 := hle
    _ = (1 + 3 * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) := by ring

/-- The total closed-form producer bound for `logMobiusFermiErrorEnergy N` (`N ≥ 2`), combining the
small-$t$ tail bound $(1 + 3N)^2 / (N + 1)$ and the normalized Wall 1 Chebyshev head bound
$(\log 4 + 4)^2 N / (\log N)^2$. -/
def logMobiusTotalEnergyProducer (N : ℕ) : ℝ :=
  (1 + 3 * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) +
    (Real.log 4 + 4) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 2

/-- **Complete Closed-Form Total Energy Producer Bound on `logMobiusFermiErrorEnergy N`:**
For every `N ≥ 2`, combining `logMobiusFermiErrorEnergy_le_tail_add_head_producer` with
`integral_normSq_dyadicHaar_sub_logMobiusFermiApprox_tail_le` bounds the entire $L^2(0, 1]$ error
energy (both small-$t$ tail and Chebyshev head) in closed form:
$$\operatorname{logMobiusFermiErrorEnergy}(N)
  \;\le\; \frac{(1 + 3N)^2}{N + 1} + \frac{(\log 4 + 4)^2 N}{(\log N)^2}.$$ -/
theorem logMobiusFermiErrorEnergy_le_total_producer {N : ℕ} (hN : 2 ≤ N) :
    logMobiusFermiErrorEnergy N ≤ logMobiusTotalEnergyProducer N := by
  unfold logMobiusTotalEnergyProducer
  exact (logMobiusFermiErrorEnergy_le_tail_add_head_producer hN).trans
    (add_le_add (integral_normSq_dyadicHaar_sub_logMobiusFermiApprox_tail_le hN) le_rfl)

/-- **Hypothesis-Free Total Energy Producer Bound at Shifted Cutoff `N + 2`:**
For EVERY `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{logMobiusFermiErrorEnergy}(N + 2)
  \;\le\; \operatorname{logMobiusTotalEnergyProducer}(N + 2).$$ -/
theorem logMobiusFermiErrorEnergy_succ_succ_le_total_producer (N : ℕ) :
    logMobiusFermiErrorEnergy (N + 2) ≤ logMobiusTotalEnergyProducer (N + 2) :=
  logMobiusFermiErrorEnergy_le_total_producer (by omega)

/-- Every `w : L2FermiWitness` is unconditionally orthogonal to `logMobiusFermiApprox N` on `(0, 1]`. -/
theorem L2FermiWitness.integral_logMobiusFermiApprox_mul_conj_eq_zero
    (w : L2FermiWitness) (N : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, logMobiusFermiApprox N t * (starRingEnd ℂ) (w t) = 0 := by
  have hcomb : (fun t => logMobiusFermiApprox N t * (starRingEnd ℂ) (w t)) =
      fun t => -(∑ d ∈ Finset.Icc 1 N,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ) *
          (fermiNymanGen (d : ℝ) t * (starRingEnd ℂ) (w t))) := by
    funext t
    unfold logMobiusFermiApprox
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcomb, integral_neg, integral_finsetSum _ (fun d _ =>
    (integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq).const_mul _)]
  rw [Finset.sum_eq_zero, neg_zero]
  intro d hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  rw [integral_const_mul, w.isWitness.orth (d : ℝ) hd1, mul_zero]

/-- **Unconditional Witness Invariance Under `logMobiusFermiApprox N` Subtraction:**
For EVERY `w : L2FermiWitness` and `N : ℕ` (with **zero hypotheses**!),
$$\int_0^1 h(t)\,\overline{w(t)}\,dt
  = \int_0^1 \bigl(h(t) - \operatorname{logMobiusFermiApprox}(N, t)\bigr)\,\overline{w(t)}\,dt.$$ -/
theorem L2FermiWitness.integral_dyadicHaar_sub_logMobiusFermiApprox_mul_conj_eq
    (w : L2FermiWitness) (N : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)) =
      ∫ t in Ioc (0 : ℝ) 1,
        (dyadicHaar t - logMobiusFermiApprox N t) * (starRingEnd ℂ) (w t) := by
  have h1 : IntegrableOn (fun t => dyadicHaar t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq measurable_dyadicHaar w.measurable_toFun
      integrableOn_normSq_dyadicHaar w.integrableOn_normSq
  have hdiff_sq : IntegrableOn (fun t => ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N
  have happrox_sq : IntegrableOn (fun t => ‖logMobiusFermiApprox N t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    have heq : (fun t => logMobiusFermiApprox N t) =
        fun t => dyadicHaar t - (dyadicHaar t - logMobiusFermiApprox N t) := by
      funext t; ring
    rw [heq]
    exact integrableOn_normSq_sub measurable_dyadicHaar
      (measurable_dyadicHaar.sub (measurable_logMobiusFermiApprox N))
      integrableOn_normSq_dyadicHaar hdiff_sq
  have h2 : IntegrableOn (fun t => logMobiusFermiApprox N t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_logMobiusFermiApprox N) w.measurable_toFun
      happrox_sq w.integrableOn_normSq
  have hsplit : (fun t => (dyadicHaar t - logMobiusFermiApprox N t) * (starRingEnd ℂ) (w t)) =
      fun t => dyadicHaar t * (starRingEnd ℂ) (w t) -
        logMobiusFermiApprox N t * (starRingEnd ℂ) (w t) := by
    funext t; ring
  rw [hsplit, integral_sub h1 h2, w.integral_logMobiusFermiApprox_mul_conj_eq_zero N, sub_zero]

/-- **Unconditional Cauchy–Schwarz Bound Coupling Global Witness Pairing to `logMobiusFermiErrorEnergy N`:**
For EVERY `w : L2FermiWitness` and `N : ℕ` (with **zero hypotheses**!),
$$\left\|\int_0^1 h(t)\,\overline{w(t)}\,dt\right\|^2
  \;\le\; \operatorname{witnessMass}(w, 1)\,\operatorname{logMobiusFermiErrorEnergy}(N).$$ -/
theorem L2FermiWitness.norm_sq_dyadicHaar_pairing_le_witnessMass_mul_logMobiusFermiErrorEnergy
    (w : L2FermiWitness) (N : ℕ) :
    ‖∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      witnessMass w 1 * logMobiusFermiErrorEnergy N := by
  rw [w.integral_dyadicHaar_sub_logMobiusFermiApprox_mul_conj_eq N]
  set S : Set ℝ := Ioc (0 : ℝ) 1
  set g : ℝ → ℂ := fun t => dyadicHaar t - logMobiusFermiApprox N t
  have hg_meas : Measurable g := measurable_dyadicHaar.sub (measurable_logMobiusFermiApprox N)
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) S :=
    integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N
  have hw2 : IntegrableOn (fun t => ‖w t‖ ^ 2) S := w.integrableOn_normSq
  have h1 : ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ≤ ∫ t in S, ‖g t‖ * ‖w t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have h2 := sq_integral_mul_le (μ := volume.restrict S) (f := fun t => ‖g t‖)
    (g := fun t => ‖w t‖) hg_meas.aestronglyMeasurable.norm
    w.measurable_toFun.aestronglyMeasurable.norm hg2 hw2
  calc ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ^ 2
      ≤ (∫ t in S, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∫ t in S, ‖g t‖ ^ 2) * ∫ t in S, ‖w t‖ ^ 2 := h2
    _ = witnessMass w 1 * logMobiusFermiErrorEnergy N := by
        unfold witnessMass logMobiusFermiErrorEnergy S g
        ring

/-- **Unconditional Closed-Form Log-Möbius Producer Bound on Global Witness Pairing:**
For EVERY `w : L2FermiWitness` and `N : ℕ` (with **zero hypotheses**!), at cutoff `N + 2 ≥ 2`,
$$\left\|\int_0^1 h(t)\,\overline{w(t)}\,dt\right\|^2
  \;\le\; \operatorname{witnessMass}(w, 1)\,\operatorname{logMobiusTotalEnergyProducer}(N + 2).$$ -/
theorem L2FermiWitness.norm_sq_dyadicHaar_pairing_le_logMobiusTotalEnergyProducer
    (w : L2FermiWitness) (N : ℕ) :
    ‖∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      witnessMass w 1 * logMobiusTotalEnergyProducer (N + 2) := by
  refine (w.norm_sq_dyadicHaar_pairing_le_witnessMass_mul_logMobiusFermiErrorEnergy (N + 2)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (logMobiusFermiErrorEnergy_succ_succ_le_total_producer N)
    (witnessMass_nonneg w 1)

/-! ## §2. Two-Sided Stirling Producer Sandwich & Geometric Schur Bounds for `DyadicRenewalChain` -/

/-- Exact bridge at dyadic powers: `Chebyshev.psi (2 ^ k) = RHTower.chebyshevPsi (2 ^ k)`. -/
theorem chebyshev_psi_two_pow_eq (k : ℕ) :
    Chebyshev.psi ((2 : ℝ) ^ k) = RHTower.chebyshevPsi (2 ^ k) := by
  rw [show (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) by push_cast; rfl]
  exact chebyshev_psi_natCast_eq_chebyshevPsi (2 ^ k)

/-- Exact bridge at shifted dyadic powers: `Chebyshev.psi (2 ^ (k + 1)) = RHTower.chebyshevPsi (2 * 2 ^ k)`. -/
theorem chebyshev_psi_two_pow_succ_eq (k : ℕ) :
    Chebyshev.psi ((2 : ℝ) ^ (k + 1)) = RHTower.chebyshevPsi (2 * 2 ^ k) := by
  rw [show (2 : ℝ) ^ (k + 1) = ((2 * 2 ^ k : ℕ) : ℝ) by push_cast; ring]
  exact chebyshev_psi_natCast_eq_chebyshevPsi (2 * 2 ^ k)

/-- For every `k : ℕ`, the dyadic Chebyshev block increment `ψ(2^{k+1}) - ψ(2^k)` is non-negative
and bounded above by the alternating log-factorial producer `chebyshevAlternatingProducer (2 ^ k)`:
$$0 \;\le\; \psi(2^{k+1}) - \psi(2^k) \;\le\; \operatorname{chebyshevAlternatingProducer}(2^k).$$ -/
theorem chebyshev_psi_two_pow_succ_sub_bounds (k : ℕ) :
    0 ≤ Chebyshev.psi ((2 : ℝ) ^ (k + 1)) - Chebyshev.psi ((2 : ℝ) ^ k) ∧
      Chebyshev.psi ((2 : ℝ) ^ (k + 1)) - Chebyshev.psi ((2 : ℝ) ^ k) ≤
        chebyshevAlternatingProducer (2 ^ k) := by
  rw [chebyshev_psi_two_pow_succ_eq k, chebyshev_psi_two_pow_eq k]
  exact ⟨chebyshevPsi_two_mul_sub_nonneg (2 ^ k),
    chebyshevPsi_two_mul_sub_le_alternatingProducer (2 ^ k)⟩

/-- **Stirling Producer Upper Bound on the Dyadic Chebyshev Block Increment:**
For every `k : ℕ`,
$$\psi(2^{k+1}) - \psi(2^k)
  \;\le\; (2\log 2)\,2^k + 2\log(2 \cdot 2^k + 1) + 1.$$ -/
theorem chebyshev_psi_two_pow_succ_sub_le_stirling (k : ℕ) :
    Chebyshev.psi ((2 : ℝ) ^ (k + 1)) - Chebyshev.psi ((2 : ℝ) ^ k) ≤
      (2 * Real.log 2) * (2 : ℝ) ^ k + (2 * Real.log (2 * (2 : ℝ) ^ k + 1) + 1) := by
  have h1 := (chebyshev_psi_two_pow_succ_sub_bounds k).2
  have h2 := chebyshevAlternatingProducer_le_stirling_linear_add_log (m := 2 ^ k) Nat.one_le_two_pow
  rw [Nat.cast_pow, Nat.cast_ofNat] at h2
  linarith

/-- **Two-Sided Alternating-Producer Sandwich on `chainInput (Real.log 2) k`:**
For every `k : ℕ`, the dyadic renewal chain input satisfies:
$$-(\sqrt{2})^{-(k+1)}\bigl(2^k + \log 2\bigr)
  \;\le\; \operatorname{chainInput}(\log 2, k)
  \;\le\; (\sqrt{2})^{-(k+1)}\bigl(\operatorname{chebyshevAlternatingProducer}(2^k) - 2^k - \log 2\bigr).$$ -/
theorem chainInput_log_two_alternating_sandwich (k : ℕ) :
    -((Real.sqrt 2)⁻¹ ^ (k + 1) * ((2 : ℝ) ^ k + Real.log 2)) ≤
      chainInput (Real.log 2) k ∧
    chainInput (Real.log 2) k ≤
      (Real.sqrt 2)⁻¹ ^ (k + 1) *
        (chebyshevAlternatingProducer (2 ^ k) - (2 : ℝ) ^ k - Real.log 2) := by
  rw [chainInput_log_two k]
  obtain ⟨h0, hle⟩ := chebyshev_psi_two_pow_succ_sub_bounds k
  have hfac : 0 ≤ (Real.sqrt 2)⁻¹ ^ (k + 1) := by positivity
  constructor
  · have hsub : -((2 : ℝ) ^ k + Real.log 2) ≤
        (Chebyshev.psi ((2 : ℝ) ^ (k + 1)) - Chebyshev.psi ((2 : ℝ) ^ k)) -
          (2 : ℝ) ^ k - Real.log 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsub hfac
    linarith
  · exact mul_le_mul_of_nonneg_left (by linarith) hfac

/-- **Stirling Producer Upper Bound on `chainInput (Real.log 2) k`:**
For every `k : ℕ`,
$$\operatorname{chainInput}(\log 2, k)
  \;\le\; (\sqrt{2})^{-(k+1)}\bigl((2\log 2 - 1)\,2^k + 2\log(2 \cdot 2^k + 1) + 1 - \log 2\bigr).$$ -/
theorem chainInput_log_two_le_stirling (k : ℕ) :
    chainInput (Real.log 2) k ≤
      (Real.sqrt 2)⁻¹ ^ (k + 1) *
        ((2 * Real.log 2 - 1) * (2 : ℝ) ^ k + 2 * Real.log (2 * (2 : ℝ) ^ k + 1) + 1 - Real.log 2) := by
  rw [chainInput_log_two k]
  have hst := chebyshev_psi_two_pow_succ_sub_le_stirling k
  have hfac : 0 ≤ (Real.sqrt 2)⁻¹ ^ (k + 1) := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hfac

/-- The explicit prime-free Stirling envelope for the `k`-th dyadic renewal block input
`|chainInput (Real.log 2) k|`. -/
def dyadicRenewalStirlingInputProducer (k : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ ^ (k + 1) *
    max ((2 : ℝ) ^ k + Real.log 2)
      (chebyshevAlternatingProducer (2 ^ k) - (2 : ℝ) ^ k - Real.log 2)

/-- `dyadicRenewalStirlingInputProducer k` is unconditionally non-negative for all `k : ℕ`. -/
theorem dyadicRenewalStirlingInputProducer_nonneg (k : ℕ) :
    0 ≤ dyadicRenewalStirlingInputProducer k := by
  unfold dyadicRenewalStirlingInputProducer
  have h1 : 0 ≤ (2 : ℝ) ^ k + Real.log 2 :=
    add_nonneg (pow_nonneg (by norm_num) k) (Real.log_nonneg (by norm_num))
  exact mul_nonneg (by positivity) ( h1.trans (le_max_left _ _) )

/-- **Pointwise Producer Bound on `|chainInput (Real.log 2) k|` and `chainInput (Real.log 2) k ^ 2`:**
For every `k : ℕ`,
$$|\operatorname{chainInput}(\log 2, k)| \;\le\; \operatorname{dyadicRenewalStirlingInputProducer}(k),$$
$$\operatorname{chainInput}(\log 2, k)^2 \;\le\; \operatorname{dyadicRenewalStirlingInputProducer}(k)^2.$$ -/
theorem abs_chainInput_log_two_le_producer (k : ℕ) :
    |chainInput (Real.log 2) k| ≤ dyadicRenewalStirlingInputProducer k ∧
      chainInput (Real.log 2) k ^ 2 ≤ dyadicRenewalStirlingInputProducer k ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := chainInput_log_two_alternating_sandwich k
  have hfac : 0 ≤ (Real.sqrt 2)⁻¹ ^ (k + 1) := by positivity
  have habs : |chainInput (Real.log 2) k| ≤ dyadicRenewalStirlingInputProducer k := by
    unfold dyadicRenewalStirlingInputProducer
    rw [abs_le]
    constructor
    · have hm : (2 : ℝ) ^ k + Real.log 2 ≤
          max ((2 : ℝ) ^ k + Real.log 2)
            (chebyshevAlternatingProducer (2 ^ k) - (2 : ℝ) ^ k - Real.log 2) :=
        le_max_left _ _
      have hmul := mul_le_mul_of_nonneg_left hm hfac
      linarith
    · have hm : chebyshevAlternatingProducer (2 ^ k) - (2 : ℝ) ^ k - Real.log 2 ≤
          max ((2 : ℝ) ^ k + Real.log 2)
            (chebyshevAlternatingProducer (2 ^ k) - (2 : ℝ) ^ k - Real.log 2) :=
        le_max_right _ _
      exact hhigh.trans (mul_le_mul_of_nonneg_left hm hfac)
  refine ⟨habs, ?_⟩
  rw [← sq_abs (chainInput (Real.log 2) k)]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **Geometric Schur Producer Bound on the Dyadic Renewal Chain State Energy:**
For every `N K : ℕ` with `K * log 2 ≤ cutoff N`, the sum of squared dyadic chain states is bounded
above by the prime-free `dyadicRenewalStirlingInputProducer`:
$$\sum_{k < K} \operatorname{chainState}(N, \log 2, k)^2
  \;\le\; \bigl(1 - (\sqrt{2})^{-1}\bigr)^{-2}
    \sum_{j < K} \operatorname{dyadicRenewalStirlingInputProducer}(j)^2.$$ -/
theorem sum_chainState_log_two_sq_le_stirlingProducer (N : ℕ) {K : ℕ}
    (hK : K * Real.log 2 ≤ cutoff N) :
    ∑ k ∈ Finset.range K, chainState N (Real.log 2) k ^ 2 ≤
      (1 - (Real.sqrt 2)⁻¹)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range K, dyadicRenewalStirlingInputProducer j ^ 2 := by
  have h1 := sum_chainState_sq_le N (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hK
  rw [dyadic_ratio] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  exact Finset.sum_le_sum fun j _ => (abs_chainInput_log_two_le_producer j).2

/-- **Dyadic Coarse–Fine Producer Bound on the Causal Response Window Energy:**
For every `N K : ℕ` with `K * log 2 ≤ cutoff N`,
$$\int_0^{K\log 2} R_N(t)^2\,dt
  \;\le\; 2\log 2\,\bigl(1 - (\sqrt{2})^{-1}\bigr)^{-2}
    \sum_{j < K} \operatorname{dyadicRenewalStirlingInputProducer}(j)^2
    + 2 \sum_{k < K} \operatorname{blockEnergy}(N, \log 2, k).$$ -/
theorem integral_sq_causalResponse_le_dyadic_stirlingProducer (N : ℕ) {K : ℕ}
    (hK : K * Real.log 2 ≤ cutoff N) :
    (∫ t in (0 : ℝ)..(K * Real.log 2), causalResponse N t ^ 2) ≤
      2 * Real.log 2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range K, dyadicRenewalStirlingInputProducer j ^ 2) +
        2 * ∑ k ∈ Finset.range K, blockEnergy N (Real.log 2) k := by
  have h1 := integral_sq_causalResponse_le_inputs N (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hK
  rw [dyadic_ratio] at h1
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  refine h1.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hlog) le_rfl)
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Finset.sum_le_sum fun j _ => (abs_chainInput_log_two_le_producer j).2

/-! ## §3. Explicit Möbius & Von Mangoldt Producer Specializations of the Selberg `Λ²`-Sieve Tail -/

/-- The raw Möbius divisor weight `c(d) = μ(d)` as a real sequence. -/
def moebiusDivisorWeight (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- For every `d : ℕ`, `|moebiusDivisorWeight d| ≤ 1`. -/
theorem abs_moebiusDivisorWeight_le_one (d : ℕ) :
    |moebiusDivisorWeight d| ≤ 1 := by
  unfold moebiusDivisorWeight
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- For every `N : ℕ`, `∑_{d=1}^N |μ(d)| ≤ N`. -/
theorem sum_abs_moebiusDivisorWeight_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, |moebiusDivisorWeight d|) ≤ (N : ℝ) := by
  calc (∑ d ∈ Finset.Icc 1 N, |moebiusDivisorWeight d|)
      ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => abs_moebiusDivisorWeight_le_one d
    _ = (N : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, show N + 1 - 1 = N by omega, nsmul_eq_mul, mul_one]

/-- **Unconditional Selberg Sieve Mean-Square Producer Bound for Raw Möbius Weights:**
For every `N K : ℕ`, the sieved Möbius divisor sum `s_{N,μ}(k) = ∑_{d ∣ k, 1 ≤ d ≤ N} μ(d)` satisfies:
$$\sum_{k=1}^{N+K} s_{N,\mu}(k)^2
  \;\le\; (N + K) \sum_{e=1}^N \varphi(e)
    \left(\sum_{\substack{1 \le d \le N \\ e \mid d}} \frac{\mu(d)}{d}\right)^2 + N^2.$$ -/
theorem sievedDivisorMeanSquare_moebius_le_selberg_diagonal_add_sq (N K : ℕ) :
    (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N moebiusDivisorWeight k ^ (2 : ℕ)) ≤
      ((N + K : ℕ) : ℝ) * (∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d),
          moebiusDivisorWeight d / (d : ℝ)) ^ (2 : ℕ)) +
      (N : ℝ) ^ (2 : ℕ) := by
  refine (sievedDivisorMeanSquare_le_selberg_diagonal_add_l1_sq N K moebiusDivisorWeight).trans ?_
  refine add_le_add le_rfl ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (sum_abs_moebiusDivisorWeight_le N) 2

/-- For every `N : ℕ`, the `ℓ¹` norm of `vonMangoldtDivisorWeight d = -μ(d) log d` on `[1, N]` is
bounded above by the log-factorial `floorSummatory chebyshevPsi N = ∑_{d=1}^N log d`:
$$\sum_{d=1}^N |-\mu(d)\log d| \;\le\; \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N.$$ -/
theorem sum_abs_vonMangoldtDivisorWeight_le_floorSummatory (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, |vonMangoldtDivisorWeight d|) ≤
      floorSummatory RHTower.chebyshevPsi N := by
  rw [floorSummatory_chebyshevPsi]
  exact Finset.sum_le_sum fun d _ => abs_vonMangoldtDivisorWeight_le_log d

/-- **Unconditional Selberg Sieve Mean-Square Producer Bound for Von Mangoldt Divisor Weights:**
For every `N K : ℕ`, the sieved von Mangoldt divisor sum
`s_{N,-μ log}(k) = ∑_{d ∣ k, 1 ≤ d ≤ N} (-μ(d) log d)` satisfies:
$$\sum_{k=1}^{N+K} s_{N,-\mu\log}(k)^2
  \;\le\; (N + K) \sum_{e=1}^N \varphi(e)
    \left(\sum_{\substack{1 \le d \le N \\ e \mid d}} \frac{-\mu(d)\log d}{d}\right)^2
    + \bigl(\operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N\bigr)^2.$$ -/
theorem sievedDivisorMeanSquare_vonMangoldt_le_selberg_diagonal_add_floorSummatory_sq (N K : ℕ) :
    (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N vonMangoldtDivisorWeight k ^ (2 : ℕ)) ≤
      ((N + K : ℕ) : ℝ) * (∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d),
          vonMangoldtDivisorWeight d / (d : ℝ)) ^ (2 : ℕ)) +
      floorSummatory RHTower.chebyshevPsi N ^ (2 : ℕ) := by
  refine (sievedDivisorMeanSquare_le_selberg_diagonal_add_l1_sq N K vonMangoldtDivisorWeight).trans ?_
  refine add_le_add le_rfl ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (sum_abs_vonMangoldtDivisorWeight_le_floorSummatory N) 2

/-- **Unconditional Origin-Tail Selberg Sieve Mean-Square Bound for Von Mangoldt Weights (`N + 1 ≤ k ≤ N + K`):**
On the bulk head `1 ≤ k ≤ N`, `∑_{d ∣ k} (-μ(d) log d) = Λ(k)`, so isolating the small-$t$ origin
tail `N + 1 ≤ k ≤ N + K` subtracts the exact prime-power bulk energy `∑_{k=1}^N Λ(k)²`:
$$\sum_{k=N+1}^{N+K} s_{N,-\mu\log}(k)^2
  \;\le\; (N + K) \sum_{e=1}^N \varphi(e)
    \left(\sum_{\substack{1 \le d \le N \\ e \mid d}} \frac{-\mu(d)\log d}{d}\right)^2
    + \bigl(\operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N\bigr)^2
    - \sum_{k=1}^N \Lambda(k)^2.$$ -/
theorem tailSievedDivisorMeanSquare_vonMangoldt_le_selberg_diagonal_add_floorSummatory_sq (N K : ℕ) :
    (∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N vonMangoldtDivisorWeight k ^ (2 : ℕ)) ≤
      ((N + K : ℕ) : ℝ) * (∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) *
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d),
          vonMangoldtDivisorWeight d / (d : ℝ)) ^ (2 : ℕ)) +
      floorSummatory RHTower.chebyshevPsi N ^ (2 : ℕ) -
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k) ^ (2 : ℕ) := by
  have h1 := tailSievedDivisorMeanSquare_le_selberg_diagonal N K vonMangoldtDivisorWeight
  have hhead : (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, vonMangoldtDivisorWeight d) ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_divisors_vonMangoldtDivisorWeight_eq k]
  rw [hhead] at h1
  have hl1 : (∑ d ∈ Finset.Icc 1 N, |vonMangoldtDivisorWeight d|) ^ (2 : ℕ) ≤
      floorSummatory RHTower.chebyshevPsi N ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (sum_abs_vonMangoldtDivisorWeight_le_floorSummatory N) 2
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
