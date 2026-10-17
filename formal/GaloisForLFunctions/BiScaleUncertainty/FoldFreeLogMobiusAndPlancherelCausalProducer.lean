import GaloisForLFunctions.BiScaleUncertainty.DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer
import GaloisForLFunctions.BiScaleUncertainty.FoldFreeKernelGramAndFranelGcdCancellation
import GaloisForLFunctions.BiScaleUncertainty.PacketEnergyPlancherel
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalMoments

/-!
# Pillar XXXVI: Fold-Free Log-Möbius Pythagoras Decomposition, Causal Tent-Factorial Producer, Plancherel–Laplace Bridge & Franel–Selberg GCD–LCM Law

This module synthesizes four producer mechanisms across the Wall 1 fold-free kernel $\ker P$, the
tent-convolved causal factorial producer `sourceFactorialCausal`, the Plancherel representation of
`packetEnergy`, and the Franel–Selberg GCD–LCM Gram bridge:

1. **Exact Fold-Free Kernel Projection $\tilde{\Phi}_{\mathrm{log}\mu, N} \in \ker P$ & Harmonic-Shadow
   Pythagoras Decomposition of `logMobiusFermiErrorEnergy N` (§1):**
   We compute the exact inner product of `logMobiusFermiApprox N` with the canonical self-similar
   profile `canonicalSelfSimilar t = selfSimilarExtension (u ↦ u⁻¹) t`, proving that it equals the
   log-smoothed Möbius harmonic shadow
   $$\operatorname{logMobiusHarmonicShadow}(N)
     := \sum_{d=1}^N \frac{\mu(d)\log(N/d)}{d\,\log N}
     = \operatorname{finiteHarmonicSum}(N, \mu) + \frac{\operatorname{moebiusLogHarmonicSum}(N)}{\log N}.$$
   Subtracting $\frac{1}{2}\operatorname{logMobiusHarmonicShadow}(N) s_0(t)$ constructs the
   **fold-free log-Möbius approximant** `foldFreeLogMobiusFermiApprox N`, which is strictly
   orthogonal to $s_0$ on $(0, 1]$ and satisfies the exact orthogonal Pythagoras decomposition:
   $$\operatorname{logMobiusFermiErrorEnergy}(N)
     = \int_0^1 \bigl\|\operatorname{dyadicHaar}(t) - \operatorname{foldFreeLogMobiusFermiApprox}(N, t)\bigr\|^2\,dt
       + \frac{\operatorname{logMobiusHarmonicShadow}(N)^2}{2}.$$
   Combining this with `logMobiusFermiErrorEnergy_le_total_producer` yields a strict producer
   improvement on the $\ker P$ error energy and an unconditional closed-form bound on
   $\operatorname{logMobiusHarmonicShadow}(N)^2$.

2. **Exact Full Pairing & Quantitative $O(\log N / \sqrt{N})$ Bound for `sourceFactorialCausal N` (§2):**
   Using the exponential tent moments of `SignedPrimePolarCausalMoments`, we prove that the
   tent-convolved causal factorial source `sourceFactorialCausal N` (bundled as
   `causalFactorialProducer : ℕ → C_c(ℝ, ℝ)`) preserves all integer-grid values
   `sourceFactorialCausal N (log n) = factorialBiNull N (log n)`, has exact polar integral
   $$\int_0^\infty \operatorname{polarDensity}(x)\,\operatorname{sourceFactorialCausal}(N, x)\,dx
     = \frac{\operatorname{sourceFactorialCoefficient}(N)\,\operatorname{harmonicCorrection}(N)
       - \operatorname{chebyshevBiNullProducer}(N)}{\sqrt{N}},$$
   and satisfies the exact full-pairing identity
   $$\operatorname{fullPairing}(\operatorname{sourceFactorialCausal}\,N)
     = \frac{2\,\operatorname{chebyshevBiNullProducer}(N)
       - \operatorname{sourceFactorialCoefficient}(N)\,\operatorname{harmonicCorrection}(N)}{\sqrt{N}}$$
   with unconditional $O(\log N / \sqrt{N})$ bound
   $|\operatorname{fullPairing}(\operatorname{sourceFactorialCausal}\,N)| \le (10\log(4N+1) + 3 + 1/(4N))/\sqrt{N}$.

3. **Plancherel–Laplace Spectral Band Producer Bridge (§3):**
   Combining `packetEnergy_eq_integral_fourier_mul_spectralDensity` from `PacketEnergyPlancherel`
   with our prime-free `laplaceEnergyProducerBound N` bounds any finite-band weighted spectral
   integral $\int_{-\xi_0}^{\xi_0} \|\mathcal{F}f(\xi)\|^2 (\frac{1}{4} + 4\pi^2\xi^2) S_N(\xi)\,d\xi$
   directly by the archimedean Laplace producer.

4. **Exact Franel–Selberg GCD–LCM Gram Law (§4):**
   Using $\gcd(a+1, b+1)\operatorname{lcm}(a+1, b+1) = (a+1)(b+1)$, we prove that the periodic
   Franel sawtooth Gram entry `franelGramEntry a b` equals $\frac{\gcd(a+1, b+1)}{12\,\operatorname{lcm}(a+1, b+1)}$,
   dominating the smooth Selberg LCM kernel $\frac{1}{12\,\operatorname{lcm}(a+1, b+1)}$ everywhere
   and coinciding with it on coprime pairs.
-/

open Complex MeasureTheory Set Filter Topology Finset
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped BigOperators CompactlySupported Real FourierTransform ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Fold-Free Log-Möbius Approximant in `ker P` & Harmonic-Shadow Pythagoras Decomposition -/

/-- The harmonic shadow coefficient of `logMobiusFermiApprox N` along the canonical self-similar
profile `canonicalSelfSimilar`:
$$\operatorname{logMobiusHarmonicShadow}(N)
  := \sum_{d=1}^N \frac{\mu(d)\log(N / d)}{d\,\log N}.$$ -/
def logMobiusHarmonicShadow (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N) / (d : ℝ)

/-- **Exact Arithmetic Decomposition of `logMobiusHarmonicShadow N`:**
For every `N ≥ 2`, the harmonic shadow of `logMobiusFermiApprox N` splits into the raw Möbius
harmonic sum `finiteHarmonicSum N moebiusDivisorWeight = ∑_{d=1}^N μ(d)/d` plus
`moebiusLogHarmonicSum N / log N`:
$$\operatorname{logMobiusHarmonicShadow}(N)
  = \operatorname{finiteHarmonicSum}(N, \operatorname{moebiusDivisorWeight})
    + \frac{\operatorname{moebiusLogHarmonicSum}(N)}{\log N}.$$ -/
theorem logMobiusHarmonicShadow_eq_moebius_add_log_harmonic {N : ℕ} (hN : 2 ≤ N) :
    logMobiusHarmonicShadow N =
      finiteHarmonicSum N moebiusDivisorWeight +
        moebiusLogHarmonicSum N / Real.log (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < (N : ℝ))).ne'
  unfold logMobiusHarmonicShadow finiteHarmonicSum moebiusLogHarmonicSum
    moebiusDivisorWeight vonMangoldtDivisorWeight
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  rw [Real.log_div hN_pos.ne' hd_pos.ne']
  field_simp [hlogN, hd_pos.ne']
  ring

/-- **Exact Inner Product of `logMobiusFermiApprox N` with `canonicalSelfSimilar`:**
For EVERY `N : ℕ` (with **zero hypotheses**!),
$$\int_0^1 \operatorname{logMobiusFermiApprox}(N, t)\,\overline{s_0(t)}\,dt
  = \operatorname{logMobiusHarmonicShadow}(N).$$ -/
theorem integral_logMobiusFermiApprox_mul_conj_canonicalSelfSimilar (N : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      logMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
    ((logMobiusHarmonicShadow N : ℝ) : ℂ) := by
  have hrew : (fun t => logMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      fun t => -(∑ d ∈ Finset.Icc 1 N,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N : ℝ) : ℂ) *
          (fermiNymanGen (d : ℝ) t * (starRingEnd ℂ) (canonicalSelfSimilar t))) := by
    funext t
    unfold logMobiusFermiApprox
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hrew, integral_neg, integral_finsetSum _ (fun d _ =>
    (integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) measurable_canonicalSelfSimilar
      (integrableOn_normSq_fermiNymanGen _) integrableOn_normSq_canonicalSelfSimilar).const_mul _)]
  unfold logMobiusHarmonicShadow
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hd_eq : (d : ℝ) = ((d - 1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hd1).symm
  rw [integral_const_mul, hd_eq, integral_fermiNymanGen_nat_mul_conj_canonicalSelfSimilar (d - 1)]
  have hd_eq_C : (((d - 1 + 1 : ℕ) : ℂ)) = (d : ℂ) := by
    exact_mod_cast Nat.sub_add_cancel hd1
  rw [hd_eq_C]
  ring

/-- The **fold-free log-Möbius approximant** in $\ker P$, obtained by subtracting the exact
self-similar shadow projection from `logMobiusFermiApprox N`:
$$\operatorname{foldFreeLogMobiusFermiApprox}(N, t)
  := \operatorname{logMobiusFermiApprox}(N, t)
    - \frac{\operatorname{logMobiusHarmonicShadow}(N)}{2}\,s_0(t).$$ -/
def foldFreeLogMobiusFermiApprox (N : ℕ) (t : ℝ) : ℂ :=
  logMobiusFermiApprox N t -
    ((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ) * canonicalSelfSimilar t

theorem measurable_foldFreeLogMobiusFermiApprox (N : ℕ) :
    Measurable (foldFreeLogMobiusFermiApprox N) :=
  (measurable_logMobiusFermiApprox N).sub
    (measurable_const.mul measurable_canonicalSelfSimilar)

theorem integrableOn_normSq_logMobiusFermiApprox (N : ℕ) :
    IntegrableOn (fun t => ‖logMobiusFermiApprox N t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have heq : (fun t => ‖logMobiusFermiApprox N t‖ ^ 2) =
      fun t => ‖dyadicHaar t - (dyadicHaar t - logMobiusFermiApprox N t)‖ ^ 2 := by
    funext t; congr 2; ring
  rw [heq]
  exact integrableOn_normSq_sub measurable_dyadicHaar
    (measurable_dyadicHaar.sub (measurable_logMobiusFermiApprox N))
    integrableOn_normSq_dyadicHaar
    (integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N)

theorem integrableOn_normSq_foldFreeLogMobiusFermiApprox (N : ℕ) :
    IntegrableOn (fun t => ‖foldFreeLogMobiusFermiApprox N t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  unfold foldFreeLogMobiusFermiApprox
  have hS : IntegrableOn
      (fun t => ‖((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ) * canonicalSelfSimilar t‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
    have hrew : (fun t => ‖((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ) * canonicalSelfSimilar t‖ ^ 2) =
        fun t => ‖((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ)‖ ^ 2 * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t; rw [norm_mul, mul_pow]
    rw [hrew]
    exact integrableOn_normSq_canonicalSelfSimilar.const_mul _
  exact integrableOn_normSq_sub (measurable_logMobiusFermiApprox N)
    (measurable_const.mul measurable_canonicalSelfSimilar)
    (integrableOn_normSq_logMobiusFermiApprox N) hS

/-- **Unconditional Orthogonality of `foldFreeLogMobiusFermiApprox N` to $s_0$:**
For EVERY `N : ℕ` (with **zero hypotheses**!),
$$\int_0^1 \operatorname{foldFreeLogMobiusFermiApprox}(N, t)\,\overline{s_0(t)}\,dt = 0.$$ -/
theorem integral_foldFreeLogMobiusFermiApprox_mul_conj_canonicalSelfSimilar (N : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      foldFreeLogMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 := by
  have h1 : IntegrableOn
      (fun t => logMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_logMobiusFermiApprox N)
      measurable_canonicalSelfSimilar (integrableOn_normSq_logMobiusFermiApprox N)
      integrableOn_normSq_canonicalSelfSimilar
  have h2 : IntegrableOn
      (fun t => ((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ) *
        (canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)))
      (Ioc (0 : ℝ) 1) :=
    (integrableOn_mul_conj_of_sq measurable_canonicalSelfSimilar
      measurable_canonicalSelfSimilar integrableOn_normSq_canonicalSelfSimilar
      integrableOn_normSq_canonicalSelfSimilar).const_mul _
  have hsplit : (fun t => foldFreeLogMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      fun t => logMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t) -
        ((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ) *
          (canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
    funext t
    unfold foldFreeLogMobiusFermiApprox
    ring
  rw [hsplit, integral_sub h1 h2, integral_logMobiusFermiApprox_mul_conj_canonicalSelfSimilar N,
    integral_const_mul, integral_canonicalSelfSimilar_mul_conj_self]
  push_cast
  ring

/-- The $\ker P$ error energy of the fold-free log-Möbius approximant:
$$\operatorname{foldFreeLogMobiusErrorEnergy}(N)
  := \int_0^1 \bigl\|\operatorname{dyadicHaar}(t) - \operatorname{foldFreeLogMobiusFermiApprox}(N, t)\bigr\|^2\,dt.$$ -/
def foldFreeLogMobiusErrorEnergy (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - foldFreeLogMobiusFermiApprox N t‖ ^ 2

theorem foldFreeLogMobiusErrorEnergy_nonneg (N : ℕ) :
    0 ≤ foldFreeLogMobiusErrorEnergy N :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Exact Orthogonal Pythagoras Decomposition of `logMobiusFermiErrorEnergy N`:**
For EVERY `N : ℕ` (with **zero hypotheses**!), the $L^2(0, 1]$ error energy of
`logMobiusFermiApprox N` splits identically into the $\ker P$ fold-free error energy plus half the
squared harmonic shadow:
$$\operatorname{logMobiusFermiErrorEnergy}(N)
  = \operatorname{foldFreeLogMobiusErrorEnergy}(N)
    + \frac{\operatorname{logMobiusHarmonicShadow}(N)^2}{2}.$$ -/
theorem logMobiusFermiErrorEnergy_eq_foldFree_add_harmonic_shadow (N : ℕ) :
    logMobiusFermiErrorEnergy N =
      foldFreeLogMobiusErrorEnergy N + logMobiusHarmonicShadow N ^ 2 / 2 := by
  set R : ℝ → ℂ := fun t => dyadicHaar t - foldFreeLogMobiusFermiApprox N t
  set α : ℂ := -((logMobiusHarmonicShadow N / 2 : ℝ) : ℂ)
  set S : ℝ → ℂ := fun t => α * canonicalSelfSimilar t
  have hRm : Measurable R := measurable_dyadicHaar.sub (measurable_foldFreeLogMobiusFermiApprox N)
  have hSm : Measurable S := measurable_const.mul measurable_canonicalSelfSimilar
  have hR2 : IntegrableOn (fun t => ‖R t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_normSq_sub measurable_dyadicHaar (measurable_foldFreeLogMobiusFermiApprox N)
      integrableOn_normSq_dyadicHaar (integrableOn_normSq_foldFreeLogMobiusFermiApprox N)
  have hS2 : IntegrableOn (fun t => ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    have hrew : (fun t => ‖S t‖ ^ 2) = fun t => ‖α‖ ^ 2 * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t; simp only [S, norm_mul, mul_pow]
    rw [hrew]
    exact integrableOn_normSq_canonicalSelfSimilar.const_mul (‖α‖ ^ 2)
  have hRS_int : IntegrableOn (fun t => R t * (starRingEnd ℂ) (S t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq hRm hSm hR2 hS2
  have hRe_int : IntegrableOn (fun t => 2 * (R t * (starRingEnd ℂ) (S t)).re) (Ioc (0 : ℝ) 1) :=
    hRS_int.re.const_mul 2
  have hRS2 : IntegrableOn (fun t => ‖R t‖ ^ 2 + ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) := hR2.add hS2
  have hpt : (fun t => ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) =
      fun t => (‖R t‖ ^ 2 + ‖S t‖ ^ 2) + 2 * (R t * (starRingEnd ℂ) (S t)).re := by
    funext t
    have heq : dyadicHaar t - logMobiusFermiApprox N t = R t + S t := by
      simp only [R, S, α, foldFreeLogMobiusFermiApprox]
      ring
    rw [heq]
    exact complex_norm_add_sq_eq (R t) (S t)
  unfold logMobiusFermiErrorEnergy foldFreeLogMobiusErrorEnergy
  rw [hpt, integral_add hRS2 hRe_int, integral_add hR2 hS2]
  have hR_orth : (∫ t in Ioc (0 : ℝ) 1, R t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 := by
    have h1 := integrableOn_mul_conj_of_sq measurable_dyadicHaar measurable_canonicalSelfSimilar
      integrableOn_normSq_dyadicHaar integrableOn_normSq_canonicalSelfSimilar
    have h2 := integrableOn_mul_conj_of_sq (measurable_foldFreeLogMobiusFermiApprox N)
      measurable_canonicalSelfSimilar (integrableOn_normSq_foldFreeLogMobiusFermiApprox N)
      integrableOn_normSq_canonicalSelfSimilar
    have hsub : (fun t => R t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
        fun t => dyadicHaar t * (starRingEnd ℂ) (canonicalSelfSimilar t) -
          foldFreeLogMobiusFermiApprox N t * (starRingEnd ℂ) (canonicalSelfSimilar t) := by
      funext t; dsimp [R]; ring
    rw [hsub, integral_sub h1 h2, integral_dyadicHaar_mul_conj_canonicalSelfSimilar,
      integral_foldFreeLogMobiusFermiApprox_mul_conj_canonicalSelfSimilar N, sub_zero]
  have hcross : (∫ t in Ioc (0 : ℝ) 1, 2 * (R t * (starRingEnd ℂ) (S t)).re) = 0 := by
    rw [integral_const_mul, ← RCLike.re_eq_complex_re, integral_re hRS_int]
    have hRS_zero : (∫ t in Ioc (0 : ℝ) 1, R t * (starRingEnd ℂ) (S t)) = 0 := by
      have hfactor : (fun t => R t * (starRingEnd ℂ) (S t)) =
          fun t => (starRingEnd ℂ) α * (R t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
        funext t; simp only [S, map_mul]; ring
      rw [hfactor, integral_const_mul, hR_orth, mul_zero]
    rw [hRS_zero, map_zero, mul_zero]
  have hS_val : (∫ t in Ioc (0 : ℝ) 1, ‖S t‖ ^ 2) = logMobiusHarmonicShadow N ^ 2 / 2 := by
    have hrew : (fun t => ‖S t‖ ^ 2) =
        fun t => (logMobiusHarmonicShadow N ^ 2 / 4) * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t
      simp only [S, α, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, div_pow]
      ring
    rw [hrew, integral_const_mul, integral_normSq_canonicalSelfSimilar]
    ring
  rw [hcross, add_zero, hS_val]

/-- **Strict Producer Improvement for the Fold-Free Log-Möbius Error Energy (`N ≥ 2`):**
For every `N ≥ 2`, the $\ker P$ fold-free error energy is bounded above by
`logMobiusTotalEnergyProducer N` minus half the squared harmonic shadow:
$$\operatorname{foldFreeLogMobiusErrorEnergy}(N)
  \;\le\; \operatorname{logMobiusTotalEnergyProducer}(N)
    - \frac{\operatorname{logMobiusHarmonicShadow}(N)^2}{2}.$$ -/
theorem foldFreeLogMobiusErrorEnergy_le_producer_sub_shadow {N : ℕ} (hN : 2 ≤ N) :
    foldFreeLogMobiusErrorEnergy N ≤
      logMobiusTotalEnergyProducer N - logMobiusHarmonicShadow N ^ 2 / 2 := by
  have h1 := logMobiusFermiErrorEnergy_le_total_producer hN
  have h2 := logMobiusFermiErrorEnergy_eq_foldFree_add_harmonic_shadow N
  linarith

/-- **Unconditional Producer Bound on `logMobiusHarmonicShadow N ^ 2` (`N ≥ 2`):**
Because `0 ≤ foldFreeLogMobiusErrorEnergy N`, the squared harmonic shadow is unconditionally
bounded by `2 * logMobiusTotalEnergyProducer N`:
$$\operatorname{logMobiusHarmonicShadow}(N)^2
  \;\le\; 2\,\operatorname{logMobiusTotalEnergyProducer}(N).$$ -/
theorem logMobiusHarmonicShadow_sq_le_two_mul_producer {N : ℕ} (hN : 2 ≤ N) :
    logMobiusHarmonicShadow N ^ 2 ≤ 2 * logMobiusTotalEnergyProducer N := by
  have h1 := foldFreeLogMobiusErrorEnergy_le_producer_sub_shadow hN
  have h0 := foldFreeLogMobiusErrorEnergy_nonneg N
  linarith

/-! ## §2. Exact Full Pairing & Quantitative `O(log N / √N)` Producer Bound for `sourceFactorialCausal N` -/

/-- The tent-convolved causal factorial producer bundled as an element of `C_c(ℝ, ℝ)` for every
`n : ℕ` (at scale `n + 1 ≥ 1`). -/
def causalFactorialProducer (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨sourceFactorialCausal (n + 1), continuous_sourceFactorialCausal (n + 1)⟩,
    hasCompactSupport_sourceFactorialCausal (by omega : 1 ≤ n + 1)⟩

/-- Because `sourceFactorialCausal N (Real.log n) = factorialBiNull N (Real.log n)` at every
integer `n ≥ 1`, its prime-power sequence `primeTerm (sourceFactorialCausal N)` coincides
identically with `primeTerm (factorialBiNull N)`. -/
theorem primeTerm_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    primeTerm (sourceFactorialCausal N) = primeTerm (factorialBiNull N) := by
  funext n
  unfold primeTerm
  split_ifs with hn
  · rw [sourceFactorialCausal_at_log hN (by omega)]
  · rfl

/-- For every `N ≥ 1`, `polarDensity * sourceFactorialCausal N` is integrable on `ℝ`. -/
theorem integrable_polar_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x : ℝ => polarDensity x * sourceFactorialCausal N x) :=
  (continuous_polarDensity.mul (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
    ((hasCompactSupport_sourceFactorialCausal hN).mul_left (f := polarDensity))

/-- Full admissibility of `sourceFactorialCausal N` for the global signed prime–polar measure. -/
theorem sourceFactorialCausal_admissible {N : ℕ} (hN : 1 ≤ N) :
    (Function.support (primeTerm (sourceFactorialCausal N))).Finite ∧
      Summable (fun n => |primeTerm (sourceFactorialCausal N) n|) ∧
      IntegrableOn (fun x => polarDensity x * sourceFactorialCausal N x) (Ici 0) := by
  rw [primeTerm_sourceFactorialCausal hN]
  exact ⟨(factorialBiNull_admissible N).1, (factorialBiNull_admissible N).2.1,
    (integrable_polar_sourceFactorialCausal hN).integrableOn⟩

/-- **Exact Polar Integral of `sourceFactorialCausal N` on `[0, ∞)`:**
Since $\operatorname{polarDensity}(x) = 2\cosh(x/2) = e^{x/2} + e^{-x/2}$, combining
`integral_exp_half_sourceFactorialCausal` and `integral_exp_neg_half_sourceFactorialCausal` gives:
$$\int_0^\infty \operatorname{polarDensity}(x)\,\operatorname{sourceFactorialCausal}(N, x)\,dx
  = \frac{\operatorname{sourceFactorialCoefficient}(N)\,\operatorname{harmonicCorrection}(N)
    - \operatorname{chebyshevBiNullProducer}(N)}{\sqrt{N}}.$$ -/
theorem integral_polar_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ici (0 : ℝ), polarDensity x * sourceFactorialCausal N x) =
      (sourceFactorialCoefficient N * harmonicCorrection N - chebyshevBiNullProducer N) /
        Real.sqrt N := by
  rw [← integral_weight_sourceFactorialCausal_eq_halfLine hN polarDensity]
  have hi_pos : Integrable (fun x : ℝ => Real.exp (x / 2) * sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
      ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have hi_neg : Integrable (fun x : ℝ => Real.exp (-(x / 2)) * sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
      ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have hsplit : (fun x : ℝ => polarDensity x * sourceFactorialCausal N x) =
      fun x : ℝ => Real.exp (x / 2) * sourceFactorialCausal N x +
        Real.exp (-(x / 2)) * sourceFactorialCausal N x := by
    funext x
    unfold polarDensity
    rw [Real.cosh_eq]
    ring
  rw [hsplit, integral_add hi_pos hi_neg,
    integral_exp_half_sourceFactorialCausal hN,
    integral_exp_neg_half_sourceFactorialCausal hN]
  ring

/-- **Exact Full Pairing Identity for `sourceFactorialCausal N`:**
For every `N ≥ 1`,
$$\operatorname{fullPairing}(\operatorname{sourceFactorialCausal}\,N)
  = \frac{2\,\operatorname{chebyshevBiNullProducer}(N)
    - \operatorname{sourceFactorialCoefficient}(N)\,\operatorname{harmonicCorrection}(N)}{\sqrt{N}}.$$ -/
theorem fullPairing_sourceFactorialCausal_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (sourceFactorialCausal N) =
      (2 * chebyshevBiNullProducer N -
        sourceFactorialCoefficient N * harmonicCorrection N) / Real.sqrt N := by
  unfold fullPairing
  rw [primeTerm_sourceFactorialCausal hN, tsum_primeTerm_factorialBiNull N,
    integral_polar_sourceFactorialCausal hN]
  ring

/-- **Unconditional Quantitative `O(log N / √N)` Producer Bound on `fullPairing (sourceFactorialCausal N)`:**
For every `N ≥ 1`,
$$\bigl|\operatorname{fullPairing}(\operatorname{sourceFactorialCausal}\,N)\bigr|
  \;\le\; \frac{10\log(4N + 1) + 3 + \frac{1}{4N}}{\sqrt{N}}.$$ -/
theorem abs_fullPairing_sourceFactorialCausal_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (sourceFactorialCausal N)| ≤
      (10 * Real.log (4 * (N : ℝ) + 1) + 3 + 1 / (4 * (N : ℝ))) / Real.sqrt N := by
  rw [fullPairing_sourceFactorialCausal_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have hb := abs_chebyshevBiNullProducer_le hN
  obtain ⟨hc0, hc1⟩ := harmonicCorrection_bounds hN
  obtain ⟨hcoeff_lo, hcoeff_hi⟩ := sourceFactorialCoefficient_bounds hN
  have hcoeff_nonneg : 0 ≤ sourceFactorialCoefficient N := by linarith
  calc |2 * chebyshevBiNullProducer N - sourceFactorialCoefficient N * harmonicCorrection N|
      ≤ |2 * chebyshevBiNullProducer N| + |sourceFactorialCoefficient N * harmonicCorrection N| :=
        abs_sub _ _
    _ = 2 * |chebyshevBiNullProducer N| + sourceFactorialCoefficient N * harmonicCorrection N := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (mul_nonneg hcoeff_nonneg hc0)]
    _ ≤ 2 * (5 * Real.log (4 * (N : ℝ) + 1) + 1) + (1 + 1 / (4 * (N : ℝ))) * 1 := by
        nlinarith [mul_le_mul hcoeff_hi hc1 hc0 (by positivity)]
    _ = 10 * Real.log (4 * (N : ℝ) + 1) + 3 + 1 / (4 * (N : ℝ)) := by ring

/-- Hypothesis-free `O(log(n+1) / √(n+1))` full-pairing bound for `causalFactorialProducer n`. -/
theorem abs_fullPairing_causalFactorialProducer_le (n : ℕ) :
    |fullPairing (causalFactorialProducer n)| ≤
      (10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 + 1 / (4 * ((n + 1 : ℕ) : ℝ))) /
        Real.sqrt (n + 1 : ℕ) :=
  abs_fullPairing_sourceFactorialCausal_le (by omega : 1 ≤ n + 1)

/-! ## §3. Plancherel–Laplace Spectral Producer Bridge for `packetEnergy` -/

/-- **Unconditional Plancherel–Laplace Producer Bound:**
For every `C¹` compactly supported source `f : C_c(ℝ, ℝ)` and `N : ℕ`, the full Plancherel
spectral integral of `packetEnergy f N` equals
$$\int_{\mathbb{R}} \|\mathcal{F}f(\xi)\|^2 \left(\frac{1}{4} + 4\pi^2\xi^2\right) S_N(\xi)\,d\xi$$
and is bounded unconditionally from above by the prime-free archimedean Laplace producer
`laplaceEnergyProducerBound N`:
$$\int_{\mathbb{R}} \|\mathcal{F}f(\xi)\|^2 \left(\frac{1}{4} + 4\pi^2\xi^2\right) S_N(\xi)\,d\xi
  \;\le\; 3\left(10 + 2\,\operatorname{laplaceEnergyProducerBound}(N)
    + 2\bigl((1 - L_N)e^{-L_N/2}\bigr)^2\right)\operatorname{autocorr}(f, 0)
    + 3\left(\int |D_{1/2}f|\right)^2 \bigl(2\,\operatorname{laplaceEnergyProducerBound}(N) + 2\bigr).$$ -/
theorem integral_fourier_mul_spectralDensity_le_laplaceProducer
    (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    (∫ ξ, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * (1 / 4 + (2 * π * ξ) ^ 2) * spectralDensity N ξ) ≤
      3 * (10 + 2 * laplaceEnergyProducerBound N +
            2 * ((1 - SignedPrimePolar.cutoff N) *
              Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2) * autocorr f 0 +
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (2 * laplaceEnergyProducerBound N + 2) := by
  rw [← packetEnergy_eq_integral_fourier_mul_spectralDensity f N]
  have hp := packetEnergy_le_laplaceEnergy_gauge f hf N
  have hl := laplaceEnergy_le_laplaceEnergyProducerBound N
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have h1 :
      3 * (10 + 2 * ChebyshevGauge.laplaceEnergy N +
            2 * ((1 - SignedPrimePolar.cutoff N) *
              Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2) * autocorr f 0 ≤
        3 * (10 + 2 * laplaceEnergyProducerBound N +
              2 * ((1 - SignedPrimePolar.cutoff N) *
                Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2) * autocorr f 0 := by
    nlinarith
  have h2 :
      3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (2 * ChebyshevGauge.laplaceEnergy N + 2) ≤
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (2 * laplaceEnergyProducerBound N + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-! ## §4. Exact Franel–Selberg GCD–LCM Gram Law -/

/-- **Exact Franel–Selberg GCD–LCM Gram Identity (`franelGramEntry_eq_gcd_div_lcm`):**
For EVERY `a b : ℕ` (with **zero hypotheses**!), since
$\gcd(a + 1, b + 1)\,\operatorname{lcm}(a + 1, b + 1) = (a + 1)(b + 1)$, the periodic Franel
sawtooth Gram matrix entry `franelGramEntry a b` equals one-twelfth of the GCD-to-LCM ratio:
$$\operatorname{franelGramEntry}(a, b)
  = \frac{\gcd(a + 1, b + 1)}{12\,\operatorname{lcm}(a + 1, b + 1)}.$$ -/
theorem franelGramEntry_eq_gcd_div_lcm (a b : ℕ) :
    franelGramEntry a b =
      (Nat.gcd (a + 1) (b + 1) : ℝ) / (12 * (Nat.lcm (a + 1) (b + 1) : ℝ)) := by
  rw [franelGramEntry_eq_gcd a b]
  have hprod : ((Nat.gcd (a + 1) (b + 1) : ℝ) * (Nat.lcm (a + 1) (b + 1) : ℝ)) =
      ((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm (a + 1) (b + 1)
  have hgcd_pos : 0 < Nat.gcd (a + 1) (b + 1) :=
    Nat.gcd_pos_of_pos_left (b + 1) (Nat.succ_pos a)
  have hlcm_pos : 0 < Nat.lcm (a + 1) (b + 1) :=
    Nat.lcm_pos (Nat.succ_pos a) (Nat.succ_pos b)
  have hgcd_ne : (Nat.gcd (a + 1) (b + 1) : ℝ) ≠ 0 := by exact_mod_cast hgcd_pos.ne'
  have hlcm_ne : (Nat.lcm (a + 1) (b + 1) : ℝ) ≠ 0 := by exact_mod_cast hlcm_pos.ne'
  have hab : 12 * ((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) =
      12 * ((Nat.gcd (a + 1) (b + 1) : ℝ) * (Nat.lcm (a + 1) (b + 1) : ℝ)) := by
    rw [hprod]
    ring
  rw [hab]
  field_simp [hgcd_ne, hlcm_ne]

/-- **Unconditional Pointwise Dominance of the Smooth Selberg LCM Kernel by the Franel Gram Entry:**
For EVERY `a b : ℕ` (with **zero hypotheses**!), since $\gcd(a + 1, b + 1) \ge 1$,
$$\frac{1}{12\,\operatorname{lcm}(a + 1, b + 1)} \;\le\; \operatorname{franelGramEntry}(a, b).$$ -/
theorem one_div_twelve_lcm_le_franelGramEntry (a b : ℕ) :
    1 / (12 * (Nat.lcm (a + 1) (b + 1) : ℝ)) ≤ franelGramEntry a b := by
  rw [franelGramEntry_eq_gcd_div_lcm a b]
  have hgcd : (1 : ℝ) ≤ (Nat.gcd (a + 1) (b + 1) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (b + 1) (Nat.succ_pos a)
  exact div_le_div_of_nonneg_right hgcd (by positivity)

/-- **Exact Agreement of the Franel Gram Entry and the Selberg LCM Kernel on Coprime Scales:**
Whenever `a + 1` and `b + 1` are coprime,
$$\operatorname{franelGramEntry}(a, b) = \frac{1}{12\,\operatorname{lcm}(a + 1, b + 1)}.$$ -/
theorem franelGramEntry_eq_one_div_twelve_lcm_of_coprime {a b : ℕ}
    (hcop : Nat.Coprime (a + 1) (b + 1)) :
    franelGramEntry a b = 1 / (12 * (Nat.lcm (a + 1) (b + 1) : ℝ)) := by
  rw [franelGramEntry_eq_gcd_div_lcm a b, hcop.gcd_eq_one, Nat.cast_one]

end

end GaloisForLFunctions.BiScaleUncertainty
