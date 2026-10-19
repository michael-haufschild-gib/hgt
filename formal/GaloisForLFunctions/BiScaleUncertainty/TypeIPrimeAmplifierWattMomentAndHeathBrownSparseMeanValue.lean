import GaloisForLFunctions.BiScaleUncertainty.CriticalBandLargeValuesAndHalaszSpectralBounds
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDivisorEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourcePowerDecay
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueLemma34

/-!
# Type-I Prime-Amplifier Watt Moment, Uniform Height Power Decay, and Heath–Brown Sparse Mean Value

This module connects `BiScaleUncertainty` (`CriticalBandLargeValuesAndHalaszSpectralBounds`) to four
unconditional engines in `RHTower/Sieve/` that were previously isolated from the `BiScaleUncertainty`
programme:

1. **Watt Reciprocal Unit-Block $N^{-2}$ Divisor Energy and Mixed Fourth–Second Moment
   (`mtWatt_unit_and_divisor_fourth_second_moment`):**
   Connects `sum_norm_sq_mtWattUnitCoeff_le_inv`,
   `exists_sum_norm_sq_mtWattProductDirCoeff_le_divisor`, and
   `exists_integral_mtWatt_divisorEnergy` (`MatomakiTeravainenWattDivisorEnergy.lean:10, 87, 158`)
   to `BiScaleUncertainty`, showing that multiplicative convolution of two reciprocal unit blocks
   $U_N(t)^2$ with a coefficient block $A(t)$ retains both $N^{-1}$ unit-block energies up to an
   arbitrarily small divisor power $O_\varepsilon(T^\varepsilon)$ on $[T/2, T]$.

2. **Restricted Type-I Mean Square over the Powered-Prime Amplifier Large Set and Uniform Height
   Power Decay
   (`mtTypeI_primeAmplifier_restricted_mean_square`,
   `mtTypeI_primeAmplifier_heathBrown_layer_source_power_decay`):**
   - Connects `exists_setIntegral_mtTypeI_primeAmplifier_coveredRange`
     (`MatomakiTeravainenTypeIPrimeAmplifierMoment.lean:44`) to bound the restricted Type-I mean
     square $\int_{E_{P,\ell}(T,V)} \|A(t)\|^2 \|U_N(t)\|^2 \, dt$ over the canonical powered-prime
     amplifier large set `mtTypeIPrimeAmplifierLargeSet P ell T V` via its $\ell$-block dyadic cover
     $B_r = P^\ell 2^r$.
   - Connects `exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourcePowerDecay`
     (`MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourcePowerDecay.lean:152`) to insert the
     ordered-prime density and uniform height power savings $T^{-9/2000}$ and $T^{-9/8000}$ across
     the paper interval $\alpha \in [10999/10000, 2]$ and sub-height range $X^{1/4} \le T \le X$.

3. **Heath–Brown One-Line Sparse-by-Dense Mean Value Theorem and Refined Regime
   (`heathBrown_oneLine_sparse_dense_mean_square_and_refined`):**
   Connects `integral_Icc_normSq_heathBrown_oneLine_le_lemma34` and
   `integral_Icc_normSq_heathBrown_oneLine_le_lemma34_refined`
   (`HeathBrownSparseMeanValueLemma34.lean:519, 616`) to `BiScaleUncertainty`, bounding the one-line
   mean square of a sparse unit-bounded Dirichlet polynomial $S_A(t)$ times a signed real dense
   dyadic Dirichlet polynomial $D_B(t)$ on $[-T, T]$, and eliminating the mixed $|A|^{7/4} T^{3/4}$
   term whenever $N \ge T^{2/3}$ or $|A| \le T^{1/3}$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open Zeta23 RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped BigOperators Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Watt Reciprocal Unit-Block $N^{-2}$ Divisor Energy and Mixed Fourth–Second Moment -/

/-- **Watt Reciprocal Unit-Block Energy and Mixed Fourth–Second Moment on $[T/2, T]$
(`mtWatt_unit_and_divisor_fourth_second_moment`):**
1. For $1 \le N$ and $N' \le 2N$, the $\ell^2$ energy of the reciprocal unit-block coefficients
   `mtWattUnitCoeff N N'` is at most $1/N$.
2. For every $\varepsilon > 0$, there exists $C > 0$ such that for all $1 \le A$, $1 \le N$,
   $N' \le 2N$, and $1 \le T$:
   - The multiplicative convolution coefficients `mtWattProductDirCoeff a A N N'` of $U_N^2 A$
     satisfy $\sum_r \|c_r\|^2 \le C^2 (2 A N'^2)^{\varepsilon/2} (N'^2)^{\varepsilon/2} A^{-2} (\sum_{A < n \le 2A} \|a_n\|^2) N^{-2}$.
   - The mixed fourth–second moment $\int_{T/2}^T \|U_N(t)\|^4 \|A(t)\|^2 \, dt$ is bounded by
     $C (2 A N'^2)^{\varepsilon/2} (N'^2)^{\varepsilon/2} (T + 2 A N'^2) A^{-2} (\sum_{A < n \le 2A} \|a_n\|^2) N^{-2}$. -/
theorem mtWatt_unit_and_divisor_fourth_second_moment :
    (∀ {N N' : ℕ}, 1 ≤ N → N' ≤ 2 * N →
      (∑ j : Fin N', ‖mtWattUnitCoeff N N' j‖ ^ 2) ≤ 1 / (N : ℝ)) ∧
    (∀ {ε : ℝ}, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
        1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
        (∑ r : Fin ((2 * A) * (N' * N')),
            ‖mtWattProductDirCoeff a A N N' r‖ ^ 2) ≤
          C ^ 2 * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
            ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
            (1 / (A : ℝ) ^ 2) *
            (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
            (1 / (N : ℝ)) ^ 2) ∧
    (∀ {ε : ℝ}, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
        1 ≤ A → 1 ≤ N → N' ≤ 2 * N →
        ∀ T : ℝ, 1 ≤ T →
        (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
          C * (((2 * A) * (N' * N') : ℕ) : ℝ) ^ (ε / 2) *
            ((N' * N' : ℕ) : ℝ) ^ (ε / 2) *
            (T + (((2 * A) * (N' * N') : ℕ) : ℝ)) *
            (1 / (A : ℝ) ^ 2) *
            (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
            (1 / (N : ℝ)) ^ 2) :=
  ⟨fun hN hN' => sum_norm_sq_mtWattUnitCoeff_le_inv hN hN',
   fun hε => exists_sum_norm_sq_mtWattProductDirCoeff_le_divisor hε,
   fun hε => exists_integral_mtWatt_divisorEnergy hε⟩

/-! ## §2. Restricted Type-I Mean Square over the Powered-Prime Amplifier Large Set -/

/-- **Restricted Type-I Mean Square over the Powered-Prime Amplifier Large Set
(`mtTypeI_primeAmplifier_restricted_mean_square`):**
For every $\varepsilon > 0$, there exists $C > 0$ such that whenever the $\ell$ dyadic blocks
$B_r = P^\ell 2^r$ of the powered-$(P, 2P]$ prime amplifier satisfy the Deshouillers–Iwaniec / Watt
Lemma 3.5 range conditions, the restricted Type-I mean square over
`mtTypeIPrimeAmplifierLargeSet P ell T V` is bounded by the sum of the $\ell$ block bounds
`mtTypeIPrimeBlockMomentBound C ε a A P ell N T V r`. -/
theorem mtTypeI_primeAmplifier_restricted_mean_square {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ),
      1 ≤ A → 1 ≤ P → 0 < ell → 1 ≤ N → N < N' → N' ≤ 2 * N →
      2 ≤ T → 0 < V →
      (∀ r : Fin ell,
        T ≤ (N : ℝ) ∨
          (((mtTypeIPrimeBlockLength P ell r : ℕ) : ℝ) ≤ T ∧
            ((((2 * mtTypeIPrimeBlockLength P ell r) * (N' * N') : ℕ) : ℝ) ≤
              ((mtTypeIPrimeBlockLength P ell r : ℕ) : ℝ) ^ (5 / 4 : ℝ) *
                T ^ (3 / 4 : ℝ)))) →
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ) *
            ‖mtWattUnitBlock N N' t‖ ^ (2 : ℕ)) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeBlockMomentBound C ε a A P ell N T V r :=
  exists_setIntegral_mtTypeI_primeAmplifier_coveredRange hε

/-- **Uniform Height Power Decay ($T^{-9/2000}$ and $T^{-9/8000}$) in the Heath–Brown Type-I Source
Layers (`mtTypeI_primeAmplifier_heathBrown_layer_source_power_decay`):**
Combines `mtTypeIPrimeDegree_negativeHalf_le_heightDecay`,
`mtTypeIPrimeDegree_negativeEighth_le_heightDecay`, and
`exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourcePowerDecay`:
1. On the paper interval $\alpha \ge 10999/10000$, the variable prime-amplifier powers
   $(P^\ell)^{-(1 - 1/\alpha)/2}$ and $(P^\ell)^{-(1 - 1/\alpha)/8}$ are bounded uniformly by
   $T^{-9/2000}$ and $T^{-9/8000}$.
2. For any divisor-bounded coefficient sequence $\|a_n\| \le C d(n)^w$, the restricted Type-I mean
   square over `mtTypeIPrimeSourceLargeSet P T epsilon` is eventually bounded across
   $X^{1/4} \le T \le X$ by the sum of `mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound`. -/
theorem mtTypeI_primeAmplifier_heathBrown_layer_source_power_decay :
    (∀ {P : ℕ} {T alpha : ℝ}, 2 ≤ P → 1 ≤ T → (10999 / 10000 : ℝ) ≤ alpha →
      (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ^ (-(1 - 1 / alpha) / 2) ≤
        T ^ (-9 / 2000 : ℝ) ∧
      (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ^ (-(1 - 1 / alpha) / 8) ≤
        T ^ (-9 / 8000 : ℝ)) ∧
    (∀ {epsilon etaLayer : ℝ}, 0 < epsilon → 0 < etaLayer →
      ∀ (C : ℝ) (w : ℕ),
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ᶠ X : ℝ in atTop,
            ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
            (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
            X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
            (∀ {n : ℕ}, 0 < n →
              ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) →
            1 ≤ A → (A : ℝ) ≤ T →
            2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N →
            let P := mtTypeIPrimeScale X alpha
            let ell := mtTypeIPrimeDegree P T
            let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
            (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
                ‖mtWattCoefficientBlock a A t‖ ^ 2 *
                  ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
              ∑ r : Fin ell,
                mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound
                  C₀ (epsilon / 100) (epsilon / 100) etaLayer
                    X A ell N T V r) :=
  ⟨fun hP hT halpha =>
    ⟨mtTypeIPrimeDegree_negativeHalf_le_heightDecay hP hT halpha,
     mtTypeIPrimeDegree_negativeEighth_le_heightDecay hP hT halpha⟩,
   exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourcePowerDecay⟩

/-! ## §3. Heath–Brown One-Line Sparse-by-Dense Mean Value Theorem -/

/-- **Heath–Brown One-Line Sparse-by-Dense Mean Value Theorem and Refined Regime
(`heathBrown_oneLine_sparse_dense_mean_square_and_refined`):**
For any sparse support $A \subseteq [M, T]$ with unit-bounded complex coefficients $\|\varepsilon_m\| \le 1$,
any dyadic dense support $B \subseteq (N, 2N]$ ($N \ge 2$) with signed real coefficients $a_n$, and
any $\eta > 0$:
1. **General One-Line Bound (`integral_Icc_normSq_heathBrown_oneLine_le_lemma34`):**
   $$\int_{-T}^T \|S_A(t) D_B(t)\|^2 \, dt \le C(\eta) (\max_{n \in B} |a_n|)^2
     \left(\frac{|A|^2}{M^2} + (NT)^\eta \frac{|A| T + |A|^{7/4} T^{3/4}}{M^2 N}\right).$$
2. **Refined Regime (`integral_Icc_normSq_heathBrown_oneLine_le_lemma34_refined`):**
   Whenever $N \ge T^{2/3}$ or $|A| \le T^{1/3}$, the mixed $|A|^{7/4} T^{3/4}$ term is eliminated:
   $$\int_{-T}^T \|S_A(t) D_B(t)\|^2 \, dt \le C_{\mathrm{ref}}(\eta) (\max_{n \in B} |a_n|)^2
     \left(\frac{|A|^2}{M^2} + (NT)^\eta \frac{|A| T}{M^2 N}\right).$$ -/
theorem heathBrown_oneLine_sparse_dense_mean_square_and_refined
    (A B : Finset PNat) (eps : ℕ → ℂ) (a : ℕ → ℝ)
    {M : ℝ} (hM : 1 ≤ M)
    (hAM : ∀ m ∈ A, M ≤ ((m : ℕ) : ℝ))
    (heps : ∀ m ∈ A, ‖eps (m : ℕ)‖ ≤ 1)
    (T : Set.Ioi (0 : ℝ)) (hMT : M ≤ (T : ℝ))
    (hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 2 ≤ N)
    (hBN : ∀ n ∈ B, N < (n : ℕ))
    (hB2N : ∀ n ∈ B, (n : ℕ) ≤ 2 * N)
    {eta : ℝ} (heta : 0 < eta) :
    ((∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B a t‖ ^ 2) ≤
      heathBrownLemma34Coefficient eta *
        (heathBrownDenseCoefficientMax B a) ^ 2 *
        (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ)) +
            (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              (M ^ 2 * (N : ℝ))))) ∧
    (((T : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ∨
        (A.card : ℝ) ≤ (T : ℝ) ^ (1 / 3 : ℝ)) →
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseOneLineFactor A eps t *
            heathBrownDenseOneLineFactor B a t‖ ^ 2) ≤
        heathBrownLemma34RefinedCoefficient eta *
          (heathBrownDenseCoefficientMax B a) ^ 2 *
          (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ))))) :=
  ⟨integral_Icc_normSq_heathBrown_oneLine_le_lemma34
      A B eps a hM hAM heps T hMT hAT hN hBN hB2N heta,
   fun hregime =>
     integral_Icc_normSq_heathBrown_oneLine_le_lemma34_refined
       A B eps a hM hAM heps T hMT hAT hN hBN hB2N hregime heta⟩

end

end GaloisForLFunctions.BiScaleUncertainty
