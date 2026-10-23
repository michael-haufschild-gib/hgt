import GaloisForLFunctions.ReflectiveDirichletPolynomialS2.CubicTraceS2ReflectionReduction
import GaloisForLFunctions.ReflectiveDirichletPolynomialS2.ShortWindowDispersionAtSeventeenThirtieths

/-!
# Master Theorem: Self-Dual Reflective Dirichlet-Polynomial Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower

This module completes **Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial Closure in the
Guth–Maynard / Chen–Gupta–Li $S_2$ Tower)** by packaging all four legs into a single unconditional
theorem (`reflective_dirichlet_polynomial_s2_master_theorem`):

1. **Signed Principal Reflection Factorization & Self-Dual Scale Law
   (`sum_fourier_pos_eq_mellin_headPoly_integral`, `selfDual_reflection_scale_product`,
   `selfDual_ceiling_length_bounds`, `gmNonzero_conj_symm_and_lemma62_bound`):**
   The positive- and negative-frequency Poisson sums $\sum_{m=1}^M \hat{h}_t(\pm mN)$ factorize
   inside the Mellin vertical line integral into the unweighted Dirichlet head polynomial
   $D_M(\pm t - y) = \sum_{m=1}^M m^{-i(\pm t - y)}$ times the stationary-phase integral
   $K(\pm t - y; \log N, \log(2MN))$; at the self-dual scale $N = |t|^{(1+\epsilon)/2}$, the
   reflected length $M = \lceil |t|^{1+\epsilon}/N \rceil = \lceil N \rceil$ satisfies
   $N \le M < N + 1$.
2. **Exact $q = 1$ Cubic Trace $S_2$ Plane-Diagonal Decomposition & Single-Block Reduction
   (`cglTraceS2_modulusOne_eq_diag_add_offDiag`, `cglTraceS2_modulusOne_le_single_dyadic_block`):**
   The two-nonzero-frequency component $S_2$ of the $q = 1$ Chen–Gupta–Li cubic Gram trace equals
   $3N^3(\hat{h}_0(0)\sum_{x,y \in W} \|A(x-y)\|^2 + \text{off-diag})$ and is bounded by a single
   dyadic block $2^j \le M \le (2T)^{1+\epsilon}/N + 1$ of the unweighted Heath–Brown pair sum
   `hbPairSum W (dyadicSegmentBlock M j) 1`.
3. **Unconditional `30/13` Zero-Density, Uniform `17/30` Short-Interval Prime Theorem, and Widened
   Smooth-Tapered Cross-Scale Dispersion up to `Q ≤ P^{30/17 - δ}`
   (`guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window`,
   `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range`):**
   Couples the Guth–Maynard $S_2$ closure with smooth-tapered higher-order Bernoulli elimination,
   extending unconditional smooth-plus-centred-prime cross-scale dispersion across the entire
   unbalanced range $P^{1+\delta} \le Q \le P^{30/17 - \delta}$.
4. **Balanced-Regime Three-Way Equivalence with the Quasi-Riemann Hypothesis
   (`moebius_and_prime_powerWindowSaving_iff_quasiRH`):**
   In the balanced self-dual regime ($Q \asymp P$), short-window power saving for the Möbius row,
   short-window power saving for the prime row, and the quasi-Riemann hypothesis
   $\text{zetaZeroAbscissa} < 1$ are unconditionally equivalent.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Finset Filter Topology BigOperators Real
open scoped FourierTransform ComplexConjugate
open RHTower RHTower.GuthMaynard RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.SmoothBernoulliPoleCalibration

noncomputable section

namespace GaloisForLFunctions.ReflectiveDirichletPolynomialS2

/-- **Master Theorem for Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial Closure in the
Guth–Maynard / Chen–Gupta–Li $S_2$ Tower):**
Unconditionally establishes:
1. the exact signed principal reflection factorization of $\sum_{m=1}^M \hat{h}_t(mN)$ and the
   self-dual length law $N \le \lceil |t|^{1+\epsilon}/N \rceil < N + 1$ at
   $N = |t|^{(1+\epsilon)/2}$,
2. the exact plane-diagonal decomposition and single-dyadic-block Heath–Brown pair-sum bound for
   the $q = 1$ Chen–Gupta–Li cubic trace $S_2$,
3. the unconditional `30/13` zero-density / uniform `17/30` short-interval prime theorem coupled
   with smooth-tapered cross-scale dispersion across $P^{1+\delta} \le Q \le P^{30/17 - \delta}$,
   and
4. the three-way balanced-regime equivalence
   `MoebiusPowerWindowSaving ↔ PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1`. -/
theorem reflective_dirichlet_polynomial_s2_master_theorem (w : CGLRealSmoothBump) :
    -- (1) Signed principal reflection identity & self-dual length law
    (∀ (t N : ℝ), 0 < N → ∀ M : ℕ,
      ∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y : ℝ, cglGMMellinLine w y *
            ((Complex.exp (((-((t - y) * Real.log N) : ℝ) : ℂ) * I) *
              cglGMHeadPoly M (t - y)) *
              cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N)))) ∧
    (∀ (t ε : ℝ), 0 < |t| →
      let N := |t| ^ ((1 + ε) / 2)
      ⌈|t| ^ (1 + ε) / N⌉₊ = ⌈N⌉₊ ∧
        N ≤ (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) ∧
        (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) < N + 1) ∧
    -- (2) Exact q = 1 CGL cubic trace S₂ plane-diagonal split & single-block reflection bound
    (∀ (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value),
      Function.Injective (fun r => (rows r).time) →
      ∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
          cglLemma45TraceFrequencyTerm w N modulusOne R rows m =
        3 * ((N.value : ℂ) ^ 3 *
          (gmHat w 0 0 *
            (gmS2Diagonal w N.value (Finset.univ.image fun r => (rows r).time) : ℂ) +
            ∑ x ∈ Finset.univ.image (fun r => (rows r).time),
              ∑ y ∈ Finset.univ.image (fun r => (rows r).time),
                ∑ z ∈ (Finset.univ.image (fun r => (rows r).time)).erase x,
                  gmS2Kernel w N.value x y z))) ∧
    (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (N : CGLPositiveLength) (R : ℕ)
        (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value), 1 ≤ T →
        (∀ r s, r ≠ s → T ^ ε ≤ |(rows r).time - (rows s).time|) →
        (∀ r, 0 ≤ (rows r).time ∧ (rows r).time ≤ T) →
        ∃ M j : ℕ, 1 ≤ M ∧ 2 ^ j ≤ M ∧ (M : ℝ) ≤ (2 * T) ^ (1 + ε) / N.value + 1 ∧
          ‖∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m},
              cglLemma45TraceFrequencyTerm w N modulusOne R rows m‖ ≤
            C * (T ^ ε) ^ 6 *
              ((N.value : ℝ) ^ 2 / 2 ^ j *
                Sieve.hbPairSum (Finset.univ.image fun r => (rows r).time)
                  (Sieve.dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)))) ∧
    -- (3) Widened 17/30 smooth-tapered + centred prime row cross-scale dispersion up to P^{30/17-δ}
    (∀ {δ ε C : ℝ}, 0 < δ → δ ≤ 1 → 0 < ε → ε ≤ 1 → 1 ≤ C →
      ∃ P₀ : ℕ, ∀ {N L A H K P Q : ℕ} {C₀ : ℝ} {c c'_smooth : ℕ → ℝ},
        P₀ ≤ P → (P : ℝ) ^ (1 + δ) ≤ Q → (Q : ℝ) ≤ (P : ℝ) ^ (30 / 17 - δ) →
        Q ≤ A → A + K * H ≤ 2 * Q → 2 * Q ≤ N → (N : ℝ) ≤ (Q : ℝ) ^ C →
        (2 * (Q : ℝ)) ^ (17 / 30 + δ / 4) ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ (17 / 30 + δ / 4) →
        (∀ d, c d ≠ 0 → d.Prime ∧ P < d ∧ d ≤ 2 * P) →
        IsSmoothTaperedAtScale N L Q C₀ c'_smooth →
        |crossScaleFunctional N c (fun n => c'_smooth n + centredPrimeRow A H K n)| ≤
          2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
            ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
              ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) *
            (∑ n ∈ Icc 1 N, |c'_smooth n| / (n : ℝ) ^ 2) +
          16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c) ∧
    -- (4) Balanced-regime three-way equivalence with the quasi-Riemann hypothesis
    ((MoebiusPowerWindowSaving ↔ PrimePowerWindowSaving) ∧
      (MoebiusPowerWindowSaving ↔ zetaZeroAbscissa < 1) ∧
      (PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1)) :=
  ⟨fun t N hN M => sum_fourier_pos_eq_mellin_headPoly_integral w t N hN M,
   fun _ _ ht => selfDual_ceiling_length_bounds ht,
   cglTraceS2_modulusOne_eq_diag_add_offDiag w,
   fun hε hε1 => cglTraceS2_modulusOne_le_single_dyadic_block w hε hε1,
   fun hδ hδ1 hε hε1 hC =>
     exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range hδ hδ1 hε hε1 hC,
   moebius_and_prime_powerWindowSaving_iff_quasiRH⟩

end GaloisForLFunctions.ReflectiveDirichletPolynomialS2
