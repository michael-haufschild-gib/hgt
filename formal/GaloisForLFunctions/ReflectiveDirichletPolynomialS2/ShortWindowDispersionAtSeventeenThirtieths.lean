import GaloisForLFunctions.ArithmeticCompensationTheory.TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.SmoothTaperedCrossScaleDispersion
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis

/-!
# Widened `17/30` Smooth-Tapered Cross-Scale Dispersion and Balanced-Regime Quasi-RH Equivalence

This module formalizes the third leg of **Mechanism 5 (Self-Dual Reflective Dirichlet-Polynomial
Closure in the Guth–Maynard / Chen–Gupta–Li $S_2$ Tower)**:

1. **Unconditional `30/13` Zero-Density & Uniform `17/30` Short-Interval Prime Theorem
   (`guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window`):**
   Packages the unconditional Guth–Maynard zero-density bound
   `#(zeroHeightBox σ T) ≤ D (1 + log T)^B T^{(30/13 + ε)(1 - σ)}` with the uniform-in-length
   short-interval prime theorem `|ψ(x + h) - ψ(x) - h| ≤ ε h` for `x^α ≤ h ≤ x/2` (`17/30 < α < 1`)
   and the existence of primes in `(x, x + x^α]`.
2. **Smooth-Tapered + Centred Prime Row Cross-Scale Dispersion at the `17/30` Exponent
   (`exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_seventeenThirtieths`,
   `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range`):**
   Couples `abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale` with
   `exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths` and
   `exists_abs_rowBilinear_centredPrimeRow_le_of_range`, extending unconditional
   smooth-plus-centred-prime cross-scale dispersion from Huxley's `Q ≤ P^{12/7 - δ}` to the full
   Guth–Maynard unbalanced range `P^{1 + δ} ≤ Q ≤ P^{30/17 - δ}` (cross-scale exponent
   `θ = 2 log P / log Q > 17/15`).
3. **Balanced-Regime Three-Way Equivalence with the Quasi-Riemann Hypothesis
   (`moebius_and_prime_powerWindowSaving_iff_quasiRH`):**
   In the balanced self-dual regime (`Q ≍ P`), power-saving cancellation in short windows of
   length `⌈Q^α⌉` (`0 < α < 1`) for the Möbius row (`MoebiusPowerWindowSaving`) and for the prime
   row (`PrimePowerWindowSaving`) are unconditionally equivalent to each other and to the
   quasi-Riemann hypothesis `zetaZeroAbscissa < 1`.
-/

set_option autoImplicit false

open Finset Filter Topology BigOperators Real RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.SmoothBernoulliPoleCalibration

noncomputable section

namespace GaloisForLFunctions.ReflectiveDirichletPolynomialS2

/-! ### 1. Unconditional `30/13` Zero-Density and Uniform `17/30` Short-Interval Prime Theorem -/

/-- **Unconditional `30/13` Zero-Density and Uniform `17/30` Short-Interval Prime Package:**
For every `0 < ε ≤ 1` and `17/30 < α < 1`:
1. there exist `D ≥ 0`, `B : ℕ`, and `T₀ ≥ 1` such that for all `T ≥ T₀` and `σ ∈ [1/2, 1]`,
   `#(zeroHeightBox σ T) ≤ D (1 + log T)^B T^{(30/13 + ε)(1 - σ)}`,
2. `(ψ(x + x^α) - ψ(x)) / x^α → 1` as `x → ∞`,
3. for all sufficiently large `x` and all `x^α ≤ h ≤ x/2`, `|ψ(x + h) - ψ(x) - h| ≤ ε h`, and
4. for all sufficiently large `x`, there is a prime `p` with `x < p ≤ x + x^α`. -/
theorem guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window
    {α ε : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ →
      σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ ((30 / 13 + ε) * (1 - σ))) ∧
    Tendsto (fun x : ℝ => (Chebyshev.psi (x + x ^ α) - Chebyshev.psi x) / x ^ α) atTop (𝓝 1) ∧
    (∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x ^ α ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h) ∧
    (∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α) :=
  ⟨exists_zeroHeightBox_ncard_le_thirtyThirteenths hε hε1,
   tendsto_psi_short_window_div_seventeenThirtieths hα hα1,
   eventually_abs_psi_window_sub_le_seventeenThirtieths hα hα1 hε,
   eventually_exists_prime_short_interval_seventeenThirtieths hα hα1⟩

/-! ### 2. Smooth-Tapered + Centred Prime Row Cross-Scale Dispersion up to `Q ≤ P^{30/17 - δ}` -/

/-- **Smooth-Tapered + Centred Prime Row Cross-Scale Dispersion at the `17/30` Exponent:**
For every block exponent `17/30 < α < 1` and `0 < ε ≤ 1`, there exists a threshold `Q₀` such that
any superposition `c'_smooth + centredPrimeRow A H K` of an `L`-smooth-tapered baseline at scale `Q`
and the centred prime row on `[A, A + KH) ⊆ [Q, 2Q]` simultaneously eliminates the polynomial
Bernoulli tower on `c'_smooth` and achieves the `16 ε` rank-two dispersion bound on
`centredPrimeRow A H K`. -/
theorem exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_seventeenThirtieths
    {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q₀ : ℕ, ∀ {N L A H K P Q : ℕ} {C₀ : ℝ} {c c'_smooth : ℕ → ℝ},
      Q₀ ≤ Q → Q ≤ A → A + K * H ≤ 2 * Q → 2 * Q ≤ N → 1 ≤ P →
      (2 * (Q : ℝ)) ^ α ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ α →
      (∀ d, c d ≠ 0 → d.Prime ∧ P < d ∧ d ≤ 2 * P) →
      IsSmoothTaperedAtScale N L Q C₀ c'_smooth →
      (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8 ≤ ε * P →
      3 * (P : ℝ) ≤ 2 * ε * Q →
      |crossScaleFunctional N c (fun n => c'_smooth n + centredPrimeRow A H K n)| ≤
        2 * ((L : ℝ) + 1) * (4 : ℝ) ^ L * (L + 1).factorial *
          ((2 : ℝ) ^ L * C₀ * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ L +
            ∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) *
          (∑ n ∈ Icc 1 N, |c'_smooth n| / (n : ℝ) ^ 2) +
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_rowBilinear_centredPrimeRow_le_seventeenThirtieths hα hα1 hε hε1
  refine ⟨Q₀, ?_⟩
  intro N L A H K P Q C₀ c c'_smooth hQ hA hAK hN hP hH1 hH2 hc hsmooth hterm2 hterm3
  have h_bridge := abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale
    N L P Q C₀ (c'_osc := centredPrimeRow A H K)
    (fun d hd => ⟨(hc d hd).1, (hc d hd).2.2⟩) hsmooth
  have h_osc : |crossScaleFunctional N c (centredPrimeRow A H K)| ≤
      16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c :=
    hQ₀ hQ hA hAK hN hP hH1 hH2 (fun d hd => (hc d hd).2) hterm2 hterm3
  exact h_bridge.trans (add_le_add_right h_osc _)

/-- **Smooth-Tapered + Centred Prime Row Dispersion Across the Widened Range
`P^{1+δ} ≤ Q ≤ P^{30/17 - δ}`:**
For `0 < δ ≤ 1`, `0 < ε ≤ 1`, and `C ≥ 1`, there exists `P₀` such that for all `P ≥ P₀`,
`P^{1+δ} ≤ Q ≤ P^{30/17 - δ}`, horizons `2Q ≤ N ≤ Q^C`, windows `[A, A + KH) ⊆ [Q, 2Q]`, and
blocks `(2Q)^{17/30 + δ/4} ≤ H ≤ 4 Q^{17/30 + δ/4}`, any decomposed row
`c'_smooth + centredPrimeRow A H K` satisfies the joint order-`L` smooth-tapered + short-window
prime dispersion bound. -/
theorem exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le_of_range
    {δ ε C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 1 ≤ C) :
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
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  obtain ⟨P₀, hP₀⟩ := exists_abs_rowBilinear_centredPrimeRow_le_of_range hδ hδ1 hε hε1 hC
  refine ⟨P₀, ?_⟩
  intro N L A H K P Q C₀ c c'_smooth hP hQlo hQhi hA hAK hN hNC hH1 hH2 hc hsmooth
  have h_bridge := abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale
    N L P Q C₀ (c'_osc := centredPrimeRow A H K)
    (fun d hd => ⟨(hc d hd).1, (hc d hd).2.2⟩) hsmooth
  have h_osc : |crossScaleFunctional N c (centredPrimeRow A H K)| ≤
      16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c :=
    hP₀ hP hQlo hQhi hA hAK hN hNC hH1 hH2 (fun d hd => (hc d hd).2)
  exact h_bridge.trans (add_le_add_right h_osc _)

/-! ### 3. Balanced-Regime Three-Way Equivalence with the Quasi-Riemann Hypothesis -/

/-- **Balanced-Regime Equivalence: Short-Window Möbius Saving ↔ Short-Window Prime Saving ↔
Quasi-Riemann Hypothesis (`zetaZeroAbscissa < 1`):**
In the balanced regime (`Q ≍ P`), a power saving over the trivial `Q^{1 + 2α}` window energy at
any power length `0 < α < 1` for the Möbius function (`MoebiusPowerWindowSaving`) is
unconditionally equivalent to a power saving for the von Mangoldt function
(`PrimePowerWindowSaving`), and both are equivalent to the existence of a zero-free strip
`zetaZeroAbscissa < 1`. -/
theorem moebius_and_prime_powerWindowSaving_iff_quasiRH :
    (MoebiusPowerWindowSaving ↔ PrimePowerWindowSaving) ∧
    (MoebiusPowerWindowSaving ↔ zetaZeroAbscissa < 1) ∧
    (PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1) :=
  ⟨moebiusPowerWindowSaving_iff.trans primePowerWindowSaving_iff.symm,
   moebiusPowerWindowSaving_iff,
   primePowerWindowSaving_iff⟩

end GaloisForLFunctions.ReflectiveDirichletPolynomialS2
