import GaloisForLFunctions.TransHorizonIncidenceMechanics.WindowedQuarterZeroDensityAndCHMDBoundStateCount
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonRoughAbsorptionAndReset
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowSharpLevel
import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.GallagherRange
import GaloisForLFunctions.RHTower.Sieve.LinearVsMultiplicativeWindow
import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisFiveSixths
import GaloisForLFunctions.RHTower.ZetaZeroDensityTwelveFifths

/-!
# Fourth-Root Prime-Window Sieve, Gallagher Linear Transfer, and Uniform Quarter-Zero Density

This module connects `TransHorizonIncidenceMechanics` to three further unconditional engines in
`RHTower/` and `RHTower/Sieve/`:

1. **Fourth-Root Brun–Titchmarsh Prime-Window Sieve and Exact $\log q$ Cancellation on von Mangoldt Weights
   (`vonMangoldt_prime_nearDiagonal_weight_eq`, `integral_Icc_normSq_logPoly_vonMangoldt_le_prime_sharp`,
   `integral_Icc_normSq_LSeries_prime_sieve_le`):**
   In `RHTower/Sieve/PrimeWindowSharpLevel.lean`, taking the Brun–Titchmarsh sieve level at the fourth
   root $z = q^{1/4}$ bounds the unit-window prime neighbour count by $700 q / \log q + 1$.
   When specialized to prime-supported von Mangoldt weights $a_q = c_q \Lambda(q) = c_q \log q$,
   one factor of $\log q$ in $\|a_q\|^2 = (\log q)^2 \|c_q\|^2$ cancels identically against the
   denominator of $700 q / \log q$, reducing the near-diagonal weight from $O(q (\log q)^2)$ to
   $700 q \log q + (\log q)^2$.

2. **Gallagher's Multiplicative-to-Linear Short-Interval Transfer for Möbius Ensembles
   (`norm_moebiusReal_le_one`, `normSq_linear_moebiusReal_le_multiplicative_length`,
   `setIntegral_normSq_multiplicative_moebiusReal_window_le`):**
   Connects `LinearVsMultiplicativeWindow.normSq_linear_le_multiplicative_length` and
   `GallagherRange.setIntegral_normSq_multiplicative_window_le` to `moebiusReal`, transferring
   Gallagher's frequency-split bound on multiplicative windows $(e^u, e^u e^\delta]$ to linear
   short intervals $(x, x + L]$ up to the explicit length excess $2(y - (x + L) + 1)^2$.

3. **Uniform Huxley ($12/5 + \varepsilon$) and Density-Hypothesis ($2 + \varepsilon$) Bounds on
   `windowedQuarterZeros σ T`
   (`exists_windowedQuarterZeros_ncard_le_twelve_fifths`,
   `exists_windowedQuarterZeros_ncard_le_density_hypothesis`):**
   Upgrades the pointwise Ingham–Huxley bound of `WindowedQuarterZeroDensityAndCHMDBoundStateCount.lean`
   to bounds that hold **uniformly** in $\sigma \in [1/2, 1]$ (with exponent $(12/5 + \varepsilon)(1 - \sigma)$)
   and **uniformly** in $\sigma \in [5/6, 1]$ (with the Density Hypothesis exponent $(2 + \varepsilon)(1 - \sigma)$).
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open scoped Real BigOperators ArithmeticFunction.Moebius
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilDeletion
open _root_.RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Fourth-Root Prime-Window Sieve and Exact $\log q$ Cancellation on von Mangoldt Weights -/

/-- **Exact $\log q$ Cancellation in the Prime-Window Near-Diagonal Weight
(`vonMangoldt_prime_nearDiagonal_weight_eq`):**
For any prime $q$ and coefficient $c \in \mathbb{C}$, the fourth-root Brun–Titchmarsh prime-window
weight $(700 q / \log q + 1) \|c \cdot \Lambda(q)\|^2$ simplifies identically to
$(700 q \log q + (\log q)^2) \|c\|^2$, cancelling one power of $\log q$. -/
theorem vonMangoldt_prime_nearDiagonal_weight_eq {q : ℕ} (hq : q.Prime) (c : ℂ) :
    (700 * ((q : ℝ) / Real.log q) + 1) * ‖c * ((Λ q : ℝ) : ℂ)‖ ^ (2 : ℕ) =
      (700 * (q : ℝ) * Real.log q + Real.log q ^ (2 : ℕ)) * ‖c‖ ^ (2 : ℕ) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
  have hlog_pos : 0 < Real.log q := Real.log_pos (by linarith)
  have hlog_ne : Real.log q ≠ 0 := hlog_pos.ne'
  rw [ArithmeticFunction.vonMangoldt_apply_prime hq, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hlog_pos.le, mul_pow]
  field_simp

/-- **Sharp Prime-Supported Mean Value Theorem for von Mangoldt Weights
(`integral_Icc_normSq_logPoly_vonMangoldt_le_prime_sharp`):**
Combines `PrimeWindowSharpLevel.integral_Icc_normSq_logPoly_le_prime_sharp` (`PrimeWindowSharpLevel.lean:133`)
with `vonMangoldt_prime_nearDiagonal_weight_eq` so that on any prime support $s$, the near-diagonal
weight for $a_q = c_q \Lambda(q)$ drops from $O(q (\log q)^2)$ to $700 q \log q + (\log q)^2$. -/
theorem integral_Icc_normSq_logPoly_vonMangoldt_le_prime_sharp
    (c : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime) {W : ℝ} (hW : 2 * Real.pi * 1 * W ≤ 1) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun q => c q * ((Λ q : ℝ) : ℂ)) s w‖ ^ (2 : ℕ)) ≤
      (5 / 4) * ∑ q ∈ s,
        (700 * (q : ℝ) * Real.log q + Real.log q ^ (2 : ℕ)) * ‖c q‖ ^ (2 : ℕ) := by
  refine (integral_Icc_normSq_logPoly_le_prime_sharp
    (fun q => c q * ((Λ q : ℝ) : ℂ)) s hs hW).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  exact vonMangoldt_prime_nearDiagonal_weight_eq (hs q hq) (c q)

/-- **Truncated Mean Square of a Prime-Supported Dirichlet Series on the Perron Line
(`integral_Icc_normSq_LSeries_prime_sieve_le`):**
Connects `TruncatedPrimeSieveMeanSquare.integral_Icc_normSq_LSeries_le_prime_sieve`
(`TruncatedPrimeSieveMeanSquare.lean:26`) to `TransHorizonIncidenceMechanics`, bounding the
truncated Perron-line mean square $\int_{-T}^T \|L(a, \sigma + iy)\|^2 \, dy$ at the reciprocal
multiplicative window scale $\delta = 1/T$. -/
theorem integral_Icc_normSq_LSeries_prime_sieve_le {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * ((5 * T / 4) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1) / Real.log Y
            + selbergFibreError z Y + (z : ℝ))
              * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) :=
  integral_Icc_normSq_LSeries_le_prime_sieve hs0 hsupp hprime σ hT z Y hY hYz hz hlog

/-! ## §2. Gallagher's Multiplicative-to-Linear Short-Interval Transfer for Möbius Ensembles -/

/-- Every value of `moebiusReal n` has complex modulus at most `1`. -/
theorem norm_moebiusReal_le_one (n : ℕ) : ‖(moebiusReal n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hsq := (moebiusReal_le_one n).1
  nlinarith [sq_abs (moebiusReal n), abs_nonneg (moebiusReal n)]

/-- **Linear-to-Multiplicative Short-Interval Transfer for `moebiusReal`
(`normSq_linear_moebiusReal_le_multiplicative_length`):**
Applies `LinearVsMultiplicativeWindow.normSq_linear_le_multiplicative_length`
(`LinearVsMultiplicativeWindow.lean:117`) to `moebiusReal`: for any support $s \subseteq \mathbb{N}$
and $0 \le x, 0 \le L$ with $x + L \le y$, the squared linear short-interval Möbius sum over
$(x, x + L]$ is bounded by twice the squared multiplicative-window sum over $(x, y]$ plus the
length-excess term $2(y - (x + L) + 1)^2$. -/
theorem normSq_linear_moebiusReal_le_multiplicative_length (s : Finset ℕ)
    {x L y : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), (moebiusReal n : ℂ)‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), (moebiusReal n : ℂ)‖ ^ 2
        + 2 * (y - (x + L) + 1) ^ 2 :=
  normSq_linear_le_multiplicative_length (fun n => (moebiusReal n : ℂ)) s
    norm_moebiusReal_le_one hx hL h

/-- **Gallagher Multiplicative Short-Interval Mean-Square Bound for `moebiusReal`
(`setIntegral_normSq_multiplicative_moebiusReal_window_le`):**
Applies `GallagherRange.setIntegral_normSq_multiplicative_window_le` (`GallagherRange.lean:47`) to
`moebiusReal`, bounding the mean square of the multiplicative short-interval Möbius sum over
$u \in (\log A, \log B]$ by $M_1 \delta + M_2 \frac{2}{\pi^2 W}$ whenever `logPoly` is bounded by
$M_1$ on $[-W, W]$ and by $M_2$ globally. -/
theorem setIntegral_normSq_multiplicative_moebiusReal_window_le (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {δ M₁ M₂ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly (fun n => (moebiusReal n : ℂ)) s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly (fun n => (moebiusReal n : ℂ)) s w‖ ^ 2 ≤ M₂) (A B : ℝ) :
    (∫ u in Set.Ioc (Real.log A) (Real.log B),
        ‖∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ),
            (moebiusReal n : ℂ)‖ ^ 2)
      ≤ M₁ * δ + M₂ * (2 / (Real.pi ^ 2 * W)) :=
  setIntegral_normSq_multiplicative_window_le (fun n => (moebiusReal n : ℂ)) s hs
    hδ hW hM₁ hM₂ h₁ h₂ A B

/-! ## §3. Uniform Huxley and Density-Hypothesis Bounds on `windowedQuarterZeros σ T` -/

/-- **Uniform Huxley ($12/5 + \varepsilon$) Bound on `windowedQuarterZeros σ T`
(`exists_windowedQuarterZeros_ncard_le_twelve_fifths`):**
Combines `ncard_windowedQuarterZeros_le_zeroHeightBox` with
`RHTower.exists_zeroHeightBox_ncard_le_twelve_fifths` (`ZetaZeroDensityTwelveFifths.lean:175`) to
bound `((windowedQuarterZeros σ T).ncard : ℝ)` **uniformly** across all $\sigma \in [1/2, 1]$. -/
theorem exists_windowedQuarterZeros_ncard_le_twelve_fifths {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        ((windowedQuarterZeros σ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ (expDetCountLogExponent + 4) *
            T ^ ((12 / 5 + ε) * (1 - σ)) := by
  obtain ⟨D, hD, T₀, hT₀, hbound⟩ := exists_zeroHeightBox_ncard_le_twelve_fifths hε hε1
  refine ⟨D, hD, T₀, hT₀, fun T hT σ hσ12 hσ1 => ?_⟩
  have hle : ((windowedQuarterZeros σ T).ncard : ℝ) ≤ ((zeroHeightBox σ T).ncard : ℝ) := by
    exact_mod_cast ncard_windowedQuarterZeros_le_zeroHeightBox σ T
  exact hle.trans (hbound T hT σ hσ12 hσ1)

/-- **Uniform Density-Hypothesis ($2 + \varepsilon$) Bound on `windowedQuarterZeros σ T` for $\sigma \ge 5/6$
(`exists_windowedQuarterZeros_ncard_le_density_hypothesis`):**
Combines `ncard_windowedQuarterZeros_le_zeroHeightBox` with
`RHTower.exists_zeroHeightBox_ncard_le_density_hypothesis` (`ZetaZeroDensityHypothesisFiveSixths.lean:154`)
to bound `((windowedQuarterZeros σ T).ncard : ℝ)` **uniformly** across all $\sigma \in [5/6, 1]$ with
the Density Hypothesis exponent $(2 + \varepsilon)(1 - \sigma)$. -/
theorem exists_windowedQuarterZeros_ncard_le_density_hypothesis {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 5 / 6 ≤ σ → σ ≤ 1 →
        ((windowedQuarterZeros σ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ (dhLogExponent ε + 4) *
            T ^ ((2 + ε) * (1 - σ)) := by
  obtain ⟨D, hD, T₀, hT₀, hbound⟩ := exists_zeroHeightBox_ncard_le_density_hypothesis hε hε1
  refine ⟨D, hD, T₀, hT₀, fun T hT σ hσ56 hσ1 => ?_⟩
  have hle : ((windowedQuarterZeros σ T).ncard : ℝ) ≤ ((zeroHeightBox σ T).ncard : ℝ) := by
    exact_mod_cast ncard_windowedQuarterZeros_le_zeroHeightBox σ T
  exact hle.trans (hbound T hT σ hσ56 hσ1)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
