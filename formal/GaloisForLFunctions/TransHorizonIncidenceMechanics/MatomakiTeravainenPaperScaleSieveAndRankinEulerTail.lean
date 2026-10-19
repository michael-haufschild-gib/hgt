import GaloisForLFunctions.TransHorizonIncidenceMechanics.FourthRootPrimeWindowSieveAndGallagherLinearTransfer
import GaloisForLFunctions.RHTower.Sieve.SiftTailDivisorEulerBound
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1Coefficient
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC2PaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3PaperScale

/-!
# Matomäki–Teräväinen Paper-Scale Sieve Coefficients ($c_{1,n}, c_{2,n}, c_{3,n}$) and Rankin–Euler Tail Bounds

This module connects `TransHorizonIncidenceMechanics` (`FourthRootPrimeWindowSieveAndGallagherLinearTransfer`)
to four unconditional Buchstab/Legendre sieve-decomposition modules in `RHTower/Sieve/`:

1. **Rankin–Euler Bound on the Discarded Smooth Divisor Tail
   (`rankin_euler_largeSiftDivisors_tail_bound`):**
   Connects `divisor_rpow_invLog_le_exp_card_primeFactors`, `card_pow_mul_rpow_invLog_le`, and
   `sum_largeSiftDivisors_card_pow_div_le` (`SiftTailDivisorEulerBound.lean:21, 44, 68`) to
   `TransHorizonIncidenceMechanics`: for any sifting level $z \ge 2$, truncation cutoff $D > 0$,
   and divisor power $K \in \mathbb{N}$, every divisor $e \mid P(z)$ satisfies
   $d(e)^K e^{1/\log z} \le (2^K e)^{\omega(e)}$, and the discarded-divisor harmonic sum over
   `largeSiftDivisors z D` = $\{e \mid P(z) : e > D\}$ is bounded by
   $$D^{-1/\log z} \exp\!\bigl(2^K e (\log \log z + C_{\mathrm{Mertens}})\bigr).$$

2. **Literal Legendre-Truncation Error $c_{1,n}$ Weighted by $d_3(n)$
   (`mtC1_legendre_truncation_ternary_divisor_bound`):**
   Connects `norm_mtC1Coefficient_le`, `ternaryDivisorCount_mul_norm_mtC1Coefficient_le`, and
   `sum_ternaryDivisorCount_mul_norm_mtC1Coefficient_le` (`MatomakiTeravainenC1Coefficient.lean:25, 59, 80`):
   for any bounded sequence $\|\alpha_m\| \le B$, the Legendre truncation error
   `mtC1Coefficient α z D n` satisfies
   $$\sum_{n=1}^Y d_3(n) \|c_{1,n}\| \le
     B Y (1 + \log Y)^7 D^{-1/\log z} \exp\!\bigl(8 e (\log \log z + C_{\mathrm{Mertens}})\bigr).$$

3. **Paper-Scale $(\log X)^{-3A}$ Saving for the Endpoint Spill $c_{2,n}$ and Band-Discretization
   Error $c_{3,n}$ (`eventually_mtC2_and_mtC3_ternary_weighted_log_rpow_saving`):**
   Connects `eventually_sum_ternaryWeighted_norm_mtC2_le_log_rpow`
   (`MatomakiTeravainenC2PaperScale.lean:71`) and
   `eventually_sum_ternaryWeighted_norm_mtC3_le_log_rpow`
   (`MatomakiTeravainenC3PaperScale.lean:141`): for every $A \ge 2$ and all sufficiently large $X$,
   both the endpoint spill coefficient `mtC2Coefficient` and the band-discretization error
   `mtC3Coefficient` have $d_3(n)$-weighted first moments over $1 \le n \le Y \le 4X$ bounded by
   $B Y (\log X)^{-3A}$, absorbing all seven logarithmic powers from $d_3(n)$ and the outer prime
   harmonic factor into the paper width $\delta_A = (\log X)^{-10A}$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open scoped Real BigOperators ArithmeticFunction.Moebius
open _root_.Zeta23 _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Rankin–Euler Bound on the Discarded Smooth Divisor Tail -/

/-- **Rankin–Euler Bound on `largeSiftDivisors z D` (`rankin_euler_largeSiftDivisors_tail_bound`):**
For any sifting level $z \ge 2$, truncation cutoff $D > 0$, and divisor exponent $K \in \mathbb{N}$:
1. Every divisor $e \mid P(z)$ has Rankin tilt $e^{1/\log z} \le e^{\omega(e)}$ and combined
   divisor-Rankin weight $d(e)^K e^{1/\log z} \le (2^K e)^{\omega(e)}$.
2. The discarded-divisor harmonic sum $\sum_{e \in \operatorname{largeSiftDivisors}(z, D)} d(e)^K / e$
   is bounded by $D^{-1/\log z} \exp(2^K e (\log \log z + C_{\mathrm{Mertens}}))$. -/
theorem rankin_euler_largeSiftDivisors_tail_bound
    (K : ℕ) {z D : ℕ} (hz : 2 ≤ z) (hD : 0 < D) :
    (∀ e ∈ (siftModulus z).divisors,
      (e : ℝ) ^ (1 / Real.log z) ≤ (Real.exp 1) ^ e.primeFactors.card ∧
      ((e.divisors.card : ℝ) ^ K) * (e : ℝ) ^ (1 / Real.log z) ≤
        (((2 : ℝ) ^ K) * Real.exp 1) ^ e.primeFactors.card) ∧
    (∑ e ∈ largeSiftDivisors z D,
        ((e.divisors.card : ℝ) ^ K) / (e : ℝ) ≤
      (D : ℝ) ^ (-(1 / Real.log z)) *
        Real.exp ((((2 : ℝ) ^ K) * Real.exp 1) *
          (logLog z + mertensSecondUpperConst))) :=
  ⟨fun _ he => ⟨divisor_rpow_invLog_le_exp_card_primeFactors hz he,
                card_pow_mul_rpow_invLog_le K hz he⟩,
   sum_largeSiftDivisors_card_pow_div_le K hz hD⟩

/-! ## §2. Literal Legendre-Truncation Error $c_{1,n}$ Weighted by $d_3(n)$ -/

/-- **Pointwise and $d_3(n)$-Weighted First Moment Bounds for `mtC1Coefficient`
(`mtC1_legendre_truncation_ternary_divisor_bound`):**
For any coefficient sequence $\alpha : \mathbb{N} \to \mathbb{C}$ with $\|\alpha_m\| \le B$ ($B \ge 0$),
sifting level $z \ge 2$, truncation cutoff $D > 0$, and horizon $Y \ge 1$:
1. For every $n > 0$, $(d_3(n) : \mathbb{R}) \|c_{1,n}\| \le B \cdot \operatorname{weightedSiftTailDivisorCount}(3, z, D, n)$.
2. The $d_3(n)$-weighted sum over $1 \le n \le Y$ satisfies
   $$\sum_{n=1}^Y d_3(n) \|c_{1,n}\| \le
     B Y (1 + \log Y)^7 D^{-1/\log z} \exp\!\bigl(8 e (\log \log z + C_{\mathrm{Mertens}})\bigr).$$ -/
theorem mtC1_legendre_truncation_ternary_divisor_bound
    (α : ℕ → ℂ) {z D Y : ℕ} (hz : 2 ≤ z) (hD : 0 < D) (hY : 1 ≤ Y)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    (∀ {n : ℕ}, 0 < n →
      (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
        B * weightedSiftTailDivisorCount 3 z D n) ∧
    (∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC1Coefficient α z D n‖ ≤
      B * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        ((D : ℝ) ^ (-(1 / Real.log z)) *
          Real.exp ((((2 : ℝ) ^ 3) * Real.exp 1) *
            (logLog z + mertensSecondUpperConst))))) :=
  ⟨fun hn => ternaryDivisorCount_mul_norm_mtC1Coefficient_le α hn hB hα,
   sum_ternaryDivisorCount_mul_norm_mtC1Coefficient_le α hz hD hY hB hα⟩

/-! ## §3. Paper-Scale $(\log X)^{-3A}$ Saving for $c_{2,n}$ and $c_{3,n}$ -/

/-- **Simultaneous Paper-Scale $(\log X)^{-3A}$ Saving for `mtC2Coefficient` and `mtC3Coefficient`
(`eventually_mtC2_and_mtC3_ternary_weighted_log_rpow_saving`):**
For every $A \ge 2$, eventually as $X \to \infty$, both the endpoint spill coefficient
`mtC2Coefficient` and the band-discretization coefficient `mtC3Coefficient` satisfy the
$d_3(n)$-weighted first-moment bound $\le B Y (\log X)^{-3A}$ across all $1 \le Y \le 4X$. -/
theorem eventually_mtC2_and_mtC3_ternary_weighted_log_rpow_saving (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      (∀ (α : ℕ → ℂ) (level : ℕ → ℕ)
          (aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
        1 ≤ Y → (Y : ℝ) ≤ 4 * X →
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
        aLower ≤ bLower →
        ((bLower - 1 : ℕ) : ℝ) ≤
          (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
        aUpper ≤ bUpper →
        ((bUpper - 1 : ℕ) : ℝ) ≤
          (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
        0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
        ∑ n ∈ Finset.Icc 1 Y,
            (ternaryDivisorCount n : ℝ) *
              ‖mtC2Coefficient α (primesIco aLower bLower)
                (primesIco aUpper bUpper) level n‖ ≤
          B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) ∧
      (∀ (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (Y N : ℕ) (B : ℝ),
        1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
        (∀ q ∈ S, q.Prime) → (∀ q ∈ S, q ≤ N) →
        (∀ q ∈ S,
          mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
        (∀ q ∈ S, lower q ≤ q) →
        (∀ q ∈ S, ((q - 1 : ℕ) : ℝ) ≤
          (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
        0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
        ∑ n ∈ Finset.Icc 1 Y,
            (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
          B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) :=
  (eventually_sum_ternaryWeighted_norm_mtC2_le_log_rpow A hA).and
    (eventually_sum_ternaryWeighted_norm_mtC3_le_log_rpow A hA)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
