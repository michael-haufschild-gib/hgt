import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeLogSigmaRate
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelMoments
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedOriginalForms
import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogThresholdNatRatio
import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedDiagonalProductEnergy

/-!
# Differentiated Barban–Vehov Kernels, Smooth-Prime $\sigma_{-1/2}$ Rate, and Mollified Product-Fibre Energy

This module connects `BezoutValuationIncidence` (`BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge`)
to five unconditional sieve and mollifier engines in `RHTower/Sieve/`:

1. **Moving-Modulus Coprime Logarithmic Möbius Asymptotic with Chen's $\sigma_{-1/2}(r)$ Factor
   (`coprimeLogMoebius_totientRatio_sigmaNegHalf_rate`):**
   Upgrades the constant upper bound $|M_r(Y)| \le A$ used in
   `BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge.lean` to the quantitative
   moving-modulus asymptotic `exists_abs_coprimeLogMoebius_sub_totientRatio_sigmaNegHalfBound`
   (`SmoothPrimeCoprimeLogSigmaRate.lean:16`): for every squarefree modulus $r$,
   $$\left|\operatorname{coprimeLogMoebius}(r, Y) - \frac{r}{\varphi(r)}\right| \le
     C \frac{r / \varphi(r)}{(\log(Y/D))^2} +
       (7 + |\gamma|) D^{-1/4} \cdot 4^{16} \sigma_{-1/2}(r)$$
   for all $1 \le D \le \lfloor Y \rfloor$ with $Y / D \ge K$.

2. **Differentiated Barban–Vehov Long Kernels and Min-Logarithm Omitted-Head Selberg Boundaries
   (`differentiated_barbanVehov_kernel_moments_and_omitted_selberg_min_forms`):**
   - Expresses `barbanVehovLongHarmonicKernel L U q r`, `barbanVehovLongFirstLogKernel L U q r`,
     and `barbanVehovLongSecondLogKernel L U q r` in terms of `1 / lcm(q, r)` and the scaled
     logarithmic window moments `harmonicLogWindowMoment m (L / lcm(q, r)) (U / lcm(q, r))`
     ($m = 0, 1, 2$) (`DifferentiatedBarbanVehovKernelMoments.lean:18, 26, 42`).
   - Identifies the omitted-head base, cross, and derivative-square Barban–Vehov polynomial main
     terms with the exact Selberg-coefficient quadratic forms in $A = \log(M/p_1)$,
     $B = \log(M/p_2)$, and $u = \min(A, B)$
     (`DifferentiatedBarbanVehovOmittedOriginalForms.lean:69, 84, 100, 131, 146, 164`).

3. **Natural-Ratio Thresholded Shifted Möbius Kernels and Zero-Twist Mollified Product-Fibre Energy
   (`moebius_shifted_log_nat_ratio_and_mollified_product_energy`):**
   - Connects `sum_moebius_log_threshold_nat_ratio_eq_shifted` and
     `sum_moebius_log_sq_threshold_nat_ratio_eq_shifted`
     (`MoebiusShiftedLogThresholdNatRatio.lean:19, 45`) to express thresholded linear and quadratic
     Selberg–Möbius sums at natural ratio $N/q$ via `moebiusShiftedLogKernelReal t ((N/q) e^{-t})`
     and `moebiusShiftedLogSqKernelReal t ((N/q) e^{-t})`.
   - Connects `mollifiedTwistedDiagonal_zero_eq_productEnergy` and
     `mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq`
     (`MollifiedTwistedDiagonalProductEnergy.lean:116, 135`) to express the zero-twist four-index
     mollified diagonal as the exact product-fibre Gram energy of `mollifiedProductCoeff`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-! ## §1. Moving-Modulus Coprime Logarithmic Möbius Rate with $\sigma_{-1/2}(r)$ -/

/-- **Moving-Modulus Coprime Logarithmic Möbius Asymptotic with Chen's $\sigma_{-1/2}(r)$ Factor
(`coprimeLogMoebius_totientRatio_sigmaNegHalf_rate`):**
For every squarefree modulus $r$, there exist $C \ge 0$ and $K \ge e$ such that for all $Y \in \mathbb{R}$
and $1 \le D \le \lfloor Y \rfloor$ with $K \le Y / D$, the coprime logarithmic Möbius sum
`coprimeLogMoebius r Y` approximates the singular totient ratio $r / \varphi(r)$ within
$$C \frac{r / \varphi(r)}{(\log(Y/D))^2} + (7 + |\gamma|) D^{-1/4} \cdot 4^{16} \sigma_{-1/2}(r).$$ -/
theorem coprimeLogMoebius_totientRatio_sigmaNegHalf_rate {r : ℕ} (hr : Squarefree r) :
    ∃ C K : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ K ∧
      ∀ (Y : ℝ) (D : ℕ), 1 ≤ D → D ≤ ⌊Y⌋₊ → K ≤ Y / (D : ℝ) →
        |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
          C * ((r : ℝ) / (Nat.totient r : ℝ)) /
              (Real.log (Y / (D : ℝ))) ^ 2 +
            (7 + |Real.eulerMascheroniConstant|) *
              ((D : ℝ) ^ (-(1 / 4 : ℝ)) *
                ((4 : ℝ) ^ 16 * squarefreeSigmaNegHalf r)) :=
  exists_abs_coprimeLogMoebius_sub_totientRatio_sigmaNegHalfBound hr

/-! ## §2. Differentiated Barban–Vehov Long Kernels and Omitted-Head Selberg Min-Forms -/

/-- **Differentiated Barban–Vehov Long Kernel Moments and Omitted-Head Selberg Min-Logarithm Forms
(`differentiated_barbanVehov_kernel_moments_and_omitted_selberg_min_forms`):**
1. For any $0 < q, r$ and window $(L, U]$, the long harmonic, first-logarithmic, and
   second-logarithmic Barban–Vehov kernels factor through `1 / lcm(q, r)` and the scaled logarithmic
   window moments `harmonicLogWindowMoment m (L / lcm(q, r)) (U / lcm(q, r))` ($m = 0, 1, 2$).
2. For any $0 < M$ and shift $\ell \in \mathbb{R}$, the omitted-head base, cross, and
   derivative-square Barban–Vehov polynomial main terms equal the exact Selberg-coefficient
   min-logarithm quadratic forms in $A = \log(M/p_1)$, $B = \log(M/p_2)$, and $u = \min(A, B)$. -/
theorem differentiated_barbanVehov_kernel_moments_and_omitted_selberg_min_forms
    {L U q r M : ℕ} (hq : 0 < q) (hr : 0 < r) (hM : 0 < M) (ell : ℝ) :
    (barbanVehovLongHarmonicKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) ∧
    barbanVehovLongFirstLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
            harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          harmonicLogWindowMoment 1 (L / Nat.lcm q r) (U / Nat.lcm q r)) ∧
    barbanVehovLongSecondLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
              harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
              harmonicLogWindowMoment 1 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          harmonicLogWindowMoment 2 (L / Nat.lcm q r) (U / Nat.lcm q r))) ∧
    ((barbanVehovOmittedLongBasePolynomialMain M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        selbergOriginalCoeff p.1 p.2 * (A * B * min A B)) ∧
    (barbanVehovOmittedLongCrossPolynomialMain ell M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        let u := min A B
        (-1 : ℝ) * selbergOriginalCoeff p.1 p.2 * (A * B) *
          (u * (ell + B) - u ^ (2 : ℕ) / 2)) ∧
    (barbanVehovOmittedLongDerivativePolynomialMain ell M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        let u := min A B
        selbergOriginalCoeff p.1 p.2 * (A * B) *
          (u * (ell + A) * (ell + B) -
            u ^ (2 : ℕ) / 2 * (2 * ell + A + B) + u ^ (3 : ℕ) / 3))) := by
  refine ⟨⟨barbanVehovLongHarmonicKernel_eq_moment hq hr,
    barbanVehovLongFirstLogKernel_eq_moments hq hr,
    barbanVehovLongSecondLogKernel_eq_moments hq hr⟩, ?_, ?_, ?_⟩
  · rw [barbanVehovOmittedLongBasePolynomialMain_eq_originalBoundary,
      selbergOriginalOmittedBaseBoundary_eq_min M hM]
  · rw [barbanVehovOmittedLongCrossPolynomialMain_eq_originalBoundary,
      selbergOriginalOmittedCrossBoundary_eq_min ell M hM]
  · rw [barbanVehovOmittedLongDerivativePolynomialMain_eq_originalBoundary,
      selbergOriginalOmittedDerivativeBoundary_eq_min ell M hM]

/-! ## §3. Natural-Ratio Thresholded Shifted Möbius Kernels and Mollified Product-Fibre Energy -/

/-- **Natural-Ratio Thresholded Shifted Möbius Kernels and Zero-Twist Mollified Product-Fibre Energy
(`moebius_shifted_log_nat_ratio_and_mollified_product_energy`):**
1. For any $0 < N$, $0 < q$, and $0 \le t$, the thresholded linear and quadratic Selberg–Möbius sums
   over $1 \le u \le N / q$ equal `moebiusShiftedLogKernelReal t ((N/q) e^{-t})` and
   `moebiusShiftedLogSqKernelReal t ((N/q) e^{-t})`.
2. For any coefficient families $a, b, u, v : \mathbb{N} \to \mathbb{C}$, finite supports $s, q$,
   and initial cutoffs $L, M$, the zero-twist mollified diagonal equals `mollifiedProductEnergy`,
   and the self-paired zero-twist diagonal on $[1, L] \times [1, M]$ is the sum of squared moduli
   of the product-fibre coefficients `mollifiedProductCoeff`. -/
theorem moebius_shifted_log_nat_ratio_and_mollified_product_energy
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t)
    (a b u v : ℕ → ℂ) (s qSet : Finset ℕ) (L M : ℕ) :
    ((∑ k ∈ Finset.Icc 1 (N / q),
        (selbergMoebiusReciprocalCoeff k *
          Real.log ((N : ℝ) / ((q * k : ℕ) : ℝ))) *
            (if t ≤ Real.log ((N : ℝ) / ((q * k : ℕ) : ℝ)) then (1 : ℝ) else 0)) =
        moebiusShiftedLogKernelReal t (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) ∧
      (∑ k ∈ Finset.Icc 1 (N / q),
        (selbergMoebiusReciprocalCoeff k *
          Real.log ((N : ℝ) / ((q * k : ℕ) : ℝ)) ^ (2 : ℕ)) *
            (if t ≤ Real.log ((N : ℝ) / ((q * k : ℕ) : ℝ)) then (1 : ℝ) else 0)) =
        moebiusShiftedLogSqKernelReal t (((N : ℝ) / (q : ℝ)) * Real.exp (-t))) ∧
    ((mollifiedTwistedDiagonal a b u v s qSet 0 =
        mollifiedProductEnergy a b u v s qSet) ∧
      (mollifiedTwistedDiagonalIcc a a u u L M 0 =
        ∑ r ∈ ((Finset.Icc 1 L) ×ˢ (Finset.Icc 1 M)).image (fun p => p.1 * p.2),
          ((Complex.normSq
            (mollifiedProductCoeff a u (Finset.Icc 1 L) (Finset.Icc 1 M) r) : ℝ) : ℂ))) :=
  ⟨⟨sum_moebius_log_threshold_nat_ratio_eq_shifted N q hN hq t ht,
    sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N q hN hq t ht⟩,
   ⟨mollifiedTwistedDiagonal_zero_eq_productEnergy a b u v s qSet,
    mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq a u L M⟩⟩

end GaloisForLFunctions.BezoutValuationIncidence

end
