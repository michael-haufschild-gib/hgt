import GaloisForLFunctions.«arithmetic-positivity-theory».SelbergExponentialNearLineAndThreeRegimeZeroDensity
import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistDegreeResonanceTrace
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistSpectrumGaps
import GaloisForLFunctions.Bottcher.ThetaDiscriminant

/-!
# Square-Root Threshold Prime-Tail Coupling, Selberg Twist Spectrum Gaps, and Self-Dual Theta Seam

This module connects `ArithmeticPositivityTheory` across the Lean corpus to `SquareRootThreshold`,
`SelbergClass`, and `Bottcher`:

1. **Localized Weil Prime-Tail Coupling, $2 \times 2$ Pole Compression, and Unconditional High-Height
   Positivity (`squareRootThreshold_primeTail_coupling_and_highHeight_positivity`):**
   - Connects `riemannHypothesis_iff_primePolynomial_le_archPart` and
     `primePolynomial_le_archPart_iff_poleCompression` (`PrimeTailCouplingCriterion.lean:66, 91`):
     positivity of the localized Weil form $W_\zeta(S_\xi f, S_\xi f) = A_f(\xi) - \Pi_f(\xi)$ at
     every aperture $a$ and height $2\pi\xi$ is equivalent to the $2 \times 2$ CCM Weil pole
     compression inequality $|\operatorname{ccmWeilPoleCross}(a)| \le \operatorname{ccmWeilPoleDiagonal}(a)$.
   - Connects `exists_archPart_zero_lt_primePolynomial` (`PrimeTailCouplingCriterion.lean:567`):
     unconditionally, there exists an aperture $a > 0$ and a $C^2$ profile $f$ supported in $[-a, a]$
     with $\operatorname{Re} A_f(0) < 0$ and $\operatorname{Re} A_f(0) < \operatorname{Re} \Pi_f(\xi)$
     at some height $\xi$, so the archimedean–pole budget cannot be frozen at height $0$.
   - Connects `zetaZeroConfig_re_W_heightShift_ge` and `exists_zetaZeroConfig_re_W_heightShift_nonneg`
     (`ZetaSingleHeightPositivityAboveArchimedeanHorizon.lean:232, 267`): every compactly supported
     $C^2$ profile has nonnegative localized Weil forms at all sufficiently large heights $|\xi| \ge \Xi$.

2. **Windowed Variance Below the Square-Root Threshold and Negative-Height Measure Bound
   (`windowed_weil_variance_and_bad_heights_measure_bound`):**
   - Connects `integral_windowed_sq_deviation_eq`, `lintegral_bad_heights_le`, and
     `exists_primeVariance_le` (`ZetaLocalizedFormWindowedVarianceLaw.lean:234, 264, 400`):
     for any window $\eta$ supported in $[-r, r]$ with $2 r e^{2a} \le 1$, the off-diagonal prime
     correlations vanish identically in the windowed mean square of $W_\zeta - A_f$, and the window
     weight of heights in $U$ where $\operatorname{Re} W_\zeta < 0$ is bounded by $\|\eta\|_2^2 V_f / A_0^2$.

3. **Selberg-Class Degree-Resonance Bohr Trace, Discrete Twist Spectrum Right-Gaps, and Jacobi–Böttcher
   Self-Dual Theta Seam (`selbergClass_degreeResonance_spectrum_gaps_and_thetaThree_seam`):**
   - Connects `bohrMean_positiveWeightedTangentFlow_degree_resonance` and
     `bohrMean_positiveWeightedTangentFlow_equal_degree`
     (`MultipleStandardTwistDegreeResonanceTrace.lean:102, 116`): the Bohr mean of the Selberg-class
     polar-hyperplane tangent flow projects onto the exact degree-resonance locus $m^{d_G} = n^{d_F}$
     (and onto the diagonal $m = n$ when $d_F = d_G = d > 0$).
   - Connects `MultipleStandardTwistData.spectralSublevel_finite` and
     `MultipleStandardTwistData.exists_spectrum_right_gap`
     (`MultipleStandardTwistSpectrumGaps.lean:26, 112`): Kaczorowski–Perelli multiple standard twists
     have finite spectral sublevel sets and positive right-hand spectral gaps above every real level.
   - Connects `thetaThree_logDeriv_at_I` and `ofReal_completedThetaProfile_eq_thetaThree`
     (`Bottcher/ThetaDiscriminant.lean:568, 592`): at the self-dual point $\tau = i$, Jacobi's
     $\theta_3$ satisfies $\theta_3'(i)/\theta_3(i) = i/4$ and parameterizes the completed real
     theta profile $e^{x/2}\theta_3(i e^{2x})$.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate BigOperators
open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SelbergClass
open Bottcher

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory

set_option autoImplicit false

/-! ## §1. Localized Weil Prime-Tail Coupling, Pole Compression, and High-Height Positivity -/

/-- **Localized Weil Prime-Tail Coupling, $2 \times 2$ Pole Compression, and High-Height Positivity
(`squareRootThreshold_primeTail_coupling_and_highHeight_positivity`):**
1. RH is equivalent to $\operatorname{Re} \Pi_f(\xi) \le \operatorname{Re} A_f(\xi)$ for all $a, f, \xi$,
   which in turn is equivalent to the $2 \times 2$ CCM Weil pole compression inequality
   $|\operatorname{ccmWeilPoleCross}(a)| \le \operatorname{ccmWeilPoleDiagonal}(a)$.
2. Unconditionally, the archimedean–pole budget cannot be frozen at height $0$: there exist $a > 0$,
   a $C^2$ profile $f$ supported in $[-a, a]$, and a height $\xi$ such that
   $\operatorname{Re} A_f(0) < 0$ and $\operatorname{Re} A_f(0) < \operatorname{Re} \Pi_f(\xi)$.
3. Unconditionally, every compactly supported $C^2$ profile $f$ satisfies the explicit single-height
   lower bound `zetaZeroConfig_re_W_heightShift_ge` and has $\operatorname{Re} W_\zeta(S_\xi f, S_\xi f) \ge 0$
   at all sufficiently large heights $|\xi| \ge \Xi$. -/
theorem squareRootThreshold_primeTail_coupling_and_highHeight_positivity :
    ((RiemannHypothesis ↔
        ∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re) ∧
      ((∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re) ↔
        ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a)) ∧
    (∃ a : ℝ, 0 < a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (archPart f 0).re < 0 ∧
        ∃ ξ : ℝ, (archPart f 0).re < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re) ∧
    (∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ Ξ : ℝ, ∀ ξ : ℝ, Ξ ≤ |ξ| →
        0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re) :=
  ⟨⟨riemannHypothesis_iff_primePolynomial_le_archPart,
    primePolynomial_le_archPart_iff_poleCompression⟩,
   exists_archPart_zero_lt_primePolynomial,
   fun hf hfc => exists_zetaZeroConfig_re_W_heightShift_nonneg hf hfc⟩

/-! ## §2. Windowed Variance Below the Square-Root Threshold and Negative-Height Measure Bound -/

/-- **Windowed Variance Below the Square-Root Threshold and Negative-Height Measure Bound
(`windowed_weil_variance_and_bad_heights_measure_bound`):**
1. For any profile $f \in C^2_c([-a, a])$ and window $\eta \in C^2_c([-r, r])$ with
   $2 r e^{2a} \le 1$, the windowed mean square of $W_\zeta(S_{\xi+\xi_0} f, S_{\xi+\xi_0} f) - A_f(\xi+\xi_0)$
   equals $\|\eta\|_2^2 V_f$ with zero off-diagonal prime correlations, and the window measure of
   heights in $U$ where $\operatorname{Re} W_\zeta < 0$ (assuming $\operatorname{Re} A_f \ge A_0 > 0$ on $U$)
   is at most $\|\eta\|_2^2 V_f / A_0^2$.
2. There is an absolute constant $C \ge 0$ bounding the diagonal prime variance by
   $V_f \le 2 \|f\|_2^4 \cdot 2a(2a + C)$ for all $a \ge 0$. -/
theorem windowed_weil_variance_and_bad_heights_measure_bound
    {a r : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ)
    {U : Set ℝ} {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hU : ∀ ξ ∈ U, A₀ ≤ (archPart f (ξ + ξ₀)).re) :
    ((∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊) ∧
    (∫⁻ ξ, (U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / A₀ ^ 2))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), 0 ≤ b → ∀ g : ℝ → ℂ, Continuous g → HasCompactSupport g →
      primeVariance g ⌊Real.exp (2 * b)⌋₊ ≤
        2 * (∫ t, ‖g t‖ ^ 2) ^ 2 * (2 * b * (2 * b + C))) :=
  ⟨⟨integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀,
    lintegral_bad_heights_le ha hf hfs hη hηs hX ξ₀ hA₀ hU⟩,
   exists_primeVariance_le⟩

/-! ## §3. Selberg-Class Degree-Resonance Bohr Trace, Twist Spectrum Gaps, and Self-Dual Theta Seam -/

/-- **Selberg-Class Degree-Resonance Bohr Trace, Discrete Twist Spectrum Right-Gaps, and
Jacobi–Böttcher Self-Dual Theta Seam (`selbergClass_degreeResonance_spectrum_gaps_and_thetaThree_seam`):**
1. The Bohr mean of `positiveWeightedTangentFlow dF dG c s` selects the exact degree-resonance locus
   $m^{d_G} = n^{d_F}$, and for equal positive degree $d > 0$ selects the diagonal $m = n$.
2. Every Kaczorowski–Perelli `MultipleStandardTwistData N` has finite spectral sublevel sets
   $\{n : \operatorname{spectralValue}(n) < a\}$ and a strictly positive right-hand spectral gap
   above every real level $\alpha$.
3. Jacobi's theta nullwert $\theta_3$ satisfies $\theta_3'(i)/\theta_3(i) = i/4$ at $\tau = i$, and
   `completedThetaProfile x` equals $e^{x/2} \theta_3(i e^{2x})$. -/
theorem selbergClass_degreeResonance_spectrum_gaps_and_thetaThree_seam
    (dF dG d : ℝ) (hd : 0 < d) (c : ℕ+ × ℕ+ → ℂ) (s : Finset (ℕ+ × ℕ+))
    {N : ℕ} (D : MultipleStandardTwistData N) (a α x : ℝ) :
    ((bohrMean (positiveWeightedTangentFlow dF dG c s) =
        ∑ p ∈ s.filter (fun p => ((p.1 : ℕ) : ℝ) ^ dG = ((p.2 : ℕ) : ℝ) ^ dF), c p) ∧
      (bohrMean (positiveWeightedTangentFlow d d c s) =
        ∑ p ∈ s.filter (fun p => p.1 = p.2), c p)) ∧
    ({n : Fin N → ℕ+ | D.spectralValue n < a}.Finite ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, β ∈ D.spectrum → α < β → α + ε ≤ β) ∧
    ((deriv thetaThree I / thetaThree I = I / 4) ∧
      (((completedThetaProfile x : ℝ) : ℂ) =
        ((Real.exp (x / 2) : ℝ) : ℂ) * thetaThree (I * (Real.exp (2 * x) : ℂ)))) :=
  ⟨⟨bohrMean_positiveWeightedTangentFlow_degree_resonance dF dG c s,
    bohrMean_positiveWeightedTangentFlow_equal_degree d hd c s⟩,
   ⟨D.spectralSublevel_finite a, D.exists_spectrum_right_gap α⟩,
   ⟨thetaThree_logDeriv_at_I, ofReal_completedThetaProfile_eq_thetaThree x⟩⟩

end GaloisForLFunctions.ArithmeticPositivityTheory

end
