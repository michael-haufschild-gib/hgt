import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearArithmeticWeightsAndChebyshevCellIncrement
import GaloisForLFunctions.BiScaleUncertainty.CoprimeFactorialLiftAndSpectralLaplaceProducer
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarContinuousFactorialLift

/-!
# Pillar XXXIII: Unconditional Chebyshev Head Integral Producer, Shear-Cell Producer & Continuous Coprime `(2, 3)` Factorial Producer

This module delivers four genuine unconditional producer bridges and quantitative bounds across the
Wall 1 dyadic Chebyshev difference, the integer-centered Nyquist-cell von Mangoldt shear sum, the
continuous logarithmically smoothed Fermi head energy, and the compactly supported continuous
coprime `(2, 3)` factorial producer in `C_c(ℝ, ℝ)`:

1. **Exact Bridge `Chebyshev.psi (m : ℝ) = RHTower.chebyshevPsi m` & Two-Sided Stirling Producer
   Sandwich for `dyadicChebyshevDiffSeq`:**
   We prove that Mathlib's `Chebyshev.psi (m : ℝ)` and `RHTower.chebyshevPsi m` coincide identically
   at every integer `m : ℕ` (`chebyshev_psi_natCast_eq_chebyshevPsi`). Combining this with the
   additive shear sequence `dyadicChebyshevDiffSeq (2 * m) = 2 * ψ(m) - ψ(2m)` and the Stirling-controlled
   alternating producer `chebyshevAlternatingProducer m = T(2m) - 2T(m)` yields the unconditional
   two-sided Stirling producer sandwich:
   $$\psi(m) - (2\log 2)m - \bigl(2\log(2m+1) + 1\bigr)
     \;\le\; \operatorname{dyadicChebyshevDiffSeq}(2m)
     \;\le\; 2\psi(m) - (2\log 2)m + \bigl(2\log(2m+1) + 1\bigr),$$
   together with the pure-Stirling upper bound at every dyadic scale $2 \cdot 2^K$ via
   `dyadicCumulativeChebyshevProducer K`.
2. **Unconditional Producer Bounds on `integerCenteredChebyshevCellSum N`, the Bilinear Von Mangoldt
   Shear Sum, and `integerCenteredGaugeBound f N`:**
   Using `chebyshevProducerSlope = log 4 + 3`, we prove that every cell term in
   `integerCenteredChebyshevCellSum N` satisfies
   $$(\psi(k+1) - (k+1))^2 / ((k+1)(k+2)) \le (\log 4 + 3)^2,$$
   giving `integerCenteredChebyshevCellSum N ≤ (log 4 + 3)^2 * (N + 1)`, bounding the harmonic sum
   of bilinear von Mangoldt shear increments via Abel summation
   (`vonMangoldt_shear_harmonic_sum_le`), and replacing `integerCenteredGaugeBound f N` by the
   100% prime-free `archimedeanIntegerCenteredGaugeProducerBound f N`.
3. **Closed-Form Unconditional Producer Bound on the Wall 1 Chebyshev Head Integral in
   `logMobiusFermiErrorEnergy`:**
   Because $0 \le \psi(x) \le (\log 4 + 4)x$ and $0 \le 2\psi(x/2) \le (\log 4 + 4)x$ for all
   $x \ge 0$, their difference satisfies $|2\psi(x/2) - \psi(x)| \le (\log 4 + 4)x$. Integrating
   $(1/t)^2$ in closed form over $t \in (1/(N+1), 1]$ via the antiderivative $-1/t$ yields
   $\int_{1/(N+1)}^1 (1/t)^2\,dt = N$, proving the unconditional closed-form bound
   $$\int_{1/(N+1)}^1 \bigl(2\psi(1/(2t)) - \psi(1/t)\bigr)^2\,dt \;\le\; (\log 4 + 4)^2 N$$
   and bounding the normalized Chebyshev head of `logMobiusFermiErrorEnergy N` (`N ≥ 2`) by
   $(\log 4 + 4)^2 N / (\log N)^2$.
4. **Unconditional Continuous Coprime `(2, 3)` Factorial Producer in `C_c(ℝ, ℝ)`:**
   Using `smoothFactorialLift` at collar width `coprimeFactorialCollar N = 1 / (6N)`, we construct
   the compactly supported continuous coprime `(2, 3)` factorial producer
   `smoothFactorialCoprimeTwoThree N` (bundled as `continuousCoprimeFactorialProducer : ℕ → C_c(ℝ, ℝ)`).
   Because the coprime `(2, 3)` stencil weights `(1, -2, -3, 6)` satisfy $6N - 2(3N) - 3(2N) + 6N = 0$,
   the linear collar logarithmic correction cancels identically, yielding the exact pairing identity
   $$\operatorname{fullPairing}(\operatorname{smoothFactorialCoprimeTwoThree}\,N)
     = \frac{2\,\operatorname{coprimeTwoThreeChebyshevProducer}(N)
       - (1 + \frac{1}{12N})\,\operatorname{coprimeHarmonicCorrection}(N)}{\sqrt{N}}$$
   and the unconditional $O(\log N / \sqrt{N})$ bound while peaking at $\sqrt{6}$ at $\log(6N)$ and
   vanishing at $0$.
-/

open Complex MeasureTheory Set Filter Topology Finset
open Zeta23 RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Bridge `Chebyshev.psi (m : ℝ) = RHTower.chebyshevPsi m` & Stirling Producer Sandwich for `dyadicChebyshevDiffSeq` -/

/-- **Exact Bridge Between Mathlib's `Chebyshev.psi` and `RHTower.chebyshevPsi`:**
For EVERY natural number `m : ℕ` (with **zero hypotheses**!),
$$\operatorname{Chebyshev.psi}(m : \mathbb{R}) = \operatorname{RHTower.chebyshevPsi}(m).$$ -/
theorem chebyshev_psi_natCast_eq_chebyshevPsi (m : ℕ) :
    Chebyshev.psi (m : ℝ) = RHTower.chebyshevPsi m := by
  unfold Chebyshev.psi RHTower.chebyshevPsi
  rw [Nat.floor_natCast]
  have hsets : Finset.Ioc 0 m = Finset.Icc 1 m := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hsets]

/-- `chebyshevPsiSeq m` coincides identically with `RHTower.chebyshevPsi m` for all `m : ℕ`. -/
theorem chebyshevPsiSeq_eq_chebyshevPsi (m : ℕ) :
    chebyshevPsiSeq m = RHTower.chebyshevPsi m :=
  chebyshev_psi_natCast_eq_chebyshevPsi m

/-- **Exact Decomposition of `dyadicChebyshevDiffSeq (2 * m)` into `ψ(m)` Minus Dyadic Increment:**
For EVERY `m : ℕ` (with **zero hypotheses**!),
$$\operatorname{dyadicChebyshevDiffSeq}(2m)
  = \psi(m) - \bigl(\psi(2m) - \psi(m)\bigr).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_eq (m : ℕ) :
    dyadicChebyshevDiffSeq (2 * m) =
      RHTower.chebyshevPsi m - (RHTower.chebyshevPsi (2 * m) - RHTower.chebyshevPsi m) := by
  unfold dyadicChebyshevDiffSeq
  rw [chebyshev_psi_even_half_eq m, chebyshev_psi_natCast_eq_chebyshevPsi m,
    chebyshev_psi_natCast_eq_chebyshevPsi (2 * m)]
  ring

/-- **Unconditional Alternating-Producer Lower Bound on `dyadicChebyshevDiffSeq (2 * m)`:**
Because $\psi(2m) - \psi(m) \le \operatorname{chebyshevAlternatingProducer}(m)$ for all `m : ℕ`,
$$\psi(m) - \operatorname{chebyshevAlternatingProducer}(m)
  \;\le\; \operatorname{dyadicChebyshevDiffSeq}(2m).$$ -/
theorem sub_alternatingProducer_le_dyadicChebyshevDiffSeq_two_mul (m : ℕ) :
    RHTower.chebyshevPsi m - chebyshevAlternatingProducer m ≤
      dyadicChebyshevDiffSeq (2 * m) := by
  rw [dyadicChebyshevDiffSeq_two_mul_eq]
  have h := chebyshevPsi_two_mul_sub_le_alternatingProducer m
  linarith

/-- **Unconditional Alternating-Producer Upper Bound on `dyadicChebyshevDiffSeq (2 * m)`:**
Because $\operatorname{chebyshevAlternatingProducer}(m) \le \psi(2m)$ for all `m : ℕ`,
$$\operatorname{dyadicChebyshevDiffSeq}(2m)
  \;\le\; 2\,\psi(m) - \operatorname{chebyshevAlternatingProducer}(m).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_le_two_mul_sub_alternatingProducer (m : ℕ) :
    dyadicChebyshevDiffSeq (2 * m) ≤
      2 * RHTower.chebyshevPsi m - chebyshevAlternatingProducer m := by
  unfold dyadicChebyshevDiffSeq
  rw [chebyshev_psi_even_half_eq m, chebyshev_psi_natCast_eq_chebyshevPsi m,
    chebyshev_psi_natCast_eq_chebyshevPsi (2 * m)]
  have h := chebyshevAlternatingProducer_le_chebyshevPsi_two_mul m
  linarith

/-- **Unconditional Stirling Producer Lower Bound on `dyadicChebyshevDiffSeq (2 * m)`:**
For every `m ≥ 1`,
$$\psi(m) - (2\log 2)m - \bigl(2\log(2m + 1) + 1\bigr)
  \;\le\; \operatorname{dyadicChebyshevDiffSeq}(2m).$$ -/
theorem stirling_lower_bound_dyadicChebyshevDiffSeq_two_mul {m : ℕ} (hm : 1 ≤ m) :
    RHTower.chebyshevPsi m - (2 * Real.log 2) * (m : ℝ) -
        (2 * Real.log (2 * (m : ℝ) + 1) + 1) ≤
      dyadicChebyshevDiffSeq (2 * m) := by
  have h1 := sub_alternatingProducer_le_dyadicChebyshevDiffSeq_two_mul m
  have h2 := (abs_le.mp (abs_chebyshevAlternatingProducer_sub_linear_le hm)).2
  linarith

/-- **Unconditional Stirling Producer Upper Bound on `dyadicChebyshevDiffSeq (2 * m)`:**
For every `m ≥ 1`,
$$\operatorname{dyadicChebyshevDiffSeq}(2m)
  \;\le\; 2\,\psi(m) - (2\log 2)m + \bigl(2\log(2m + 1) + 1\bigr).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_le_stirling_upper_bound {m : ℕ} (hm : 1 ≤ m) :
    dyadicChebyshevDiffSeq (2 * m) ≤
      2 * RHTower.chebyshevPsi m - (2 * Real.log 2) * (m : ℝ) +
        (2 * Real.log (2 * (m : ℝ) + 1) + 1) := by
  have h1 := dyadicChebyshevDiffSeq_two_mul_le_two_mul_sub_alternatingProducer m
  have h2 := (abs_le.mp (abs_chebyshevAlternatingProducer_sub_linear_le hm)).1
  linarith

/-- **Unconditional Pure-Factorial Producer Upper Bound at Dyadic Scales `2 * 2^K`:**
Combining `dyadicChebyshevDiffSeq_two_mul_le_two_mul_sub_alternatingProducer` with the telescoping
dyadic cumulative producer `chebyshevPsi_two_pow_le_dyadicCumulativeProducer K` bounds
`dyadicChebyshevDiffSeq (2 * 2^K)` purely in terms of factorial/Stirling producers for ALL `K : ℕ`
(with **zero hypotheses**!):
$$\operatorname{dyadicChebyshevDiffSeq}(2 \cdot 2^K)
  \;\le\; 2\,\operatorname{dyadicCumulativeChebyshevProducer}(K)
    - \operatorname{chebyshevAlternatingProducer}(2^K).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_two_pow_le_cumulative_sub_alternating (K : ℕ) :
    dyadicChebyshevDiffSeq (2 * 2 ^ K) ≤
      2 * dyadicCumulativeChebyshevProducer K - chebyshevAlternatingProducer (2 ^ K) := by
  have h1 := dyadicChebyshevDiffSeq_two_mul_le_two_mul_sub_alternatingProducer (2 ^ K)
  have h2 := chebyshevPsi_two_pow_le_dyadicCumulativeChebyshevProducer K
  linarith

/-- **Unconditional Stirling Linear-Plus-Log Upper Bound at Dyadic Scales `2 * 2^K`:**
For EVERY `K : ℕ` (with **zero hypotheses**!),
$$\operatorname{dyadicChebyshevDiffSeq}(2 \cdot 2^K)
  \;\le\; (2\log 2)(2^K - 2)
    + 2K\bigl(2\log(2^K + 1) + 1\bigr)
    + \bigl(2\log(2 \cdot 2^K + 1) + 1\bigr).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_two_pow_le_stirling_linear_add_log (K : ℕ) :
    dyadicChebyshevDiffSeq (2 * 2 ^ K) ≤
      (2 * Real.log 2) * ((2 : ℝ) ^ K - 2) +
        2 * (K : ℝ) * (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) +
        (2 * Real.log (2 * (2 : ℝ) ^ K + 1) + 1) := by
  have h1 := dyadicChebyshevDiffSeq_two_mul_two_pow_le_cumulative_sub_alternating K
  have h2 := dyadicCumulativeChebyshevProducer_le K
  have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h3 := (abs_le.mp (abs_chebyshevAlternatingProducer_sub_linear_le hpow)).1
  push_cast at h3
  linarith

/-! ## §2. Unconditional Producer Bounds on `integerCenteredChebyshevCellSum N`, the Von Mangoldt Shear Sum, and `integerCenteredGaugeBound f N` -/

/-- **Unconditional Pointwise Bound on the Integer-Centered Chebyshev Error Sequence:**
For EVERY `n : ℕ` (with **zero hypotheses**!),
$$|\psi(n) - n| \;\le\; (\log 4 + 3)\,n.$$ -/
theorem abs_chebyshevErrorSeq_le (n : ℕ) :
    |chebyshevErrorSeq n| ≤ chebyshevProducerSlope * (n : ℝ) := by
  unfold chebyshevErrorSeq chebyshevProducerSlope
  exact abs_chebyshev_psi_sub_self_le (Nat.cast_nonneg n)

/-- **Unconditional Nyquist-Cell Term Bound for `chebyshevErrorSeq`:**
For EVERY `k : ℕ` (with **zero hypotheses**!),
$$\frac{(\psi(k+1) - (k+1))^2}{(k+1)(k+2)} \;\le\; \operatorname{chebyshevProducerSlope}^2.$$ -/
theorem chebyshevErrorSeq_sq_div_cell_le (k : ℕ) :
    chebyshevErrorSeq (k + 1) ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
      chebyshevProducerSlope ^ 2 := by
  have hden_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hden_pos]
  have habs := abs_chebyshevErrorSeq_le (k + 1)
  have hslope_pos : 0 ≤ chebyshevProducerSlope := by
    unfold chebyshevProducerSlope
    positivity
  have hsq : chebyshevErrorSeq (k + 1) ^ 2 ≤
      (chebyshevProducerSlope * ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [sq_abs (chebyshevErrorSeq (k + 1)), abs_nonneg (chebyshevErrorSeq (k + 1))]
  have hcell : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by
    nlinarith
  nlinarith

/-- **Unconditional Linear Producer Bound on `integerCenteredChebyshevCellSum N`:**
For EVERY `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{integerCenteredChebyshevCellSum}(N)
  \;\le\; (\log 4 + 3)^2\,(N + 1).$$ -/
theorem integerCenteredChebyshevCellSum_le (N : ℕ) :
    integerCenteredChebyshevCellSum N ≤ chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) := by
  unfold integerCenteredChebyshevCellSum
  calc (∑ k ∈ Finset.range (N + 1),
          chebyshevErrorSeq (k + 1) ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)))
      ≤ ∑ _ ∈ Finset.range (N + 1), chebyshevProducerSlope ^ 2 :=
        Finset.sum_le_sum fun k _ => chebyshevErrorSeq_sq_div_cell_le k
    _ = chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Unconditional Upper Bound on the Harmonic Sum of Bilinear Von Mangoldt Shear Increments:**
Combining the exact Abel decomposition `integerCenteredChebyshevCellSum_eq_vonMangoldt_shear_sum`
with `integerCenteredChebyshevCellSum_le` and `abs_chebyshevErrorSeq_le (N + 1)` bounds the
harmonic bilinear von Mangoldt shear sum unconditionally for EVERY `N : ℕ`:
$$\sum_{k=0}^{N-1} \frac{(\Lambda(k+2) - 1)\bigl(2(\psi(k+1) - (k+1)) + \Lambda(k+2) - 1\bigr)}{k+2}
  \;\le\; 2(\log 4 + 3)^2\,(N + 1) - 1.$$ -/
theorem vonMangoldt_shear_harmonic_sum_le (N : ℕ) :
    (∑ k ∈ Finset.range N,
      ((ArithmeticFunction.vonMangoldt (k + 2) - 1) *
        (2 * chebyshevErrorSeq (k + 1) +
          (ArithmeticFunction.vonMangoldt (k + 2) - 1))) /
        ((k + 2 : ℕ) : ℝ)) ≤
      2 * chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) - 1 := by
  have habel := integerCenteredChebyshevCellSum_eq_vonMangoldt_shear_sum N
  have hsum_le := integerCenteredChebyshevCellSum_le N
  have hbd : chebyshevErrorSeq (N + 1) ^ 2 / ((N + 2 : ℕ) : ℝ) ≤
      chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) := by
    have hden_pos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hden_pos]
    have habs := abs_chebyshevErrorSeq_le (N + 1)
    have hslope_pos : 0 ≤ chebyshevProducerSlope := by
      unfold chebyshevProducerSlope
      positivity
    have hsq : chebyshevErrorSeq (N + 1) ^ 2 ≤
        (chebyshevProducerSlope * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      nlinarith [sq_abs (chebyshevErrorSeq (N + 1)), abs_nonneg (chebyshevErrorSeq (N + 1))]
    have hle : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) + 1) * ((N + 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    nlinarith
  linarith

/-- **Prime-Free Archimedean Producer Majorant for `integerCenteredGaugeBound`:**
Depends purely on `autocorr f 0`, the gauge derivative `L¹` norm `∫ |f' - f/2|`, the support cutoff
`N`, and the universal Chebyshev constant `chebyshevProducerSlope = log 4 + 3`. -/
def archimedeanIntegerCenteredGaugeProducerBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  3 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) * autocorr f 0 +
  6 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
    (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2)

/-- **Unconditional Dominance of `archimedeanIntegerCenteredGaugeProducerBound` over
`integerCenteredGaugeBound`:**
For EVERY `f : C_c(ℝ, ℝ)` and EVERY `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{integerCenteredGaugeBound}(f, N)
  \;\le\; \operatorname{archimedeanIntegerCenteredGaugeProducerBound}(f, N).$$ -/
theorem integerCenteredGaugeBound_le_archimedeanProducer (f : C_c(ℝ, ℝ)) (N : ℕ) :
    integerCenteredGaugeBound f N ≤ archimedeanIntegerCenteredGaugeProducerBound f N := by
  unfold integerCenteredGaugeBound archimedeanIntegerCenteredGaugeProducerBound
  have h1 := normalizedLogError_cutoff_sq_le N
  have h2 := integerCenteredChebyshevCellSum_le N
  have hauto : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hgauge : 0 ≤ (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 := sq_nonneg _
  nlinarith

/-- **Unconditional Full Weil Functional Prime-Free Integer-Centered Producer Lower Bound:**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), the full Weil
explicit-formula functional of `Λ` is bounded below using the 100% prime-free
`archimedeanIntegerCenteredGaugeProducerBound`: -/
theorem RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_archimedeanIntegerCenteredProducer_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        archimedeanIntegerCenteredGaugeProducerBound f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  refine le_trans ?_
    (f.unconditional_weilFullFunctional_vonMangoldt_integerCenteredGauge_lower_bound a b c)
  have hint_pos :
      0 ≤ ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.exp_pos b]) fun y hy => ?_
    have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos a) hy.1
    exact mul_nonneg (Real.exp_pos _).le (Real.sinh_pos_iff.mpr hy_pos).le
  have hcell :
      integerCenteredGaugeBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      archimedeanIntegerCenteredGaugeProducerBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
    refine mul_le_mul_of_nonneg_right ?_ hint_pos
    exact div_le_div_of_nonneg_right
      (integerCenteredGaugeBound_le_archimedeanProducer
        f.toCompactlySupported f.supportScale)
      (by positivity)
  linarith only [hcell]

/-! ## §3. Closed-Form Unconditional Producer Bound on the Wall 1 Chebyshev Head Integral in `logMobiusFermiErrorEnergy` -/

/-- **Unconditional Pointwise Bound on the Continuous Dyadic Chebyshev Difference
`2 * ψ(x / 2) - ψ(x)`:**
Because both $2\psi(x/2)$ and $\psi(x)$ lie in $[0, (\log 4 + 4)x]$ for every $x \ge 0$, their
difference satisfies:
$$|2\psi(x/2) - \psi(x)| \;\le\; (\log 4 + 4)\,x.$$ -/
theorem abs_two_mul_chebyshev_psi_half_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |2 * Chebyshev.psi (x / 2) - Chebyshev.psi x| ≤ (Real.log 4 + 4) * x := by
  have hx2 : 0 ≤ x / 2 := by linarith
  have hpsi_x_nonneg : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hpsi_x_le : Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self hx
  have hpsi_half_nonneg : 0 ≤ Chebyshev.psi (x / 2) := Chebyshev.psi_nonneg (x / 2)
  have hpsi_half_le : Chebyshev.psi (x / 2) ≤ (Real.log 4 + 4) * (x / 2) :=
    Chebyshev.psi_le_const_mul_self hx2
  rw [abs_le]
  constructor <;> linarith

/-- **Unconditional Quadratic Bound on `(2 * ψ(x / 2) - ψ(x))²`:**
For every `x ≥ 0`,
$$\bigl(2\psi(x/2) - \psi(x)\bigr)^2 \;\le\; \bigl((\log 4 + 4)\,x\bigr)^2.$$ -/
theorem sq_two_mul_chebyshev_psi_half_sub_le {x : ℝ} (hx : 0 ≤ x) :
    (2 * Chebyshev.psi (x / 2) - Chebyshev.psi x) ^ 2 ≤ ((Real.log 4 + 4) * x) ^ 2 := by
  have habs := abs_two_mul_chebyshev_psi_half_sub_le hx
  have hpos : 0 ≤ (Real.log 4 + 4) * x := by positivity
  nlinarith [sq_abs (2 * Chebyshev.psi (x / 2) - Chebyshev.psi x),
    abs_nonneg (2 * Chebyshev.psi (x / 2) - Chebyshev.psi x)]

/-- Integrability of `(1 / t) ^ 2` on `Ioc a 1` for any `0 < a ≤ 1`. -/
theorem integrableOn_inv_sq_Ioc {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun t : ℝ => (1 / t) ^ 2) (Ioc a 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ha1]
  intro t ht
  exact ((continuousOn_const.div continuousOn_id fun x hx =>
    (lt_of_lt_of_le ha0 hx.1).ne').pow 2) t ht

/-- **Exact Closed-Form Integral of `(1 / t)²` on `Ioc a 1`:**
For any `0 < a ≤ 1`,
$$\int_{t \in (a, 1]} \left(\frac{1}{t}\right)^2 dt = \frac{1}{a} - 1.$$ -/
theorem integral_inv_sq_Ioc {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∫ t in Ioc a 1, (1 / t) ^ 2) = 1 / a - 1 := by
  rw [← intervalIntegral.integral_of_le ha1]
  let F : ℝ → ℝ := fun t => -t⁻¹
  have hderiv : ∀ t ∈ uIcc a 1, HasDerivAt F ((1 / t) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le ha1] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le ha0 ht.1).ne'
    have hd := (hasDerivAt_inv ht0).neg
    have heq : - -(t ^ 2)⁻¹ = (1 / t) ^ 2 := by ring
    rw [heq] at hd
    exact hd
  have hint : IntervalIntegrable (fun t : ℝ => (1 / t) ^ 2) volume a 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact integrableOn_inv_sq_Ioc ha0 ha1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  ring

/-- **Unconditional Closed-Form Producer Bound on the Wall 1 Chebyshev Head Integral:**
For EVERY `N : ℕ` (with **zero hypotheses**!), the continuous dyadic Chebyshev head integral over
`Ioc (1 / (N + 1)) 1` is bounded in closed form by `(log 4 + 4)² * N`:
$$\int_{t \in (1/(N+1), 1]} \bigl(2\psi(1/(2t)) - \psi(1/t)\bigr)^2\,dt
  \;\le\; (\log 4 + 4)^2\,N.$$ -/
theorem integral_wall_one_chebyshev_head_le (N : ℕ) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
      (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2) ≤
    (Real.log 4 + 4) ^ 2 * (N : ℝ) := by
  by_cases hf : IntegrableOn
      (fun t : ℝ => (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2)
      (Ioc (1 / ((N : ℝ) + 1)) 1)
  · have ha0 : 0 < 1 / ((N : ℝ) + 1) := by positivity
    have ha1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
    have hint : IntegrableOn (fun t : ℝ => (Real.log 4 + 4) ^ 2 * (1 / t) ^ 2)
        (Ioc (1 / ((N : ℝ) + 1)) 1) :=
      (integrableOn_inv_sq_Ioc ha0 ha1).const_mul _
    have hmono :
        (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2) ≤
        ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, (Real.log 4 + 4) ^ 2 * (1 / t) ^ 2 := by
      refine setIntegral_mono_on hf hint measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := lt_trans ha0 ht.1
      have h1 := sq_two_mul_chebyshev_psi_half_sub_le (show 0 ≤ 1 / t by positivity)
      have hhalf : (1 / t) / 2 = 1 / (2 * t) := by ring
      rw [hhalf] at h1
      calc (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2
          ≤ ((Real.log 4 + 4) * (1 / t)) ^ 2 := h1
        _ = (Real.log 4 + 4) ^ 2 * (1 / t) ^ 2 := by ring
    calc (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
            (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2)
        ≤ ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, (Real.log 4 + 4) ^ 2 * (1 / t) ^ 2 := hmono
      _ = (Real.log 4 + 4) ^ 2 * ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, (1 / t) ^ 2 :=
          integral_const_mul _ _
      _ = (Real.log 4 + 4) ^ 2 * (1 / (1 / ((N : ℝ) + 1)) - 1) := by
          rw [integral_inv_sq_Ioc ha0 ha1]
      _ = (Real.log 4 + 4) ^ 2 * (N : ℝ) := by
          rw [one_div_one_div]
          ring
  · rw [integral_undef hf]
    positivity

/-- **Unconditional Producer Bound on the Chebyshev Head of `logMobiusFermiErrorEnergy`:**
For every `N ≥ 2`, combining `logMobiusFermiErrorEnergy_decomposition` with
`integral_wall_one_chebyshev_head_le` bounds the Chebyshev head energy in closed form by
$(\log 4 + 4)^2 N / (\log N)^2$:
$$\operatorname{logMobiusFermiErrorEnergy}(N)
  \;\le\; \int_{t \in (0, 1/(N+1)]} \|\operatorname{dyadicHaar}(t) - \operatorname{logMobiusFermiApprox}(N, t)\|^2\,dt
    + \frac{(\log 4 + 4)^2\,N}{(\log N)^2}.$$ -/
theorem logMobiusFermiErrorEnergy_le_tail_add_head_producer {N : ℕ} (hN : 2 ≤ N) :
    logMobiusFermiErrorEnergy N ≤
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) +
      (Real.log 4 + 4) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  rw [logMobiusFermiErrorEnergy_decomposition N hN]
  have hhead := integral_wall_one_chebyshev_head_le N
  have hdiv :
      (1 / Real.log (N : ℝ) ^ 2) *
        (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2) ≤
      (Real.log 4 + 4) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
    calc (1 / Real.log (N : ℝ) ^ 2) *
          (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
            (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2)
        ≤ (1 / Real.log (N : ℝ) ^ 2) * ((Real.log 4 + 4) ^ 2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hhead (by positivity)
      _ = (Real.log 4 + 4) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by ring
  linarith

/-! ## §4. Unconditional Continuous Coprime `(2, 3)` Factorial Producer in `C_c(ℝ, ℝ)` -/

/-- Collar width `1 / (6N)` for the continuous coprime `(2, 3)` factorial lift, chosen so that
`coprimeFactorialCollar N * K ≤ 1` for all four coprime stencil scales `K ∈ {N, 2N, 3N, 6N}`. -/
def coprimeFactorialCollar (N : ℕ) : ℝ := 1 / (6 * (N : ℝ))

/-- **Continuous Coprime `(2, 3)` Factorial Producer (`smoothFactorialCoprimeTwoThree`):**
Applies the coprime `(2, 3)` bi-null stencil `(1 - 2 · 2^{-s})(1 - 3 · 3^{-s})` to the continuous
ramp-smoothed factorial lift `smoothFactorialLift (coprimeFactorialCollar N) K x`:
$$\operatorname{smoothFactorialCoprimeTwoThree}(N, x)
  := \frac{F_\varepsilon(6N, x) - 2 F_\varepsilon(3N, x) - 3 F_\varepsilon(2N, x) + 6 F_\varepsilon(N, x)}{\sqrt{N}}.$$ -/
def smoothFactorialCoprimeTwoThree (N : ℕ) (x : ℝ) : ℝ :=
  (smoothFactorialLift (coprimeFactorialCollar N) (6 * N) x -
    2 * smoothFactorialLift (coprimeFactorialCollar N) (3 * N) x -
    3 * smoothFactorialLift (coprimeFactorialCollar N) (2 * N) x +
    6 * smoothFactorialLift (coprimeFactorialCollar N) N x) / Real.sqrt (N : ℝ)

theorem coprimeFactorialCollar_pos {N : ℕ} (hN : 1 ≤ N) : 0 < coprimeFactorialCollar N := by
  unfold coprimeFactorialCollar
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem coprimeFactorialCollar_mul_le_one {N K : ℕ} (hN : 1 ≤ N) (hK : K ≤ 6 * N) :
    coprimeFactorialCollar N * (K : ℝ) ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (K : ℝ) ≤ 6 * (N : ℝ) := by exact_mod_cast hK
  unfold coprimeFactorialCollar
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity : 0 < 6 * (N : ℝ))).2 (by simpa using hk)

theorem continuous_smoothFactorialCoprimeTwoThree (N : ℕ) :
    Continuous (smoothFactorialCoprimeTwoThree N) :=
  ((((continuous_smoothFactorialLift _ _).sub
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).sub
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).add
    (continuous_const.mul (continuous_smoothFactorialLift _ _))).div_const _

/-- At every integer logarithmic node `log n` (`n ≥ 1`), the continuous coprime `(2, 3)` producer
agrees identically with the step-function producer `factorialCoprimeTwoThree N (log n)`. -/
theorem smoothFactorialCoprimeTwoThree_at_log {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    smoothFactorialCoprimeTwoThree N (Real.log n) =
      factorialCoprimeTwoThree N (Real.log n) := by
  unfold smoothFactorialCoprimeTwoThree factorialCoprimeTwoThree
  rw [smoothFactorialLift_at_log (coprimeFactorialCollar_pos hN)
      (coprimeFactorialCollar_mul_le_one hN (by omega : 6 * N ≤ 6 * N)) hn,
    smoothFactorialLift_at_log (coprimeFactorialCollar_pos hN)
      (coprimeFactorialCollar_mul_le_one hN (by omega : 3 * N ≤ 6 * N)) hn,
    smoothFactorialLift_at_log (coprimeFactorialCollar_pos hN)
      (coprimeFactorialCollar_mul_le_one hN (by omega : 2 * N ≤ 6 * N)) hn,
    smoothFactorialLift_at_log (coprimeFactorialCollar_pos hN)
      (coprimeFactorialCollar_mul_le_one hN (by omega : N ≤ 6 * N)) hn]

/-- `smoothFactorialCoprimeTwoThree N x = 0` for all `x ≤ 0` (`N ≥ 1`) because
`6N - 2(3N) - 3(2N) + 6N = 0`. -/
theorem smoothFactorialCoprimeTwoThree_of_nonpos {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ≤ 0) :
    smoothFactorialCoprimeTwoThree N x = 0 := by
  unfold smoothFactorialCoprimeTwoThree
  rw [smoothFactorialLift_of_nonpos (coprimeFactorialCollar_pos hN) hx,
    smoothFactorialLift_of_nonpos (coprimeFactorialCollar_pos hN) hx,
    smoothFactorialLift_of_nonpos (coprimeFactorialCollar_pos hN) hx,
    smoothFactorialLift_of_nonpos (coprimeFactorialCollar_pos hN) hx]
  push_cast
  ring

/-- `smoothFactorialCoprimeTwoThree N x = 0` for all `x ≥ log(6N + 1)` (`N ≥ 1`). -/
theorem smoothFactorialCoprimeTwoThree_tail {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : Real.log (6 * (N : ℝ) + 1) ≤ x) :
    smoothFactorialCoprimeTwoThree N x = 0 := by
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < 6 * (N : ℝ) + 1)] at he
  have hz (K : ℕ) (hk0 : 1 ≤ K) (hk : K ≤ 6 * N) :
      smoothFactorialLift (coprimeFactorialCollar N) K x = 0 := by
    apply smoothFactorialLift_eq_zero (coprimeFactorialCollar_pos hN) hk0
    have hb := coprimeFactorialCollar_mul_le_one hN hk
    have hk' : (K : ℝ) ≤ 6 * (N : ℝ) := by exact_mod_cast hk
    nlinarith
  simp [smoothFactorialCoprimeTwoThree,
    hz (6 * N) (by omega) (by omega),
    hz (3 * N) (by omega) (by omega),
    hz (2 * N) (by omega) (by omega),
    hz N hN (by omega)]

/-- `smoothFactorialCoprimeTwoThree N` has compact support contained in `[0, log(6N + 1)]`. -/
theorem hasCompactSupport_smoothFactorialCoprimeTwoThree {N : ℕ} (hN : 1 ≤ N) :
    HasCompactSupport (smoothFactorialCoprimeTwoThree N) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc 0 (Real.log (6 * (N : ℝ) + 1))) isCompact_Icc
  intro x hx
  constructor
  · by_contra! hn
    exact hx (smoothFactorialCoprimeTwoThree_of_nonpos hN hn.le)
  · by_contra! hn
    exact hx (smoothFactorialCoprimeTwoThree_tail hN hn.le)

/-- **Bundled Compactly Supported Continuous Coprime `(2, 3)` Factorial Producer in `C_c(ℝ, ℝ)`:** -/
def continuousCoprimeFactorialProducer (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨smoothFactorialCoprimeTwoThree (n + 1), continuous_smoothFactorialCoprimeTwoThree (n + 1)⟩,
    hasCompactSupport_smoothFactorialCoprimeTwoThree (by omega)⟩

theorem primeTerm_smoothFactorialCoprimeTwoThree {N : ℕ} (hN : 1 ≤ N) :
    primeTerm (smoothFactorialCoprimeTwoThree N) = primeTerm (factorialCoprimeTwoThree N) := by
  funext n
  unfold primeTerm
  split_ifs with hn
  · rw [smoothFactorialCoprimeTwoThree_at_log hN (by omega)]
  · rfl

theorem integrable_polar_smoothFactorialCoprimeTwoThree {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => polarDensity x * smoothFactorialCoprimeTwoThree N x) :=
  (continuous_polarDensity.mul (continuous_smoothFactorialCoprimeTwoThree N)).integrable_of_hasCompactSupport
    ((hasCompactSupport_smoothFactorialCoprimeTwoThree hN).mul_left (f := polarDensity))

/-- **Unconditional Admissibility of `smoothFactorialCoprimeTwoThree N`:** -/
theorem smoothFactorialCoprimeTwoThree_admissible {N : ℕ} (hN : 1 ≤ N) :
    (Function.support (primeTerm (smoothFactorialCoprimeTwoThree N))).Finite ∧
      Summable (fun n => |primeTerm (smoothFactorialCoprimeTwoThree N) n|) ∧
      IntegrableOn (fun x => polarDensity x * smoothFactorialCoprimeTwoThree N x) (Ici 0) := by
  rw [primeTerm_smoothFactorialCoprimeTwoThree hN]
  exact ⟨(factorialCoprimeTwoThree_admissible N).1, (factorialCoprimeTwoThree_admissible N).2.1,
    (integrable_polar_smoothFactorialCoprimeTwoThree hN).integrableOn⟩

private theorem integral_polar_coprime_stencil (F : ℕ → ℝ → ℝ) (N : ℕ)
    (hi : ∀ K, IntegrableOn (fun x => polarDensity x * F K x) (Ici 0)) :
    (∫ x in Ici (0 : ℝ),
        polarDensity x * ((F (6 * N) x - 2 * F (3 * N) x - 3 * F (2 * N) x + 6 * F N x) /
          Real.sqrt (N : ℝ))) =
      ((∫ x in Ici (0 : ℝ), polarDensity x * F (6 * N) x) -
        2 * (∫ x in Ici (0 : ℝ), polarDensity x * F (3 * N) x) -
        3 * (∫ x in Ici (0 : ℝ), polarDensity x * F (2 * N) x) +
        6 * (∫ x in Ici (0 : ℝ), polarDensity x * F N x)) / Real.sqrt (N : ℝ) := by
  have hi6 : IntegrableOn (fun x => polarDensity x * F (6 * N) x) (Ici 0) := hi (6 * N)
  have hi3 : IntegrableOn (fun x => 2 * (polarDensity x * F (3 * N) x)) (Ici 0) :=
    (hi (3 * N)).const_mul 2
  have hi2 : IntegrableOn (fun x => 3 * (polarDensity x * F (2 * N) x)) (Ici 0) :=
    (hi (2 * N)).const_mul 3
  have hi1 : IntegrableOn (fun x => 6 * (polarDensity x * F N x)) (Ici 0) :=
    (hi N).const_mul 6
  have hsub1 : IntegrableOn
      (fun x => polarDensity x * F (6 * N) x - 2 * (polarDensity x * F (3 * N) x)) (Ici 0) :=
    hi6.sub hi3
  have hsub2 : IntegrableOn
      (fun x => polarDensity x * F (6 * N) x - 2 * (polarDensity x * F (3 * N) x) -
        3 * (polarDensity x * F (2 * N) x)) (Ici 0) :=
    hsub1.sub hi2
  have he :
      (fun x => polarDensity x *
        ((F (6 * N) x - 2 * F (3 * N) x - 3 * F (2 * N) x + 6 * F N x) / Real.sqrt (N : ℝ))) =
      fun x => (polarDensity x * F (6 * N) x - 2 * (polarDensity x * F (3 * N) x) -
        3 * (polarDensity x * F (2 * N) x) + 6 * (polarDensity x * F N x)) / Real.sqrt (N : ℝ) := by
    funext x
    ring
  rw [he, integral_div, integral_add hsub2 hi1, integral_sub hsub1 hi2,
    integral_sub hi6 hi3, integral_const_mul, integral_const_mul, integral_const_mul]

/-- **Exact Collar Correction for `fullPairing (smoothFactorialCoprimeTwoThree N)`:**
Because the coprime `(2, 3)` stencil weights satisfy $6N - 2(3N) - 3(2N) + 6N = 0$, the linear
`rampLogCorrection` term cancels identically, leaving only the harmonic correction: -/
theorem fullPairing_smoothFactorialCoprimeTwoThree_correction {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (smoothFactorialCoprimeTwoThree N) =
      fullPairing (factorialCoprimeTwoThree N) -
        (coprimeFactorialCollar N / 2 * coprimeHarmonicCorrection N) / Real.sqrt (N : ℝ) := by
  unfold fullPairing
  rw [primeTerm_smoothFactorialCoprimeTwoThree hN]
  unfold smoothFactorialCoprimeTwoThree factorialCoprimeTwoThree
  rw [integral_polar_coprime_stencil _ N
      (integrableOn_polar_smoothFactorialLift (coprimeFactorialCollar_pos hN)),
    integral_polar_coprime_stencil _ N (fun K => (factorialLift_admissible K).2.2)]
  rw [integral_polar_smoothFactorialLift (coprimeFactorialCollar_pos hN),
    integral_polar_smoothFactorialLift (coprimeFactorialCollar_pos hN),
    integral_polar_smoothFactorialLift (coprimeFactorialCollar_pos hN),
    integral_polar_smoothFactorialLift (coprimeFactorialCollar_pos hN)]
  unfold coprimeHarmonicCorrection
  push_cast
  ring

/-- **Exact Evaluation of `fullPairing (smoothFactorialCoprimeTwoThree N)`:** -/
theorem fullPairing_smoothFactorialCoprimeTwoThree_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (smoothFactorialCoprimeTwoThree N) =
      (2 * coprimeTwoThreeChebyshevProducer N -
        (1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N) / Real.sqrt (N : ℝ) := by
  rw [fullPairing_smoothFactorialCoprimeTwoThree_correction hN,
    fullPairing_factorialCoprimeTwoThree_eq hN]
  unfold coprimeFactorialCollar
  ring

/-- **Unconditional `O(log N / √N)` Bound for `fullPairing (smoothFactorialCoprimeTwoThree N)`:**
For every `N ≥ 1`,
$$|\operatorname{fullPairing}(\operatorname{smoothFactorialCoprimeTwoThree}\,N)|
  \;\le\; \frac{24\log(6N + 1) + 7 + \frac{1}{4N}}{\sqrt{N}}.$$ -/
theorem abs_fullPairing_smoothFactorialCoprimeTwoThree_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (smoothFactorialCoprimeTwoThree N)| ≤
      (24 * Real.log (6 * (N : ℝ) + 1) + 7 + 1 / (4 * (N : ℝ))) / Real.sqrt (N : ℝ) := by
  rw [fullPairing_smoothFactorialCoprimeTwoThree_eq hN, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := abs_coprimeTwoThreeChebyshevProducer_le hN
  obtain ⟨hc0, hc1⟩ := coprimeHarmonicCorrection_bounds hN
  have hq : 0 ≤ 1 + 1 / (12 * (N : ℝ)) := by positivity
  have hmul : (1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N ≤
      3 + 1 / (4 * (N : ℝ)) := by
    calc (1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N
        ≤ (1 + 1 / (12 * (N : ℝ))) * 3 := mul_le_mul_of_nonneg_left hc1 hq
      _ = 3 + 1 / (4 * (N : ℝ)) := by ring
  calc
    |2 * coprimeTwoThreeChebyshevProducer N -
        (1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N|
        ≤ |2 * coprimeTwoThreeChebyshevProducer N| +
            |(1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N| := abs_sub _ _
    _ = 2 * |coprimeTwoThreeChebyshevProducer N| +
          (1 + 1 / (12 * (N : ℝ))) * coprimeHarmonicCorrection N := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (mul_nonneg hq hc0)]
    _ ≤ 24 * Real.log (6 * (N : ℝ) + 1) + 7 + 1 / (4 * (N : ℝ)) := by
        linarith [hb, hmul]

theorem continuousCoprimeFactorialProducer_zero (n : ℕ) :
    continuousCoprimeFactorialProducer n 0 = 0 :=
  smoothFactorialCoprimeTwoThree_of_nonpos (by omega) le_rfl

theorem continuousCoprimeFactorialProducer_top (n : ℕ) :
    continuousCoprimeFactorialProducer n (Real.log (6 * ((n + 1 : ℕ) : ℝ))) = Real.sqrt 6 := by
  have hg := smoothFactorialCoprimeTwoThree_at_log (N := n + 1) (n := 6 * (n + 1)) (by omega) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hg
  change smoothFactorialCoprimeTwoThree (n + 1) _ = _
  rw [hg, factorialCoprimeTwoThree_top (by omega)]

/-- **Unconditional Non-Autocorrelation Theorem for `continuousCoprimeFactorialProducer`:**
For every `n : ℕ` and every `f : C_c(ℝ, ℝ)`, the compactly supported continuous coprime `(2, 3)`
factorial producer is NEVER an autocorrelation `autocorr f`, because it vanishes at `0` while
attaining `√6 > 0` at `log(6(n + 1))`. -/
theorem continuousCoprimeFactorialProducer_ne_autocorr (n : ℕ) (f : C_c(ℝ, ℝ)) :
    (continuousCoprimeFactorialProducer n : ℝ → ℝ) ≠ RHTower.ArchimedeanAnomaly.autocorr f := by
  intro heq
  have hz := congrFun heq 0
  rw [continuousCoprimeFactorialProducer_zero] at hz
  have ht := congrFun heq (Real.log (6 * ((n + 1 : ℕ) : ℝ)))
  rw [continuousCoprimeFactorialProducer_top] at ht
  have hc := autocorr_eq_zero_of_zero_eq_zero f.hasCompactSupport f.continuous hz.symm
    (Real.log (6 * ((n + 1 : ℕ) : ℝ)))
  have hsqrt6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
