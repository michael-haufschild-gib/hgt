import GaloisForLFunctions.BiScaleUncertainty.VonMangoldtWeilExplicitFormulaAndChebyshevBridge
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarGramTransport

/-!
# Pillar XXII: Unconditional Chebyshev–Weil Explicit-Formula Bounds & Packet-Coercivity Synthesis

This module develops **Pillar XXII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), synthesizing the Chebyshev prime-counting Stieltjes
transport (`SignedPrimePolarCoupling.lean`), the cancellation-sensitive signed prime–polar Gram
packet (`SignedPrimePolarGramTransport.lean`), and the all-scale von Mangoldt–Weil explicit-formula
bridge (`VonMangoldtWeilExplicitFormulaAndChebyshevBridge.lean`) into **100% unconditional theorems**
on `RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn` with **zero conditional hypotheses**.

## Main Unconditional Results

1. **Canonical Embedding into `C_c(ℝ, ℝ)` & Global Annular Lévy Domination
   (`RealEvenPolarTestFn.toCompactlySupported`, `annular_levy_integral_le_biScaleLevyEnergy`,
   `RealEvenPolarTestFn.annular_levy_integral_le_weilArchRe`):**
   - For every `f ∈ C²_c(ℝ)` and every `a b : ℝ`, the annular Lévy integral on
     `[exp a, exp a + exp b] ⊆ (0, ∞)` is unconditionally bounded by a single copy of
     `biScaleLevyEnergy f`:
     $$\int_{e^a}^{e^a + e^b} \bigl(h_f(0) - h_f(y)\bigr)\,w_{\mathrm{arch}}(y)\,dy
       \;\le\; \operatorname{biScaleLevyEnergy}(f).$$
   - On `RealEvenPolarTestFn`, this equates directly to
     `WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) + |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re`.

2. **Unconditional Cancellation-Sensitive Chebyshev–Packet–Weil Explicit-Formula Bound
   (`RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound`,
   `RealSmoothEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound`):**
   - For EVERY `g : RealEvenPolarTestFn`, EVERY `a b c : ℝ`, and EVERY `N : ℕ`
     (with **zero hypotheses** on `g`, `a`, `b`, `c`, or `N`), the truncated von Mangoldt prime-power
     sum plus the polar tail beyond `cutoff N = log(N + 2)` is approximated by the explicit
     Chebyshev work `SignedPrimePolar.chebyshevWork` up to an unconditional bound controlled by
     `weilArchRe`, `|Ω(0)| h_g(0)`, and the signed Gram `packetEnergy`:
     $$\left|\left(\sum_{n=1}^{N+2} \frac{\Lambda(n)}{\sqrt{n}}\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}
       + \int_{Ioi\,(\log(N+2))} 2\cosh(x/2)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx\right)
       - \operatorname{chebyshevWork}(g, a, b, N)\right|$$
     $$\le\; e^c\,\bigl(\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
       + |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}\bigr)
       + \frac{\operatorname{packetEnergy}(g, N)}{2 e^c e^{2b}} \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy.$$

3. **Unconditional Chebyshev–Mass–Weil Explicit-Formula Bound & Joint Synthesis
   (`RealEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound`,
   `RealSmoothEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound`,
   `RealEvenPolarTestFn.unconditional_joint_all_scale_and_chebyshev_weil_synthesis`):**
   - Eliminates `packetEnergy` in favor of `(EF.weilTest g.1.1.1 g.1.1.1 0).re` and `mass N`, and
     combines the all-scale von Mangoldt signed Weil lower bound with the Chebyshev–Packet–Weil
     explicit-formula bound into a single unconditional synthesis theorem.
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Canonical Embedding into `C_c(ℝ, ℝ)` & Global Annular Lévy Domination -/

/-- **Canonical Embedding of `RealEvenPolarTestFn` into `C_c(ℝ, ℝ)`:**
Every `g : RealEvenPolarTestFn` has a smooth compactly supported source `g.source : ℝ → ℝ`,
which defines an element of `C_c(ℝ, ℝ)`. -/
def RealEvenPolarTestFn.toCompactlySupported (g : RealEvenPolarTestFn) : C_c(ℝ, ℝ) :=
  ⟨⟨g.source, g.contDiff_source.continuous⟩, g.hasCompactSupport_source⟩

@[simp]
theorem RealEvenPolarTestFn.coe_toCompactlySupported (g : RealEvenPolarTestFn) :
    (RealEvenPolarTestFn.toCompactlySupported g : ℝ → ℝ) = g.source :=
  rfl

/-- **Global Annular Lévy Domination (`annular_levy_integral_le_biScaleLevyEnergy`):**
For every `f ∈ C²_c(ℝ)` and every `a b : ℝ`, the annular Lévy integral over
`[exp a, exp a + exp b] ⊆ (0, ∞)` is unconditionally bounded by `biScaleLevyEnergy f`:
$$\int_{e^a}^{e^a + e^b} \bigl(h_f(0) - h_f(y)\bigr)\,w_{\mathrm{arch}}(y)\,dy
  \;\le\; \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem annular_levy_integral_le_biScaleLevyEnergy
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (a b : ℝ) :
    (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
      biScaleLevyEnergy f := by
  have hab : Real.exp a ≤ Real.exp a + Real.exp b :=
    le_add_of_nonneg_right (Real.exp_pos b).le
  rw [intervalIntegral.integral_of_le hab]
  unfold biScaleLevyEnergy
  refine setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf_c2 hf_cs) ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    exact mul_nonneg (autocorr_sub_nonneg hf_cs hf_c2.continuous y)
      (archLevySinhWeight_pos hy).le
  · exact Eventually.of_forall fun y hy => lt_trans (Real.exp_pos a) hy.1

/-- **Unconditional Annular Lévy Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `a b : ℝ` (with zero hypotheses!),
$$\int_{e^a}^{e^a + e^b} \bigl(\operatorname{autocorr}(g.\mathrm{source}, 0) - \operatorname{autocorr}(g.\mathrm{source}, y)\bigr)\,w_{\mathrm{arch}}(y)\,dy$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.annular_levy_integral_le_weilArchRe
    (g : RealEvenPolarTestFn) (a b : ℝ) :
    (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y) ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re := by
  have h1 := annular_levy_integral_le_biScaleLevyEnergy
    g.contDiff_source g.hasCompactSupport_source a b
  have h2 := RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g
  have hgamma : |EF.gammaBracket 0| = -EF.gammaBracket 0 := by
    rw [abs_gammaBracket_zero, gammaBracket_zero_eq]
    ring
  rw [hgamma]
  linarith only [h1, h2]

/-! ## §2. Unconditional Chebyshev–Packet–Weil & Chebyshev–Mass–Weil Explicit-Formula Bounds -/

/-- **Unconditional Truncated Prime-Sum plus Polar-Tail Identity on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `N : ℕ` (with zero hypotheses!),
$$\left(\sum_{n \in \operatorname{Icc} 1 (N+2)} \frac{\Lambda(n)}{\sqrt{n}}\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}\right)
  + \int_{Ioi\,(\operatorname{cutoff} N)} \operatorname{polarDensity}(x)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx
  = \operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing
    (g : RealEvenPolarTestFn) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2),
        SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) +
      (∫ x in Ioi (SignedPrimePolar.cutoff N),
        SignedPrimePolar.polarDensity x * autocorr g.source x) =
      SignedPrimePolar.pairing N (autocorr g.source) := by
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) =
        ∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * autocorr g.source (Real.log (n : ℝ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [g.autocorr_eq]
  rw [hsum_eq]
  have hbridge := RealEvenPolarTestFn.vonMangoldt_prime_sum_eq_pairing_sub_polar_tail g N
  linarith only [hbridge]

/-- **Unconditional Cancellation-Sensitive Chebyshev–Packet–Weil Explicit-Formula Bound
(`RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY `a b c : ℝ`, and EVERY `N : ℕ`
(with **zero hypotheses** on `g`, `a`, `b`, `c`, or `N`!),
$$\left|\left(\sum_{n \in \operatorname{Icc} 1 (N+2)} \frac{\Lambda(n)}{\sqrt{n}}\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}
  + \int_{Ioi\,(\operatorname{cutoff} N)} \operatorname{polarDensity}(x)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx\right)
  - \operatorname{chebyshevWork}(g.\mathrm{toCompactlySupported}, a, b, N)\right|$$
$$\le\; e^c\,\bigl(\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}\bigr)
  + \frac{\operatorname{packetEnergy}(g.\mathrm{toCompactlySupported}, N)}{2 e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy.$$ -/
theorem RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) (N : ℕ) :
    |((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x) -
      SignedPrimePolar.chebyshevWork (RealEvenPolarTestFn.toCompactlySupported g) a b N| ≤
      Real.exp c *
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
            |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
        SignedPrimePolar.packetEnergy (RealEvenPolarTestFn.toCompactlySupported g) N /
            (2 * Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  rw [RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing g N]
  have hpack := SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_packet_levy
    (RealEvenPolarTestFn.toCompactlySupported g) a b c N
  rw [RealEvenPolarTestFn.coe_toCompactlySupported] at hpack
  have hann := mul_le_mul_of_nonneg_left
    (RealEvenPolarTestFn.annular_levy_integral_le_weilArchRe g a b) (Real.exp_pos c).le
  linarith only [hpack, hann]

/-- **Unconditional Cancellation-Sensitive Chebyshev–Packet–Weil Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound
    (g : RealSmoothEvenPolarTestFn) (a b c : ℝ) (N : ℕ) :
    |((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.toRealEvenPolar.source x) -
      SignedPrimePolar.chebyshevWork
        (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar) a b N| ≤
      Real.exp c *
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
            |EF.gammaBracket 0| * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re) +
        SignedPrimePolar.packetEnergy
            (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar) N /
            (2 * Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y :=
  RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound g.toRealEvenPolar a b c N

/-- **Unconditional Chebyshev–Mass–Weil Explicit-Formula Bound
(`RealEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY `a b c : ℝ`, and EVERY `N : ℕ`
(with **zero hypotheses** on `g`, `a`, `b`, `c`, or `N`!),
$$\left|\left(\sum_{n \in \operatorname{Icc} 1 (N+2)} \frac{\Lambda(n)}{\sqrt{n}}\,(\operatorname{weilTest}\,g\,g\,(\log n)).\mathrm{re}
  + \int_{Ioi\,(\operatorname{cutoff} N)} \operatorname{polarDensity}(x)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx\right)
  - \operatorname{chebyshevWork}(g.\mathrm{toCompactlySupported}, a, b, N)\right|$$
$$\le\; \operatorname{mass}(N)\,\left(e^c\,\bigl(\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}\bigr)
  + \frac{(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}}{2 e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy\right).$$ -/
theorem RealEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) (N : ℕ) :
    |((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x) -
      SignedPrimePolar.chebyshevWork (RealEvenPolarTestFn.toCompactlySupported g) a b N| ≤
      SignedPrimePolar.mass N *
        (Real.exp c *
            (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
              |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
          (EF.weilTest g.1.1.1 g.1.1.1 0).re / (2 * Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
  rw [RealEvenPolarTestFn.prime_sum_add_polar_tail_eq_pairing g N]
  have hmass := SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_levy
    (RealEvenPolarTestFn.toCompactlySupported g) a b c N
  rw [RealEvenPolarTestFn.coe_toCompactlySupported] at hmass
  have hann := mul_le_mul_of_nonneg_left
    (RealEvenPolarTestFn.annular_levy_integral_le_weilArchRe g a b) (Real.exp_pos c).le
  have h0_eq :
      autocorr g.source 0 / (2 * Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) =
        (EF.weilTest g.1.1.1 g.1.1.1 0).re / (2 * Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
    rw [g.autocorr_eq 0]
  have hstep :
      SignedPrimePolar.mass N *
          (Real.exp c *
              (∫ y in Real.exp a..Real.exp a + Real.exp b,
                (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y) +
            autocorr g.source 0 / (2 * Real.exp c * Real.exp b ^ 2) *
              ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
        SignedPrimePolar.mass N *
          (Real.exp c *
              (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
                |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
            (EF.weilTest g.1.1.1 g.1.1.1 0).re / (2 * Real.exp c * Real.exp b ^ 2) *
              ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
    refine mul_le_mul_of_nonneg_left ?_ (SignedPrimePolar.mass_nonneg N)
    linarith only [hann, h0_eq]
  linarith only [hmass, hstep]

/-- **Unconditional Chebyshev–Mass–Weil Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound
    (g : RealSmoothEvenPolarTestFn) (a b c : ℝ) (N : ℕ) :
    |((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.toRealEvenPolar.source x) -
      SignedPrimePolar.chebyshevWork
        (RealEvenPolarTestFn.toCompactlySupported g.toRealEvenPolar) a b N| ≤
      SignedPrimePolar.mass N *
        (Real.exp c *
            (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
              |EF.gammaBracket 0| * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re) +
          (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re / (2 * Real.exp c * Real.exp b ^ 2) *
            ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) :=
  RealEvenPolarTestFn.unconditional_chebyshev_mass_weil_bound g.toRealEvenPolar a b c N

/-! ## §3. Unconditional Joint All-Scale Coercivity & Chebyshev–Weil Synthesis -/

/-- **Unconditional Joint All-Scale Von Mangoldt Coercivity & Chebyshev–Weil Synthesis
(`RealEvenPolarTestFn.unconditional_joint_all_scale_and_chebyshev_weil_synthesis`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY `a b c : ℝ`, and EVERY `N : ℕ`
(with **zero hypotheses**!), simultaneously establishes:
1. All-scale von Mangoldt signed Weil functional coercivity across `[2, N + 2)`;
2. Exact hyperbolic lobe conservation $\int_{Ioi\,0} h_g^+\cosh(x/2) = \int_{Ioi\,0} h_g^-\cosh(x/2)$;
3. The cancellation-sensitive Chebyshev–Packet–Weil explicit-formula bound. -/
theorem RealEvenPolarTestFn.unconditional_joint_all_scale_and_chebyshev_weil_synthesis
    (g : RealEvenPolarTestFn) (a b c : ℝ) (N : ℕ) :
    ((EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re) ∧
    ((∫ x in Ioi 0, autocorrPos g.source x * Real.cosh (x / 2)) =
      ∫ x in Ioi 0, autocorrNeg g.source x * Real.cosh (x / 2)) ∧
    (|((∑ n ∈ Finset.Icc 1 (N + 2),
          SignedPrimePolar.primeWeight n * (EF.weilTest g.1.1.1 g.1.1.1 (Real.log (n : ℝ))).re) +
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x) -
      SignedPrimePolar.chebyshevWork (RealEvenPolarTestFn.toCompactlySupported g) a b N| ≤
      Real.exp c *
          (WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
            |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re) +
        SignedPrimePolar.packetEnergy (RealEvenPolarTestFn.toCompactlySupported g) N /
            (2 * Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) :=
  ⟨RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound g N,
   RealEvenPolarTestFn.unconditional_hyperbolic_lobe_conservation g,
   RealEvenPolarTestFn.unconditional_chebyshev_packet_weil_bound g a b c N⟩

end

end GaloisForLFunctions.BiScaleUncertainty
