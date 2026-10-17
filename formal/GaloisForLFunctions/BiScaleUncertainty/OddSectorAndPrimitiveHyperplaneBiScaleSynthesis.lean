import GaloisForLFunctions.BiScaleUncertainty.MultiNodeSignedCliqueWeilCoercivity

/-!
# Pillar XXV: Unconditional Odd-Sector, Full Real-Weil & Primitive-Hyperplane Bi-Scale Coercivity

This module develops **Pillar XXV** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), extending the entire Layer V unconditional explicit-formula
apparatus from the even pole-free sector (`RealEvenPolarTestFn`) to:
1. **The Full Real Weil Test Space (`RealWeilTestFn`)**,
2. **The Real Odd Weil Test Sector (`RealOddTestFn`)**, and
3. **The Real Primitive-Hyperplane Generators (`RealHyperplaneGenerator := RealOddTestFn ⊕ RealEvenPolarTestFn`)**.

## The Universal Pole-Weight-Zero Identity Across All Parities

A key structural discovery formalized here is that for **every** real test function
$f \in C^2_c(\mathbb{R})$ (even, odd, pole-free, or completely arbitrary), the archimedean Weil
functional `weilArchRe` and the real pole term `(weilPoleTerm k_f).re` satisfy the exact
identities:
$$(\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}
  = 2\left(\left(\int_{\mathbb{R}} f(u)\,\cosh(u/2)\,du\right)^2
    - \left(\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du\right)^2\right),$$
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,F\,F)
  = (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}
    + \Omega(0)\,\operatorname{autocorr}(f, 0) + \operatorname{biScaleLevyEnergy}(f).$$
Consequently, for **every** pole weight $\beta \in \mathbb{R}$ and **every** real test
$f : \operatorname{RealWeilTestFn}$:
$$\operatorname{poleWeightArchRe}(\beta, f.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    + 2\beta\left(\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\cosh(u/2)\,du\right)^2
      - \left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2\right),$$
and at **pole weight $\beta = 0$**, the pole term cancels identically on **all** of
`RealWeilTestFn`:
$$\operatorname{poleWeightArchRe}(0, f.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$

On the **odd sector** (`f : RealOddTestFn`), the cosh pairing vanishes identically by odd parity
(`∫ u, f.source u * cosh(u / 2) = 0`), so for every $\beta \in \mathbb{R}$:
$$\operatorname{poleWeightArchRe}(\beta, f.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\beta\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2.$$
At $\beta = 1$, this yields the exact physical-space **Sinh-Capacity Weil Identity**:
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
  + 2\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}),$$
allowing every unconditional Layer V theorem (dyadic Nyquist, all-scale critical-line, all-scale
von Mangoldt, Chebyshev–Packet, and multi-node dyadic-coset coercivity) to lift unconditionally to
`RealWeilTestFn`, `RealOddTestFn`, and `RealHyperplaneGenerator`.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Universal Pole & Archimedean Identities for Arbitrary Real $C^2_c(\mathbb{R})$ Sources -/

/-- For every `f ∈ C²_c(ℝ)`, the Bochner integral `biScaleLevyEnergy f` equals the `toReal` of the
`ENNReal` Lebesgue integral in `weilArchRe_eq_autocorrelation_form`. -/
theorem biScaleLevyEnergy_eq_lintegral_toReal {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    biScaleLevyEnergy f =
      (∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0 - autocorr f x) *
        (Real.exp (x / 2) / Real.sinh x))).toReal := by
  have hint : IntegrableOn
      (fun x => (autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x)) (Ioi 0) :=
    integrableOn_biScaleLevyIntegrand hf hfc
  have hnn : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ (autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x) := fun x hx =>
    mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
  unfold biScaleLevyEnergy archLevySinhWeight
  exact integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono hnn) hint.aestronglyMeasurable

/-- **Exact Hyperbolic Difference-of-Squares Formula for `weilPoleTerm` on Real Sources:**
For EVERY continuous compactly supported `f : ℝ → ℝ`,
$$(\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}
  = 2\left(\left(\int_{\mathbb{R}} f(u)\,\cosh(u/2)\,du\right)^2
    - \left(\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du\right)^2\right).$$ -/
theorem re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ((∫ u, f u * Real.cosh (u / 2)) ^ 2 - (∫ u, f u * Real.sinh (u / 2)) ^ 2) := by
  unfold weilPoleTerm
  rw [re_pole_weilTest_ofReal hf hfc]
  have hprod := WeilLevyPole.integral_prod_cosh_eq hfc hf
  have hsq := ArchimedeanAnomaly.integral_prod_cosh_eq_sq hfc hf
  linarith only [hprod, hsq]

/-- **Universal Archimedean–Lévy–Pole Decomposition for Real $C^2_c(\mathbb{R})$ Sources:**
For EVERY `f ∈ C²_c(ℝ)` (with zero parity or polar assumptions),
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,F\,F)
  = (\operatorname{weilPoleTerm}(\operatorname{weilTest}\,F\,F)).\mathrm{re}
    + \Omega(0)\,\operatorname{autocorr}(f, 0) + \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re +
        EF.gammaBracket 0 * autocorr f 0 + biScaleLevyEnergy f := by
  rw [ArchimedeanAnomaly.weilArchRe_eq_autocorrelation_form hf hfc,
    ← biScaleLevyEnergy_eq_lintegral_toReal hf hfc,
    re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq hf.continuous hfc]

/-- **Universal Hyperbolic Cosh/Sinh Decomposition of `weilArchRe` for Real $C^2_c(\mathbb{R})$ Sources:**
For EVERY `f ∈ C²_c(ℝ)`,
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,F\,F)
  = 2\left(\left(\int_{\mathbb{R}} f(u)\,\cosh(u/2)\,du\right)^2
      - \left(\int_{\mathbb{R}} f(u)\,\sinh(u/2)\,du\right)^2\right)
    + \Omega(0)\,\operatorname{autocorr}(f, 0) + \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem weilArchRe_ofReal_eq_cosh_sq_sub_sinh_sq_add_gamma_add_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      2 * ((∫ u, f u * Real.cosh (u / 2)) ^ 2 - (∫ u, f u * Real.sinh (u / 2)) ^ 2) +
        EF.gammaBracket 0 * autocorr f 0 + biScaleLevyEnergy f := by
  rw [ArchimedeanAnomaly.weilArchRe_eq_autocorrelation_form hf hfc,
    ← biScaleLevyEnergy_eq_lintegral_toReal hf hfc]

/-! ## §2. The Full Real Weil Test Space `RealWeilTestFn` & Universal Pole-Weight-Zero Coercivity -/

/-- **The Full Real-Valued Weil Test Space (`RealWeilTestFn`):**
All `C²` compactly supported test functions `f : WeilTestFn` whose values are real (`(f.1 u).im = 0`),
with **no** parity or polar-vanishing restrictions. -/
def RealWeilTestFn : Type := {f : WeilTestFn // ∀ u, (f.1 u).im = 0}

namespace RealWeilTestFn

/-- The underlying real source `f.source : ℝ → ℝ` of `f : RealWeilTestFn`. -/
def source (f : RealWeilTestFn) (u : ℝ) : ℝ := (f.1.1 u).re

theorem source_eq (f : RealWeilTestFn) :
    (fun u => (f.source u : ℂ)) = f.1.1 := by
  funext u
  apply Complex.ext
  · rfl
  · simpa using (f.2 u).symm

theorem contDiff_source (f : RealWeilTestFn) : ContDiff ℝ 2 f.source :=
  Complex.reCLM.contDiff.comp f.1.2.1

theorem hasCompactSupport_source (f : RealWeilTestFn) : HasCompactSupport f.source :=
  f.1.2.2.comp_left Complex.zero_re

/-- Canonical embedding of `RealWeilTestFn` into `C_c(ℝ, ℝ)`. -/
def toCompactlySupported (f : RealWeilTestFn) : C_c(ℝ, ℝ) :=
  ⟨⟨f.source, f.contDiff_source.continuous⟩, f.hasCompactSupport_source⟩

@[simp]
theorem coe_toCompactlySupported (f : RealWeilTestFn) :
    (RealWeilTestFn.toCompactlySupported f : ℝ → ℝ) = f.source :=
  rfl

/-- For every `f : RealWeilTestFn` and `x : ℝ`, `autocorr f.source x = (weilTest f f x).re`. -/
theorem autocorr_eq (f : RealWeilTestFn) (x : ℝ) :
    autocorr f.source x = (EF.weilTest f.1.1 f.1.1 x).re := by
  have h := congrArg Complex.re (autocorr_eq_weilTest f.source (-x))
  simpa only [autocorr_neg, neg_neg, f.source_eq, Complex.ofReal_re] using h

/-- For every `f : RealWeilTestFn` and `x : ℝ`, `(weilTest f f (-x)).re = (weilTest f f x).re`. -/
theorem weilTest_neg_re_eq (f : RealWeilTestFn) (x : ℝ) :
    (EF.weilTest f.1.1 f.1.1 (-x)).re = (EF.weilTest f.1.1 f.1.1 x).re := by
  rw [← f.autocorr_eq (-x), ← f.autocorr_eq x, autocorr_neg]

/-- **Unconditional `logValue` Formula on `RealWeilTestFn`:**
For every `f : RealWeilTestFn` and `n : ℕ`,
`logValue f.1.1 n = 2 * (weilTest f.1.1 f.1.1 (log n)).re / √n`. -/
theorem logValue_eq_two_mul_weilTest_re_div_sqrt (f : RealWeilTestFn) (n : ℕ) :
    WeilOneSided.logValue f.1.1 n =
      2 * (EF.weilTest f.1.1 f.1.1 (Real.log (n : ℝ))).re / Real.sqrt (n : ℝ) := by
  unfold WeilOneSided.logValue
  rw [Complex.add_re, f.weilTest_neg_re_eq (Real.log (n : ℝ))]
  ring

/-- **Exact `poleWeightArchRe` Formula on `RealWeilTestFn` at Arbitrary Pole Weight `β : ℝ`:**
For EVERY `f : RealWeilTestFn` and EVERY `β : ℝ`,
$$\operatorname{poleWeightArchRe}(\beta, f.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    + 2\beta\left(\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\cosh(u/2)\,du\right)^2
      - \left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2\right).$$ -/
theorem poleWeightArchRe_eq (f : RealWeilTestFn) (β : ℝ) :
    poleWeightArchRe β f.1 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
        biScaleLevyEnergy f.source +
        2 * β * ((∫ u, f.source u * Real.cosh (u / 2)) ^ 2 -
          (∫ u, f.source u * Real.sinh (u / 2)) ^ 2) := by
  unfold poleWeightArchRe
  have harch := weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy
    f.contDiff_source f.hasCompactSupport_source
  have hpole := re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq
    f.contDiff_source.continuous f.hasCompactSupport_source
  rw [f.source_eq] at harch hpole
  rw [f.autocorr_eq 0] at harch
  change WeilOneSided.weilArchRe (EF.weilTest f.1.1 f.1.1) +
    (β - 1) * (weilPoleTerm (EF.weilTest f.1.1 f.1.1)).re = _
  rw [harch, hpole]
  ring

/-- **Universal Pole-Weight-Zero Identity on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` (with **zero** parity or polar hypotheses!),
$$\operatorname{poleWeightArchRe}(0, f.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy (f : RealWeilTestFn) :
    poleWeightArchRe 0 f.1 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
        biScaleLevyEnergy f.source := by
  have h := f.poleWeightArchRe_eq 0
  linarith only [h]

/-- **Unconditional All-Scale Von Mangoldt Signed Lower Bound for `poleWeightArchRe 0` on
`RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `N : ℕ` (with **zero hypotheses**!),
$$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}$$
$$\le\; \operatorname{poleWeightArchRe}(0, f.1)
  + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,
    (\operatorname{weilTest}\,f\,f\,(\log(k+2))).\mathrm{re}.$$ -/
theorem unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound
    (f : RealWeilTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest f.1.1 f.1.1 0).re ≤
      poleWeightArchRe 0 f.1 +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest f.1.1 f.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have hcoerc := global_vonMangoldt_all_scale_signed_coercivity
    f.contDiff_source f.hasCompactSupport_source N
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  rw [← f.autocorr_eq 0] at hpole ⊢
  have hsum :
      (∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest f.1.1 f.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re) =
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            autocorr f.source (Real.log ((k + 2 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [f.autocorr_eq]
  rw [hsum]
  linarith only [hcoerc, hpole]

end RealWeilTestFn

/-! ## §3. The Real Odd Weil Test Sector `RealOddTestFn` & Unconditional Sinh-Capacity Coercivity -/

/-- **The Real-Valued Odd Weil Test Space (`RealOddTestFn`):**
All odd Weil test functions `f : WeilOddTestFn` whose values are real (`(f.1.1 u).im = 0`). -/
def RealOddTestFn : Type := {f : WeilOddTestFn // ∀ u, (f.1.1 u).im = 0}

namespace RealOddTestFn

/-- Canonical embedding of `RealOddTestFn` into `RealWeilTestFn`. -/
def toRealWeilTestFn (f : RealOddTestFn) : RealWeilTestFn := ⟨f.1.1, f.2⟩

/-- The underlying real odd source `f.source : ℝ → ℝ` of `f : RealOddTestFn`. -/
def source (f : RealOddTestFn) (u : ℝ) : ℝ := (f.1.1.1 u).re

theorem source_eq (f : RealOddTestFn) :
    (fun u => (f.source u : ℂ)) = f.1.1.1 :=
  f.toRealWeilTestFn.source_eq

theorem contDiff_source (f : RealOddTestFn) : ContDiff ℝ 2 f.source :=
  f.toRealWeilTestFn.contDiff_source

theorem hasCompactSupport_source (f : RealOddTestFn) : HasCompactSupport f.source :=
  f.toRealWeilTestFn.hasCompactSupport_source

/-- Canonical embedding of `RealOddTestFn` into `C_c(ℝ, ℝ)`. -/
def toCompactlySupported (f : RealOddTestFn) : C_c(ℝ, ℝ) :=
  f.toRealWeilTestFn.toCompactlySupported

/-- The real source of `f : RealOddTestFn` is an odd function: `f.source (-u) = -f.source u`. -/
theorem source_neg (f : RealOddTestFn) (u : ℝ) :
    f.source (-u) = -f.source u := by
  unfold source
  have hodd := congrArg Complex.re (f.1.2 u)
  simpa only [Complex.neg_re] using hodd

theorem autocorr_eq (f : RealOddTestFn) (x : ℝ) :
    autocorr f.source x = (EF.weilTest f.1.1.1 f.1.1.1 x).re :=
  f.toRealWeilTestFn.autocorr_eq x

/-- **Odd-Parity Vanishing of the Cosh Moment on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn`, `∫ u, f.source u * cosh(u / 2) = 0`. -/
theorem integral_source_mul_cosh_eq_zero (f : RealOddTestFn) :
    (∫ u : ℝ, f.source u * Real.cosh (u / 2)) = 0 := by
  have hneg := integral_neg_eq_self (μ := volume) (fun u : ℝ => f.source u * Real.cosh (u / 2))
  have hodd : (fun u : ℝ => f.source (-u) * Real.cosh (-u / 2)) =
      fun u : ℝ => -(f.source u * Real.cosh (u / 2)) := by
    funext u
    rw [f.source_neg u, show (-u : ℝ) / 2 = -(u / 2) by ring, Real.cosh_neg]
    ring
  rw [hodd, integral_neg] at hneg
  linarith only [hneg]

/-- **Exact Sinh-Square Formula for `weilPoleTerm` on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn`,
$$(\operatorname{weilPoleTerm}(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = -2\,\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2 \le 0.$$ -/
theorem re_weilPoleTerm_eq_neg_two_mul_sinh_sq (f : RealOddTestFn) :
    (weilPoleTerm (EF.weilTest f.1.1.1 f.1.1.1)).re =
      -2 * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 := by
  have hpole := re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq
    f.contDiff_source.continuous f.hasCompactSupport_source
  rw [f.source_eq, f.integral_source_mul_cosh_eq_zero] at hpole
  linarith only [hpole]

/-- **Exact `poleWeightArchRe` Formula on `RealOddTestFn` at Arbitrary Pole Weight `β : ℝ`:**
For EVERY `f : RealOddTestFn` and EVERY `β : ℝ`,
$$\operatorname{poleWeightArchRe}(\beta, f.1.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\beta\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2.$$ -/
theorem poleWeightArchRe_eq (f : RealOddTestFn) (β : ℝ) :
    poleWeightArchRe β f.1.1 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source -
        2 * β * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 := by
  have h := f.toRealWeilTestFn.poleWeightArchRe_eq β
  change poleWeightArchRe β f.1.1 =
    EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
      biScaleLevyEnergy f.source +
      2 * β * ((∫ u, f.source u * Real.cosh (u / 2)) ^ 2 -
        (∫ u, f.source u * Real.sinh (u / 2)) ^ 2) at h
  rw [h, f.integral_source_mul_cosh_eq_zero]
  ring

/-- **Unconditional Pole-Weight-Zero Identity on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn`,
$$\operatorname{poleWeightArchRe}(0, f.1.1)
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy (f : RealOddTestFn) :
    poleWeightArchRe 0 f.1.1 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source :=
  f.toRealWeilTestFn.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy

/-- **Unconditional Sinh-Capacity Weil Identity on `RealOddTestFn` ($\beta = 1$):**
For EVERY `f : RealOddTestFn`,
$$\operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
  + 2\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source}).$$ -/
theorem weilArchRe_add_two_mul_sinh_sq_eq_gamma_add_biScaleLevyEnergy (f : RealOddTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) +
        2 * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 =
      EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re +
        biScaleLevyEnergy f.source := by
  have h1 := f.poleWeightArchRe_eq 1
  have h2 : poleWeightArchRe 1 f.1.1 = WeilOneSided.weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) := by
    unfold poleWeightArchRe
    ring
  linarith only [h1, h2]

/-- **Unconditional Dyadic-Window Signed Lower Bound on `RealOddTestFn` at $\beta = 0$:**
For EVERY `f : RealOddTestFn` and EVERY `M : ℕ` (with zero hypotheses!),
$$\bigl(\Omega(0) + \mathcal{C}_{\mathrm{Nyq}}(M+2)\bigr)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}$$
$$\le\; \operatorname{poleWeightArchRe}(0, f.1.1)
  + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
    (\operatorname{weilTest}\,f\,f\,(\log(M+2+k))).\mathrm{re}.$$ -/
theorem unconditional_dyadic_signed_poleWeightArchRe_zero_lower_bound
    (f : RealOddTestFn) (M : ℕ) :
    (EF.gammaBracket 0 + dyadicNyquistCoerciveConstant (M + 2)) *
        (EF.weilTest f.1.1.1 f.1.1.1 0).re ≤
      poleWeightArchRe 0 f.1.1 +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest f.1.1.1 f.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re := by
  have hN : 2 ≤ M + 2 := by omega
  have hcoerc := global_dyadic_nyquist_signed_coercivity
    f.contDiff_source f.hasCompactSupport_source hN
  change dyadicNyquistCoerciveConstant (M + 2) * autocorr f.source 0 ≤ _ at hcoerc
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  rw [← f.autocorr_eq 0] at hpole ⊢
  have hsum :
      (∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest f.1.1.1 f.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re) =
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            autocorr f.source (Real.log ((M + 2 + k : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [f.autocorr_eq]
  rw [hsum]
  linarith only [hcoerc, hpole]

/-- **Unconditional All-Scale Von Mangoldt Signed Lower Bound on `RealOddTestFn` at $\beta = 0$:** -/
theorem unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound
    (f : RealOddTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest f.1.1.1 f.1.1.1 0).re ≤
      poleWeightArchRe 0 f.1.1 +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest f.1.1.1 f.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re :=
  f.toRealWeilTestFn.unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound N

/-- **Unconditional All-Scale Von Mangoldt Signed Sinh-Capacity Weil Lower Bound on `RealOddTestFn` ($\beta = 1$):**
For EVERY `f : RealOddTestFn` and EVERY `N : ℕ` (with **zero hypotheses**!),
$$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,f\,f)
  + 2\left(\int_{\mathbb{R}} f.\mathrm{source}(u)\,\sinh(u/2)\,du\right)^2
  + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,
    (\operatorname{weilTest}\,f\,f\,(\log(k+2))).\mathrm{re}.$$ -/
theorem unconditional_vonMangoldt_all_scale_signed_weilArchRe_sinh_lower_bound
    (f : RealOddTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest f.1.1.1 f.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) +
        2 * (∫ u, f.source u * Real.sinh (u / 2)) ^ 2 +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest f.1.1.1 f.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have h0 := f.unconditional_vonMangoldt_all_scale_signed_poleWeightArchRe_zero_lower_bound N
  have hp0 := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  have hp1 := f.weilArchRe_add_two_mul_sinh_sq_eq_gamma_add_biScaleLevyEnergy
  linarith only [h0, hp0, hp1]

/-- **Unconditional Dyadic-Coset Multi-Node Signed Collar Bound on `RealOddTestFn`:**
For EVERY `f : RealOddTestFn`, `m K : ℕ`, `w : ℕ → ℝ`, and `c y : ℝ` (with **zero hypotheses**!),
the `K` dyadic coset nodes `dyadicCosetNode m i = log((m + 1) · 2^{i + 1})` satisfy: -/
theorem unconditional_dyadic_coset_multi_node_signed_collar_bound
    (f : RealOddTestFn) (m K : ℕ) (w : ℕ → ℝ) (c y : ℝ) :
    (∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
        (EF.weilTest f.1.1.1 f.1.1.1 0).re ≤
      Real.exp c *
          ((EF.weilTest f.1.1.1 f.1.1.1 0).re - (EF.weilTest f.1.1.1 f.1.1.1 y).re) +
        (∑ i ∈ Finset.range K,
          w i * ((EF.weilTest f.1.1.1 f.1.1.1 0).re -
            (EF.weilTest f.1.1.1 f.1.1.1 (dyadicCosetNode m i + y)).re)) +
        (∑ i ∈ Finset.range K,
          w i * (EF.weilTest f.1.1.1 f.1.1.1 (dyadicCosetNode m i)).re) +
        (1 / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest f.1.1.1 f.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re := by
  have hbase := autocorr_multi_node_signed_collar_offDiag_ge
    f.hasCompactSupport_source f.contDiff_source.continuous
    (Finset.range K) w (dyadicCosetNode m) (Real.exp_pos c) y
  have hoff :
      (∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr f.source (dyadicCosetNode m i - dyadicCosetNode m j)) =
        ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr f.source (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [autocorr_dyadicCosetNode_sub_eq]
  rw [hoff] at hbase
  simp_rw [f.autocorr_eq] at hbase
  exact hbase

end RealOddTestFn

/-! ## §4. Real Primitive-Hyperplane Generators `RealHyperplaneGenerator` -/

/-- **The Real Generators of the Primitive Hyperplane (`RealHyperplaneGenerator`):**
The disjoint sum of real odd tests (`RealOddTestFn`) and real even pole-free tests
(`RealEvenPolarTestFn`), corresponding to `RHTower.EvenSector.hyperplaneTest`. -/
abbrev RealHyperplaneGenerator : Type := RealOddTestFn ⊕ RealEvenPolarTestFn

namespace RealHyperplaneGenerator

/-- Canonical projection to `WeilOddTestFn ⊕ WeilEvenPolarTestFn`. -/
def toHyperplaneSum : RealHyperplaneGenerator → WeilOddTestFn ⊕ WeilEvenPolarTestFn
  | Sum.inl f => Sum.inl f.1
  | Sum.inr g => Sum.inr g.1

/-- Canonical projection to `RealWeilTestFn`. -/
def toRealWeilTestFn : RealHyperplaneGenerator → RealWeilTestFn
  | Sum.inl f => f.toRealWeilTestFn
  | Sum.inr g => ⟨g.1.1, g.2⟩

/-- Compatibility with `RHTower.EvenSector.hyperplaneTest`:
`(x.toRealWeilTestFn).1 = hyperplaneTest x.toHyperplaneSum`. -/
@[simp]
theorem toRealWeilTestFn_val_eq_hyperplaneTest (x : RealHyperplaneGenerator) :
    (x.toRealWeilTestFn).1 = RHTower.EvenSector.hyperplaneTest x.toHyperplaneSum := by
  rcases x with f | g <;> rfl

/-- The underlying real source `x.source : ℝ → ℝ` of a primitive-hyperplane generator. -/
def source (x : RealHyperplaneGenerator) : ℝ → ℝ :=
  x.toRealWeilTestFn.source

/-- **Unconditional Primitive-Hyperplane Pole-Weight-Zero Identity:**
For EVERY primitive-hyperplane generator `x : RealHyperplaneGenerator` (odd or even pole-free),
$$\operatorname{poleWeightArchRe}\bigl(0, \operatorname{hyperplaneTest}(x.\mathrm{toHyperplaneSum})\bigr)
  = \Omega(0)\,\operatorname{autocorr}(x.\mathrm{source}, 0)
    + \operatorname{biScaleLevyEnergy}(x.\mathrm{source}).$$ -/
theorem poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
    (x : RealHyperplaneGenerator) :
    poleWeightArchRe 0 (RHTower.EvenSector.hyperplaneTest x.toHyperplaneSum) =
      EF.gammaBracket 0 * autocorr x.source 0 + biScaleLevyEnergy x.source := by
  rw [← x.toRealWeilTestFn_val_eq_hyperplaneTest,
    x.toRealWeilTestFn.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy,
    ← x.toRealWeilTestFn.autocorr_eq 0]
  rfl

/-- **Unconditional All-Scale Von Mangoldt Signed Lower Bound on `RealHyperplaneGenerator`:**
For EVERY `x : RealHyperplaneGenerator` and EVERY `N : ℕ` (with **zero hypotheses**!),
$$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,\operatorname{autocorr}(x.\mathrm{source}, 0)$$
$$\le\; \operatorname{poleWeightArchRe}\bigl(0, \operatorname{hyperplaneTest}(x.\mathrm{toHyperplaneSum})\bigr)
  + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,
    \operatorname{autocorr}(x.\mathrm{source}, \log(k+2)).$$ -/
theorem unconditional_vonMangoldt_all_scale_signed_lower_bound
    (x : RealHyperplaneGenerator) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) * autocorr x.source 0 ≤
      poleWeightArchRe 0 (RHTower.EvenSector.hyperplaneTest x.toHyperplaneSum) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 3 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            autocorr x.source (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hcoerc := global_vonMangoldt_all_scale_signed_coercivity
    x.toRealWeilTestFn.contDiff_source x.toRealWeilTestFn.hasCompactSupport_source N
  have hpole := x.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  unfold source at hpole ⊢
  rw [hpole]
  linarith only [hcoerc]

end RealHyperplaneGenerator

end

end GaloisForLFunctions.BiScaleUncertainty
