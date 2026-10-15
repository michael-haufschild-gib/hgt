import GaloisForLFunctions.RHTower.MarkovShiftPolarizationAndEvenPrimitivePBAP

/-!
# Markov Resolvent Coercivity, Pole-Free Lebesgue–Atom Decomposition, and Euler–Maclaurin Conservation Laws on the Primitive Hyperplane and Odd Sector

This module advances Route HF and the Prime-Blind Archimedean Positivity (PBAP) program by
discovering and proving the **Universal Pole-Free Resolvent Coercivity Identity** and the **Exact
Unit-Step + Euler–Maclaurin + Resolvent Conservation Law** across all three tiers of the Markov /
Weil hierarchy (Full Cone, Primitive Hyperplane, Even Primitive Sector, and Odd Sector).

## Key Mathematical Results

1. **Section 1 (The Bochner–Poisson Resolvent Energy `bochnerResolventEnergy`, the Atom Pair
   `atomPairRe`, the Exact Pole-Free Coercive Identity for `markovArchRe`, and Global $L^2$
   Coercivity):**
   - For any test autocorrelation `k : ℝ → ℂ`, we define the **Bochner–Poisson resolvent energy**
     `bochnerResolventEnergy k := ∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re`
     and the **atom pair evaluation**
     `atomPairRe k := (k (1 / 10000) + k (-(1 / 10000))).re`.
   - For every `f : WeilTestFn`, `bochnerResolventEnergy (EF.weilTest f.1 f.1)` equals the
     nonnegative spectral integral
     `(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) ≥ 0`
     (`bochnerResolventEnergy_weilTest_eq`, `bochnerResolventEnergy_weilTest_nonneg`).
   - Combining `weilArchRe_eq_re_lebesgueAtomWeilFunctional_add` with
     `re_integral_primeIntegrand_lebesguePart_add_exp_neg_abs_eq_re_weilPoleTerm`, we prove that
     subtracting `(weilPoleTerm k).re` from `weilArchRe k` cancels the growing continuum pole
     integral `(∫ x, primeIntegrand k x ∂lebesguePart).re` identically on **all** continuous
     compactly supported `k : ℝ → ℂ` (complex or real, without any parity or hyperplane
     restriction!):
     `markovArchRe k + bochnerResolventEnergy k + atomPairRe k = (lebesgueAtomWeilFunctional k).re`
     (`markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional`).
   - Consequently (`one_hundredth_l2_le_markovArchRe_add_bochnerResolventEnergy_add_atomPairRe`),
     for every `f : WeilTestFn`:
     `(1 / 100) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 ≤ markovArchRe k_f + bochnerResolventEnergy k_f + atomPairRe k_f`,
     and `markovCountertermEnergy lam f.1` admits the universal pole-free coercive decomposition
     `markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re - atomPairRe k_f - bochnerResolventEnergy k_f - primeBlindCounterterm lam f`.

2. **Section 2 (Universal Parity Split (`evenPartReal` + `oddPartReal`) and Shift-Polarization
   Additivity (`evenShift` + `oddShift`) of `atomPairRe`, `bochnerResolventEnergy`, and
   `lebesgueAtomWeilFunctional.re`):**
   - For every odd function `w : ℝ → ℝ`, `∫ u : ℝ, Real.exp (-|u| / 2) * w u = 0`
     (`integral_expNegHalfAbs_mul_of_odd`), so the odd cross-correlations `crossCorr Fe Fo` and
     `crossCorr Fo Fe` integrate to zero against `exp(-|u| / 2)`.
   - Thus `atomPairRe`, `bochnerResolventEnergy`, `(∫ x, primeIntegrand k x ∂lebesguePart).re`, and
     `(lebesgueAtomWeilFunctional k).re` all split additively across `F = evenPartReal F + oddPartReal F`
     for every `F ∈ C²_c(ℝ)` AND across `evenShift g h` and `oddShift g h` for every `g ∈ C²_c(ℝ)`
     and `h ∈ ℝ`.

3. **Section 3 (The Universal Unit-Step + Euler–Maclaurin + Resolvent = Pole Conservation Law across
   Full, Primitive, Even-Primitive, and Odd Sectors):**
   - Eliminating `(∫ x, primeIntegrand k_f x ∂lebesguePart).re` between the Euler–Maclaurin cell
     quadrature identities (`rightCellQuadratureDefect`, `leftCellQuadratureDefect`,
     `trapezoidalCellQuadratureDefect`) and the pole-resolvent identity yields the exact
     conservation law for every `f : WeilTestFn` and cutoff `1 ≤ N`:
     `primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N + bochnerResolventEnergy k_f = (weilPoleTerm k_f).re`
     (`unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm`, and
     analogously for `leftCellQuadratureDefect` and `trapezoidalCellQuadratureDefect`).
   - On the **primitive hyperplane** `coshHalfMoment f = 0` (and in particular on all **odd tests**),
     `(weilPoleTerm k_f).re = -2 * sinhHalfMoment f ^ 2 ≤ 0`, so the sum of four terms
     `primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N + bochnerResolventEnergy k_f + 2 * sinhHalfMoment f ^ 2 = 0`
     vanishes identically!
   - On the **even primitive sector** `EvenPrimitiveWeilTestFn`, both half-moments vanish, so
     `primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N + bochnerResolventEnergy k_f = 0`.

4. **Section 4 (Pole-Free Resolvent Sufficiency Criteria for `WeilPositiveFull`,
   `MarkovPositivePrimitive`, `MarkovPositiveEvenPrimitive`, `MarkovPositiveOdd`, and
   `RiemannHypothesis`, plus Short-Support Shift Identities):**
   - Whenever `primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ ‖f‖²`
     holds on the odd sector (or primitive hyperplane, or even-primitive sector), `MarkovPositiveOdd lam`
     (or `MarkovPositivePrimitive lam`, or `MarkovPositiveEvenPrimitive lam`) and `RiemannHypothesis` hold.
   - For short-support bumps `g` supported in `[-1/4, 1/4]`, we give the exact pole-free coercive
     decompositions of `markovCountertermEnergy lam (oddShift g h)` and
     `markovCountertermEnergy lam (evenShift g h)` in terms of `windowSum hg hgc hsupp lam h`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Bochner–Poisson Resolvent Energy `bochnerResolventEnergy`, the Atom Pair `atomPairRe`, the Exact Pole-Free Coercive Identity for `markovArchRe`, and Global $L^2$ Coercivity -/

/-- The **Bochner–Poisson resolvent energy** of a correlation kernel `k : ℝ → ℂ`:
`bochnerResolventEnergy k = ∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re`. -/
def bochnerResolventEnergy (k : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re

/-- The **atom pair evaluation** of `k : ℝ → ℂ` at `±1/10000`:
`atomPairRe k = (k (1 / 10000) + k (-(1 / 10000))).re`. -/
def atomPairRe (k : ℝ → ℂ) : ℝ :=
  (k (1 / 10000) + k (-(1 / 10000))).re

/-- **Spectral Formula for `bochnerResolventEnergy` on `WeilTestFn`**:
for every `f : WeilTestFn`,
`bochnerResolventEnergy (EF.weilTest f.1 f.1) = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))`. -/
theorem bochnerResolventEnergy_weilTest_eq (f : WeilTestFn) :
    bochnerResolventEnergy (EF.weilTest f.1 f.1) =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
  re_integral_expNegHalfAbs_weilTest_eq f

/-- **Bochner Nonnegativity of `bochnerResolventEnergy` on `WeilTestFn`**:
for every `f : WeilTestFn`, `0 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1)`. -/
theorem bochnerResolventEnergy_weilTest_nonneg (f : WeilTestFn) :
    0 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) :=
  re_integral_expNegHalfAbs_weilTest_nonneg f

/-- **Exact Pole–Resolvent Decomposition of the Continuum `lebesguePart` Integral**:
for every continuous compactly supported `k : ℝ → ℂ`,
`(∫ x, primeIntegrand k x ∂lebesguePart).re + bochnerResolventEnergy k = (weilPoleTerm k).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    (∫ x, primeIntegrand k x ∂lebesguePart).re + bochnerResolventEnergy k =
      (weilPoleTerm k).re :=
  re_integral_primeIntegrand_lebesguePart_add_exp_neg_abs_eq_re_weilPoleTerm hk hkc

/-- **Universal Pole-Free Resolvent Identity (`markovArchRe + bochnerResolventEnergy + atomPairRe = lebesgueAtomWeilFunctional.re`)**:
for every continuous compactly supported `k : ℝ → ℂ`, subtracting `(weilPoleTerm k).re` from
`weilArchRe k` cancels the growing continuum pole integral `(∫ x, primeIntegrand k x ∂lebesguePart).re`
identically up to `bochnerResolventEnergy k`:
`markovArchRe k + bochnerResolventEnergy k + atomPairRe k = (lebesgueAtomWeilFunctional k).re`. -/
theorem markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    markovArchRe k + bochnerResolventEnergy k + atomPairRe k =
      (lebesgueAtomWeilFunctional k).re := by
  have h1 := weilArchRe_eq_re_lebesgueAtomWeilFunctional_add k
  have h2 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    hk hkc
  unfold markovArchRe atomPairRe
  rw [Complex.sub_re] at h1
  linarith

/-- Rearranged form of `markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional`:
`markovArchRe k = (lebesgueAtomWeilFunctional k).re - atomPairRe k - bochnerResolventEnergy k`. -/
theorem markovArchRe_eq_re_lebesgueAtomWeilFunctional_sub_atomPairRe_sub_bochnerResolventEnergy
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    markovArchRe k =
      (lebesgueAtomWeilFunctional k).re - atomPairRe k - bochnerResolventEnergy k := by
  have h :=
    markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional hk hkc
  linarith

/-- Specialization of `markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional`
to `EF.weilTest f.1 f.1` for any `f : WeilTestFn`. -/
theorem markovArchRe_weilTest_add_bochnerResolventEnergy_add_atomPairRe (f : WeilTestFn) :
    markovArchRe (EF.weilTest f.1 f.1) + bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        atomPairRe (EF.weilTest f.1 f.1) =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  exact markovArchRe_add_bochnerResolventEnergy_add_atomPairRe_eq_re_lebesgueAtomWeilFunctional
    hkd.continuous hkc

/-- Specialization of `markovArchRe_weilTest_add_bochnerResolventEnergy_add_atomPairRe` to a real
test `f ∈ C²_c(ℝ)`. -/
theorem markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) +
        bochnerResolventEnergy (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) +
        atomPairRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      (lebesgueAtomWeilFunctional
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re :=
  markovArchRe_weilTest_add_bochnerResolventEnergy_add_atomPairRe (realWeilTestFn f hf hfc)

/-- **Universal Pole-Free $L^2$ Coercivity of `markovArchRe + bochnerResolventEnergy + atomPairRe`**:
for every `f : WeilTestFn` (complex or real, without any parity or hyperplane condition),
`(1 / 100) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 ≤ markovArchRe (EF.weilTest f.1 f.1) + bochnerResolventEnergy (EF.weilTest f.1 f.1) + atomPairRe (EF.weilTest f.1 f.1)`. -/
theorem one_hundredth_l2_le_markovArchRe_add_bochnerResolventEnergy_add_atomPairRe
    (f : WeilTestFn) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      markovArchRe (EF.weilTest f.1 f.1) + bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        atomPairRe (EF.weilTest f.1 f.1) := by
  rw [markovArchRe_weilTest_add_bochnerResolventEnergy_add_atomPairRe f]
  exact lebesgueAtomWeilFunctional_coercive f.2.1 f.2.2

/-- **Universal Pole-Free Coercive Lower Bound for `markovArchRe`**:
for every `f : WeilTestFn`,
`(1 / 100) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 - atomPairRe k_f - bochnerResolventEnergy k_f ≤ markovArchRe k_f`. -/
theorem one_hundredth_l2_sub_atomPairRe_sub_bochnerResolventEnergy_le_markovArchRe
    (f : WeilTestFn) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - atomPairRe (EF.weilTest f.1 f.1) -
        bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤
      markovArchRe (EF.weilTest f.1 f.1) := by
  have h := one_hundredth_l2_le_markovArchRe_add_bochnerResolventEnergy_add_atomPairRe f
  linarith

/-- **Universal Pole-Free Coercive Decomposition of `markovCountertermEnergy` on all `WeilTestFn`**:
for every `f : WeilTestFn` and every counterterm sequence `lam : ℕ → ℝ`,
`markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re - atomPairRe k_f - bochnerResolventEnergy k_f - primeBlindCounterterm lam f`. -/
theorem markovCountertermEnergy_eq_re_lebesgueAtomWeilFunctional_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm
    (lam : ℕ → ℝ) (f : WeilTestFn) :
    markovCountertermEnergy lam f.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re -
        atomPairRe (EF.weilTest f.1 f.1) -
        bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        primeBlindCounterterm lam f := by
  rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam f,
    ← markovArchRe_weilTest_add_bochnerResolventEnergy_add_atomPairRe f]
  ring

/-- **Universal Pole-Free Coercive Lower Bound for `markovCountertermEnergy` on all `WeilTestFn`**:
for every `f : WeilTestFn` and every counterterm sequence `lam : ℕ → ℝ`,
`(1 / 100) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 - atomPairRe k_f - bochnerResolventEnergy k_f - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f.1`. -/
theorem one_hundredth_l2_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm_le_markovCountertermEnergy
    (lam : ℕ → ℝ) (f : WeilTestFn) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        atomPairRe (EF.weilTest f.1 f.1) -
        bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        primeBlindCounterterm lam f ≤
      markovCountertermEnergy lam f.1 := by
  have h1 := one_hundredth_l2_sub_atomPairRe_sub_bochnerResolventEnergy_le_markovArchRe f
  have h2 := markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam f
  linarith

/-! ## Section 2: Universal Parity Split (`evenPartReal` + `oddPartReal`) and Shift-Polarization Additivity (`evenShift` + `oddShift`) of `atomPairRe`, `bochnerResolventEnergy`, and `lebesgueAtomWeilFunctional.re` -/

/-- Any odd real function `w : ℝ → ℝ` (`∀ u, w (-u) = -w u`) integrates to zero against the even
weight `Real.exp (-|u| / 2)`. -/
theorem integral_expNegHalfAbs_mul_of_odd {w : ℝ → ℝ} (hodd : ∀ u, w (-u) = -w u) :
    ∫ u : ℝ, Real.exp (-|u| / 2) * w u = 0 := by
  have h : ∫ u : ℝ, Real.exp (-|u| / 2) * w u = -∫ u : ℝ, Real.exp (-|u| / 2) * w u := by
    rw [← integral_neg, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [abs_neg, hodd u, mul_neg]
  linarith

/-- **Parity Split of `atomPairRe`**:
for any continuous compactly supported real function `F : ℝ → ℝ`, `atomPairRe` splits additively
across `F = evenPartReal F + oddPartReal F`. -/
theorem atomPairRe_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    atomPairRe (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) =
      atomPairRe (EF.weilTest (fun u => (evenPartReal F u : ℂ))
          (fun u => (evenPartReal F u : ℂ))) +
        atomPairRe (EF.weilTest (fun u => (oddPartReal F u : ℂ))
          (fun u => (oddPartReal F u : ℂ))) := by
  unfold atomPairRe
  have h := weilTest_ofReal_add_neg_eq_even_add_odd hF hFc (1 / 10000 : ℝ)
  have hre := congrArg Complex.re h
  simpa only [Complex.add_re] using hre

/-- **Parity Split of `bochnerResolventEnergy`**:
for any `F ∈ C²_c(ℝ)`, `bochnerResolventEnergy` splits additively across
`F = evenPartReal F + oddPartReal F` because the odd cross-correlations `crossCorr Fe Fo` and
`crossCorr Fo Fe` integrate to zero against `exp(-|u| / 2)`. -/
theorem bochnerResolventEnergy_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    bochnerResolventEnergy (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) =
      bochnerResolventEnergy (EF.weilTest (fun u => (evenPartReal F u : ℂ))
          (fun u => (evenPartReal F u : ℂ))) +
        bochnerResolventEnergy (EF.weilTest (fun u => (oddPartReal F u : ℂ))
          (fun u => (oddPartReal F u : ℂ))) := by
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFed : ContDiff ℝ 2 Fe := contDiff_evenPartReal hF
  have hFod : ContDiff ℝ 2 Fo := contDiff_oddPartReal hF
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  have hFC : ContDiff ℝ 2 fun x => (F x : ℂ) := Complex.ofRealCLM.contDiff.comp hF
  have hFcC : HasCompactSupport fun x => (F x : ℂ) := hFc.comp_left Complex.ofReal_zero
  have hFedC : ContDiff ℝ 2 fun x => (Fe x : ℂ) := Complex.ofRealCLM.contDiff.comp hFed
  have hFodC : ContDiff ℝ 2 fun x => (Fo x : ℂ) := Complex.ofRealCLM.contDiff.comp hFod
  have hFecC : HasCompactSupport fun x => (Fe x : ℂ) := hFec.comp_left Complex.ofReal_zero
  have hFocC : HasCompactSupport fun x => (Fo x : ℂ) := hFoc.comp_left Complex.ofReal_zero
  have hk : ∀ u : ℝ,
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) u).re =
        (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re +
          (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re +
          (crossCorr Fe Fo u + crossCorr Fo Fe u) := by
    intro u
    have hFsum : (fun x => Fe x + Fo x) = F := funext (evenPartReal_add_oddPartReal F)
    have hcc := crossCorr_add_add hFed.continuous hFec hFod.continuous hFoc u
    rw [hFsum] at hcc
    rw [weilTest_ofReal_eq, weilTest_ofReal_eq, weilTest_ofReal_eq]
    simp only [Complex.ofReal_re]
    exact hcc
  have iF : Integrable fun u : ℝ =>
      Real.exp (-|u| / 2) * (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) u).re := by
    have hc : Continuous fun u : ℝ =>
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) u).re :=
      Complex.continuous_re.comp (EF.weilTest_contDiff hFC hFC.continuous hFcC).continuous
    have hs : HasCompactSupport fun u : ℝ =>
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) u).re :=
      (EF.weilTest_hasCompactSupport hFcC hFcC).comp_left Complex.zero_re
    exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-|u| / 2)).mul hc).integrable_of_hasCompactSupport
      hs.mul_left
  have ie : Integrable fun u : ℝ =>
      Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re := by
    have hc : Continuous fun u : ℝ =>
        (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re :=
      Complex.continuous_re.comp (EF.weilTest_contDiff hFedC hFedC.continuous hFecC).continuous
    have hs : HasCompactSupport fun u : ℝ =>
        (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re :=
      (EF.weilTest_hasCompactSupport hFecC hFecC).comp_left Complex.zero_re
    exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-|u| / 2)).mul hc).integrable_of_hasCompactSupport
      hs.mul_left
  have io : Integrable fun u : ℝ =>
      Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re := by
    have hc : Continuous fun u : ℝ =>
        (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re :=
      Complex.continuous_re.comp (EF.weilTest_contDiff hFodC hFodC.continuous hFocC).continuous
    have hs : HasCompactSupport fun u : ℝ =>
        (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re :=
      (EF.weilTest_hasCompactSupport hFocC hFocC).comp_left Complex.zero_re
    exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-|u| / 2)).mul hc).integrable_of_hasCompactSupport
      hs.mul_left
  unfold bochnerResolventEnergy
  have ieo : Integrable fun u : ℝ =>
      Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re +
        Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re :=
    ie.add io
  have h1 := integral_add ie io
  have h2 := integral_sub iF ieo
  have h3 : ∫ u : ℝ, Real.exp (-|u| / 2) * (crossCorr Fe Fo u + crossCorr Fo Fe u) =
      (∫ u : ℝ, Real.exp (-|u| / 2) *
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) u).re) -
      ∫ u : ℝ,
        (Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) u).re +
          Real.exp (-|u| / 2) * (EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) u).re) := by
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [hk u]
    ring
  have hodd_cross : ∀ u : ℝ,
      crossCorr Fe Fo (-u) + crossCorr Fo Fe (-u) =
        -(crossCorr Fe Fo u + crossCorr Fo Fe u) := by
    intro u
    rw [crossCorr_even_odd_neg (evenPartReal_neg F) (oddPartReal_neg F),
      crossCorr_odd_even_neg (evenPartReal_neg F) (oddPartReal_neg F)]
    ring
  have hzero : ∫ u : ℝ, Real.exp (-|u| / 2) * (crossCorr Fe Fo u + crossCorr Fo Fe u) = 0 :=
    integral_expNegHalfAbs_mul_of_odd hodd_cross
  linarith

/-- **Parity Split of the Continuum `lebesguePart` Integral**:
for every `F ∈ C²_c(ℝ)`, `(∫ x, primeIntegrand k_F x ∂lebesguePart).re` splits additively across
`evenPartReal F` and `oddPartReal F`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_eq_even_add_odd {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) x
        ∂lebesguePart).re =
      (∫ x, primeIntegrand (EF.weilTest (fun u => (evenPartReal F u : ℂ))
          (fun u => (evenPartReal F u : ℂ))) x ∂lebesguePart).re +
        (∫ x, primeIntegrand (EF.weilTest (fun u => (oddPartReal F u : ℂ))
          (fun u => (oddPartReal F u : ℂ))) x ∂lebesguePart).re := by
  have h1 := re_integral_primeIntegrand_lebesguePart_ofReal_eq hF hFc
  have h2 := re_integral_primeIntegrand_lebesguePart_ofReal_eq
    (contDiff_evenPartReal hF) (hasCompactSupport_evenPartReal hFc)
  have h3 := re_integral_primeIntegrand_lebesguePart_ofReal_eq
    (contDiff_oddPartReal hF) (hasCompactSupport_oddPartReal hFc)
  have hce := coshHalfMoment_eq_evenPartReal hF.continuous hFc
  have hse := sinhHalfMoment_eq_zero_of_even (evenPartReal_neg F)
  have hco := coshHalfMoment_eq_zero_of_odd (oddPartReal_neg F)
  have hso := sinhHalfMoment_eq_oddPartReal hF.continuous hFc
  have hres := bochnerResolventEnergy_ofReal_eq_even_add_odd hF hFc
  unfold bochnerResolventEnergy at hres
  rw [← hce, hse] at h2
  rw [hco, ← hso] at h3
  linarith

/-- **Parity Split of `(lebesgueAtomWeilFunctional k_F).re`**:
for every `F ∈ C²_c(ℝ)`, `(lebesgueAtomWeilFunctional k_F).re` splits additively across
`evenPartReal F` and `oddPartReal F`. -/
theorem re_lebesgueAtomWeilFunctional_ofReal_eq_even_add_odd {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    (lebesgueAtomWeilFunctional
        (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (evenPartReal F u : ℂ))
          (fun u => (evenPartReal F u : ℂ)))).re +
        (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (oddPartReal F u : ℂ))
          (fun u => (oddPartReal F u : ℂ)))).re := by
  have h1 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe hF hFc
  have h2 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_evenPartReal hF) (hasCompactSupport_evenPartReal hFc)
  have h3 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_oddPartReal hF) (hasCompactSupport_oddPartReal hFc)
  linarith [markovArchRe_ofReal_eq_even_add_odd hF hFc,
    bochnerResolventEnergy_ofReal_eq_even_add_odd hF hFc,
    atomPairRe_ofReal_eq_even_add_odd hF.continuous hFc]

/-- **Shift-Polarization Additivity of `atomPairRe`**:
for every continuous compactly supported `g : ℝ → ℝ` and `h ∈ ℝ`,
`atomPairRe (k_{evenShift g h}) + atomPairRe (k_{oddShift g h}) = atomPairRe k_g`. -/
theorem atomPairRe_evenShift_add_oddShift {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    atomPairRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) +
      atomPairRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) =
      atomPairRe (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) := by
  unfold atomPairRe
  have h1 := weilTest_evenShift_add_oddShift hg hgc h (1 / 10000 : ℝ)
  have h2 := weilTest_evenShift_add_oddShift hg hgc h (-(1 / 10000 : ℝ))
  have h1r := congrArg Complex.re h1
  have h2r := congrArg Complex.re h2
  simp only [Complex.add_re] at h1r h2r ⊢
  linarith

/-- **Shift-Polarization Additivity of `bochnerResolventEnergy`**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`bochnerResolventEnergy (k_{evenShift g h}) + bochnerResolventEnergy (k_{oddShift g h}) = bochnerResolventEnergy k_g`. -/
theorem bochnerResolventEnergy_evenShift_add_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    bochnerResolventEnergy (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ))) +
      bochnerResolventEnergy (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) =
      bochnerResolventEnergy (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) := by
  have hed : ContDiff ℝ 2 fun u => (evenShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_evenShift hg h)
  have hec : HasCompactSupport fun u => (evenShift g h u : ℂ) :=
    (hasCompactSupport_evenShift hgc h).comp_left Complex.ofReal_zero
  have hod : ContDiff ℝ 2 fun u => (oddShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hg h)
  have hoc : HasCompactSupport fun u => (oddShift g h u : ℂ) :=
    (hasCompactSupport_oddShift hgc h).comp_left Complex.ofReal_zero
  have hke_cont : Continuous fun u : ℝ =>
      Real.exp (-|u| / 2) *
        (EF.weilTest (fun x => (evenShift g h x : ℂ))
          (fun x => (evenShift g h x : ℂ)) u).re := by
    have : Continuous fun u : ℝ =>
        (EF.weilTest (fun x => (evenShift g h x : ℂ))
          (fun x => (evenShift g h x : ℂ)) u).re :=
      Complex.continuous_re.comp (EF.weilTest_contDiff hed hed.continuous hec).continuous
    exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-|u| / 2)).mul this
  have hke_cpt : HasCompactSupport fun u : ℝ =>
      Real.exp (-|u| / 2) *
        (EF.weilTest (fun x => (evenShift g h x : ℂ))
          (fun x => (evenShift g h x : ℂ)) u).re := by
    have : HasCompactSupport fun u : ℝ =>
        (EF.weilTest (fun x => (evenShift g h x : ℂ))
          (fun x => (evenShift g h x : ℂ)) u).re :=
      (EF.weilTest_hasCompactSupport hec hec).comp_left Complex.zero_re
    exact this.mul_left
  have hko_cont : Continuous fun u : ℝ =>
      Real.exp (-|u| / 2) *
        (EF.weilTest (fun x => (oddShift g h x : ℂ))
          (fun x => (oddShift g h x : ℂ)) u).re := by
    have : Continuous fun u : ℝ =>
        (EF.weilTest (fun x => (oddShift g h x : ℂ))
          (fun x => (oddShift g h x : ℂ)) u).re :=
      Complex.continuous_re.comp (EF.weilTest_contDiff hod hod.continuous hoc).continuous
    exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-|u| / 2)).mul this
  have hko_cpt : HasCompactSupport fun u : ℝ =>
      Real.exp (-|u| / 2) *
        (EF.weilTest (fun x => (oddShift g h x : ℂ))
          (fun x => (oddShift g h x : ℂ)) u).re := by
    have : HasCompactSupport fun u : ℝ =>
        (EF.weilTest (fun x => (oddShift g h x : ℂ))
          (fun x => (oddShift g h x : ℂ)) u).re :=
      (EF.weilTest_hasCompactSupport hoc hoc).comp_left Complex.zero_re
    exact this.mul_left
  unfold bochnerResolventEnergy
  rw [← integral_add (hke_cont.integrable_of_hasCompactSupport hke_cpt)
    (hko_cont.integrable_of_hasCompactSupport hko_cpt)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  have hsum := congrArg Complex.re (weilTest_evenShift_add_oddShift hg.continuous hgc h u)
  rw [Complex.add_re] at hsum
  rw [← mul_add, hsum]

/-- **Shift-Polarization Additivity of the Continuum `lebesguePart` Integral**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`(∫ x, primeIntegrand k_{evenShift g h} x ∂lebesguePart).re + (∫ x, primeIntegrand k_{oddShift g h} x ∂lebesguePart).re = (∫ x, primeIntegrand k_g x ∂lebesguePart).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_evenShift_add_oddShift {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (evenShift g h u : ℂ))
          (fun u => (evenShift g h u : ℂ))) x ∂lebesguePart).re +
      (∫ x, primeIntegrand (EF.weilTest (fun u => (oddShift g h u : ℂ))
          (fun u => (oddShift g h u : ℂ))) x ∂lebesguePart).re =
      (∫ x, primeIntegrand (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) x
        ∂lebesguePart).re := by
  have hed : ContDiff ℝ 2 fun u => (evenShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_evenShift hg h)
  have hec : HasCompactSupport fun u => (evenShift g h u : ℂ) :=
    (hasCompactSupport_evenShift hgc h).comp_left Complex.ofReal_zero
  have hod : ContDiff ℝ 2 fun u => (oddShift g h u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hg h)
  have hoc : HasCompactSupport fun u => (oddShift g h u : ℂ) :=
    (hasCompactSupport_oddShift hgc h).comp_left Complex.ofReal_zero
  have hgd : ContDiff ℝ 2 fun u => (g u : ℂ) := Complex.ofRealCLM.contDiff.comp hg
  have hgc' : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have h1 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (EF.weilTest_contDiff hed hed.continuous hec).continuous (EF.weilTest_hasCompactSupport hec hec)
  have h2 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (EF.weilTest_contDiff hod hod.continuous hoc).continuous (EF.weilTest_hasCompactSupport hoc hoc)
  have h3 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (EF.weilTest_contDiff hgd hgd.continuous hgc').continuous
    (EF.weilTest_hasCompactSupport hgc' hgc')
  linarith [re_weilPoleTerm_evenShift_add_oddShift hg.continuous hgc h,
    bochnerResolventEnergy_evenShift_add_oddShift hg hgc h]

/-- **Shift-Polarization Additivity of `(lebesgueAtomWeilFunctional k).re`**:
for every `g ∈ C²_c(ℝ)` and `h ∈ ℝ`,
`(lebesgueAtomWeilFunctional k_{evenShift g h}).re + (lebesgueAtomWeilFunctional k_{oddShift g h}).re = (lebesgueAtomWeilFunctional k_g).re`. -/
theorem re_lebesgueAtomWeilFunctional_evenShift_add_oddShift {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (evenShift g h u : ℂ))
        (fun u => (evenShift g h u : ℂ)))).re +
      (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))).re =
      (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (g u : ℂ))
        (fun u => (g u : ℂ)))).re := by
  have h1 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_evenShift hg h) (hasCompactSupport_evenShift hgc h)
  have h2 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h)
  have h3 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe hg hgc
  linarith [markovArchRe_evenShift_add_oddShift hg hgc h,
    bochnerResolventEnergy_evenShift_add_oddShift hg hgc h,
    atomPairRe_evenShift_add_oddShift hg.continuous hgc h]

/-! ## Section 3: The Universal Unit-Step + Euler–Maclaurin + Resolvent = Pole Conservation Law across Full, Primitive, Even-Primitive, and Odd Sectors -/

/-- **Universal Right-Endpoint Euler–Maclaurin + Resolvent = Pole Conservation Law**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`, the sum of the discrete unit-step counterterm
`primeBlindCounterterm unitStepCountertermWeight f`, the right-endpoint cell quadrature defect
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`, and the Bochner–Poisson resolvent
energy `bochnerResolventEnergy (EF.weilTest f.1 f.1)` equals `(weilPoleTerm (EF.weilTest f.1 f.1)).re`. -/
theorem unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight f +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N +
        bochnerResolventEnergy (EF.weilTest f.1 f.1) =
      (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have h1 := re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect f hN1 hN
  have h2 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    hkd.continuous hkc
  linarith

/-- **Universal Left-Endpoint Euler–Maclaurin + Resolvent = Pole Conservation Law**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`primeBlindCounterterm unitStepCountertermWeight f + leftCellQuadratureDefect (weilContinuumLogProfile f.1) N + bochnerResolventEnergy (EF.weilTest f.1 f.1) = (weilPoleTerm (EF.weilTest f.1 f.1)).re`. -/
theorem unitStep_add_leftCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight f +
        leftCellQuadratureDefect (weilContinuumLogProfile f.1) N +
        bochnerResolventEnergy (EF.weilTest f.1 f.1) =
      (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have h1 := re_integral_lebesguePart_sub_unitStep_eq_leftCellQuadratureDefect f hN1 hN
  have h2 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    hkd.continuous hkc
  linarith

/-- **Universal Trapezoidal Euler–Maclaurin + Resolvent = Pole Conservation Law**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`primeBlindCounterterm unitStepCountertermWeight f + trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N + bochnerResolventEnergy (EF.weilTest f.1 f.1) = (weilPoleTerm (EF.weilTest f.1 f.1)).re`. -/
theorem unitStep_add_trapezoidalCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight f +
        trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N +
        bochnerResolventEnergy (EF.weilTest f.1 f.1) =
      (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have h1 := re_integral_lebesguePart_sub_unitStep_eq_trapezoidalCellQuadratureDefect f hN1 hN
  have h2 := re_integral_primeIntegrand_lebesguePart_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    hkd.continuous hkc
  linarith

/-- **Real-Test Rank-2 `(1, 1)` Conservation Law (`2 C(f)² - 2 S(f)²`)**:
for every real test `f ∈ C²_c(ℝ)` and support cutoff `1 ≤ N`,
`primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f) N + bochnerResolventEnergy k_f = 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2`. -/
theorem unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_ofReal_eq
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
        bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 := by
  rw [unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    (realWeilTestFn f hf hfc) hN1 hN]
  exact re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.continuous hfc

/-- **Zero-Sum Conservation Law on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
for every real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0` (and in
particular every odd test) and support cutoff `1 ≤ N`, the sum of the unit-step counterterm, the
right-endpoint Euler–Maclaurin quadrature defect, the nonnegative Bochner–Poisson resolvent energy,
and the nonnegative square `2 * sinhHalfMoment f ^ 2` vanishes identically:
`primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f) N + bochnerResolventEnergy k_f + 2 * sinhHalfMoment f ^ 2 = 0`. -/
theorem unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
        bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 = 0 := by
  have h := unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_ofReal_eq
    hf hfc hN1 hN
  rw [hcosh] at h
  linarith

/-- **Zero-Sum Conservation Law on the Odd Sector (`∀ x, f (-x) = -f x`)**:
for every odd real test `f ∈ C²_c(ℝ)` and support cutoff `1 ≤ N`,
`primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f) N + bochnerResolventEnergy k_f + 2 * sinhHalfMoment f ^ 2 = 0`. -/
theorem unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_odd
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
        bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 = 0 :=
  unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hN

/-- **Three-Term Zero-Sum Conservation Law on the Even Primitive Sector (`EvenPrimitiveWeilTestFn`)**:
for every `f : EvenPrimitiveWeilTestFn` and support cutoff `1 ≤ N`, both half-moments vanish, so
`primeBlindCounterterm unitStepCountertermWeight f + rightCellQuadratureDefect (weilContinuumLogProfile f) N + bochnerResolventEnergy k_f = 0`. -/
theorem EvenPrimitiveWeilTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
    (f : EvenPrimitiveWeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1 (Real.log x) = 0 ∧
        EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight f.toWeilTestFn +
        rightCellQuadratureDefect (weilContinuumLogProfile f.toWeilTestFn.1) N +
        bochnerResolventEnergy (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) = 0 := by
  rw [unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    f.toWeilTestFn hN1 hN, f.re_weilPoleTerm_eq_zero]

/-! ## Section 4: Pole-Free Resolvent Sufficiency Criteria for `WeilPositiveFull`, `MarkovPositivePrimitive`, `MarkovPositiveEvenPrimitive`, `MarkovPositiveOdd`, and `RiemannHypothesis`, plus Short-Support Shift Identities -/

/-- **Pointwise Nonnegativity of `markovCountertermEnergy` from Pole-Free Resolvent + Coercive
Domination**:
for any `f : WeilTestFn` and any counterterm sequence `lam : ℕ → ℝ`, if
`primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`,
then `0 ≤ markovCountertermEnergy lam f.1`. -/
theorem markovCountertermEnergy_nonneg_of_counterterm_add_bochnerResolventEnergy_le_coercive
    (lam : ℕ → ℝ) (f : WeilTestFn)
    (hdom : primeBlindCounterterm lam f + bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        atomPairRe (EF.weilTest f.1 f.1) ≤
      (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) :
    0 ≤ markovCountertermEnergy lam f.1 := by
  have h :=
    one_hundredth_l2_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm_le_markovCountertermEnergy
      lam f
  linarith

/-- **Odd-Sector Markov Positivity from Pole-Free Resolvent + Coercive Domination**:
if for every odd real test `f ∈ C²_c(ℝ)`,
`primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ ‖f‖²`,
then `MarkovPositiveOdd lam` holds. -/
theorem markovPositiveOdd_of_counterterm_add_bochnerResolventEnergy_le_coercive
    {lam : ℕ → ℝ}
    (hdom : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) +
          bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) :
    MarkovPositiveOdd lam := by
  intro f hf hfc hodd
  exact markovCountertermEnergy_nonneg_of_counterterm_add_bochnerResolventEnergy_le_coercive
    lam (realWeilTestFn f hf hfc) (hdom f hf hfc hodd)

/-- **Primitive-Hyperplane Markov Positivity from Pole-Free Resolvent + Coercive Domination**:
if for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`,
`primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ ‖f‖²`,
then `MarkovPositivePrimitive lam` holds. -/
theorem markovPositivePrimitive_of_counterterm_add_bochnerResolventEnergy_le_coercive
    {lam : ℕ → ℝ}
    (hdom : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      coshHalfMoment f = 0 →
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) +
          bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) :
    MarkovPositivePrimitive lam := by
  intro f hf hfc hcosh
  exact markovCountertermEnergy_nonneg_of_counterterm_add_bochnerResolventEnergy_le_coercive
    lam (realWeilTestFn f hf hfc) (hdom f hf hfc hcosh)

/-- **Even-Primitive Markov Positivity from Pole-Free Resolvent + Coercive Domination**:
if for every even real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`,
`primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ ‖f‖²`,
then `MarkovPositiveEvenPrimitive lam` holds. -/
theorem markovPositiveEvenPrimitive_of_counterterm_add_bochnerResolventEnergy_le_coercive
    {lam : ℕ → ℝ}
    (hdom : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = f x) → coshHalfMoment f = 0 →
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) +
          bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) :
    MarkovPositiveEvenPrimitive lam := by
  intro f hf hfc heven hcosh
  exact markovCountertermEnergy_nonneg_of_counterterm_add_bochnerResolventEnergy_le_coercive
    lam (realWeilTestFn f hf hfc) (hdom f hf hfc heven hcosh)

/-- **Unconditional `RiemannHypothesis` from Odd-Sector Pole-Free Resolvent + Coercive Domination**:
if there exists *any* counterterm sequence `lam : ℕ → ℝ` (or for each odd test `f` a sequence `lam`
with `primeBlindCounterterm Λ f ≤ primeBlindCounterterm lam f`) satisfying
`primeBlindCounterterm lam f + bochnerResolventEnergy k_f + atomPairRe k_f ≤ (1 / 100) * ∫ ‖f‖²`
on all odd real tests `f ∈ C²_c(ℝ)`, then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_odd_exists_counterterm_add_bochnerResolventEnergy_le_coercive
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ lam : ℕ → ℝ,
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) +
            bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
              (realWeilTestFn f hf hfc).1) +
            atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1
              (realWeilTestFn f hf hfc).1) ≤
          (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ∧
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn f hf hfc) ≤
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_odd_exists_counterterm_markov_nonneg fun f hf hfc hodd => ?_
  obtain ⟨lam, hdom, hle⟩ := h f hf hfc hodd
  exact ⟨lam,
    markovCountertermEnergy_nonneg_of_counterterm_add_bochnerResolventEnergy_le_coercive
      lam (realWeilTestFn f hf hfc) hdom,
    hle⟩

/-- **Exact Pole-Free Coercive Window Decomposition of `markovCountertermEnergy` on `oddShift g h`**:
when `g ∈ C²_c(ℝ)` is supported in `[-1/4, 1/4]`, for every counterterm sequence `lam : ℕ → ℝ` and
shift `h ∈ ℝ`,
`markovCountertermEnergy lam (oddShift g h) = (lebesgueAtomWeilFunctional k_{oddShift g h}).re - atomPairRe k_{oddShift g h} - bochnerResolventEnergy k_{oddShift g h} + (1 / 2) * windowSum hg hgc hsupp lam h`. -/
theorem markovCountertermEnergy_oddShift_eq_lebesgueAtom_sub_atomPair_sub_resolvent_add_half_windowSum
    (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (oddShift g h u : ℂ))
          (fun u => (oddShift g h u : ℂ)))).re -
        atomPairRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
          (fun u => (oddShift g h u : ℂ))) -
        bochnerResolventEnergy (EF.weilTest (fun u => (oddShift g h u : ℂ))
          (fun u => (oddShift g h u : ℂ))) +
        (1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  have h1 := markovCountertermEnergy_oddShift_eq_arch_add_half_windowSum lam hg hgc hsupp h
  have h2 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h)
  linarith

/-- **Exact Pole-Free Coercive Window Decomposition of `markovCountertermEnergy` on `evenShift g h`**:
when `g ∈ C²_c(ℝ)` is supported in `[-1/4, 1/4]`, for every counterterm sequence `lam : ℕ → ℝ` and
shift `h ∈ ℝ`,
`markovCountertermEnergy lam (evenShift g h) = (lebesgueAtomWeilFunctional k_{evenShift g h}).re - atomPairRe k_{evenShift g h} - bochnerResolventEnergy k_{evenShift g h} - (1 / 2) * windowSum hg hgc hsupp lam h`. -/
theorem markovCountertermEnergy_evenShift_eq_lebesgueAtom_sub_atomPair_sub_resolvent_sub_half_windowSum
    (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    markovCountertermEnergy lam (fun u => (evenShift g h u : ℂ)) =
      (lebesgueAtomWeilFunctional (EF.weilTest (fun u => (evenShift g h u : ℂ))
          (fun u => (evenShift g h u : ℂ)))).re -
        atomPairRe (EF.weilTest (fun u => (evenShift g h u : ℂ))
          (fun u => (evenShift g h u : ℂ))) -
        bochnerResolventEnergy (EF.weilTest (fun u => (evenShift g h u : ℂ))
          (fun u => (evenShift g h u : ℂ))) -
        (1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  have h1 := markovCountertermEnergy_evenShift_eq_arch_sub_half_windowSum lam hg hgc hsupp h
  have h2 := markovArchRe_ofReal_add_bochnerResolventEnergy_add_atomPairRe
    (contDiff_evenShift hg h) (hasCompactSupport_evenShift hgc h)
  linarith

end RHTower

end
