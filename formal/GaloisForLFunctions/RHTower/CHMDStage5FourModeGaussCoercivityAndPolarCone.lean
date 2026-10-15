import GaloisForLFunctions.RHTower.CHMDStage1MultiplicativeResolventAndClampedBeam
import GaloisForLFunctions.RHTower.CHMDStage2KleinGordonTransmutationAndTContourBochner
import GaloisForLFunctions.RHTower.CHMDStage4EllipticHyperbolicClosure
import GaloisForLFunctions.RHTower.MarkovOddShiftWindowAndPlasticCrossoverPBAP

/-!
# CHMD Stage 5: Atom-Free 4-Mode Gauss Coercivity, the $\psi(17/4 + ir/2)$ Digamma Shift Identity, and Polar-Cone Lower Bounds

In `LebesgueAtomArchimedeanWeilDensity.lean`, `LebesgueAtomWeilPositivity.lean`, and
`MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean`, a single step of the digamma recurrence
(`half_digamma_add_inv_criticalLine`) shifted `1/4 + ir/2` to `5/4 + ir/2`:
$$\operatorname{EF.gammaBracket}\ r + \frac{1}{1/4 + r^2} = \operatorname{Re}\psi\left(\frac{5}{4} + i\frac{r}{2}\right) - \log \pi.$$
Because $\psi(5/4) - \log \pi \approx -1.372 < 0$ is still negative at $r = 0$, those modules
had to introduce a non-spectral fake atom `2 * cos(r / 10000)` (`atomPairRe k_f`), which destroyed
global $L^2$ coercivity (`(1/100) ∫ |f|² - atomPairRe k_f < 0`).

This module eliminates `atomPairRe` completely by carrying out the **4-mode Gauss extraction and
4-step digamma shift** ($M = 4$, shifting $1/4 + ir/2$ to $17/4 + ir/2$):

1. **Section 1 (3-Mode and 4-Mode Gauss Decompositions of `archLevyDensity` and `jumpEnergy`)**:
   - `archLevyDensity_eq_threeMode` and `archLevyDensity_ge_threeMode`.
   - `m4GaussExtractionGain` (`= 3248 / 585`) and `gammaBracket_zero_add_m4GaussExtractionGain_gt_pos`.
   - `ofReal_fourMode_le_jumpEnergy`: for every bounded compactly supported $h$, `jumpEnergy h` is
     bounded below by $\frac{3248}{585}\int h^2 - \sum_{m=0}^3 \iint h(u)h(v) e^{-(2m+1/2)|u-v|}$.

2. **Section 2 (Atom-Free 4-Mode Gauss Coercive Lower Bounds for `markovArchRe`, `weilArchRe`, and
   `markovCountertermEnergy`)**:
   - `fourMode_gauss_le_markovArchRe` and `forty_two_div_585_l2_le_markovArchRe_add_fourMode_gauss`:
     for **every** signed real test $f \in C^2_c(\mathbb{R})$,
     $$\frac{42}{585}\int_{\mathbb{R}} f(u)^2\,du \le \left(\operatorname{EF.gammaBracket}\ 0 + \frac{3248}{585}\right)\int_{\mathbb{R}} f(u)^2\,du \le \operatorname{markovArchRe}(k_f) + \sum_{m=0}^3 \iint_{\mathbb{R}^2} f(u)f(v) e^{-(2m+1/2)|u-v|}\,du\,dv,$$
     giving a strictly positive $L^2$ coercive lower bound with constant $\frac{42}{585} > \frac{7}{100}$
     and **no `atomPairRe` term at all**.
   - `fourMode_gauss_pole_le_weilArchRe` and `forty_two_div_585_l2_add_fourMode_pole_le_weilArchRe`:
     combining the 4-mode Gauss bound with `2 cosh((u-v)/2)` cancels $e^{-|u-v|/2}$ identically and
     gives for **every** signed real test $f \in C^2_c(\mathbb{R})$:
     $$\frac{42}{585}\int_{\mathbb{R}} f(u)^2\,du + \iint_{\mathbb{R}^2} f(u)f(v) \left(e^{|u-v|/2} - e^{-5|u-v|/2} - e^{-9|u-v|/2} - e^{-13|u-v|/2}\right) du\,dv \le \operatorname{weilArchRe}(k_f).$$
   - `fourMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero`: on the primitive
     hyperplane `coshHalfMoment f = 0` (and on all odd tests), `markovCountertermEnergy lam f`
     gains the bonus square $+ 2 \operatorname{sinhHalfMoment}(f)^2$ on top of the 4-mode bound.

3. **Section 3 (The 4-Mode Shifted Digamma Spectral Density $\rho_4(r) = \operatorname{Re}\psi(17/4 + ir/2) - \log \pi$
   and Global Pointwise Positivity on $\mathbb{R}$)**:
   - `fourModeShiftedArchDensity_eq_re_digamma_seventeen_quarters`: iterating the digamma
     functional equation 4 times on the critical line proves
     $$\rho_4(r) := \operatorname{EF.gammaBracket}\ r + \sum_{m=0}^3 \frac{2(2m+1/2)}{(2m+1/2)^2 + r^2} = \operatorname{Re}\psi\left(\frac{17}{4} + i\frac{r}{2}\right) - \log \pi.$$
   - `fourModeShiftedArchDensity_zero_le`, `forty_two_div_585_lt_fourModeShiftedArchDensity`, and
     `fourModeShiftedArchDensity_pos`: by `digamma_real_le_re_digamma_add_mul_I`, $\rho_4(r)$
     attains its global minimum on $\mathbb{R}$ at $r = 0$, so
     $$\forall r \in \mathbb{R}, \qquad \frac{42}{585} < \operatorname{EF.gammaBracket}\ 0 + \frac{3248}{585} = \rho_4(0) \le \rho_4(r).$$

4. **Section 4 (Atom-Free 4-Mode Sufficiency Criteria for `weilArchRe`, `markovCountertermEnergy`,
   and `RiemannHypothesis`)**:
   - `weilArchRe_nonneg_of_neg_fourMode_pole_le`,
     `markovCountertermEnergy_nonneg_of_fourMode_gauss_add_counterterm_le`,
     `markovPositiveOdd_of_fourMode_gauss_add_counterterm_le`, and
     `riemannHypothesis_of_forall_odd_exists_counterterm_add_fourMode_gauss_le`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ContDiff FourierTransform BigOperators
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.QuantileTransport

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: 3-Mode and 4-Mode Gauss Decompositions of `archLevyDensity` and `jumpEnergy` -/

/-- The 4-mode Gauss $L^2$ extraction gain `4 + 4/5 + 4/9 + 4/13 = 3248 / 585`. -/
def m4GaussExtractionGain : ℝ := 3248 / 585

/-- `EF.gammaBracket 0 + m4GaussExtractionGain > 42 / 585 > 0`. -/
theorem gammaBracket_zero_add_m4GaussExtractionGain_gt_pos :
    (42 : ℝ) / 585 < EF.gammaBracket 0 + m4GaussExtractionGain :=
  CHMDStage1.gammaBracket_zero_add_fourMode_gt

/-- Three-mode Gauss decomposition of `archLevyDensity`:
`ω(x) = e^{-x/2} + e^{-5x/2} + e^{-9x/2} + e^{-6x} ω(x)` for `x ≠ 0`. -/
theorem archLevyDensity_eq_threeMode {x : ℝ} (hx : x ≠ 0) :
    archLevyDensity x =
      Real.exp (-x / 2) + Real.exp (-5 * x / 2) + Real.exp (-9 * x / 2) +
        Real.exp (-6 * x) * archLevyDensity x := by
  have h2 := archLevyDensity_eq_twoMode hx
  have h1 := archLevyDensity_eq_oneMode hx
  have hexp : Real.exp (-4 * x) * Real.exp (-x / 2) = Real.exp (-9 * x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hexp2 : Real.exp (-4 * x) * Real.exp (-2 * x) = Real.exp (-6 * x) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination h2 + Real.exp (-4 * x) * h1 + hexp + archLevyDensity x * hexp2

/-- On `(0, ∞)`, `archLevyDensity` dominates its first three Gauss modes. -/
theorem archLevyDensity_ge_threeMode {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) + Real.exp (-5 * x / 2) + Real.exp (-9 * x / 2) ≤ archLevyDensity x := by
  rw [archLevyDensity_eq_threeMode hx.ne']
  have hpos : 0 ≤ Real.exp (-6 * x) * archLevyDensity x :=
    mul_nonneg (Real.exp_pos _).le (archLevyDensity_pos hx).le
  linarith

/-- **Four-mode pole cancellation**:
`2 cosh(r/2) - (e^{-r/2} + e^{-5r/2} + e^{-9r/2} + e^{-13r/2}) = e^{r/2} - e^{-5r/2} - e^{-9r/2} - e^{-13r/2}`. -/
theorem two_mul_cosh_sub_fourMode (r : ℝ) :
    2 * Real.cosh (r / 2) -
        (Real.exp (-r / 2) + Real.exp (-5 * r / 2) + Real.exp (-9 * r / 2) +
          Real.exp (-13 * r / 2)) =
      Real.exp (r / 2) - Real.exp (-5 * r / 2) - Real.exp (-9 * r / 2) -
        Real.exp (-13 * r / 2) := by
  rw [Real.cosh_eq, show -(r / 2) = -r / 2 by ring]
  ring

/-- The four-mode residual pole kernel
`W_4(r) = e^{r/2} - e^{-5r/2} - e^{-9r/2} - e^{-13r/2}`. -/
def fourModeResidualPoleKernel (r : ℝ) : ℝ :=
  Real.exp (r / 2) - Real.exp (-5 * r / 2) - Real.exp (-9 * r / 2) - Real.exp (-13 * r / 2)

/-- The four-mode Gauss pair sum for a real function `h : ℝ → ℝ`:
`∑_{m=0}^3 ∫∫ h(u) h(v) exp(-(2m + 1/2)|u - v|) du dv`. -/
def fourModeGaussPairSum (h : ℝ → ℝ) : ℝ :=
  (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
    (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
    (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
    (∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|))

/-- **Four-mode Gauss lower bound on `jumpEnergy h` in `ENNReal`**:
for any `BddSupp A h C`,
`ENNReal.ofReal ((3248 / 585) * ∫ h² - fourModeGaussPairSum h) ≤ jumpEnergy h`. -/
theorem ofReal_fourMode_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) :
    ENNReal.ofReal (m4GaussExtractionGain * (∫ u, h u ^ 2) - fourModeGaussPairSum h) ≤
      jumpEnergy h :=
  CHMDStage1.ofReal_fourMode_le_jumpEnergy hh

/-! ## Section 2: Atom-Free 4-Mode Gauss Lower Bounds for `markovArchRe`, `weilArchRe`, and `markovCountertermEnergy` -/

/-- **Pole-Free Four-Mode Gauss Lower Bound for `markovArchRe` (All Signed Real Tests)**:
for every real test `f ∈ C²_c(ℝ)`,
`(EF.gammaBracket 0 + 3248 / 585) * ∫ f² - fourModeGaussPairSum f ≤ markovArchRe k_f`. -/
theorem fourMode_gauss_le_markovArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u : ℝ, f u ^ 2) -
        fourModeGaussPairSum f ≤
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1 := ENNReal.toReal_mono hJ (ofReal_fourMode_le_jumpEnergy hB)
  rw [markovArchRe_ofReal_eq_levy hf hfc]
  rcases le_or_gt 0 (m4GaussExtractionGain * (∫ u, f u ^ 2) - fourModeGaussPairSum f) with ha | ha
  · rw [ENNReal.toReal_ofReal ha] at h1
    linarith
  · have h2 : 0 ≤ (jumpEnergy f).toReal := ENNReal.toReal_nonneg
    linarith

/-- **Strict Atom-Free $L^2$ Coercivity of `markovArchRe` + 4-Mode Gauss Resolvents**:
for every signed real test `f ∈ C²_c(ℝ)`,
`(42 / 585) * ∫ u : ℝ, f u ^ 2 ≤ markovArchRe k_f + fourModeGaussPairSum f`.
This improves the `1 / 100` coercive bound of `MarkovResolventCoercivityAndEulerMaclaurinPBAP`
by more than a factor of 7 (`42 / 585 = 14 / 195 > 7 / 100`) while completely eliminating the
non-spectral fake atom `atomPairRe`. -/
theorem forty_two_div_585_l2_le_markovArchRe_add_fourMode_gauss {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (42 / 585 : ℝ) * (∫ u : ℝ, f u ^ 2) ≤
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) +
        fourModeGaussPairSum f := by
  have h1 := fourMode_gauss_le_markovArchRe hf hfc
  have h2 := gammaBracket_zero_add_m4GaussExtractionGain_gt_pos
  have hsq : 0 ≤ ∫ u : ℝ, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Four-Mode Gauss–Pole Lower Bound for `weilArchRe` (All Signed Real Tests)**:
for every real `C²` compactly supported test `f`,
`(EF.gammaBracket 0 + 3248 / 585) * ∫ f² + ∫∫ f(u) f(v) W_4(|u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem fourMode_gauss_pole_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * fourModeResidualPoleKernel |p.1 - p.2|) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1 := ENNReal.toReal_mono hJ (ofReal_fourMode_le_jumpEnergy hB)
  have h4' : m4GaussExtractionGain * (∫ u, f u ^ 2) - fourModeGaussPairSum f ≤
      (jumpEnergy f).toReal := by
    rcases le_or_gt 0 (m4GaussExtractionGain * (∫ u, f u ^ 2) - fourModeGaussPairSum f) with
      ha | ha
    · rwa [ENNReal.toReal_ofReal ha] at h1
    · exact ha.le.trans ENNReal.toReal_nonneg
  have hcs_cosh : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1' | h2'
    · rw [image_eq_zero_of_notMem_tsupport h1']; ring
    · rw [image_eq_zero_of_notMem_tsupport h2']; ring
  have hI_cosh : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hcs_cosh
  have hI1 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI2 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI3 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI4 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI12 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) +
        f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|) := hI1.add hI2
  have hI123 : Integrable fun p : ℝ × ℝ =>
      (f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) +
        f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
        f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|) := hI12.add hI3
  have hI1234 : Integrable fun p : ℝ × ℝ =>
      ((f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) +
        f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) +
        f p.1 * f p.2 * Real.exp (-(9 / 2) * |p.1 - p.2|)) +
        f p.1 * f p.2 * Real.exp (-(13 / 2) * |p.1 - p.2|) := hI123.add hI4
  have hcomb : 2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
      fourModeGaussPairSum f =
      ∫ p : ℝ × ℝ, f p.1 * f p.2 * fourModeResidualPoleKernel |p.1 - p.2| := by
    unfold fourModeGaussPairSum
    rw [← integral_add hI1 hI2, ← integral_add hI12 hI3, ← integral_add hI123 hI4,
      ← integral_const_mul, ← integral_sub (hI_cosh.const_mul 2) hI1234]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [fourModeResidualPoleKernel]
    have hca : Real.cosh ((p.1 - p.2) / 2) = Real.cosh (|p.1 - p.2| / 2) := by
      rw [← Real.cosh_abs, abs_div, abs_two]
    have hlin := two_mul_cosh_sub_fourMode |p.1 - p.2|
    rw [hca,
      show -(1 / 2 : ℝ) * |p.1 - p.2| = -|p.1 - p.2| / 2 by ring,
      show -(5 / 2 : ℝ) * |p.1 - p.2| = -5 * |p.1 - p.2| / 2 by ring,
      show -(9 / 2 : ℝ) * |p.1 - p.2| = -9 * |p.1 - p.2| / 2 by ring,
      show -(13 / 2 : ℝ) * |p.1 - p.2| = -13 * |p.1 - p.2| / 2 by ring]
    linear_combination f p.1 * f p.2 * hlin
  rw [weilArchRe_eq_levy_pole hf hfc]
  change _ ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + (jumpEnergy f).toReal +
    2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  linarith

/-- **Rational 4-Mode Gauss–Pole Coercive Lower Bound for `weilArchRe`**:
for every real `C²` compactly supported test `f`,
`(42 / 585) * ∫ f² + ∫∫ f(u) f(v) W_4(|u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem forty_two_div_585_l2_add_fourMode_pole_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (42 / 585 : ℝ) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * fourModeResidualPoleKernel |p.1 - p.2|) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have h1 := fourMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := gammaBracket_zero_add_m4GaussExtractionGain_gt_pos
  have hsq : 0 ≤ ∫ u : ℝ, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Four-Mode Gauss–Pole + Sinh-Square Lower Bound for `markovCountertermEnergy` on the Primitive
Hyperplane**:
for any `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (in particular any odd test) and any counterterm
`lam : ℕ → ℝ`,
`(EF.gammaBracket 0 + 3248 / 585) * ∫ f² + 2 * sinhHalfMoment f ^ 2 + ∫∫ f(u) f(v) W_4(|u - v|) du dv - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f`. -/
theorem fourMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u : ℝ, f u ^ 2) +
        2 * sinhHalfMoment f ^ 2 +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * fourModeResidualPoleKernel |p.1 - p.2|) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := fourMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero hf.continuous hfc hcosh
  have h3 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-- **Rational 4-Mode Coercive Lower Bound for `markovCountertermEnergy` on all Signed Real Tests**:
for every `f ∈ C²_c(ℝ)` and every counterterm sequence `lam : ℕ → ℝ`,
`(42 / 585) * ∫ f² - fourModeGaussPairSum f - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f`. -/
theorem forty_two_div_585_l2_sub_fourMode_gauss_sub_counterterm_le_markovCountertermEnergy
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (42 / 585 : ℝ) * (∫ u : ℝ, f u ^ 2) - fourModeGaussPairSum f -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := forty_two_div_585_l2_le_markovArchRe_add_fourMode_gauss hf hfc
  have h2 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-! ## Section 3: The 4-Mode Shifted Digamma Spectral Density $\rho_4(r) = \operatorname{Re}\psi(17/4 + ir/2) - \log \pi$ and Global Pointwise Positivity on $\mathbb{R}$ -/

/-- The **4-mode shifted archimedean spectral density** on the critical line:
`ρ_4(r) = EF.gammaBracket r + 1 / (1 / 4 + r²) + 5 / (25 / 4 + r²) + 9 / (81 / 4 + r²) + 13 / (169 / 4 + r²)`. -/
def fourModeShiftedArchDensity (r : ℝ) : ℝ :=
  EF.gammaBracket r + 1 / (1 / 4 + r ^ 2) + 5 / (25 / 4 + r ^ 2) +
    9 / (81 / 4 + r ^ 2) + 13 / (169 / 4 + r ^ 2)

/-- At `r = 0`, `fourModeShiftedArchDensity 0 = EF.gammaBracket 0 + 3248 / 585`. -/
theorem fourModeShiftedArchDensity_zero :
    fourModeShiftedArchDensity 0 = EF.gammaBracket 0 + m4GaussExtractionGain := by
  unfold fourModeShiftedArchDensity m4GaussExtractionGain
  ring

/-- Single-step digamma shift identity for the real part on a vertical line `a + i r / 2` (`a > 0`):
`Re ψ(a + 1 + i r / 2) = Re ψ(a + i r / 2) + 4a / (4a² + r²)`. -/
theorem re_digamma_add_one_add_half_mul_I {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (Complex.digamma (((a + 1 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re =
      (Complex.digamma ((a : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re +
        (4 * a) / (4 * a ^ 2 + r ^ 2) := by
  set w : ℂ := (a : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hw
  have hwre : w.re = a := by simp [hw]
  have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    rw [hwre] at hre
    simp at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one w hne
  have hshift : (((a + 1 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I) = w + 1 := by
    rw [hw]; push_cast; ring
  have hinv : (w⁻¹).re = (4 * a) / (4 * a ^ 2 + r ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [hw, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one, add_zero, zero_add]
    have hpos1 : 0 < a * a + r / 2 * (r / 2) :=
      add_pos_of_pos_of_nonneg (mul_pos ha ha) (mul_self_nonneg (r / 2))
    have hden : a * a + r / 2 * (r / 2) ≠ 0 := hpos1.ne'
    have hden2 : 4 * a ^ 2 + r ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hshift, hrec, Complex.add_re, hinv]

/-- **Exact 4-Step Digamma Shift Identity on the Critical Line**:
for every `r : ℝ`, adding the first four Gauss resolvent modes to `EF.gammaBracket r` shifts the
digamma argument from `1/4 + ir/2` to `17/4 + ir/2`:
`fourModeShiftedArchDensity r = Re ψ(17/4 + ir/2) - log π`. -/
theorem fourModeShiftedArchDensity_eq_re_digamma_seventeen_quarters (r : ℝ) :
    fourModeShiftedArchDensity r =
      (Complex.digamma (((17 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re - Real.log Real.pi := by
  have h0 := WeilHerglotz.gammaBracket_eq r
  have s1 := re_digamma_add_one_add_half_mul_I (a := 1 / 4) (by norm_num) r
  have s2 := re_digamma_add_one_add_half_mul_I (a := 5 / 4) (by norm_num) r
  have s3 := re_digamma_add_one_add_half_mul_I (a := 9 / 4) (by norm_num) r
  have s4 := re_digamma_add_one_add_half_mul_I (a := 13 / 4) (by norm_num) r
  rw [show (1 / 4 + 1 : ℝ) = 5 / 4 by norm_num,
    show (4 * (1 / 4 : ℝ)) / (4 * (1 / 4 : ℝ) ^ 2 + r ^ 2) = 1 / (1 / 4 + r ^ 2) by ring] at s1
  rw [show (5 / 4 + 1 : ℝ) = 9 / 4 by norm_num,
    show (4 * (5 / 4 : ℝ)) / (4 * (5 / 4 : ℝ) ^ 2 + r ^ 2) = 5 / (25 / 4 + r ^ 2) by ring] at s2
  rw [show (9 / 4 + 1 : ℝ) = 13 / 4 by norm_num,
    show (4 * (9 / 4 : ℝ)) / (4 * (9 / 4 : ℝ) ^ 2 + r ^ 2) = 9 / (81 / 4 + r ^ 2) by ring] at s3
  rw [show (13 / 4 + 1 : ℝ) = 17 / 4 by norm_num,
    show (4 * (13 / 4 : ℝ)) / (4 * (13 / 4 : ℝ) ^ 2 + r ^ 2) = 13 / (169 / 4 + r ^ 2) by ring] at s4
  unfold fourModeShiftedArchDensity
  linarith

/-- Closed-form evaluation of `Re ψ(17/4) - log π`:
`(Complex.digamma (17 / 4 : ℂ)).re - Real.log Real.pi = EF.gammaBracket 0 + 3248 / 585`. -/
theorem re_digamma_seventeen_quarters_sub_log_pi_eq :
    (Complex.digamma ((17 / 4 : ℝ) : ℂ)).re - Real.log Real.pi =
      EF.gammaBracket 0 + m4GaussExtractionGain := by
  have h := fourModeShiftedArchDensity_eq_re_digamma_seventeen_quarters 0
  rw [fourModeShiftedArchDensity_zero,
    show ((0 / 2 : ℝ) : ℂ) * I = 0 by push_cast; ring, add_zero] at h
  exact h.symm

/-- **Global Minimum of `fourModeShiftedArchDensity` at `r = 0`**:
for every `r : ℝ`, `fourModeShiftedArchDensity 0 ≤ fourModeShiftedArchDensity r`. -/
theorem fourModeShiftedArchDensity_zero_le (r : ℝ) :
    fourModeShiftedArchDensity 0 ≤ fourModeShiftedArchDensity r := by
  rw [fourModeShiftedArchDensity_zero, ← re_digamma_seventeen_quarters_sub_log_pi_eq,
    fourModeShiftedArchDensity_eq_re_digamma_seventeen_quarters]
  have hmin := digamma_real_le_re_digamma_add_mul_I (a := 17 / 4) (by norm_num) (r / 2)
  linarith

/-- **Global Pointwise Lower Bound `42 / 585 < fourModeShiftedArchDensity r` on `ℝ` (Without Atoms!)**:
for every `r : ℝ`, `42 / 585 < fourModeShiftedArchDensity r`. -/
theorem forty_two_div_585_lt_fourModeShiftedArchDensity (r : ℝ) :
    (42 : ℝ) / 585 < fourModeShiftedArchDensity r := by
  calc (42 : ℝ) / 585 < EF.gammaBracket 0 + m4GaussExtractionGain :=
        gammaBracket_zero_add_m4GaussExtractionGain_gt_pos
    _ = fourModeShiftedArchDensity 0 := fourModeShiftedArchDensity_zero.symm
    _ ≤ fourModeShiftedArchDensity r := fourModeShiftedArchDensity_zero_le r

/-- Every value of `fourModeShiftedArchDensity` on `ℝ` is strictly positive. -/
theorem fourModeShiftedArchDensity_pos (r : ℝ) :
    0 < fourModeShiftedArchDensity r :=
  lt_trans (by norm_num) (forty_two_div_585_lt_fourModeShiftedArchDensity r)

/-! ## Section 4: Atom-Free 4-Mode Sufficiency Criteria for `weilArchRe`, `markovCountertermEnergy`, and `RiemannHypothesis` -/

/-- **Atom-Free 4-Mode Sufficiency Criterion for `weilArchRe` Nonnegativity**:
if a real test `f ∈ C²_c(ℝ)` satisfies
`-∫∫ f(u) f(v) W_4(|u - v|) du dv ≤ (EF.gammaBracket 0 + 3248 / 585) * ∫ f²`
(in particular whenever `-∫∫ f(u) f(v) W_4(|u - v|) du dv ≤ (42 / 585) * ∫ f²`), then
`0 ≤ weilArchRe (EF.weilTest f f)` holds unconditionally. -/
theorem weilArchRe_nonneg_of_neg_fourMode_pole_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (h : -(∫ p : ℝ × ℝ, f p.1 * f p.2 * fourModeResidualPoleKernel |p.1 - p.2|) ≤
      (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u, f u ^ 2)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := fourMode_gauss_pole_le_weilArchRe hf hfc
  linarith

/-- **Atom-Free 4-Mode Sufficiency Criterion for `markovCountertermEnergy` Nonnegativity**:
if a real test `f ∈ C²_c(ℝ)` satisfies
`fourModeGaussPairSum f + primeBlindCounterterm lam f ≤ (EF.gammaBracket 0 + 3248 / 585) * ∫ f²`
(in particular whenever `≤ (42 / 585) * ∫ f²`), then `0 ≤ markovCountertermEnergy lam f`. -/
theorem markovCountertermEnergy_nonneg_of_fourMode_gauss_add_counterterm_le
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (h : fourModeGaussPairSum f + primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u : ℝ, f u ^ 2)) :
    0 ≤ markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := fourMode_gauss_le_markovArchRe hf hfc
  have h2 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-- **Odd-Sector Markov Positivity from Atom-Free 4-Mode Gauss + Coercive Domination**:
if for every odd real test `f ∈ C²_c(ℝ)`,
`fourModeGaussPairSum f + primeBlindCounterterm lam f ≤ (EF.gammaBracket 0 + 3248 / 585) * ∫ f²`,
then `MarkovPositiveOdd lam` holds. -/
theorem markovPositiveOdd_of_fourMode_gauss_add_counterterm_le {lam : ℕ → ℝ}
    (hdom : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      fourModeGaussPairSum f + primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
        (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u : ℝ, f u ^ 2)) :
    MarkovPositiveOdd lam := by
  intro f hf hfc hodd
  exact markovCountertermEnergy_nonneg_of_fourMode_gauss_add_counterterm_le
    lam hf hfc (hdom f hf hfc hodd)

/-- **Unconditional `RiemannHypothesis` from Odd-Sector Atom-Free 4-Mode Coercive Domination**:
if for every odd real test `f ∈ C²_c(ℝ)` there exists `lam : ℕ → ℝ` with
`primeBlindCounterterm Λ f ≤ primeBlindCounterterm lam f` and
`fourModeGaussPairSum f + primeBlindCounterterm lam f ≤ (EF.gammaBracket 0 + 3248 / 585) * ∫ f²`
(without any `atomPairRe` term!), then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_odd_exists_counterterm_add_fourMode_gauss_le
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ lam : ℕ → ℝ,
        fourModeGaussPairSum f + primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
          (EF.gammaBracket 0 + m4GaussExtractionGain) * (∫ u : ℝ, f u ^ 2) ∧
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn f hf hfc) ≤
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_odd_exists_counterterm_markov_nonneg fun f hf hfc hodd => ?_
  obtain ⟨lam, hdom, hle⟩ := h f hf hfc hodd
  exact ⟨lam,
    markovCountertermEnergy_nonneg_of_fourMode_gauss_add_counterterm_le lam hf hfc hdom,
    hle⟩

end RHTower

end
