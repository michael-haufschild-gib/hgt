import GaloisForLFunctions.RHTower.CHMDStage16ZeroSideSymmetriesAndXiConvolutionAnnihilation
import GaloisForLFunctions.RHTower.CHMDGrowthPositivityCollapseAndTwoPointCriterion
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Exact pole-free CHMD packets on one Xi symmetry orbit

Removing the full analytic multiplicity of a selected Xi zero gives a nonzero cardinal
quotient. A bounded rational filter cancels both poles, and even Schwarz symmetrization
produces an admissible test whose divisor values are imaginary signed orbit indicators.
Consequently its complete Weil energy is the negative sum of multiplicity-weighted
orbit-indicator squares, with no contribution from any other zero.

The same energy is an exact sech-kernel integral against the original CHMD causal wave
and an exact pole-free prime–archimedean expression. It is strictly negative exactly when
the selected zero is off the critical line, without a simplicity assumption. These identities
do not establish nonnegativity of the arithmetic expression or prove RH.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower.CHMDExactPackets
open WeilSpectral EvenSector CHMDStage3 CHMDStage14 CHMDStage15 CHMDStage16

/-- The divided quotient at the full analytic multiplicity of the selected zero. -/
def terminalQuotient (ρ : XiDivisorSupport) : ℂ → ℂ :=
  xiThetaDividedChain (xiSpectralPointSupport ρ) (xiSupportMultiplicity ρ)

theorem terminalQuotient_ne_zero (ρ : XiDivisorSupport) :
    terminalQuotient ρ (xiSpectralPointSupport ρ) ≠ 0 :=
  xiThetaDividedChain_nonzero_at_multiplicity ρ

theorem terminalQuotient_analytic (ρ : XiDivisorSupport) (z : ℂ) :
    AnalyticAt ℂ (terminalQuotient ρ) z :=
  xiThetaDividedChain_analyticAt _ _ _

theorem terminalQuotient_zero (ρ : XiDivisorSupport) {z : ℂ}
    (hz : XiC z = 0) (hne : z ≠ xiSpectralPointSupport ρ) :
    terminalQuotient ρ z = 0 := by
  have h := xiThetaDividedChain_factorization ρ z
  rw [hz] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hne))

theorem terminalQuotient_strip (ρ : XiDivisorSupport) :
    ∃ C : ℝ, StripDecay (terminalQuotient ρ) (9 / 4) (3 / 4) C := by
  obtain ⟨C₀, hC₀, hXi⟩ := exists_norm_XiC_horizontal_le_wide
    (A := 9 / 4) (δ := 3 / 4) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_d2])
  let a := xiSpectralPointSupport ρ
  let R := ‖a‖ + 1
  have hc : Continuous (terminalQuotient ρ) :=
    continuous_iff_continuousAt.mpr fun z => (terminalQuotient_analytic ρ z).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_reIm_box R (9 / 4)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C₀ (M * Real.exp (3 / 4 * R)),
    ⟨fun z _ => (terminalQuotient_analytic ρ z).differentiableAt, fun z hz => ?_⟩⟩
  rcases le_or_gt |z.re| R with hsmall | hlarge
  · have hle : ‖terminalQuotient ρ z‖ ≤ M := hM z ⟨hsmall, hz⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hle
    have he : Real.exp (-(3 / 4 * R)) ≤ Real.exp (-(3 / 4 * |z.re|)) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc ‖terminalQuotient ρ z‖ ≤ M := hle
      _ = M * Real.exp (3 / 4 * R) * Real.exp (-(3 / 4 * R)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (3 / 4 * R) * Real.exp (-(3 / 4 * |z.re|)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  · have hden : 1 ≤ ‖z - a‖ := by
      have hnorm := Complex.abs_re_le_norm z
      have hdiff := norm_sub_norm_le z a
      dsimp [R] at hlarge
      linarith
    have hp : 1 ≤ ‖z - a‖ ^ xiSupportMultiplicity ρ := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hden
        (xiSupportMultiplicity ρ)
    have hfactor := congrArg norm (xiThetaDividedChain_factorization ρ z)
    simp only [norm_mul, norm_pow] at hfactor
    have hq : ‖terminalQuotient ρ z‖ ≤ ‖XiC z‖ := by
      change ‖XiC z‖ = ‖z - a‖ ^ xiSupportMultiplicity ρ * ‖terminalQuotient ρ z‖ at hfactor
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (norm_nonneg (terminalQuotient ρ z))]
    have hXi' := hXi z.re z.im hz
    rw [Complex.re_add_im] at hXi'
    exact hq.trans (hXi'.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)))

/-- A rational polar notch with singularities outside the CHMD multiplier strip. -/
def poleFilter (z : ℂ) : ℂ := (z ^ 2 + 1 / 4) / (z ^ 2 + 9)

theorem poleDen_re (z : ℂ) (hz : |z.im| ≤ 9 / 4) : 3 ≤ (z ^ 2 + 9).re := by
  have hsq : z.im ^ 2 ≤ (9 / 4 : ℝ) ^ 2 := by
    nlinarith [abs_nonneg z.im, sq_abs z.im]
  simp only [sq, Complex.add_re, Complex.mul_re]
  norm_num
  nlinarith [sq_nonneg z.re]

theorem poleDen_ne_zero (z : ℂ) (hz : |z.im| ≤ 9 / 4) : z ^ 2 + 9 ≠ 0 := by
  intro h
  have hh := poleDen_re z hz
  rw [h, Complex.zero_re] at hh
  norm_num at hh

theorem poleFilter_diff (z : ℂ) (hz : |z.im| ≤ 9 / 4) :
    DifferentiableAt ℂ poleFilter z :=
  ((differentiableAt_id.pow 2).add_const _).div
    ((differentiableAt_id.pow 2).add_const _) (poleDen_ne_zero z hz)

theorem poleFilter_bound (z : ℂ) (hz : |z.im| ≤ 9 / 4) : ‖poleFilter z‖ ≤ 4 := by
  have hd : 3 ≤ ‖z ^ 2 + 9‖ := (poleDen_re z hz).trans (Complex.re_le_norm _)
  have he : poleFilter z = 1 - (35 / 4 : ℂ) / (z ^ 2 + 9) := by
    unfold poleFilter
    field_simp [poleDen_ne_zero z hz]
    ring
  rw [he]
  calc ‖1 - (35 / 4 : ℂ) / (z ^ 2 + 9)‖ ≤
      ‖(1 : ℂ)‖ + ‖(35 / 4 : ℂ) / (z ^ 2 + 9)‖ := norm_sub_le _ _
    _ = 1 + (35 / 4 : ℝ) / ‖z ^ 2 + 9‖ := by norm_num [norm_div]
    _ ≤ 4 := by
      have : (35 / 4 : ℝ) / ‖z ^ 2 + 9‖ ≤ 3 :=
        (div_le_iff₀ (by linarith)).mpr (by linarith)
      linarith

theorem poleFilter_ne_zero {z : ℂ} (hz : |z.im| < 1 / 2) : poleFilter z ≠ 0 := by
  have hnum : 0 < (z ^ 2 + 1 / 4).re := by
    have hsq : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.div_ofNat_re, Complex.one_re]
    nlinarith [sq_nonneg z.re]
  have hne : z ^ 2 + 1 / 4 ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hnum
    exact (lt_irrefl _ hnum)
  exact div_ne_zero hne (poleDen_ne_zero z (by linarith))

@[simp] theorem poleFilter_upper : poleFilter (I / 2) = 0 := by
  norm_num [poleFilter, div_pow, Complex.I_sq]

@[simp] theorem poleFilter_lower : poleFilter (-I / 2) = 0 := by
  norm_num [poleFilter, div_pow, Complex.I_sq]

/-- The normalized, pole-free quotient, equal to one on its selected divisor fiber. -/
def cardinal (ρ : XiDivisorSupport) (z : ℂ) : ℂ :=
  poleFilter z * terminalQuotient ρ z /
    (poleFilter (xiSpectralPointSupport ρ) * terminalQuotient ρ (xiSpectralPointSupport ρ))

theorem cardinal_eval (ρ : XiDivisorSupport)
    (ha : |(xiSpectralPointSupport ρ).im| < 1 / 2) {z : ℂ} (hz : XiC z = 0) :
    cardinal ρ z = if z = xiSpectralPointSupport ρ then 1 else 0 := by
  by_cases he : z = xiSpectralPointSupport ρ
  · subst z
    simp [cardinal, poleFilter_ne_zero ha, terminalQuotient_ne_zero]
  · simp [cardinal, terminalQuotient_zero ρ hz he, he]

theorem cardinal_strip (ρ : XiDivisorSupport) :
    ∃ C : ℝ, StripDecay (cardinal ρ) (9 / 4) (3 / 4) C := by
  obtain ⟨C, hC⟩ := terminalQuotient_strip ρ
  refine ⟨4 * C / ‖poleFilter (xiSpectralPointSupport ρ) *
    terminalQuotient ρ (xiSpectralPointSupport ρ)‖, ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · exact ((poleFilter_diff z hz).mul (hC.diff z hz)).div_const _
  · unfold cardinal
    rw [norm_div, norm_mul]
    calc ‖poleFilter z‖ * ‖terminalQuotient ρ z‖ /
        ‖poleFilter (xiSpectralPointSupport ρ) * terminalQuotient ρ (xiSpectralPointSupport ρ)‖
        ≤ (4 * (C * Real.exp (-(3 / 4 * |z.re|)))) /
          ‖poleFilter (xiSpectralPointSupport ρ) * terminalQuotient ρ (xiSpectralPointSupport ρ)‖ := by
          gcongr
          · exact poleFilter_bound z hz
          · exact hC.bound z hz
      _ = _ := by ring

/-- Even Schwarz symmetrization with imaginary signed values on the selected orbit. -/
def selector (ρ : XiDivisorSupport) (z : ℂ) : ℂ :=
  I * (cardinal ρ z + cardinal ρ (-z) -
    conj (cardinal ρ (conj z) + cardinal ρ (-conj z)))

theorem selector_even (ρ : XiDivisorSupport) (z : ℂ) : selector ρ (-z) = selector ρ z := by
  simp only [selector, neg_neg, map_neg, map_add]
  ring

theorem selector_conj (ρ : XiDivisorSupport) (z : ℂ) :
    selector ρ (conj z) = conj (selector ρ z) := by
  simp only [selector, map_mul, map_sub, map_add, conj_I, conj_conj]
  ring

theorem selector_strip (ρ : XiDivisorSupport) :
    ∃ C : ℝ, StripDecay (selector ρ) (9 / 4) (3 / 4) C := by
  obtain ⟨C, hs⟩ := cardinal_strip ρ
  refine ⟨4 * C, ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · have h1 : DifferentiableAt ℂ (fun w => cardinal ρ w + cardinal ρ (-w)) z :=
      (hs.diff z hz).add ((hs.diff (-z) (by simpa using hz)).comp z differentiableAt_id.neg)
    have h2 : DifferentiableAt ℂ (fun w => cardinal ρ w + cardinal ρ (-w)) (conj z) :=
      (hs.diff (conj z) (by simpa using hz)).add
        ((hs.diff (-conj z) (by simpa using hz)).comp (conj z) differentiableAt_id.neg)
    have h3 : DifferentiableAt ℂ
        (fun w => conj (cardinal ρ (conj w) + cardinal ρ (-conj w))) z := by
      simpa only [Function.comp_def, conj_conj] using h2.conj_conj
    exact (h1.sub h3).const_mul I
  · have h1 := hs.bound z hz
    have h2 := hs.bound (-z) (by simpa using hz)
    have h3 := hs.bound (conj z) (by simpa using hz)
    have h4 := hs.bound (-conj z) (by simpa using hz)
    simp only [Complex.neg_re, Complex.conj_re, abs_neg] at h2 h3 h4
    simp only [selector, norm_mul, norm_I, one_mul]
    calc ‖cardinal ρ z + cardinal ρ (-z) -
          conj (cardinal ρ (conj z) + cardinal ρ (-conj z))‖
        ≤ ‖cardinal ρ z + cardinal ρ (-z)‖ +
          ‖conj (cardinal ρ (conj z) + cardinal ρ (-conj z))‖ := norm_sub_le _ _
      _ ≤ (‖cardinal ρ z‖ + ‖cardinal ρ (-z)‖) +
          (‖cardinal ρ (conj z)‖ + ‖cardinal ρ (-conj z)‖) := by
            rw [norm_conj]
            exact add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ _ := by linarith

theorem selector_evenStrip (ρ : XiDivisorSupport) : EvenStrip (selector ρ) := by
  obtain ⟨C, hs⟩ := selector_strip ρ
  refine ⟨⟨3 / 4, C, by norm_num,
    ⟨fun z hz => hs.diff z (by linarith), fun z hz => hs.bound z (by linarith)⟩⟩,
    selector_even ρ, fun r => ?_⟩
  have h := selector_conj ρ (r : ℂ)
  rw [conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem selector_multiplier (ρ : XiDivisorSupport) : Multiplier (sechWeight (selector ρ)) := by
  obtain ⟨C, hs⟩ := selector_strip ρ
  exact multiplier_sechWeight (by norm_num) hs (specSq_neg_of_even (selector_even ρ))

@[simp] theorem cardinal_upper (ρ : XiDivisorSupport) : cardinal ρ (I / 2) = 0 := by
  simp [cardinal]

@[simp] theorem cardinal_lower (ρ : XiDivisorSupport) : cardinal ρ (-I / 2) = 0 := by
  simp [cardinal]

theorem selector_upper (ρ : XiDivisorSupport) : selector ρ (I / 2) = 0 := by
  have hc : conj (I / 2 : ℂ) = -I / 2 := by simp only [map_div₀, conj_I, map_ofNat]
  have hn : -(I / 2 : ℂ) = -I / 2 := by ring
  have hnn : -(-I / 2 : ℂ) = I / 2 := by ring
  simp [selector, hc, hn, hnn]

theorem selector_lower (ρ : XiDivisorSupport) : selector ρ (-I / 2) = 0 := by
  rw [show (-I / 2 : ℂ) = -(I / 2) by ring, selector_even, selector_upper]

/-- Signed indicator of the reflection and conjugation orbit, with collisions retained. -/
def orbitSign (a z : ℂ) : ℝ :=
  (if z = a then 1 else 0) + (if -z = a then 1 else 0) -
    ((if conj z = a then 1 else 0) + (if -conj z = a then 1 else 0))

theorem selector_eval (ρ : XiDivisorSupport)
    (ha : |(xiSpectralPointSupport ρ).im| < 1 / 2) {z : ℂ} (hz : XiC z = 0) :
    selector ρ z = I * (orbitSign (xiSpectralPointSupport ρ) z : ℂ) := by
  have hn : XiC (-z) = 0 := by rw [XiC_even, hz]
  have hc : XiC (conj z) = 0 := by rw [XiC_conj, hz, map_zero]
  have hnc : XiC (-conj z) = 0 := by rw [XiC_even, hc]
  unfold selector orbitSign
  rw [cardinal_eval ρ ha hz, cardinal_eval ρ ha hn, cardinal_eval ρ ha hc,
    cardinal_eval ρ ha hnc]
  split_ifs <;> norm_num [map_ofNat]

theorem selector_specSq_re (ρ : XiDivisorSupport)
    (ha : |(xiSpectralPointSupport ρ).im| < 1 / 2) {z : ℂ} (hz : XiC z = 0) :
    (specSq (selector ρ) z).re = -(orbitSign (xiSpectralPointSupport ρ) z) ^ 2 := by
  unfold specSq
  rw [selector_conj, conj_conj, selector_eval ρ ha hz]
  simp [Complex.mul_re, Complex.mul_im, sq]

theorem orbitSign_self {a : ℂ} (hre : a.re ≠ 0) (him : a.im ≠ 0) : orbitSign a a = 1 := by
  have hn : -a ≠ a := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.neg_re] at hh
    exact hre (by linarith)
  have hc : conj a ≠ a := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.conj_im] at hh
    exact him (by linarith)
  have hnc : -conj a ≠ a := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hh
    exact hre (by linarith)
  simp [orbitSign, hn, hc, hnc]

theorem orbitSign_eq_zero_of_im_eq_zero {a : ℂ} (ha : a.im = 0) (z : ℂ) :
    orbitSign a z = 0 := by
  have hca : conj a = a := Complex.conj_eq_iff_im.mpr ha
  have h1 : conj z = a ↔ z = a := by
    constructor
    · intro h
      have hh := congrArg conj h
      simpa only [conj_conj, hca] using hh
    · rintro rfl
      exact hca
  have h2 : -conj z = a ↔ -z = a := by
    constructor
    · intro h
      have hh := congrArg conj h
      simpa only [map_neg, conj_conj, hca] using hh
    · intro h
      have hh := congrArg conj h
      simpa only [map_neg, hca] using hh
  simp only [orbitSign, h1, h2, sub_self]


def zeroSupport (ρ : zetaZeroConfig.carrier) : XiDivisorSupport :=
  (Classical.choose ((XiC_eq_zero_iff_exists_xiZeroCopy (gammaOf ρ)).mp
    (XiC_gammaOf_eq_zero ρ))).1

theorem zeroSupport_coordinate (ρ : zetaZeroConfig.carrier) :
    xiSpectralPointSupport (zeroSupport ρ) = gammaOf ρ := by
  have h := Classical.choose_spec ((XiC_eq_zero_iff_exists_xiZeroCopy (gammaOf ρ)).mp
    (XiC_gammaOf_eq_zero ρ))
  simpa only [xiSpectralPoint_eq_support, zeroSupport] using h

/-- The exact pole-free CHMD selector attached to an actual nontrivial zeta zero. -/
def zeroSelector (ρ : zetaZeroConfig.carrier) : ℂ → ℂ := selector (zeroSupport ρ)

theorem zeroSelector_evenStrip (ρ : zetaZeroConfig.carrier) : EvenStrip (zeroSelector ρ) :=
  selector_evenStrip _

theorem zeroSelector_multiplier (ρ : zetaZeroConfig.carrier) :
    Multiplier (sechWeight (zeroSelector ρ)) := selector_multiplier _

theorem zeroSelector_pole_zero (ρ : zetaZeroConfig.carrier) :
    zeroSelector ρ (I / 2) = 0 ∧ zeroSelector ρ (-I / 2) = 0 :=
  ⟨selector_upper _, selector_lower _⟩

/-- Every divisor value is explicit, including all multiplicities and orbit collisions. -/
theorem zeroSelector_zero_values (ρ σ : zetaZeroConfig.carrier) :
    zeroSelector ρ (gammaOf σ) = I * (orbitSign (gammaOf ρ) (gammaOf σ) : ℂ) := by
  have ha : |(xiSpectralPointSupport (zeroSupport ρ)).im| < 1 / 2 := by
    rw [zeroSupport_coordinate]
    exact CHMDGrowthCollapse.abs_im_gammaOf_lt ρ
  simpa only [zeroSelector, zeroSupport_coordinate] using
    selector_eval (zeroSupport ρ) ha (XiC_gammaOf_eq_zero σ)

theorem zeroSelector_specSq_re (ρ σ : zetaZeroConfig.carrier) :
    (specSq (zeroSelector ρ) (gammaOf σ)).re = -(orbitSign (gammaOf ρ) (gammaOf σ)) ^ 2 := by
  have ha : |(xiSpectralPointSupport (zeroSupport ρ)).im| < 1 / 2 := by
    rw [zeroSupport_coordinate]
    exact CHMDGrowthCollapse.abs_im_gammaOf_lt ρ
  simpa only [zeroSelector, zeroSupport_coordinate] using
    selector_specSq_re (zeroSupport ρ) ha (XiC_gammaOf_eq_zero σ)

/-- Every zero outside the selected symmetry orbit is annihilated exactly. -/
theorem zeroSelector_eq_zero_outside_orbit (ρ σ : zetaZeroConfig.carrier)
    (h₁ : gammaOf σ ≠ gammaOf ρ) (h₂ : -gammaOf σ ≠ gammaOf ρ)
    (h₃ : conj (gammaOf σ) ≠ gammaOf ρ) (h₄ : -conj (gammaOf σ) ≠ gammaOf ρ) :
    zeroSelector ρ (gammaOf σ) = 0 := by
  rw [zeroSelector_zero_values]
  simp [orbitSign, h₁, h₂, h₃, h₄]

/-- The full arithmetic Weil energy of the selected packet. -/
def zeroSelectorEnergy (ρ : zetaZeroConfig.carrier) : ℝ :=
  evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq (zeroSelector ρ))

/-- Exact full-energy identity: the negative multiplicity-weighted orbit mass, without a tail. -/
theorem zeroSelectorEnergy_eq (ρ : zetaZeroConfig.carrier) :
    zeroSelectorEnergy ρ = -∑' σ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult σ : ℝ) * orbitSign (gammaOf ρ) (gammaOf σ) ^ 2 := by
  rw [zeroSelectorEnergy, evenWeilDensity_specSq_vonMangoldt_eq_tsum_re (zeroSelector_evenStrip ρ),
    ← tsum_neg]
  apply tsum_congr
  intro σ
  rw [zeroSelector_specSq_re]
  ring

theorem zeroSelectorEnergy_nonpos (ρ : zetaZeroConfig.carrier) : zeroSelectorEnergy ρ ≤ 0 := by
  rw [zeroSelectorEnergy_eq]
  exact neg_nonpos.mpr (tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem zeroSelectorEnergy_eq_zero_of_criticalLine (ρ : zetaZeroConfig.carrier)
    (hρ : (ρ : ℂ).re = 1 / 2) : zeroSelectorEnergy ρ = 0 := by
  have hi : (gammaOf ρ).im = 0 := by rw [WeilEF.gammaOf_im, hρ]; ring
  rw [zeroSelectorEnergy_eq]
  simp only [orbitSign_eq_zero_of_im_eq_zero hi, zero_pow (by decide : 2 ≠ 0), mul_zero,
    tsum_zero, neg_zero]

theorem gammaOf_re_ne_zero (ρ : zetaZeroConfig.carrier) : (gammaOf ρ).re ≠ 0 := by
  intro h
  have hform : gammaOf ρ = ((gammaOf ρ).im : ℂ) * I := by
    apply Complex.ext <;> simp [h]
  have hz := XiC_gammaOf_eq_zero ρ
  rw [hform] at hz
  exact XiC_ne_zero_of_imaginary _ hz

/-- The complete selector energy is strictly negative exactly off the critical line. -/
theorem zeroSelectorEnergy_neg_iff_offLine (ρ : zetaZeroConfig.carrier) :
    zeroSelectorEnergy ρ < 0 ↔ (ρ : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hneg heq
    rw [zeroSelectorEnergy_eq_zero_of_criticalLine ρ heq] at hneg
    exact lt_irrefl _ hneg
  · intro hoff
    have hi : (gammaOf ρ).im ≠ 0 := by
      rw [WeilEF.gammaOf_im]
      intro h
      exact hoff (by linarith)
    have hself := orbitSign_self (gammaOf_re_ne_zero ρ) hi
    have hsum := summable_re_zeroSide_of_goodDensity (goodDensity_specSq (zeroSelector_evenStrip ρ))
    have hle : ∀ σ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult σ : ℝ) * (specSq (zeroSelector ρ) (gammaOf σ)).re ≤ 0 := by
      intro σ
      rw [zeroSelector_specSq_re]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (neg_nonpos.mpr (sq_nonneg _))
    have hlt : (zetaZeroConfig.mult ρ : ℝ) * (specSq (zeroSelector ρ) (gammaOf ρ)).re < 0 := by
      rw [zeroSelector_specSq_re, hself]
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
        exact_mod_cast zetaZeroConfig.one_le_mult _ ρ.2
      nlinarith
    rw [zeroSelectorEnergy, evenWeilDensity_specSq_vonMangoldt_eq_tsum_re (zeroSelector_evenStrip ρ)]
    simpa only [tsum_zero] using hsum.tsum_lt_tsum hle hlt summable_zero

theorem zeroSelectorEnergy_eq_zero_iff_criticalLine (ρ : zetaZeroConfig.carrier) :
    zeroSelectorEnergy ρ = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  constructor
  · intro heq
    by_contra hne
    have hneg := (zeroSelectorEnergy_neg_iff_offLine ρ).mpr hne
    rw [heq] at hneg
    exact lt_irrefl _ hneg
  · exact zeroSelectorEnergy_eq_zero_of_criticalLine ρ

/-- The exact selector acts on the original CHMD causal wave through its sech kernel. -/
theorem zeroSelectorEnergy_convolution (ρ : zetaZeroConfig.carrier) :
    zeroSelectorEnergy ρ = ∫ t : ℝ, sechKernel (zeroSelector ρ) t *
      CHMDGrowthCollapse.chmdWave t :=
  evenWeilDensity_specSq_vonMangoldt_eq_integral_sechKernel (zeroSelector_multiplier ρ)

/-- Pole cancellation leaves precisely the archimedean contribution minus the prime contribution. -/
theorem zeroSelectorEnergy_prime_arch (ρ : zetaZeroConfig.carrier) :
    zeroSelectorEnergy ρ =
      1 / (2 * Real.pi) * evenArchPart (specSq (zeroSelector ρ)) -
        evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq (zeroSelector ρ)) := by
  rw [zeroSelectorEnergy, evenWeilDensity_eq_parts]
  have hp : evenPolePart (specSq (zeroSelector ρ)) = 0 := by
    simp [evenPolePart, specSq, (zeroSelector_pole_zero ρ).1, (zeroSelector_pole_zero ρ).2]
  rw [hp, zero_add]

end RHTower.CHMDExactPackets
