import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.RHTower.PrimeBoundaryMonodromyEscape

/-!
# Critical-feature lattice budget as a pole--Gamma--von-Mangoldt jet

The four source legs of the real critical feature collapse on the diagonal.  At the lower
absolute-Euler pole `z = t - i`, their sum is the single first-order jet

`2 * (Re T'(z) + Im T(z))`,

where `T` is the regulator-independent prime--archimedean relative trace.  Since `T` is defined
literally from the von-Mangoldt `LSeries` and the logarithmic derivative of the completed
archimedean factor, this gives a coefficient-faithful pole--Gamma--von-Mangoldt representation of
the critical-feature lattice budget before any Xi divisor is selected.

Combining this jet collapse with the thin-strip source projector expresses the corrected lattice
budget as an explicit Euler--Gamma jet sum minus a source-only thin contour.  The file proves the
identity and provenance comparison; it does not assert the remaining quantitative `4 / 25`
upper bound.
-/

open Complex LSeries
open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The two cross-orientation source legs coalesce to the derivative of the absolute-Euler
relative trace. -/
theorem criticalHardyPrimeGammaSourceCup_diagonal (t : ℝ) :
    criticalHardyPrimeGammaSourceCup t t =
      deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) := by
  rw [criticalHardyPrimeGammaSourceCup,
    deningerPrimeGammaSourceCup_single]
  change I * I *
      deningerPrimeGammaSourceKernel (criticalHardyLowerPoint t)
        (deningerPrimeGammaPointConjEquiv (criticalHardyLowerPoint t)) = _
  rw [deningerPrimeGammaSourceKernel_reflectedDiagonal]
  rw [show (I : ℂ) * I = -1 by exact I_mul_I]
  ring

/-- The two same-orientation legs collapse to one odd Schwarz difference of source values. -/
theorem criticalHardy_sameOrientation_diagonal_add (t : ℝ) :
    criticalHardyLowerLowerPrimeArchSource t t +
        criticalHardyUpperUpperPrimeArchSource t t =
      -I * (primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) +
        primeArchSourceRelativeTrace (criticalHardyLowerPoint (-t) : ℂ)) := by
  rw [criticalHardyLowerLowerPrimeArchSource,
    criticalHardyUpperUpperPrimeArchSource]
  simp only [criticalHardyLowerPoint_coe, criticalHardyUpperPoint_coe]
  rw [show (t : ℂ) - I + (((-t : ℝ) : ℂ) - I) = -2 * I by
      push_cast
      ring,
    show (t : ℂ) + I - ((t : ℂ) - I) = 2 * I by ring]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp [hI]
  rw [I_sq]
  ring

/-- Oddness and Schwarz reality of the centered Xi trace, transported back to the absolute-Euler
source, identify the reflected lower value with minus the conjugate value. -/
theorem primeArchSourceRelativeTrace_neg_reflection (t : ℝ) :
    primeArchSourceRelativeTrace (criticalHardyLowerPoint (-t) : ℂ) =
      -(starRingEnd ℂ)
        (primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ)) := by
  have hneg :
      (criticalHardyLowerPoint (-t) : ℂ) =
        -(starRingEnd ℂ) (criticalHardyLowerPoint t : ℂ) := by
    simp [criticalHardyLowerPoint_coe]
    ring
  rw [primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (criticalHardyLowerPoint (-t)).property,
    primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (criticalHardyLowerPoint t).property,
    hneg]
  have hzconj :
      XiC ((starRingEnd ℂ) (criticalHardyLowerPoint t : ℂ)) ≠ 0 := by
    apply XiC_ne_zero_of_half_le_abs_im
    simp [criticalHardyLowerPoint_coe]
    norm_num
  have hz : XiC (criticalHardyLowerPoint t : ℂ) ≠ 0 :=
    XiC_ne_zero_of_one_lt_centered_re (criticalHardyLowerPoint t).property
  have hnegXi :
      XiC (-(starRingEnd ℂ) (criticalHardyLowerPoint t : ℂ)) ≠ 0 := by
    rw [XiC_even]
    exact hzconj
  rw [← logDeriv_XiC_eq_relativeResolventTrace hnegXi,
    logDeriv_XiC_neg, logDeriv_XiC_conj hz,
    logDeriv_XiC_eq_relativeResolventTrace hz]

/-- Coefficient-faithful pole--Gamma--von-Mangoldt jet at the safe Euler point `t - i`.
Unfolding `primeArchSourceRelativeTrace` exposes the von-Mangoldt `LSeries` and `archFactor`
logarithmic derivative literally. -/
def criticalFeaturePoleGammaVMJet (t : ℝ) : ℝ :=
  2 * ((deriv primeArchSourceRelativeTrace
          (criticalHardyLowerPoint t : ℂ)).re +
    (primeArchSourceRelativeTrace
          (criticalHardyLowerPoint t : ℂ)).im)

/-- The four-leg critical-feature source diagonal is exactly one Euler-safe arithmetic jet. -/
theorem criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet (t : ℝ) :
    criticalFeaturePrimeGammaSourceDiagonal t =
      (criticalFeaturePoleGammaVMJet t : ℂ) := by
  rw [criticalFeaturePrimeGammaSourceDiagonal,
    criticalHardyPrimeGammaSourceCup_diagonal]
  rw [show criticalHardyLowerLowerPrimeArchSource t t +
          deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) +
          (starRingEnd ℂ)
            (deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ)) +
          criticalHardyUpperUpperPrimeArchSource t t =
        (criticalHardyLowerLowerPrimeArchSource t t +
          criticalHardyUpperUpperPrimeArchSource t t) +
          deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) +
          (starRingEnd ℂ)
            (deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ)) by ring,
    criticalHardy_sameOrientation_diagonal_add,
    primeArchSourceRelativeTrace_neg_reflection]
  simp [criticalFeaturePoleGammaVMJet, Complex.ext_iff, mul_re, mul_im]
  ring

theorem re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet (t : ℝ) :
    (criticalFeaturePrimeGammaSourceDiagonal t).re =
      criticalFeaturePoleGammaVMJet t := by
  rw [criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet]
  simp

/-- Finite lattice sum of the explicit Euler-safe arithmetic jet. -/
def criticalFeaturePoleGammaVMLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePoleGammaVMJet (k : ℝ)

theorem criticalFeaturePrimeGammaRawLatticeBudget_eq_poleGammaVM (K : Finset ℤ) :
    criticalFeaturePrimeGammaRawLatticeBudget K =
      criticalFeaturePoleGammaVMLatticeBudget K := by
  rw [criticalFeaturePrimeGammaRawLatticeBudget,
    criticalFeaturePoleGammaVMLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  exact re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet (k : ℝ)

/-- Fully source-defined corrected budget: arithmetic Euler--Gamma jets minus critical-line
multiplicity extracted by one common divisor-free thin contour. -/
def criticalFeatureThinStripPoleGammaVMLatticeBudget
    (K : Finset ℤ) (A B delta : ℝ) : ℝ :=
  ∑ k ∈ K, (criticalFeaturePoleGammaVMJet (k : ℝ) -
    (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re)

theorem criticalFeatureThinStripCorrectedLatticeBudget_eq_poleGammaVM
    (K : Finset ℤ) (A B delta : ℝ) :
    criticalFeatureThinStripCorrectedLatticeBudget K A B delta =
      criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta := by
  rw [criticalFeatureThinStripCorrectedLatticeBudget,
    criticalFeatureThinStripPoleGammaVMLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  rw [re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet]

/-- Existing corrected divisor budget is majorized by an exact pole--Gamma--von-Mangoldt lattice
budget whose critical-line subtraction is supplied by one source-only thin strip. -/
theorem exists_poleGammaVM_sourceMajorant
    (K : Finset ℤ) {A B delta₀ : ℝ}
    (hAB : A < B) (hdelta₀ : 0 < delta₀)
    (hright₀ : ∀ y ∈ Set.uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft₀ : ∀ y ∈ Set.uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((A : ℂ) + y * I)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < delta₀ ∧ delta < 1 / 2 ∧
      criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
        criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta ∧
      criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta =
        ∑ k ∈ K, (criticalFeaturePoleGammaVMJet (k : ℝ) -
          finiteCriticalLineFeatureEnergy (k : ℝ) A B delta) := by
  obtain ⟨delta, hdelta, hdeltaLt, hdeltaHalf, hmajor, hfinite⟩ :=
    exists_thinStripCorrectedLattice_sourceMajorant
      K hAB hdelta₀ hright₀ hleft₀
  refine ⟨delta, hdelta, hdeltaLt, hdeltaHalf, ?_, ?_⟩
  rw [← criticalFeatureThinStripCorrectedLatticeBudget_eq_poleGammaVM]
  exact hmajor
  rw [← criticalFeatureThinStripCorrectedLatticeBudget_eq_poleGammaVM,
    hfinite]
  apply Finset.sum_congr rfl
  intro k hk
  rw [re_criticalFeaturePrimeGammaSourceDiagonal_eq_poleGammaVMJet]

/-! ## Safe Euler-coordinate expansion -/

/-- Literal von-Mangoldt minus archimedean carrier in the ordinary `s` coordinate. -/
def criticalFeatureEulerVMArchCarrier (s : ℂ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
    logDeriv archFactor s

/-- The lower critical-feature pole `t - i` is the absolute-Euler point `3/2 + it`. -/
def criticalFeatureEulerVMArchPoint (t : ℝ) : ℂ :=
  3 / 2 + (t : ℂ) * I

theorem criticalHardyLowerPoint_to_eulerPoint (t : ℝ) :
    1 / 2 + (criticalHardyLowerPoint t : ℂ) * I =
      criticalFeatureEulerVMArchPoint t := by
  simp [criticalHardyLowerPoint_coe, criticalFeatureEulerVMArchPoint]
  rw [sub_mul, I_mul_I]
  ring

@[simp]
theorem criticalFeatureEulerVMArchPoint_re (t : ℝ) :
    (criticalFeatureEulerVMArchPoint t).re = 3 / 2 := by
  simp [criticalFeatureEulerVMArchPoint]

theorem differentiableAt_criticalFeatureEulerVMArchCarrier (t : ℝ) :
    DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier
      (criticalFeatureEulerVMArchPoint t) := by
  let s := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by
      simpa [s] using criticalFeatureEulerVMArchPoint_re t]
    norm_num
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hL : DifferentiableAt ℂ
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s :=
    (LSeries_hasDerivAt habs).differentiableAt
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    rw [zero_re] at hreal
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hreal := congrArg Complex.re h
    rw [one_re] at hreal
    linarith
  have hA : AnalyticAt ℂ archFactor s := analyticAt_archFactor_of_re_pos hspos
  have hAne : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  have hlog : DifferentiableAt ℂ (logDeriv archFactor) s := by
    have hd := hA.deriv.differentiableAt.div hA.differentiableAt hAne
    simpa [logDeriv] using hd
  exact hL.sub hlog

theorem primeArchSourceRelativeTrace_eq_eulerVMArchCarrier (z : ℂ) :
    primeArchSourceRelativeTrace z =
      -I * criticalFeatureEulerVMArchCarrier (1 / 2 + z * I) := by
  rfl

theorem deriv_primeArchSourceRelativeTrace_eq_eulerVMArchCarrier (t : ℝ) :
    deriv primeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) =
      deriv criticalFeatureEulerVMArchCarrier
        (criticalFeatureEulerVMArchPoint t) := by
  let z : ℂ := criticalHardyLowerPoint t
  let s : ℂ := criticalFeatureEulerVMArchPoint t
  have hscoord : 1 / 2 + z * I = s := by
    simpa [z, s] using criticalHardyLowerPoint_to_eulerPoint t
  have hH : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier s := by
    simpa [s] using differentiableAt_criticalFeatureEulerVMArchCarrier t
  have hcoord : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
    simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
  have hcomp : HasDerivAt
      (fun w : ℂ => criticalFeatureEulerVMArchCarrier (1 / 2 + w * I))
      (deriv criticalFeatureEulerVMArchCarrier s * I) z := by
    have hH' : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier
        (1 / 2 + z * I) := by
      rw [hscoord]
      exact hH
    have hderiv := hH'.hasDerivAt.comp z hcoord
    rw [hscoord] at hderiv
    simpa [Function.comp_def] using hderiv
  have hscaled : HasDerivAt
      (fun w : ℂ => -I *
        criticalFeatureEulerVMArchCarrier (1 / 2 + w * I))
      (-I * (deriv criticalFeatureEulerVMArchCarrier s * I)) z :=
    hcomp.const_mul (-I)
  have htrace : primeArchSourceRelativeTrace =
      fun w : ℂ => -I *
        criticalFeatureEulerVMArchCarrier (1 / 2 + w * I) := by rfl
  rw [htrace, hscaled.deriv]
  ring_nf
  rw [I_sq]
  ring

/-- Exact ordinary-coordinate formula: the lattice source is the real part of `(∂s - 1)` applied
to the von-Mangoldt-minus-Gamma carrier on `Re s = 3/2`. -/
theorem criticalFeaturePoleGammaVMJet_eq_eulerVMArchJet (t : ℝ) :
    criticalFeaturePoleGammaVMJet t =
      2 * ((deriv criticalFeatureEulerVMArchCarrier
          (criticalFeatureEulerVMArchPoint t)).re -
        (criticalFeatureEulerVMArchCarrier
          (criticalFeatureEulerVMArchPoint t)).re) := by
  rw [criticalFeaturePoleGammaVMJet,
    deriv_primeArchSourceRelativeTrace_eq_eulerVMArchCarrier]
  rw [primeArchSourceRelativeTrace_eq_eulerVMArchCarrier,
    criticalHardyLowerPoint_to_eulerPoint]
  simp [mul_im]
  ring

/-- The derivative of the Euler carrier is a logarithmically weighted von-Mangoldt series plus
the first archimedean jet. -/
theorem deriv_criticalFeatureEulerVMArchCarrier_eq (t : ℝ) :
    deriv criticalFeatureEulerVMArchCarrier
        (criticalFeatureEulerVMArchPoint t) =
      -LSeries (LSeries.logMul
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
          (criticalFeatureEulerVMArchPoint t) -
        deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t) := by
  let s := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by simpa [s] using criticalFeatureEulerVMArchPoint_re t]
    norm_num
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hL : DifferentiableAt ℂ
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s :=
    (LSeries_hasDerivAt habs).differentiableAt
  have hcarrier := differentiableAt_criticalFeatureEulerVMArchCarrier t
  have hcarrier' : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier s := by
    simpa [s] using hcarrier
  have harch : DifferentiableAt ℂ (logDeriv archFactor) s := by
    have heq : logDeriv archFactor = fun w : ℂ =>
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w -
          criticalFeatureEulerVMArchCarrier w := by
      funext w
      simp [criticalFeatureEulerVMArchCarrier]
    rw [heq]
    exact hL.sub hcarrier'
  change deriv
      ((LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) -
        logDeriv archFactor) s =
    -LSeries (LSeries.logMul
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s -
      deriv (logDeriv archFactor) s
  rw [deriv_sub hL harch, LSeries_deriv habs]

/-- Completely expanded pole--Gamma--von-Mangoldt diagonal.  Prime coefficients are
`-(1 + log n) Λ(n)` on `Re s = 3/2`; all non-prime contribution is the explicit first jet of the
completed archimedean factor. -/
theorem criticalFeaturePoleGammaVMJet_eq_explicit (t : ℝ) :
    criticalFeaturePoleGammaVMJet t =
      2 * (-LSeries (LSeries.logMul
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
              (criticalFeatureEulerVMArchPoint t) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t) +
            logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
            deriv (logDeriv archFactor)
              (criticalFeatureEulerVMArchPoint t)).re := by
  rw [criticalFeaturePoleGammaVMJet_eq_eulerVMArchJet,
    deriv_criticalFeatureEulerVMArchCarrier_eq,
    criticalFeatureEulerVMArchCarrier]
  simp only [sub_re, add_re, neg_re]
  ring

/-! ## Lattice-summed prime--Gamma channels -/

/-- Signed von-Mangoldt channel of the finite critical-feature lattice. -/
def criticalFeatureVonMangoldtLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, 2 *
    (-LSeries (LSeries.logMul
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
          (criticalFeatureEulerVMArchPoint (k : ℝ)) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint (k : ℝ))).re

/-- Rational-boundary and Gamma channel of the finite critical-feature lattice. -/
def criticalFeaturePoleGammaLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, 2 *
    (logDeriv archFactor (criticalFeatureEulerVMArchPoint (k : ℝ)) -
      deriv (logDeriv archFactor)
        (criticalFeatureEulerVMArchPoint (k : ℝ))).re

/-- Thin-strip source contour that removes diagonal critical-line multiplicity. -/
def criticalFeatureThinStripLineContourLattice
    (K : Finset ℤ) (A B delta : ℝ) : ℝ :=
  ∑ k ∈ K,
    (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re

/-- Exact pre-divisor splitting of the raw lattice diagonal into von-Mangoldt and pole--Gamma
channels. -/
theorem criticalFeaturePoleGammaVMLatticeBudget_eq_channels (K : Finset ℤ) :
    criticalFeaturePoleGammaVMLatticeBudget K =
      criticalFeatureVonMangoldtLatticeBudget K +
        criticalFeaturePoleGammaLatticeBudget K := by
  rw [criticalFeaturePoleGammaVMLatticeBudget,
    criticalFeatureVonMangoldtLatticeBudget,
    criticalFeaturePoleGammaLatticeBudget, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [criticalFeaturePoleGammaVMJet_eq_explicit]
  simp only [sub_re, add_re, neg_re]
  ring

/-- Exact corrected source budget: signed von-Mangoldt lattice plus pole--Gamma lattice minus the
thin contour that extracts critical-line multiplicity. -/
theorem criticalFeatureThinStripPoleGammaVMLatticeBudget_eq_channels
    (K : Finset ℤ) (A B delta : ℝ) :
    criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta =
      criticalFeatureVonMangoldtLatticeBudget K +
        criticalFeaturePoleGammaLatticeBudget K -
          criticalFeatureThinStripLineContourLattice K A B delta := by
  rw [criticalFeatureThinStripPoleGammaVMLatticeBudget,
    criticalFeatureThinStripLineContourLattice,
    Finset.sum_sub_distrib]
  change criticalFeaturePoleGammaVMLatticeBudget K -
      (∑ k ∈ K,
        (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re) = _
  rw [criticalFeaturePoleGammaVMLatticeBudget_eq_channels]

/-! ## Absolute-convergence localization of the leading budget -/

/-- Absolute-convergence majorant for both von-Mangoldt jets on `Re s = 3 / 2`. -/
def criticalFeatureVonMangoldtUniformConstant : ℝ :=
  (∑' n : ℕ, ‖LSeries.term
      (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
      ((3 / 2 : ℝ) : ℂ) n‖) +
  (∑' n : ℕ, ‖LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℝ) : ℂ) n‖)

/-- The logarithmically weighted von-Mangoldt series is uniformly bounded on the whole safe
vertical line by its absolutely convergent real-axis majorant. -/
theorem norm_LSeries_logMul_vonMangoldt_criticalFeatureEulerVMArchPoint_le (t : ℝ) :
    ‖LSeries (LSeries.logMul
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
        (criticalFeatureEulerVMArchPoint t)‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
        ((3 / 2 : ℝ) : ℂ) n‖ := by
  let s := criticalFeatureEulerVMArchPoint t
  let f : ℕ → ℂ :=
    LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by
      simpa [s] using criticalFeatureEulerVMArchPoint_re t]
    norm_num
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hsum : LSeriesSummable f s := by
    simpa [f] using LSeriesSummable_logMul_of_lt_re habs
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    summable_norm_iff.mpr hsum
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := by
      rw [LSeries]
      exact norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, ‖LSeries.term f ((3 / 2 : ℝ) : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp [s, criticalFeatureEulerVMArchPoint]
    _ = _ := by rfl

/-- The plain von-Mangoldt series has the same uniform absolute-convergence bound. -/
theorem norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le (t : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint t)‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((3 / 2 : ℝ) : ℂ) n‖ := by
  let s := criticalFeatureEulerVMArchPoint t
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by
      simpa [s] using criticalFeatureEulerVMArchPoint_re t]
    norm_num
  have hsum : LSeriesSummable f s := by
    simpa [f] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    summable_norm_iff.mpr hsum
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := by
      rw [LSeries]
      exact norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, ‖LSeries.term f ((3 / 2 : ℝ) : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp [s, criticalFeatureEulerVMArchPoint]
    _ = _ := by rfl

/-- Every single signed prime jet is bounded by one height-independent constant. -/
theorem abs_criticalFeatureVonMangoldtLattice_summand_le (t : ℝ) :
    |2 *
      (-LSeries (LSeries.logMul
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
          (criticalFeatureEulerVMArchPoint t) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint t)).re| ≤
      2 * criticalFeatureVonMangoldtUniformConstant := by
  let A := LSeries (LSeries.logMul
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
      (criticalFeatureEulerVMArchPoint t)
  let B := LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (criticalFeatureEulerVMArchPoint t)
  have hA :=
    norm_LSeries_logMul_vonMangoldt_criticalFeatureEulerVMArchPoint_le t
  have hB := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le t
  calc
    |2 * (-A - B).re| = 2 * |(-A - B).re| := by rw [abs_mul]; norm_num
    _ ≤ 2 * ‖-A - B‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2 * (‖A‖ + ‖B‖) := by
      gcongr
      simpa using norm_sub_le (-A) B
    _ ≤ 2 * criticalFeatureVonMangoldtUniformConstant := by
      dsimp [criticalFeatureVonMangoldtUniformConstant]
      gcongr

/-- **Prime-channel lower-order law.**  On every finite lattice the entire von-Mangoldt channel is
bounded by lattice cardinality times a fixed absolute-convergence constant.  Thus any family with
`card K_T = o(N(T))` has a prime channel `o(N(T))`; a leading `4 / 25` gain cannot come from this
linear safe-half-plane channel. -/
theorem abs_criticalFeatureVonMangoldtLatticeBudget_le (K : Finset ℤ) :
    |criticalFeatureVonMangoldtLatticeBudget K| ≤
      (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by
  rw [criticalFeatureVonMangoldtLatticeBudget]
  calc
    |∑ k ∈ K, 2 *
        (-LSeries (LSeries.logMul
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
            (criticalFeatureEulerVMArchPoint (k : ℝ)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (k : ℝ))).re| ≤
        ∑ k ∈ K, |2 *
          (-LSeries (LSeries.logMul
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
              (criticalFeatureEulerVMArchPoint (k : ℝ)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (k : ℝ))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ K, 2 * criticalFeatureVonMangoldtUniformConstant := by
      gcongr with k hk
      exact abs_criticalFeatureVonMangoldtLattice_summand_le (k : ℝ)
    _ = (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by simp

/-- Abstract asymptotic form of the prime-channel lower-order law.  No Riemann hypothesis enters:
whenever lattice cardinality is negligible relative to a positive normalizer, the normalized
von-Mangoldt channel vanishes. -/
theorem tendsto_criticalFeatureVonMangoldtLatticeBudget_div_of_card_div
    (K : ℕ → Finset ℤ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (nhds 0)) :
    Tendsto (fun n => criticalFeatureVonMangoldtLatticeBudget (K n) / N n)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun n => ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant)) atTop (nhds 0) := by
    simpa using hcard.mul_const (2 * criticalFeatureVonMangoldtUniformConstant)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  filter_upwards [hN] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
  calc
    |criticalFeatureVonMangoldtLatticeBudget (K n)| / N n ≤
        ((K n).card : ℝ) *
            (2 * criticalFeatureVonMangoldtUniformConstant) / N n :=
      (div_le_div_iff_of_pos_right hn).2
        (abs_criticalFeatureVonMangoldtLatticeBudget_le (K n))
    _ = ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant) := by ring

end

end RHTower
