import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector

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

open Complex
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

end

end RHTower
