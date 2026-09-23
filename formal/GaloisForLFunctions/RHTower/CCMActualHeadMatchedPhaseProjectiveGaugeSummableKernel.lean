import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveFockCocycle
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedSymmetricFirstMomentControl
import GaloisForLFunctions.RHTower.CCMActualHeadSignedCompletedErrorGammaProducer
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Summable projective-gauge kernel for the intact matched CCM source

The exponential Fock kernel internalizes the intact oriented matched-CCM source as a positive
entry ratio, but its natural arithmetic diagonal is not summable.  The independently proved
first-moment estimate supplies a source-selected half-density

`sqrt (criticalMellinAtomWeight n ^ (2 : ℕ) / exp (log n / 2))`

whose square is summable.  Projective readout permits this density to rescale both entries of an
arithmetic row without changing their ratio.

This module performs that rescaling directly.  Two rank-one feature coordinates give one global
positive-semidefinite kernel.  Its arithmetic diagonal is summable uniformly in spectral
frequency, while the ratio of its source-anchor and weight-anchor entries recovers the complete
signed oriented phase symbol.  The zero-weight branch is closed by the existing phase-disk law,
so no division premise is exported.  Every finite actual matched prime--polar block is therefore
the spectral integral of a nonlinear projective reporter of a kernel with summable arithmetic
diagonal.

This removes the carrier-compactness obstruction.  It does not assert positivity of the signed
completed source or the Riemann hypothesis.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder RealInnerProductSpace

noncomputable section
namespace RHTower

/-- The intact oriented source is uniformly bounded on every arithmetic atom and spectral
frequency.  The proof combines the matched phase-disk law with trigonometric Cauchy--Schwarz. -/
theorem ccmActualHeadMatchedOrientedPhaseSymbol_re_sq_le_sixteen
    (n : ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re ^ (2 : ℕ) ≤ 16 := by
  let w := criticalMellinAtomWeight n
  let C := ccmActualHeadMatchedCosinePhaseProfile n xi
  let S := ccmActualHeadMatchedSinePhaseProfile n xi
  have hw0 : 0 ≤ w := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hw2 : w ≤ 2 := criticalMellinAtomWeight_le_two n
  have hC0 : 0 ≤ C := ccmActualHeadMatchedCosinePhaseProfile_nonneg n xi
  have hdisk : (C - w) ^ (2 : ℕ) + S ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := by
    simpa [C, S, w] using ccmActualHeadMatchedPhaseProfile_mem_weightDisk n xi
  have hC_le : C ≤ 2 * w := by
    by_contra hnot
    have hlt : 2 * w < C := lt_of_not_ge hnot
    have hCpos : 0 < C := lt_of_le_of_lt (mul_nonneg (by norm_num) hw0) hlt
    have hmul : 2 * w * C < C * C := mul_lt_mul_of_pos_right hlt hCpos
    nlinarith [sq_nonneg S]
  have hprofile : C ^ (2 : ℕ) + S ^ (2 : ℕ) ≤ 4 * w ^ (2 : ℕ) := by
    have hmul : 2 * w * C ≤ 4 * w ^ (2 : ℕ) := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hC_le)]
    nlinarith
  have hw_sq : w ^ (2 : ℕ) ≤ 4 := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw2)]
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re]
  let theta := 2 * Real.pi * Real.log n * xi
  have htrig : Real.sin theta ^ (2 : ℕ) + Real.cos theta ^ (2 : ℕ) = 1 :=
    Real.sin_sq_add_cos_sq theta
  have hcs :
      (Real.cos theta * C + Real.sin theta * S) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) + S ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (Real.cos theta * S - Real.sin theta * C)]
  change (Real.cos theta * C + Real.sin theta * S) ^ (2 : ℕ) ≤ 16
  nlinarith

/-- Source-selected projective gauge.  Its square is the summable arithmetic half-density. -/
def ccmActualHeadMatchedPhaseProjectiveGauge (n : ℕ) : ℝ :=
  Real.sqrt (criticalMellinAtomWeight n ^ (2 : ℕ) /
    Real.exp (Real.log n / 2))

theorem ccmActualHeadMatchedPhaseProjectiveGauge_sq (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) =
      criticalMellinAtomWeight n ^ (2 : ℕ) / Real.exp (Real.log n / 2) := by
  rw [ccmActualHeadMatchedPhaseProjectiveGauge, Real.sq_sqrt]
  exact div_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- Two fixed projective anchors and every arithmetic atom. -/
inductive CCMActualHeadMatchedPhaseProjectiveGaugeIndex
  | weightAnchor
  | sourceAnchor
  | atom (n : ℕ)
  deriving DecidableEq

/-- First rank-one feature: the common projective denominator. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature :
    CCMActualHeadMatchedPhaseProjectiveGaugeIndex → ℂ
  | .weightAnchor => 1
  | .sourceAnchor => 0
  | .atom n => ccmActualHeadMatchedPhaseProjectiveGauge n

/-- Second rank-one feature: the gauge-scaled intact signed source. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveGaugeIndex → ℂ
  | .weightAnchor => 0
  | .sourceAnchor => 1
  | .atom n => ccmActualHeadMatchedPhaseProjectiveGauge n *
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re

/-- Sum of the two rank-one Gram kernels. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeKernel (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveGaugeIndex →
      CCMActualHeadMatchedPhaseProjectiveGaugeIndex → ℂ :=
  fun a b =>
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature a *
        conj (ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature b) +
      ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi a *
        conj (ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi b)

/-- The projectively rescaled global carrier is positive semidefinite. -/
theorem ccmActualHeadMatchedPhaseProjectiveGaugeKernel_isPSDKernel (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      (ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi) := by
  exact (GaloisForLFunctions.HTGeometry.isPSDKernel_rankOne
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature).add
      (GaloisForLFunctions.HTGeometry.isPSDKernel_rankOne
        (ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature xi))

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_weightAnchor
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi (.atom n) .weightAnchor =
      (ccmActualHeadMatchedPhaseProjectiveGauge n : ℂ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_sourceAnchor
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi (.atom n) .sourceAnchor =
      (ccmActualHeadMatchedPhaseProjectiveGauge n *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re : ℝ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_diagonal
    (xi : ℝ) (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi (.atom n) (.atom n)).re =
      ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) +
        (ccmActualHeadMatchedPhaseProjectiveGauge n *
          (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) ^ (2 : ℕ) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeKernel,
    ccmActualHeadMatchedPhaseProjectiveGaugeWeightFeature,
    ccmActualHeadMatchedPhaseProjectiveGaugeSourceFeature]
  ring

/-- Nonlinear projective reporter.  The explicit zero branch makes the definition total. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeReporter (xi : ℝ) (n : ℕ) : ℝ :=
  if criticalMellinAtomWeight n = 0 then 0
  else
    (ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi
        (.atom n) .sourceAnchor).re /
      (ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi
        (.atom n) .weightAnchor).re

/-- Projective rescaling preserves the complete oriented source exactly. -/
theorem ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  by_cases hw : criticalMellinAtomWeight n = 0
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeReporter, if_pos hw]
    have hdisk := ccmActualHeadMatchedPhaseProfile_mem_weightDisk n xi
    rw [hw] at hdisk
    have hC : ccmActualHeadMatchedCosinePhaseProfile n xi = 0 := by
      nlinarith [sq_nonneg (ccmActualHeadMatchedSinePhaseProfile n xi)]
    have hS : ccmActualHeadMatchedSinePhaseProfile n xi = 0 := by
      nlinarith [sq_nonneg (ccmActualHeadMatchedCosinePhaseProfile n xi)]
    rw [ccmActualHeadMatchedOrientedPhaseSymbol_re, hC, hS]
    ring
  · rw [ccmActualHeadMatchedPhaseProjectiveGaugeReporter, if_neg hw,
      ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_sourceAnchor,
      ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_weightAnchor]
    norm_cast
    have hbase : 0 < criticalMellinAtomWeight n ^ (2 : ℕ) /
        Real.exp (Real.log n / 2) :=
      div_pos (sq_pos_of_ne_zero hw) (Real.exp_pos _)
    have hg : ccmActualHeadMatchedPhaseProjectiveGauge n ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hbase)
    exact mul_div_cancel_left₀ _ hg

/-- Arithmetic part of the kernel diagonal. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal
    (xi : ℝ) (n : ℕ) : ℝ :=
  (ccmActualHeadMatchedPhaseProjectiveGaugeKernel xi (.atom n) (.atom n)).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal_nonneg
    (xi : ℝ) (n : ℕ) :
    0 ≤ ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal xi n := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal,
    ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_diagonal]
  positivity

/-- Uniform summable majorant for the arithmetic diagonal. -/
theorem ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal_le
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal xi n ≤
      17 * (criticalMellinAtomWeight n ^ (2 : ℕ) /
        Real.exp (Real.log n / 2)) := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal,
    ccmActualHeadMatchedPhaseProjectiveGaugeKernel_atom_diagonal]
  have hs := ccmActualHeadMatchedOrientedPhaseSymbol_re_sq_le_sixteen n xi
  have ha : 0 ≤ ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) := sq_nonneg _
  calc
    ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) +
          (ccmActualHeadMatchedPhaseProjectiveGauge n *
            (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) ^ (2 : ℕ) =
        ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
          (1 + (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re ^ (2 : ℕ)) := by ring
    _ ≤ 17 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) := by nlinarith
    _ = 17 * (criticalMellinAtomWeight n ^ (2 : ℕ) /
        Real.exp (Real.log n / 2)) := by
      rw [ccmActualHeadMatchedPhaseProjectiveGauge_sq]

/-- The global positive carrier has summable arithmetic diagonal at every spectral frequency. -/
theorem summable_ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal
    (xi : ℝ) :
    Summable (ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal xi) := by
  have hmajor : Summable (fun n : ℕ =>
      17 * (criticalMellinAtomWeight n ^ (2 : ℕ) /
        Real.exp (Real.log n / 2))) :=
    summable_criticalMellinAtomWeight_sq_div_exp_half_log.mul_left 17
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal_nonneg xi n)]
  exact ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal_le xi n

/-- Finite projective reporter extracted from restrictions of the single global kernel. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedPhaseProjectiveGaugeReporter xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter_eq
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseProjectiveGaugeReporter_eq xi n

/-- Every finite actual matched prime--polar block is the spectral integral of the projective
reporter of one positive kernel with summable arithmetic diagonal. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_projectiveGaugeSummableKernel
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeFiniteReporter_eq]

end RHTower
