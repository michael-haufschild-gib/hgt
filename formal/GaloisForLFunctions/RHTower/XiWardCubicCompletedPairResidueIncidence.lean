import GaloisForLFunctions.RHTower.XiWardCubicRawConormalModularDoublet

/-!
# Cubic Ward completed pair-residue incidence

The cubic zero-side Gram is genuinely quadratic, so a scalar completed explicit formula cannot
retain all of its coefficient data.  This module forms the quadratic object before divisor
evaluation.  One leg is the completed Xi logarithmic conormal current; the other is its
functional-equation-reflected modular mate.  Both definitions are made for arbitrary complex
parameters, before either parameter is restricted to a zero.

Successive logarithmic residues recover the product of the two analytic multiplicities times the
exact reflected conormal pair.  Aperture integration then gives the complete Cauchy-cube entry.
For every finite strict-right packet these entries are a diagonal multiplicity congruence of the
existing zero Gram, hence positive semidefinite, and their trace charges every copy by at least
two base units.  Raw multiplicities are intentionally retained: their square on the diagonal is
stronger than the linear divisor charge needed to exclude a first off-line zero.

This is a coefficient-faithful pre-divisor incidence theorem, not a source trace contraction.
The remaining theorem must transport or short this completed quadratic current against the
summable primitive Euler carrier without replacing it by bare positive postprocessing.
-/

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Completed logarithmic conormal current on the functional-equation-reflected radial leg. -/
def xiWardCubicReflectedCompletedConormalColumn (z : ℂ) (r : ℝ) : ℂ :=
  logDeriv xi z * xiWardCubicReflectedConormalMateFeature z r

/-- The reflected completed current has the full analytic multiplicity as residue and lands in
the Hermitian mate of the forward conormal feature. -/
theorem xiWardCubicReflectedCompletedConormalColumn_residue
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun z : ℂ =>
        (z - rho) * xiWardCubicReflectedCompletedConormalColumn z r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (((analyticOrderAt xi rho).toNat : ℂ) *
        xiWardCubicReflectedConormalMateFeature rho r)) := by
  have hlog := xi_normalizedLogDeriv_tendsto_order rho
  have hmate : Tendsto
      (fun z : ℂ => xiWardCubicReflectedConormalMateFeature z r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (xiWardCubicReflectedConormalMateFeature rho r)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous
        (fun z : ℂ => xiWardCubicReflectedConormalMateFeature z r) := by
      unfold xiWardCubicReflectedConormalMateFeature
      unfold routePXiBaseConormalResidueFeature
      fun_prop
    exact hc.continuousAt
  have h := hlog.mul hmate
  simpa [xiWardCubicReflectedCompletedConormalColumn, mul_assoc] using h

/-- Two-variable completed conormal current, formed before either divisor residue is taken. -/
def xiWardCubicCompletedPairConormalCurrent (z w : ℂ) (r : ℝ) : ℂ :=
  xiWardCubicReflectedCompletedConormalColumn z r *
    routePCompletedXiConormalColumn w r

/-- Exact value after taking the forward-leg residue of the completed pair current. -/
def xiWardCubicCompletedPairRightResidue (z tau : ℂ) (r : ℝ) : ℂ :=
  xiWardCubicReflectedCompletedConormalColumn z r *
    (((analyticOrderAt xi tau).toNat : ℂ) *
      routePXiBaseConormalResidueFeature tau r)

/-- First residue of the quadratic current retains the other completed leg rather than
scalarizing the pair. -/
theorem xiWardCubicCompletedPairConormalCurrent_right_residue
    (z tau : ℂ) (r : ℝ) :
    Tendsto
      (fun w : ℂ =>
        (w - tau) * xiWardCubicCompletedPairConormalCurrent z w r)
      (nhdsWithin tau ({tau}ᶜ))
      (nhds (xiWardCubicCompletedPairRightResidue z tau r)) := by
  have h := (routePCompletedXiConormalColumn_residue tau r).const_mul
    (xiWardCubicReflectedCompletedConormalColumn z r)
  simpa [xiWardCubicCompletedPairConormalCurrent,
    xiWardCubicCompletedPairRightResidue, mul_assoc, mul_left_comm] using h

/-- **W-H186 pair incidence.**  The iterated residue of the pre-divisor completed current is the
full multiplicity product times the reflected cubic conormal pair. -/
theorem xiWardCubicCompletedPairConormalCurrent_iterated_residue
    (rho tau : ℂ) (r : ℝ) :
    Tendsto
      (fun z : ℂ =>
        (z - rho) * xiWardCubicCompletedPairRightResidue z tau r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds ((((analyticOrderAt xi rho).toNat : ℂ) *
          ((analyticOrderAt xi tau).toNat : ℂ)) *
        (xiWardCubicReflectedConormalMateFeature rho r *
          routePXiBaseConormalResidueFeature tau r))) := by
  have h :=
    (xiWardCubicReflectedCompletedConormalColumn_residue rho r).mul_const
      (((analyticOrderAt xi tau).toNat : ℂ) *
        routePXiBaseConormalResidueFeature tau r)
  simpa [xiWardCubicCompletedPairRightResidue, mul_assoc, mul_left_comm,
    mul_comm] using h

/-- Aperture pairing of a reflected mate and a forward feature is the exact mixed Cauchy cube. -/
theorem integral_xiWardCubicReflectedConormalMateFeature_mul_baseFeature
    {rho tau : ℂ} (hrho : 1 / 2 < rho.re) (htau : 1 / 2 < tau.re) :
    (∫ r : ℝ in Ioi 0,
      xiWardCubicReflectedConormalMateFeature rho r *
        routePXiBaseConormalResidueFeature tau r) =
      routePBaseCauchyCubicKernel 1
        (rho - 1 / 2).re (tau - 1 / 2).re
        ((tau - 1 / 2).im - (rho - 1 / 2).im) := by
  rw [show (fun r : ℝ =>
      xiWardCubicReflectedConormalMateFeature rho r *
        routePXiBaseConormalResidueFeature tau r) =
      fun r : ℝ => star (routePXiBaseConormalResidueFeature rho r) *
        routePXiBaseConormalResidueFeature tau r by
    funext r
    rw [xiWardCubicReflectedConormalMateFeature_eq_star]]
  exact integral_star_routePXiBaseConormalResidueFeature_mul hrho htau

/-- The integrated iterated-residue landing is exactly the multiplicity-weighted cubic kernel. -/
theorem integral_xiWardCubicCompletedPair_iteratedResidueLanding
    {rho tau : ℂ} (hrho : 1 / 2 < rho.re) (htau : 1 / 2 < tau.re) :
    (∫ r : ℝ in Ioi 0,
      ((((analyticOrderAt xi rho).toNat : ℂ) *
          ((analyticOrderAt xi tau).toNat : ℂ)) *
        (xiWardCubicReflectedConormalMateFeature rho r *
          routePXiBaseConormalResidueFeature tau r))) =
      (((analyticOrderAt xi rho).toNat : ℂ) *
          ((analyticOrderAt xi tau).toNat : ℂ)) *
        routePBaseCauchyCubicKernel 1
          (rho - 1 / 2).re (tau - 1 / 2).re
          ((tau - 1 / 2).im - (rho - 1 / 2).im) := by
  rw [MeasureTheory.integral_const_mul,
    integral_xiWardCubicReflectedConormalMateFeature_mul_baseFeature hrho htau]

/-- Diagonal matrix retaining the literal analytic multiplicity of every strict-right copy. -/
def xiWardCubicRawMultiplicityScalingMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    (((xiSupportMultiplicity (q i).1.1 : ℕ) : ℝ) : ℂ)

/-- Finite matrix of raw completed pair residues.  This is a multiplicity congruence, not a
postulated target-side capacity matrix. -/
def xiWardCubicRawCompletedPairResidueMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  xiWardCubicRawMultiplicityScalingMatrix q *
    routePStrictRightZeroBaseCauchyCubicKernelMatrix q *
    (xiWardCubicRawMultiplicityScalingMatrix q).conjTranspose

/-- Arbitrary collision packets of raw completed pair residues remain positive semidefinite. -/
theorem xiWardCubicRawCompletedPairResidueMatrix_posSemidef {N : ℕ}
    (q : Fin N → XiRightZeroCopy) :
    (xiWardCubicRawCompletedPairResidueMatrix q).PosSemidef := by
  exact
    (routePStrictRightZeroBaseCauchyCubicKernelMatrix_posSemidef q).mul_mul_conjTranspose_same
      (xiWardCubicRawMultiplicityScalingMatrix q)

/-- Entrywise form of the multiplicity congruence. -/
theorem xiWardCubicRawCompletedPairResidueMatrix_apply {N : ℕ}
    (q : Fin N → XiRightZeroCopy) (i j : Fin N) :
    xiWardCubicRawCompletedPairResidueMatrix q i j =
      (((xiSupportMultiplicity (q i).1.1 : ℕ) : ℝ) : ℂ) *
        routePBaseCauchyCubicKernel 1
          (xiRightCenteredZero (q i)).re
          (xiRightCenteredZero (q j)).re
          ((xiRightCenteredZero (q j)).im -
            (xiRightCenteredZero (q i)).im) *
        (((xiSupportMultiplicity (q j).1.1 : ℕ) : ℝ) : ℂ) := by
  simp [xiWardCubicRawCompletedPairResidueMatrix,
    xiWardCubicRawMultiplicityScalingMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, routePStrictRightZeroBaseCauchyCubicKernelMatrix,
    routePBaseCauchyCubicKernelMatrix]

/-- Every matrix entry is literally the aperture integral of the iterated residue of the
pre-divisor quadratic current. -/
theorem xiWardCubicRawCompletedPairResidueMatrix_apply_eq_integral {N : ℕ}
    (q : Fin N → XiRightZeroCopy) (i j : Fin N) :
    xiWardCubicRawCompletedPairResidueMatrix q i j =
      ∫ r : ℝ in Ioi 0,
        ((((analyticOrderAt xi
              (((q i).1.1 : XiDivisorSupport) : ℂ)).toNat : ℂ) *
            ((analyticOrderAt xi
              (((q j).1.1 : XiDivisorSupport) : ℂ)).toNat : ℂ)) *
          (xiWardCubicReflectedConormalMateFeature
              (((q i).1.1 : XiDivisorSupport) : ℂ) r *
            routePXiBaseConormalResidueFeature
              (((q j).1.1 : XiDivisorSupport) : ℂ) r)) := by
  have hi : 1 / 2 < ((((q i).1.1 : XiDivisorSupport) : ℂ)).re := by
    have hpos := xiRightCenteredZero_re_pos (q i)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith
  have hj : 1 / 2 < ((((q j).1.1 : XiDivisorSupport) : ℂ)).re := by
    have hpos := xiRightCenteredZero_re_pos (q j)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith
  rw [integral_xiWardCubicCompletedPair_iteratedResidueLanding hi hj]
  rw [xiWardCubicRawCompletedPairResidueMatrix_apply,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    xiRightCenteredZero_eq_support_sub_half,
    xiRightCenteredZero_eq_support_sub_half]
  push_cast
  ring

/-- Exact trace of the raw pair-residue matrix: analytic multiplicity is squared on every
diagonal entry. -/
theorem re_trace_xiWardCubicRawCompletedPairResidueMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) :
    (xiWardCubicRawCompletedPairResidueMatrix q).trace.re =
      ∑ i : Fin N, xiWardCubicRawConormalCharge (q i) := by
  change Complex.reCLM
      (∑ i : Fin N, xiWardCubicRawCompletedPairResidueMatrix q i i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have ha : 0 < (xiRightCenteredZero (q i)).re :=
    xiRightCenteredZero_re_pos (q i)
  rw [xiWardCubicRawCompletedPairResidueMatrix_apply, sub_self,
    routePBaseCauchyCubicKernel_diagonal
      (by norm_num : (0 : ℝ) < 1) ha]
  rw [xiWardCubicRawConormalCharge]
  push_cast
  norm_num
  field_simp [ha.ne']
  norm_cast

/-- Every strict-right copy consumes at least two units in the matrix-complete raw residue trace. -/
theorem two_mul_card_le_re_trace_xiWardCubicRawCompletedPairResidueMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) :
    2 * N ≤ (xiWardCubicRawCompletedPairResidueMatrix q).trace.re := by
  rw [re_trace_xiWardCubicRawCompletedPairResidueMatrix]
  calc
    2 * N = ∑ _i : Fin N, (2 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ i : Fin N, xiWardCubicRawConormalCharge (q i) := by
      exact Finset.sum_le_sum fun i _hi =>
        xiWardCubicRawConormalCharge_ge_two (q i)

end

end RHTower
