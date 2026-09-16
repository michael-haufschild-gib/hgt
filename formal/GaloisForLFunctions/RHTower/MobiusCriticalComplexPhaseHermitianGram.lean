import GaloisForLFunctions.RHTower.MobiusGammaXiSingularGraphNormalLanding

/-!
# Hermitian Gram kernel of complex Möbius phase sources

The complex-damped squarefree Möbius columns admit an exact non-diagonal
Hilbert Gram law.  The overlap of nodes `u` and `v` is the arithmetic Euler
overlap at the Hermitian displacement `v + conj u`.  Consequently this
Euler-overlap kernel is Hermitian and every finite packet is positive
semidefinite.

The singular Gamma/Xi source graph retains this entire kernel after its
forced graph-normal factor is applied.  This supplies the genuine
adjoint/conjugate orientation absent from real aperture reversal.  It does
not assert that division by the graph normalizer is uniformly bounded at
the critical boundary.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Coordinate of the centered infinitesimal imaginary clock phase.  The centering removes the
base-state component before comparison with the Fisher source tangent. -/
def infiniteMobiusCriticalCenteredImaginaryPhaseCoefficient
    (sigma : ℝ) (n : ℕ) : ℂ :=
  -I * (((sigma - 1) *
    (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
      infiniteMobiusSignedWeight sigma n

/-- The centered first imaginary phase direction has no new source coordinate: it is exactly a
quarter-turn and half-rescaling of the already present Fisher tangent. -/
theorem infiniteMobiusCriticalCenteredImaginaryPhaseCoefficient_eq_i_half_fisher
    (sigma : ℝ) (n : ℕ) :
    infiniteMobiusCriticalCenteredImaginaryPhaseCoefficient sigma n =
      (I / 2) * infiniteMobiusCriticalFisherTangentWeight sigma n := by
  unfold infiniteMobiusCriticalCenteredImaginaryPhaseCoefficient
    infiniteMobiusCriticalFisherTangentWeight
  push_cast
  ring

/-- Hermitian Euler overlap kernel of two complex inward Möbius source nodes. -/
def mobiusCriticalComplexPhaseKernel
    (sigma : ℝ) (u v : ℂ) : ℂ :=
  GaloisForLFunctions.squarefreeBoundaryOverlap
    (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
      (v + (starRingEnd ℂ) u)

private theorem complexDamped_pair_apply
    (sigma : ℝ) (u v : ℂ) (n : ℕ) :
    infiniteMobiusCriticalComplexDampedSignedWeight sigma v n *
        (starRingEnd ℂ)
          (infiniteMobiusCriticalComplexDampedSignedWeight sigma u n) =
      infiniteMobiusCriticalComplexDampedSignedWeight
          sigma (v + (starRingEnd ℂ) u) n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) := by
  rw [infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp sigma v n,
    infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp sigma u n,
    infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp
      sigma (v + (starRingEnd ℂ) u) n]
  have hexp :
      (starRingEnd ℂ)
          (Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ))) =
        Complex.exp
          (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal]
  rw [map_mul, hexp]
  rw [show
      Complex.exp
            (-v * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
          infiniteMobiusSignedWeight sigma n *
          (Complex.exp
              (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log n : ℝ) : ℂ)) *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
        (Complex.exp
            (-v * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
          Complex.exp
            (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log n : ℝ) : ℂ))) *
          infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring_nf

/-- **Exact non-diagonal source Gram law.**  Complex clock phases combine
with the Hermitian displacement `v + conj u`; no diagonalization or RH
premise is used. -/
theorem inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
    {sigma : ℝ} {u v : ℂ} (hsigma : 1 < sigma)
    (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    inner ℂ
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma v hsigma hv) =
      mobiusCriticalComplexPhaseKernel sigma u v := by
  have huv : 0 ≤ (v + (starRingEnd ℂ) u).re := by
    simp only [add_re, Complex.conj_re]
    linarith
  have hshift :
      1 < ((sigma : ℂ) +
        (v + (starRingEnd ℂ) u) * ((sigma - 1 : ℝ) : ℂ)).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, Complex.conj_re]
    nlinarith
  rw [show
      inner ℂ
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu)
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma v hsigma hv) =
        inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma (v + (starRingEnd ℂ) u) hsigma huv) by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      simp only [infiniteMobiusSignedWeightLp,
        infiniteMobiusCriticalComplexDampedSignedWeightLp,
        RCLike.inner_apply]
      apply tsum_congr
      intro n
      exact complexDamped_pair_apply sigma u v n]
  exact
    inner_infiniteMobiusSignedWeight_complexDamped_eq_squarefreeBoundaryOverlap
      hsigma huv hshift

/-- The arithmetic overlap kernel has actual Schwarz/Hilbert symmetry. -/
theorem star_mobiusCriticalComplexPhaseKernel
    {sigma : ℝ} {u v : ℂ} (hsigma : 1 < sigma)
    (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    (starRingEnd ℂ) (mobiusCriticalComplexPhaseKernel sigma u v) =
      mobiusCriticalComplexPhaseKernel sigma v u := by
  rw [← inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
      hsigma hu hv,
    ← inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
      hsigma hv hu]
  exact inner_conj_symm _ _

/-- Every finite packet of inward complex Möbius nodes has a positive
semidefinite arithmetic Euler-overlap matrix. -/
theorem re_finite_mobiusCriticalComplexPhaseKernel_quadratic_nonneg
    {ι : Type*} {sigma : ℝ} (S : Finset ι) (u : ι → ℂ)
    (hu : ∀ i, 0 ≤ (u i).re) (c : ι → ℂ)
    (hsigma : 1 < sigma) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S,
      (starRingEnd ℂ) (c i) * c j *
        mobiusCriticalComplexPhaseKernel sigma (u i) (u j)).re := by
  rw [show
      (∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ) (c i) * c j *
          mobiusCriticalComplexPhaseKernel sigma (u i) (u j)) =
        inner ℂ
          (∑ i ∈ S, c i •
            infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma (u i) hsigma (hu i))
          (∑ j ∈ S, c j •
            infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma (u j) hsigma (hu j)) by
      simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap]
      simp only [mul_assoc]]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- The forced singular graph normalizer transports the full non-diagonal
source Gram entry exactly into the Gamma/Xi graph. -/
theorem mobiusGammaXiComplexHardyGraphNormalDifference_complexDamped_zero
    {sigma : ℝ} {u v : ℂ} (hsigma : 1 < sigma)
    (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma v
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu) 0 =
      mobiusCriticalComplexPhaseKernel sigma u v := by
  rw [mobiusGammaXiComplexHardyGraphNormalDifference_eq_inner hsigma hv,
    sub_zero,
    inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
      hsigma hu hv]

end RHTower
