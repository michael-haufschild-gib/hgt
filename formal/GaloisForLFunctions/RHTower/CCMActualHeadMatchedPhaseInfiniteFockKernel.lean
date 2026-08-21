import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseFockTomography
import GaloisForLFunctions.HTGeometry.PSDKernelMatrixBridge

/-!
# One infinite trace-free Fock kernel for every matched CCM packet

Finite trace-free Fock tomography already avoids the nonsummable scalar reserve forced by local
Schur completion, but its packet-indexed statement leaves a false-looking limit problem: different
finite prime packets appear to use different positive matrices.  They do not.

This module complexifies real positive-semidefinite matrices, applies the corpus's finite-matrix to
infinite-kernel bridge, and constructs one positive-semidefinite kernel on the label type consisting
of two tomography anchors and every natural-number atom.  Each finite matched CCM source block is
an exact nonlinear reporter of a restriction of this same kernel.  Consequently no cofinal matrix
selection, Cholesky compatibility, compactness, or uniform-tail hypothesis is needed to assemble
the positive carrier.  Remaining obstruction lies after carrier assembly: converting positivity
of the kernel into control of its logarithmic source reporter under spectral integration.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder RealInnerProductSpace

noncomputable section
namespace RHTower

/-- Positive semidefiniteness survives scalar extension of a real matrix to `ℂ`.  Complex
coefficients split into independent real and imaginary quadratic energies. -/
theorem realMatrix_posSemidef_map_complex {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    (A.map (algebraMap ℝ ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact hA.isHermitian.map _ (by intro x; simp)
  · intro x
    let AC : Matrix n n ℂ := A.map (algebraMap ℝ ℂ)
    let u : n → ℝ := fun i => (x i).re
    let v : n → ℝ := fun i => (x i).im
    have hu := hA.dotProduct_mulVec_nonneg u
    have hv := hA.dotProduct_mulVec_nonneg v
    apply Complex.nonneg_iff.mpr
    constructor
    · have hre :
          (dotProduct (star x) (Matrix.mulVec AC x)).re =
            dotProduct (star u) (Matrix.mulVec A u) +
              dotProduct (star v) (Matrix.mulVec A v) := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, AC, Matrix.map_apply]
        simp_rw [Finset.mul_sum]
        change Complex.reAddGroupHom
            (∑ i, ∑ j, (starRingEnd ℂ) (x i) * ((A i j : ℂ) * x j)) = _
        rw [map_sum]
        simp_rw [map_sum]
        simp only [Complex.coe_reAddGroupHom, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
          star_trivial, u, v]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hre]
      exact add_nonneg hu hv
    · exact (hA.isHermitian.map _
        (by intro y; simp)).im_star_dotProduct_mulVec_self x |>.symm

/-- Complex scalar extension of the augmented trace-free Fock matrix, on arbitrary labels. -/
def ccmActualHeadMatchedPhaseInfiniteFockKernel {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseFockIndex ι →
      CCMActualHeadMatchedPhaseFockIndex ι → ℂ :=
  fun a b => (ccmActualHeadMatchedPhaseFockMatrix n xi a b : ℂ)

/-- The arbitrary-label trace-free Fock carrier is one genuine infinite positive-semidefinite
kernel, not merely a compatible family of finite matrices. -/
theorem ccmActualHeadMatchedPhaseInfiniteFockKernel_isPSDKernel
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      (ccmActualHeadMatchedPhaseInfiniteFockKernel n xi) := by
  apply GaloisForLFunctions.HTGeometry.isPSDKernel_of_forall_posSemidef
  · intro a b
    have hs : ccmActualHeadMatchedPhaseFockMatrix n xi a b =
        ccmActualHeadMatchedPhaseFockMatrix n xi b a := by
      simp [ccmActualHeadMatchedPhaseFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
        real_inner_comm]
    simpa [ccmActualHeadMatchedPhaseInfiniteFockKernel] using
      congrArg (fun r : ℝ => (r : ℂ)) hs
  · intro m w
    let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j k =>
      ccmActualHeadMatchedPhaseFockMatrix n xi (w j) (w k)
    have hA : A.PosSemidef := by
      have h :=
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix_fin_posSemidef
          (fun j => CCMActualHeadMatchedPhaseFockIndex.feature n xi (w j))
          (1 / 2) (by norm_num)
      convert h using 1
      ext j k
      simp [A, ccmActualHeadMatchedPhaseFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix]
    convert realMatrix_posSemidef_map_complex A hA using 1
    ext j k
    rfl

/-- Single global arithmetic kernel: two anchors plus every natural-number atom. -/
def ccmActualHeadMatchedPhaseGlobalFockKernel (xi : ℝ) :
    CCMActualHeadMatchedPhaseFockIndex ℕ →
      CCMActualHeadMatchedPhaseFockIndex ℕ → ℂ :=
  ccmActualHeadMatchedPhaseInfiniteFockKernel id xi

theorem ccmActualHeadMatchedPhaseGlobalFockKernel_isPSDKernel (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      (ccmActualHeadMatchedPhaseGlobalFockKernel xi) := by
  exact ccmActualHeadMatchedPhaseInfiniteFockKernel_isPSDKernel id xi

/-- Reporter using only entries of the single global infinite PSD kernel. -/
def ccmActualHeadMatchedPhaseGlobalFockReporter (xi : ℝ) (n : ℕ) : ℝ :=
  let theta := 2 * Real.pi * Real.log n * xi
  criticalMellinAtomWeight n * Real.cos theta +
    Real.cos theta * Real.log
      ((ccmActualHeadMatchedPhaseGlobalFockKernel xi
        (.atom n) (.cosineAnchor)).re) +
    Real.sin theta * Real.log
      ((ccmActualHeadMatchedPhaseGlobalFockKernel xi
        (.atom n) (.sineAnchor)).re)

theorem ccmActualHeadMatchedPhaseGlobalFockReporter_eq_orientedPhaseSymbol_re
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseGlobalFockReporter xi n =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  change ccmActualHeadMatchedPhaseFockTomographyReporter
      (fun j : ℕ => j) xi n =
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re
  exact ccmActualHeadMatchedPhaseFockTomographyReporter_eq_orientedPhaseSymbol_re
    (fun j : ℕ => j) xi n

/-- Every finite arithmetic packet is reported by a restriction of the same infinite kernel. -/
def ccmActualHeadMatchedPhaseGlobalFockFiniteReporter
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedPhaseGlobalFockReporter xi n

theorem ccmActualHeadMatchedPhaseGlobalFockFiniteReporter_eq_orientedFiniteSymbol_re
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseGlobalFockFiniteReporter F xi =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  unfold ccmActualHeadMatchedPhaseGlobalFockFiniteReporter
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedPhaseGlobalFockReporter_eq_orientedPhaseSymbol_re xi n

/-- Every finite actual matched prime-polar block is an exact nonlinear reporter of a restriction
of the single global infinite PSD kernel. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_globalPhaseFockKernel
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedPhaseGlobalFockFiniteReporter F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [ccmActualHeadMatchedPhaseGlobalFockFiniteReporter_eq_orientedFiniteSymbol_re]

end RHTower
