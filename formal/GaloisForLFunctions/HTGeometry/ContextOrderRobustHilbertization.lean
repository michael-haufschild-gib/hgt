import GaloisForLFunctions.HTGeometry.GramRealizationFirewall
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-!
# Normalized block Hilbertization and robust context-order separation

`GramRealizationFirewall` proves the dimension-independent equivalence between PSD and Hilbert-space
Gram realizability.  This file adds the nonduplicative consequences needed by context-order descent:

* normalized occurrence blocks are exactly orthonormal context frames on one common carrier;
* the balanced all-order anomaly has an exact separating state;
* every PSD repair is at Euclidean operator-norm distance at least the balanced margin.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

noncomputable section

/-- Occurrence-indexed block kernel with identity diagonal blocks. -/
structure NormalizedBlockKernel (I A : Type*) [DecidableEq A] where
  matrix : Matrix (I × A) (I × A) ℂ
  diagonalBlock : ∀ i a b, matrix (i, a) (i, b) = if a = b then 1 else 0

/-- A normalized block kernel is PSD exactly when all contexts occur as orthonormal frames in one
common canonical Hilbert carrier. -/
theorem normalizedBlockKernel_posSemidef_iff_exists_orthonormal_frames
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (K : NormalizedBlockKernel I A) :
    K.matrix.PosSemidef ↔
      ∃ v : I × A → EuclideanSpace ℂ (I × A),
        K.matrix = innerGramMatrix v ∧
          ∀ i, Orthonormal ℂ (fun a => v (i, a)) := by
  classical
  constructor
  · intro hK
    obtain ⟨v, hv⟩ := (posSemidef_iff_exists_innerGramMatrix (K := K.matrix)).mp hK
    refine ⟨v, hv, fun i => orthonormal_iff_ite.mpr fun a b => ?_⟩
    have hd := K.diagonalBlock i a b
    rw [hv] at hd
    simpa [innerGramMatrix_apply] using hd
  · rintro ⟨v, hv, _⟩
    rw [hv]
    exact posSemidef_innerGramMatrix v

/-- Normalized constant-line quadratic reporter. -/
def balancedContextConstantReporter (r : ℕ)
    (K : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) : ℝ :=
  (star (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ) ⬝ᵥ
      K.mulVec _root_.HTGeometry.simplexEffectiveSection).re / ((r : ℝ) + 3)

/-- The balanced anomalous kernel has reporter value exactly `-δ`. -/
theorem balancedContextConstantReporter_kernel (r : ℕ) :
    balancedContextConstantReporter r
      (contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)) =
        -balancedContextMargin r := by
  rw [balancedContextConstantReporter, balancedContext_global_section_action]
  simp [dotProduct, _root_.HTGeometry.simplexEffectiveSection]
  have hne : (r : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/-- Every PSD kernel has nonnegative constant-line reporter. -/
theorem balancedContextConstantReporter_nonneg_of_posSemidef (r : ℕ)
    (Q : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) (hQ : Q.PosSemidef) :
    0 ≤ balancedContextConstantReporter r Q := by
  have hq := hQ.dotProduct_mulVec_nonneg
    (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ)
  have hqR := (Complex.nonneg_iff.mp hq).1
  exact div_nonneg hqR (by positivity)

theorem balancedContextConstantReporter_sub (r : ℕ)
    (A B : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) :
    balancedContextConstantReporter r (A - B) =
      balancedContextConstantReporter r A - balancedContextConstantReporter r B := by
  simp [balancedContextConstantReporter, Matrix.sub_mulVec, dotProduct]
  simp [_root_.HTGeometry.simplexEffectiveSection, Finset.sum_sub_distrib]
  ring

/-- Every PSD repair is separated from the anomalous kernel by at least `δ` under the normalized
constant-line reporter. -/
theorem balancedContext_psd_separation (r : ℕ)
    (Q : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) (hQ : Q.PosSemidef) :
    balancedContextMargin r ≤
      balancedContextConstantReporter r
        (Q - contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)) := by
  rw [balancedContextConstantReporter_sub, balancedContextConstantReporter_kernel]
  have hnonneg := balancedContextConstantReporter_nonneg_of_posSemidef r Q hQ
  linarith

/-- The constant-line reporter is the real trace pairing with the rank-one harmonic state. -/
theorem balancedContextConstantReporter_eq_trace_re (r : ℕ)
    (M : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) :
    balancedContextConstantReporter r M =
      ((_root_.HTGeometry.simplexEffectiveHarmonicProjection * M).trace).re := by
  have hC :
      (star (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ) ⬝ᵥ
          M.mulVec _root_.HTGeometry.simplexEffectiveSection) / ((r + 3 : ℕ) : ℂ) =
        (_root_.HTGeometry.simplexEffectiveHarmonicProjection * M).trace := by
    simp [dotProduct, _root_.HTGeometry.simplexEffectiveSection,
      _root_.HTGeometry.simplexEffectiveHarmonicProjection,
      Matrix.trace, Matrix.mul_apply, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    exact mul_comm _ _
  rw [balancedContextConstantReporter]
  have hdiv :
    (star (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ) ⬝ᵥ
          M.mulVec _root_.HTGeometry.simplexEffectiveSection).re / ((r : ℝ) + 3) =
        ((star (_root_.HTGeometry.simplexEffectiveSection : Fin (r + 3) → ℂ) ⬝ᵥ
          M.mulVec _root_.HTGeometry.simplexEffectiveSection) / ((r + 3 : ℕ) : ℂ)).re := by
    rw [Complex.div_re, Complex.normSq_natCast]
    simp
    have hn : (r : ℝ) + 3 ≠ 0 := by positivity
    field_simp
  have hre := congrArg Complex.re hC
  exact hdiv.trans hre

/-- Every constant-line report is bounded by Euclidean operator norm. -/
theorem abs_balancedContextConstantReporter_le_l2_opNorm (r : ℕ)
    (M : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) :
    |balancedContextConstantReporter r M| ≤ ‖M‖ := by
  rw [balancedContextConstantReporter_eq_trace_re]
  calc
    |((_root_.HTGeometry.simplexEffectiveHarmonicProjection * M).trace).re| ≤
        ‖(_root_.HTGeometry.simplexEffectiveHarmonicProjection * M).trace‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖M‖ := norm_trace_densityMatrix_mul_le
      _root_.HTGeometry.simplexEffectiveHarmonicProjection_posSemidef
      _root_.HTGeometry.trace_simplexEffectiveHarmonicProjection M

/-- **Sharp robust firewall.**  Every PSD matrix is at Euclidean operator-norm distance at least
`δ = 1/(2r+3)` from the balanced anomalous kernel. -/
theorem balancedContext_operatorNorm_psd_separation (r : ℕ)
    (Q : Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ) (hQ : Q.PosSemidef) :
    balancedContextMargin r ≤
      ‖Q - contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)‖ := by
  have hsep := balancedContext_psd_separation r Q hQ
  have habs : balancedContextConstantReporter r
      (Q - contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r)) ≤
      |balancedContextConstantReporter r
        (Q - contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r))| :=
    le_abs_self _
  exact hsep.trans (habs.trans
    (abs_balancedContextConstantReporter_le_l2_opNorm r _))

end

end GaloisForLFunctions.HTGeometry
