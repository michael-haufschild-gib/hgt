import GaloisForLFunctions.HilbertMetric.QuantumInformation.FermionSpectralEntropy
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Exact two-mode temporal sampling and entropy

For two equally observed modes, sampling at integer times gives vectors
`(z^n,w^n)`. Their span is the full two-mode space exactly when the sampled
phases differ; a collision leaves the uniform one-dimensional line, for any
number of samples. Compressing the ground-state occupation `(1,0)` to this
observed space gives entropy `log 2` at a collision and zero otherwise.

This is the rank-sensitive finite-system mechanism of Appendix B of
arXiv:2611.13085, including the alias case excluded by its maximal-rank premise.
-/

noncomputable section
open scoped Matrix BigOperators
open Matrix Polynomial
namespace GaloisForLFunctions.HilbertMetric

/-- Two-mode observation at an integer sampling time. -/
def twoModeTemporalSample (z w : ℂ) (n : ℕ) : Fin 2 → ℂ := ![z ^ n, w ^ n]

/-- The single-particle space observed by all integer-time samples. -/
def twoModeTemporalSpace (z w : ℂ) : Submodule ℂ (Fin 2 → ℂ) :=
  Submodule.span ℂ (Set.range (twoModeTemporalSample z w))

/-- Orthogonal projector onto the observed space: the uniform line at a collision,
and the full space otherwise. -/
def twoModeTemporalProjection (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if z = w then !![1 / 2, 1 / 2; 1 / 2, 1 / 2] else 1

/-- One occupied and one empty physical mode, compressed to the observed space. -/
def twoModeTemporalCorrelation (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  twoModeTemporalProjection z w * Matrix.diagonal ![1, 0] * twoModeTemporalProjection z w

/-- Explicit interpolation from the first two samples, with the collision denominator cleared. -/
theorem twoModeTemporal_interpolation (z w : ℂ) (v : Fin 2 → ℂ) :
    (w - z) • v =
      (w * v 0 - z * v 1) • twoModeTemporalSample z w 0 +
        (v 1 - v 0) • twoModeTemporalSample z w 1 := by
  ext i
  fin_cases i <;> simp [twoModeTemporalSample] <;> ring

/-- Exact observed-space classifier; collisions identify the two coordinates. -/
theorem twoModeTemporalSpace_mem_iff (z w : ℂ) (v : Fin 2 → ℂ) :
    v ∈ twoModeTemporalSpace z w ↔ z ≠ w ∨ v 0 = v 1 := by
  by_cases hzw : z = w
  · subst w
    simp only [ne_self_iff_false, false_or]
    constructor
    · intro hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        simp [twoModeTemporalSample]
      | zero => rfl
      | add x y hx hy ihx ihy =>
        change x 0 + y 0 = x 1 + y 1
        rw [ihx, ihy]
      | smul a x hx ih =>
        change a * x 0 = a * x 1
        rw [ih]
    · intro hv
      have hzero : twoModeTemporalSample z z 0 ∈ twoModeTemporalSpace z z :=
        Submodule.subset_span ⟨0, rfl⟩
      have he : v = v 0 • twoModeTemporalSample z z 0 := by
        ext i
        fin_cases i <;> simp [twoModeTemporalSample, hv]
      rw [he]
      exact Submodule.smul_mem _ _ hzero
  · refine ⟨fun _ => Or.inl hzw, fun _ => ?_⟩
    have hden : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
    have h₀ : twoModeTemporalSample z w 0 ∈ twoModeTemporalSpace z w :=
      Submodule.subset_span ⟨0, rfl⟩
    have h₁ : twoModeTemporalSample z w 1 ∈ twoModeTemporalSpace z w :=
      Submodule.subset_span ⟨1, rfl⟩
    have hmem : (w - z) • v ∈ twoModeTemporalSpace z w := by
      rw [twoModeTemporal_interpolation]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₀) (Submodule.smul_mem _ _ h₁)
    have h := Submodule.smul_mem (twoModeTemporalSpace z w) (w - z)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hden, one_smul] using h

/-- The proposed projector fixes exactly the actual sampled subspace. -/
theorem twoModeTemporalProjection_fixed_iff (z w : ℂ) (v : Fin 2 → ℂ) :
    (twoModeTemporalProjection z w).mulVec v = v ↔ v ∈ twoModeTemporalSpace z w := by
  rw [twoModeTemporalSpace_mem_iff]
  by_cases h : z = w
  · simp only [twoModeTemporalProjection, h, if_true, ne_self_iff_false, false_or]
    constructor
    · intro hv
      have h₀ := congrFun hv 0
      have h₁ := congrFun hv 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₀ h₁
      linear_combination h₁ - h₀
    · intro hv
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv] <;> ring
  · simp [twoModeTemporalProjection, h]

/-- Hermiticity of the observed-space projector is proved from its explicit matrix. -/
theorem twoModeTemporalProjection_isHermitian (z w : ℂ) :
    (twoModeTemporalProjection z w).IsHermitian := by
  by_cases h : z = w
  · simp only [twoModeTemporalProjection, h, if_true, Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · simp [twoModeTemporalProjection, h]

/-- The explicit observed-space projector is idempotent. -/
theorem twoModeTemporalProjection_idempotent (z w : ℂ) :
    twoModeTemporalProjection z w * twoModeTemporalProjection z w =
      twoModeTemporalProjection z w := by
  by_cases h : z = w
  · simp only [twoModeTemporalProjection, h, if_true]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [twoModeTemporalProjection, h]

/-- Matrix entries of the exact compressed occupation. -/
theorem twoModeTemporalCorrelation_eq (z w : ℂ) :
    twoModeTemporalCorrelation z w =
      if z = w then !![1 / 4, 1 / 4; 1 / 4, 1 / 4] else Matrix.diagonal ![1, 0] := by
  by_cases h : z = w
  · simp only [twoModeTemporalCorrelation, twoModeTemporalProjection, if_pos h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · simp [twoModeTemporalCorrelation, twoModeTemporalProjection, h]

/-- The compressed correlation has spectrum `{0,1/2}` at an alias and `{0,1}` otherwise. -/
theorem twoModeTemporalCorrelation_charpoly (z w : ℂ) :
    (twoModeTemporalCorrelation z w).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (if z = w then (1 / 2 : ℂ) else 1)) := by
  rw [twoModeTemporalCorrelation_eq]
  by_cases h : z = w <;>
    norm_num [h, Matrix.charpoly_fin_two, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

/-- Exact entropy dichotomy, with all rank conditions discharged. -/
theorem twoModeTemporalCorrelation_entropy (z w : ℂ) :
    fermionSpectralEntropy (twoModeTemporalCorrelation z w) =
      if z = w then Real.log 2 else 0 := by
  rw [fermionSpectralEntropy, twoModeTemporalCorrelation_charpoly,
    Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X, Polynomial.roots_X_sub_C]
  by_cases h : z = w <;> simp [h, Real.binEntropy_two_inv]

end GaloisForLFunctions.HilbertMetric

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporal_interpolation
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalSpace_mem_iff
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalProjection_fixed_iff
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalProjection_isHermitian
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalProjection_idempotent
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalCorrelation_eq
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalCorrelation_charpoly
#print axioms GaloisForLFunctions.HilbertMetric.twoModeTemporalCorrelation_entropy
-- END PAPER AXIOM AUDIT
