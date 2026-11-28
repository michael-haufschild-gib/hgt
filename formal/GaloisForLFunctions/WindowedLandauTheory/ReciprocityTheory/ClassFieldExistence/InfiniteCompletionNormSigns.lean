import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InfiniteCompletionNormOfBaseChange
import GaloisForLFunctions.HTGeometry.ComplexMatrixRealificationDeterminant

/-! At a real base place, norms from complex completions are positive.
Norms from real completions preserve the sign. -/

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : InfinitePlace K) (w : infinitePlacesAbove L v) (hv : v.IsReal)

omit [NumberField K] in
private theorem realEquiv_apply_algebraMap (hw : w.val.IsReal) (x : v.Completion) :
    ringEquivRealOfIsReal hw (algebraMap v.Completion w.val.Completion x) =
      ringEquivRealOfIsReal hv x := by
  letI := LiesOver.extensionEmbedding_liesOver_of_isReal w.val hv
  apply Complex.ofReal_injective
  rw [ringEquivRealOfIsReal_apply, ringEquivRealOfIsReal_apply,
    extensionEmbeddingOfIsReal_apply hw, extensionEmbeddingOfIsReal_apply hv]
  exact liesOver_extensionEmbedding_apply (φ := extensionEmbedding w.val) w.val v

theorem realNormOfRealCompletion (hw : w.val.IsReal) (x : w.val.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion x) =
      extensionEmbeddingOfIsReal hw x := by
  have h : (algebraMap ℝ ℝ).comp (ringEquivRealOfIsReal hv).toRingHom =
      (ringEquivRealOfIsReal hw).toRingHom.comp (algebraMap v.Completion w.val.Completion) := by
    apply RingHom.ext
    intro a
    exact (realEquiv_apply_algebraMap v w hv hw a).symm
  have he := Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hv)
    (ringEquivRealOfIsReal hw) h x
  rw [he]
  change ringEquivRealOfIsReal hv ((ringEquivRealOfIsReal hv).symm
    (Algebra.norm ℝ (ringEquivRealOfIsReal hw x))) = ringEquivRealOfIsReal hw x
  rw [RingEquiv.apply_symm_apply]
  change Algebra.norm ℝ (algebraMap ℝ ℝ (ringEquivRealOfIsReal hw x)) = _
  rw [Algebra.norm_algebraMap, Module.finrank_self, pow_one]

omit [NumberField K] in
theorem realNormOfComplexCompletion_pos (hw : w.val.IsComplex)
    {x : w.val.Completion} (hx : x ≠ 0) :
    0 < extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion x) := by
  letI := LiesOver.extensionEmbedding_liesOver_of_isReal w.val hv
  have h : (algebraMap ℝ ℂ).comp (ringEquivRealOfIsReal hv).toRingHom =
      (ringEquivComplexOfIsComplex hw).toRingHom.comp (algebraMap v.Completion w.val.Completion) := by
    apply RingHom.ext
    intro a
    change ((extensionEmbeddingOfIsReal hv a : ℝ) : ℂ) =
      extensionEmbedding w.val (algebraMap v.Completion w.val.Completion a)
    rw [extensionEmbeddingOfIsReal_apply hv]
    exact (liesOver_extensionEmbedding_apply (φ := extensionEmbedding w.val) w.val v).symm
  have he := Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hv)
    (ringEquivComplexOfIsComplex hw) h x
  rw [he]
  change 0 < ringEquivRealOfIsReal hv ((ringEquivRealOfIsReal hv).symm
    (Algebra.norm ℝ (ringEquivComplexOfIsComplex hw x)))
  rw [RingEquiv.apply_symm_apply, GaloisForLFunctions.HTGeometry.complex_algebraNorm_eq_normSq,
    Complex.normSq_pos]
  exact (map_ne_zero (ringEquivComplexOfIsComplex hw)).mpr hx

end GlobalTheory.Reciprocity
