import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram
import GaloisForLFunctions.HTGeometry.LinearIsometryCompletion

/-!
# Unitary equivalence from two total feature families with the same Gram kernel

Two feature families in complete complex Hilbert spaces determine a canonical isometry between
their algebraic spans when all pairwise inner products agree.  If both spans are dense, completion
upgrades that isometry to a unitary equivalence of the ambient Hilbert spaces.
-/

open scoped InnerProductSpace
open Set UniformSpace Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Algebraic synthesis of finitely supported feature coefficients. -/
def featureSynthesis (v : ι → H) : (ι →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ v

@[simp] theorem featureSynthesis_single
    (v : ι → H) (i : ι) (c : ℂ) :
    featureSynthesis v (Finsupp.single i c) = c • v i := by
  simp [featureSynthesis]

/-- Equality of the feature Gram kernels extends to every finite linear combination. -/
theorem inner_featureSynthesis_eq
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (a b : ι →₀ ℂ) :
    inner ℂ (featureSynthesis v a) (featureSynthesis v b) =
      inner ℂ (featureSynthesis w a) (featureSynthesis w b) := by
  classical
  simp only [featureSynthesis, Finsupp.linearCombination_apply]
  change inner ℂ (∑ i ∈ a.support, a i • v i) (∑ j ∈ b.support, b j • v j) =
    inner ℂ (∑ i ∈ a.support, a i • w i) (∑ j ∈ b.support, b j • w j)
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hgram]

/-- Algebraic feature synthesis has range exactly the span of the feature family. -/
theorem range_featureSynthesis_eq_span (v : ι → H) :
    LinearMap.range (featureSynthesis v) =
      Submodule.span ℂ (Set.range v) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    classical
    induction a using Finsupp.induction with
    | zero => simp
    | single_add i c a hi hc ih =>
        rw [map_add, featureSynthesis_single]
        exact (Submodule.span ℂ (Set.range v)).add_mem
          ((Submodule.span ℂ (Set.range v)).smul_mem c
            (Submodule.subset_span ⟨i, rfl⟩)) ih
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact ⟨Finsupp.single i 1, by simp⟩

theorem dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
    (v : ι → H)
    (hdense : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    Dense ((LinearMap.range (featureSynthesis v) : Submodule ℂ H) : Set H) := by
  rw [range_featureSynthesis_eq_span]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hdense

/-- Isometry between the two algebraic feature ranges. -/
noncomputable def featureRangeGramEquiv
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) :
    LinearMap.range (featureSynthesis v) ≃ₗᵢ[ℂ]
      LinearMap.range (featureSynthesis w) :=
  HilbertMetric.NomologicalCrossGram.activeRangeIsometryEquiv
    (𝕜 := ℂ) (D := ι →₀ ℂ) (W := H) (W' := K)
    (featureSynthesis v) (featureSynthesis w)
    (inner_featureSynthesis_eq v w hgram)

/-- The range-Gram equivalence carries each generating feature to its counterpart. -/
theorem featureRangeGramEquiv_single
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (i : ι) :
    ((featureRangeGramEquiv v w hgram
      ⟨v i, ⟨Finsupp.single i 1, by simp⟩⟩ :
        LinearMap.range (featureSynthesis w)) : K) = w i := by
  change ((HilbertMetric.NomologicalCrossGram.activeRangeIsometryEquiv
      (featureSynthesis v) (featureSynthesis w)
      (inner_featureSynthesis_eq v w hgram)
      ⟨v i, ⟨Finsupp.single i 1, by simp⟩⟩ :
        LinearMap.range (featureSynthesis w)) : K) = w i
  simpa using
    HilbertMetric.NomologicalCrossGram.activeRangeIsometryEquiv_apply
      (featureSynthesis v) (featureSynthesis w)
      (inner_featureSynthesis_eq v w hgram) (Finsupp.single i 1)

/-- A linear isometry with dense range extends to a unitary equivalence from the completion. -/
noncomputable def completionLinearIsometryEquivOfDenseRange
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →ₗᵢ[ℂ] F) (hL : DenseRange L) :
    Completion E ≃ₗᵢ[ℂ] F where
  toLinearEquiv := LinearEquiv.ofBijective
    (completionExtendₗᵢ L).toLinearMap
    ⟨by
      intro x y hxy
      exact (completionExtendₗᵢ L).injective hxy,
      denseRange_completionExtendₗᵢ_of_denseRange L hL⟩
  norm_map' := (completionExtendₗᵢ L).norm_map

@[simp] theorem completionLinearIsometryEquivOfDenseRange_coe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →ₗᵢ[ℂ] F) (hL : DenseRange L) (x : E) :
    completionLinearIsometryEquivOfDenseRange L hL (x : Completion E) = L x := by
  exact completionExtendₗᵢ_coe L x

/-- Inclusion of the first algebraic feature range into its ambient Hilbert space. -/
def leftFeatureRangeInclusion (v : ι → H) :
    LinearMap.range (featureSynthesis v) →ₗᵢ[ℂ] H :=
  Submodule.subtypeₗᵢ _

/-- The first algebraic feature range transported into the second ambient Hilbert space. -/
noncomputable def rightFeatureRangeInclusion
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) :
    LinearMap.range (featureSynthesis v) →ₗᵢ[ℂ] K :=
  (Submodule.subtypeₗᵢ (LinearMap.range (featureSynthesis w))).comp
    (featureRangeGramEquiv v w hgram).toLinearIsometry

theorem denseRange_leftFeatureRangeInclusion
    (v : ι → H)
    (hdense : Dense ((LinearMap.range (featureSynthesis v) :
      Submodule ℂ H) : Set H)) :
    DenseRange (leftFeatureRangeInclusion v) := by
  change Dense (Set.range (leftFeatureRangeInclusion v))
  apply hdense.mono
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem denseRange_rightFeatureRangeInclusion
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (hdense : Dense ((LinearMap.range (featureSynthesis w) :
      Submodule ℂ K) : Set K)) :
    DenseRange (rightFeatureRangeInclusion v w hgram) := by
  change Dense (Set.range (rightFeatureRangeInclusion v w hgram))
  apply hdense.mono
  intro y hy
  let yr : LinearMap.range (featureSynthesis w) := ⟨y, hy⟩
  let xr := (featureRangeGramEquiv v w hgram).symm yr
  refine ⟨xr, ?_⟩
  change (((featureRangeGramEquiv v w hgram) xr :
    LinearMap.range (featureSynthesis w)) : K) = y
  rw [(featureRangeGramEquiv v w hgram).apply_symm_apply]

/-- Unitary equivalence of complete Hilbert spaces determined by two total equal-Gram feature
families. -/
noncomputable def denseFeatureGramUnitary
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (hdenseV : Dense ((LinearMap.range (featureSynthesis v) :
      Submodule ℂ H) : Set H))
    (hdenseW : Dense ((LinearMap.range (featureSynthesis w) :
      Submodule ℂ K) : Set K)) : H ≃ₗᵢ[ℂ] K :=
  (completionLinearIsometryEquivOfDenseRange
      (leftFeatureRangeInclusion v)
      (denseRange_leftFeatureRangeInclusion v hdenseV)).symm.trans
    (completionLinearIsometryEquivOfDenseRange
      (rightFeatureRangeInclusion v w hgram)
      (denseRange_rightFeatureRangeInclusion v w hgram hdenseW))

/-- The total-family unitary carries every named feature to its equal-Gram counterpart. -/
theorem denseFeatureGramUnitary_apply
    (v : ι → H) (w : ι → K)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (hdenseV : Dense ((LinearMap.range (featureSynthesis v) :
      Submodule ℂ H) : Set H))
    (hdenseW : Dense ((LinearMap.range (featureSynthesis w) :
      Submodule ℂ K) : Set K)) (i : ι) :
    denseFeatureGramUnitary v w hgram hdenseV hdenseW (v i) = w i := by
  let rv : LinearMap.range (featureSynthesis v) :=
    ⟨v i, ⟨Finsupp.single i 1, by simp⟩⟩
  let UL := completionLinearIsometryEquivOfDenseRange
    (leftFeatureRangeInclusion v)
    (denseRange_leftFeatureRangeInclusion v hdenseV)
  let UR := completionLinearIsometryEquivOfDenseRange
    (rightFeatureRangeInclusion v w hgram)
    (denseRange_rightFeatureRangeInclusion v w hgram hdenseW)
  have hUL : UL (rv : Completion (LinearMap.range (featureSynthesis v))) = v i := by
    dsimp only [UL]
    rw [completionLinearIsometryEquivOfDenseRange_coe]
    rfl
  have hULsymm : UL.symm (v i) =
      (rv : Completion (LinearMap.range (featureSynthesis v))) := by
    apply UL.injective
    rw [UL.apply_symm_apply]
    exact hUL.symm
  change UR (UL.symm (v i)) = w i
  rw [hULsymm]
  dsimp only [UR]
  rw [completionLinearIsometryEquivOfDenseRange_coe]
  exact featureRangeGramEquiv_single v w hgram i

end GaloisForLFunctions.HTGeometry
