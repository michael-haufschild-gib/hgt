import GaloisForLFunctions.HTGeometry.GramRealizationFirewall
import GaloisForLFunctions.HilbertMetric.NegativeHeightGrams
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.SwapBlockParity

/-!
# Exact realizability and dimension of reflection Gram pairs

Two finite matrices are ordinary and reflected Gram matrices precisely when
their sum and difference are positive semidefinite. The two character
sectors give a canonical realization. Every realization has the same active
dimension: the sum of the two sector ranks.
-/

noncomputable section
open scoped ComplexOrder
namespace GaloisForLFunctions.RepresentationLifting.ReflectionGrams
open GaloisForLFunctions.HTGeometry
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem half_nonneg : (0 : ℂ) ≤ 1 / 2 := by
  rw [Complex.le_def]
  norm_num

/-- The mixed Gram of a marked unitary reflection representation. -/
def mixedGram (R : E ≃ₗᵢ[ℂ] E) (v : ι → E) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (v i) (R (v j))

private theorem reflection_inner_left (R : E ≃ₗᵢ[ℂ] E)
    (hR : ∀ x, R (R x) = x) (x y : E) :
    inner ℂ (R x) y = inner ℂ x (R y) := by
  have h := R.inner_map_map x (R y)
  rwa [hR] at h

/-- Every reflection realization satisfies both positive-semidefinite sector constraints. -/
theorem sector_positive (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    (Matrix.gram ℂ v + mixedGram R v).PosSemidef ∧
      (Matrix.gram ℂ v - mixedGram R v).PosSemidef := by
  have hp : (1 / 2 : ℂ) • Matrix.gram ℂ (fun i => v i + R (v i)) =
      Matrix.gram ℂ v + mixedGram R v := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.gram, Matrix.of_apply, Matrix.add_apply,
      mixedGram, inner_add_left, inner_add_right, R.inner_map_map,
      reflection_inner_left R hR, smul_eq_mul]
    ring
  have hm : (1 / 2 : ℂ) • Matrix.gram ℂ (fun i => v i - R (v i)) =
      Matrix.gram ℂ v - mixedGram R v := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.gram, Matrix.of_apply, Matrix.sub_apply,
      mixedGram, inner_sub_left, inner_sub_right, R.inner_map_map,
      reflection_inner_left R hR, smul_eq_mul]
    ring
  constructor
  · rw [← hp]
    exact (Matrix.posSemidef_gram ℂ _).smul half_nonneg
  · rw [← hm]
    exact (Matrix.posSemidef_gram ℂ _).smul half_nonneg

/-- Canonical ambient space of the two reflection characters. -/
abbrev PairSpace (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : Bool => EuclideanSpace ℂ ι)

/-- Canonical reflection: the positive summand is fixed and the negative summand changes sign. -/
def pairReflection : PairSpace ι ≃ₗᵢ[ℂ] PairSpace ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun b : Bool =>
    if b then LinearIsometryEquiv.neg ℂ else LinearIsometryEquiv.refl ℂ _)

@[simp] theorem pairReflection_apply (x : PairSpace ι) (b : Bool) :
    pairReflection x b = if b then -(x b) else x b := by
  cases b <;> rfl

theorem pairReflection_involutive (x : PairSpace ι) : pairReflection (pairReflection x) = x := by
  ext b j
  cases b <;> simp only [pairReflection_apply, Bool.false_eq_true, if_false, if_true, neg_neg]

/-- The two sector inequalities are sufficient for an exact reflection realization. -/
theorem exists_pair_realization {G K : Matrix ι ι ℂ}
    (hp : (G + K).PosSemidef) (hm : (G - K).PosSemidef) :
    ∃ v : ι → PairSpace ι, Matrix.gram ℂ v = G ∧ mixedGram pairReflection v = K := by
  classical
  obtain ⟨u, hu⟩ := exists_innerGramMatrix_of_posSemidef
    (hp.smul half_nonneg)
  obtain ⟨w, hw⟩ := exists_innerGramMatrix_of_posSemidef
    (hm.smul half_nonneg)
  have hu' (i j : ι) : inner ℂ (u i) (u j) = (1 / 2 : ℂ) * (G i j + K i j) :=
    (congrFun (congrFun hu i) j).symm
  have hw' (i j : ι) : inner ℂ (w i) (w j) = (1 / 2 : ℂ) * (G i j - K i j) :=
    (congrFun (congrFun hw i) j).symm
  let v (i : ι) : PairSpace ι := WithLp.toLp 2 (fun b => if b then w i else u i)
  refine ⟨v, ?_, ?_⟩
  · ext i j
    change inner ℂ (v i) (v j) = G i j
    rw [PiLp.inner_apply, Fintype.sum_bool]
    change inner ℂ (w i) (w j) + inner ℂ (u i) (u j) = G i j
    rw [hu', hw']
    ring
  · ext i j
    change inner ℂ (v i) (pairReflection (v j)) = K i j
    rw [PiLp.inner_apply, Fintype.sum_bool]
    change inner ℂ (w i) (-(w j)) + inner ℂ (u i) (u j) = K i j
    rw [inner_neg_right, hu', hw']
    ring

/-- Exact feasibility classification, including degenerate and redundant Gram data. -/
theorem reflection_realizable_iff (G K : Matrix ι ι ℂ) :
    ((G + K).PosSemidef ∧ (G - K).PosSemidef) ↔
      ∃ v : ι → PairSpace ι, Matrix.gram ℂ v = G ∧ mixedGram pairReflection v = K := by
  constructor
  · rintro ⟨hp, hm⟩
    exact exists_pair_realization hp hm
  · rintro ⟨v, hG, hK⟩
    have hs := sector_positive (pairReflection (ι := ι))
      (pairReflection_involutive (ι := ι)) v
    rwa [hG, hK] at hs

private theorem gram_rank_span (v : ι → E) :
    (Matrix.gram ℂ v).rank = Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  have he : (-Matrix.gram ℂ v).mulVecLin = -(Matrix.gram ℂ v).mulVecLin :=
    LinearMap.ext (fun c => Matrix.neg_mulVec c _)
  have hr := HilbertMetric.negativeHeightGram_rank v
  change Module.finrank ℂ ((-Matrix.gram ℂ v).mulVecLin.range) = _ at hr
  rw [he, LinearMap.range_neg] at hr
  exact hr

/-- Original and reflected marks generate the smallest invariant realization. -/
def doubledFeature (R : E ≃ₗᵢ[ℂ] E) (v : ι → E) : ι ⊕ ι → E :=
  Sum.elim v (R ∘ v)

/-- The finite subspace generated by original and reflected marks. -/
abbrev activeSpace (R : E ≃ₗᵢ[ℂ] E) (v : ι → E) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range (doubledFeature R v))

instance activeSpace_finiteDimensional (R : E ≃ₗᵢ[ℂ] E) (v : ι → E) :
    FiniteDimensional ℂ (activeSpace R v) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

omit [Fintype ι] in
private theorem reflection_mem_active (R : E ≃ₗᵢ[ℂ] E)
    (hR : ∀ x, R (R x) = x) (v : ι → E) {x : E} (hx : x ∈ activeSpace R v) :
    R x ∈ activeSpace R v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | inl i => exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
    | inr i =>
      change R (R (v i)) ∈ activeSpace R v
      rw [hR]
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  | zero => rw [map_zero]; exact (activeSpace R v).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (activeSpace R v).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (activeSpace R v).smul_mem c hx

/-- Restriction to the active span realizes the sharp dimension bound by a genuine unitary involution. -/
def activeReflection (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    activeSpace R v ≃ₗᵢ[ℂ] activeSpace R v where
  toFun x := ⟨R x, reflection_mem_active R hR v x.property⟩
  invFun x := ⟨R x, reflection_mem_active R hR v x.property⟩
  left_inv x := Subtype.ext (hR x)
  right_inv x := Subtype.ext (hR x)
  map_add' x y := Subtype.ext (map_add R (x : E) (y : E))
  map_smul' c x := Subtype.ext (map_smul R c (x : E))
  norm_map' x := R.norm_map x

/-- Marks in the minimal realization. -/
def activeMark (R : E ≃ₗᵢ[ℂ] E) (v : ι → E) (i : ι) : activeSpace R v :=
  ⟨v i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩

omit [Fintype ι] in
@[simp] theorem activeReflection_involutive (R : E ≃ₗᵢ[ℂ] E)
    (hR : ∀ x, R (R x) = x) (v : ι → E) (x : activeSpace R v) :
    activeReflection R hR v (activeReflection R hR v x) = x := Subtype.ext (hR x)

omit [Fintype ι] in
/-- Passing to the minimal realization preserves both matrices exactly. -/
theorem active_matrices (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    Matrix.gram ℂ (activeMark R v) = Matrix.gram ℂ v ∧
      mixedGram (activeReflection R hR v) (activeMark R v) = mixedGram R v := ⟨rfl, rfl⟩

omit [Fintype ι] in
/-- The active feature Gram is the swap-symmetric block matrix of the two input Grams. -/
theorem doubledFeature_gram (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    Matrix.gram ℂ (doubledFeature R v) =
      Matrix.fromBlocks (Matrix.gram ℂ v) (mixedGram R v) (mixedGram R v) (Matrix.gram ℂ v) := by
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.gram, Matrix.of_apply, doubledFeature, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, mixedGram,
      R.inner_map_map, reflection_inner_left R hR]

/-- Every realization has the same minimal active dimension, read from the two sector ranks. -/
theorem active_dimension (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (doubledFeature R v))) =
      (Matrix.gram ℂ v + mixedGram R v).rank + (Matrix.gram ℂ v - mixedGram R v).rank := by
  rw [← gram_rank_span, doubledFeature_gram R hR, rank_fromBlocks_swap]

/-- No finite ambient realization can have dimension below the sum of the sector ranks. -/
theorem dimension_lower_bound [FiniteDimensional ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : ι → E) :
    (Matrix.gram ℂ v + mixedGram R v).rank + (Matrix.gram ℂ v - mixedGram R v).rank ≤
      Module.finrank ℂ E := by
  rw [← active_dimension R hR]
  exact Submodule.finrank_le _

#print axioms reflection_realizable_iff
#print axioms activeReflection
#print axioms active_matrices
#print axioms active_dimension
#print axioms dimension_lower_bound
end GaloisForLFunctions.RepresentationLifting.ReflectionGrams
