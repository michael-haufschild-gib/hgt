import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cross-Gram reconstruction

The Gram operator of a finite-dimensional Hilbert-space map determines the map up to one
isometry of its active output range.  For a family of maps with unrelated source spaces, the full
cross-Gram packet determines the whole family up to one common active-range isometry.  Keeping
only the diagonal Gram operators does not determine the relative phases.
-/

namespace HilbertMetric.NomologicalCrossGram

open scoped DirectSum

variable {𝕜 D W W' : Type*} [RCLike 𝕜]
variable [AddCommGroup D] [Module 𝕜 D]
variable [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
variable [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']

/-- Equality of all inner products of two maps forces equality of their kernels. -/
theorem ker_eq_of_inner_eq (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) : T.ker = S.ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    rw [← h x x, hx, inner_zero_left]
  · intro hx
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    rw [h x x, hx, inner_zero_left]

/-- Linear equivalence between the active ranges of two maps with identical inner-product
kernels. -/
noncomputable def activeRangeLinearEquiv (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) :
    LinearMap.range T ≃ₗ[𝕜] LinearMap.range S :=
  T.quotKerEquivRange.symm |>.trans <|
    (Submodule.quotEquivOfEq T.ker S.ker (ker_eq_of_inner_eq T S h)).trans
      S.quotKerEquivRange

@[simp]
theorem activeRangeLinearEquiv_apply (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) (x : D) :
    ((activeRangeLinearEquiv T S h
      ⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range S) : W') = S x := by
  simp [activeRangeLinearEquiv]

/-- The canonical active-range equivalence is an isometry. -/
noncomputable def activeRangeIsometryEquiv (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) :
    LinearMap.range T ≃ₗᵢ[𝕜] LinearMap.range S where
  toLinearEquiv := activeRangeLinearEquiv T S h
  norm_map' z := by
    rcases z with ⟨_, x, rfl⟩
    change ‖S x‖ = ‖T x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner, norm_sq_eq_re_inner, ← h x x]

@[simp]
theorem activeRangeIsometryEquiv_apply (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) (x : D) :
    ((activeRangeIsometryEquiv T S h
      ⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range S) : W') = S x :=
  activeRangeLinearEquiv_apply T S h x

/-- The active-range isometry carrying one map to the other is unique. -/
theorem activeRangeIsometryEquiv_unique (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (U : LinearMap.range T ≃ₗᵢ[𝕜] LinearMap.range S)
    (hU : ∀ x, ((U ⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range S) : W') = S x) :
    U = activeRangeIsometryEquiv T S h := by
  ext z
  rcases z with ⟨_, x, rfl⟩
  apply Subtype.ext
  rw [hU, activeRangeIsometryEquiv_apply]

/-- Exact phase quotient in inner-product form: equality of Gram kernels is equivalent to a unique
isometry between the active output ranges carrying one map to the other. -/
theorem innerKernel_eq_iff_existsUnique_activeRangeIsometry (T : D →ₗ[𝕜] W)
    (S : D →ₗ[𝕜] W') :
    (∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) ↔
      ∃! U : LinearMap.range T ≃ₗᵢ[𝕜] LinearMap.range S,
        ∀ x, ((U ⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range S) : W') = S x := by
  constructor
  · intro h
    refine ⟨activeRangeIsometryEquiv T S h, activeRangeIsometryEquiv_apply T S h, ?_⟩
    intro U hU
    exact activeRangeIsometryEquiv_unique T S h U hU
  · rintro ⟨U, hU, _⟩ x y
    rw [← hU x, ← hU y]
    exact U.inner_map_map _ _

/-- When both maps span their codomains, the active-range isometry is a unitary equivalence of the
whole codomains. -/
noncomputable def codomainIsometryEquivOfInnerEq (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S) : W ≃ₗᵢ[𝕜] W' where
  toLinearEquiv :=
    (T.quotKerEquivOfSurjective hT).symm |>.trans <|
      (Submodule.quotEquivOfEq T.ker S.ker (ker_eq_of_inner_eq T S h)).trans
        (S.quotKerEquivOfSurjective hS)
  norm_map' w := by
    rcases hT w with ⟨x, rfl⟩
    change ‖S x‖ = ‖T x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner, norm_sq_eq_re_inner, ← h x x]

@[simp]
theorem codomainIsometryEquivOfInnerEq_apply (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S) (x : D) :
    codomainIsometryEquivOfInnerEq T S h hT hS (T x) = S x := by
  simp [codomainIsometryEquivOfInnerEq]

/-- A codomain isometry carrying a surjective map to another one is unique. -/
theorem codomainIsometryEquivOfInnerEq_unique (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S)
    (U : W ≃ₗᵢ[𝕜] W') (hU : ∀ x, U (T x) = S x) :
    U = codomainIsometryEquivOfInnerEq T S h hT hS := by
  ext w
  rcases hT w with ⟨x, rfl⟩
  rw [hU, codomainIsometryEquivOfInnerEq_apply]

section Adjoint

variable [FiniteDimensional 𝕜 D] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 W']

local instance : CompleteSpace D := FiniteDimensional.complete 𝕜 D
local instance : CompleteSpace W := FiniteDimensional.complete 𝕜 W
local instance : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'

/-- The positive Gram operator of a continuous linear map. -/
def gram (T : D →L[𝕜] W) : D →L[𝕜] D := T† ∘L T

/-- Equality of positive Gram operators is equivalent to equality of all image inner products. -/
theorem gram_eq_iff_inner_eq (T : D →L[𝕜] W) (S : D →L[𝕜] W') :
    gram T = gram S ↔ ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜 := by
  constructor
  · intro h x y
    rw [← T.adjoint_inner_right x (T y), ← S.adjoint_inner_right x (S y)]
    change ⟪x, gram T y⟫_𝕜 = ⟪x, gram S y⟫_𝕜
    rw [h]
  · intro h
    ext y
    apply ext_inner_left 𝕜
    intro x
    change ⟪x, gram T y⟫_𝕜 = ⟪x, gram S y⟫_𝕜
    rw [T.adjoint_inner_right, S.adjoint_inner_right, h]

/-- Exact phase quotient stated with adjoint Gram operators. -/
theorem gram_eq_iff_existsUnique_activeRangeIsometry (T : D →L[𝕜] W)
    (S : D →L[𝕜] W') :
    gram T = gram S ↔
      ∃! U : LinearMap.range T.toLinearMap ≃ₗᵢ[𝕜] LinearMap.range S.toLinearMap,
        ∀ x,
          ((U ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩ :
            LinearMap.range S.toLinearMap) : W') = S x := by
  rw [gram_eq_iff_inner_eq]
  exact innerKernel_eq_iff_existsUnique_activeRangeIsometry T.toLinearMap S.toLinearMap

/-- The Gram operator has exactly the same kernel as the original map. -/
theorem ker_gram (T : D →L[𝕜] W) : LinearMap.ker (gram T).toLinearMap = T.ker := by
  simpa [gram] using T.ker_adjoint_comp_self

/-- The Gram operator has the same finite rank as the original map. -/
theorem finrank_range_gram (T : D →L[𝕜] W) :
    finrank 𝕜 (LinearMap.range (gram T).toLinearMap) = finrank 𝕜 T.range := by
  simpa [gram] using T.finrank_range_adjoint_comp_self

/-- Every singular value squared is an eigenvalue of the Gram operator. -/
theorem gram_hasEigenvalue_sq_singularValues (T : D →L[𝕜] W) {n : ℕ}
    (hn : n < finrank 𝕜 D) :
    Module.End.HasEigenvalue (gram T).toLinearMap (T.toLinearMap.singularValues n ^ 2) := by
  simpa [gram] using T.toLinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues hn

/-- The nonzero singular-value indices are exactly the indices below the rank of the map. -/
theorem support_singularValues_eq_range_rank (T : D →L[𝕜] W) :
    T.toLinearMap.singularValues.support = Finset.range (finrank 𝕜 T.range) :=
  T.toLinearMap.support_singularValues

end Adjoint

section Family

variable {ι : Type*} {V : ι → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

/-- Algebraic synthesis map for a family with possibly different source spaces. -/
def synthesis (T : ∀ i, V i →ₗ[𝕜] W) : (⨁ i, V i) →ₗ[𝕜] W :=
  DirectSum.toModule 𝕜 ι W T

@[simp]
theorem synthesis_lof (T : ∀ i, V i →ₗ[𝕜] W) (i : ι) (x : V i) :
    synthesis T (DirectSum.lof 𝕜 ι V i x) = T i x :=
  DirectSum.toModule_lof i x

/-- Cross-inner-product equality on every pair of legs extends to equality on the two synthesis
maps. -/
theorem synthesis_inner_eq_of_crossInner_eq (T : ∀ i, V i →ₗ[𝕜] W)
    (S : ∀ i, V i →ₗ[𝕜] W')
    (h : ∀ i j x y, ⟪T i x, T j y⟫_𝕜 = ⟪S i x, S j y⟫_𝕜) :
    ∀ x y, ⟪synthesis T x, synthesis T y⟫_𝕜 =
      ⟪synthesis S x, synthesis S y⟫_𝕜 := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
      intro y
      induction y using DirectSum.induction_on with
      | zero => simp
      | of j y => simpa [← DirectSum.lof_eq_of] using h i j x y
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x y hx hy =>
      intro z
      simp only [map_add, inner_add_left, hx z, hy z]

/-- Equality of the full cross-Gram packet reconstructs all relative phases, leaving one common
isometry of the total active output range. -/
theorem crossInner_eq_iff_existsUnique_commonRangeIsometry (T : ∀ i, V i →ₗ[𝕜] W)
    (S : ∀ i, V i →ₗ[𝕜] W') :
    (∀ i j x y, ⟪T i x, T j y⟫_𝕜 = ⟪S i x, S j y⟫_𝕜) ↔
      ∃! U : LinearMap.range (synthesis T) ≃ₗᵢ[𝕜] LinearMap.range (synthesis S),
        ∀ i x,
          ((U ⟨T i x, by
              exact ⟨DirectSum.lof 𝕜 ι V i x, synthesis_lof T i x⟩⟩ :
            LinearMap.range (synthesis S)) : W') = S i x := by
  constructor
  · intro h
    let hs := synthesis_inner_eq_of_crossInner_eq T S h
    refine ⟨activeRangeIsometryEquiv (synthesis T) (synthesis S) hs, ?_, ?_⟩
    · intro i x
      simpa only [synthesis_lof] using
        activeRangeIsometryEquiv_apply (synthesis T) (synthesis S) hs
          (DirectSum.lof 𝕜 ι V i x)
    · intro U hU
      apply activeRangeIsometryEquiv_unique (synthesis T) (synthesis S) hs U
      intro z
      induction z using DirectSum.induction_on with
      | zero =>
          apply Subtype.ext
          simp
      | of i x =>
          apply Subtype.ext
          simpa only [← DirectSum.lof_eq_of, synthesis_lof] using hU i x
      | add x y hx hy =>
          apply Subtype.ext
          simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) (congrArg Subtype.val hx)
            (congrArg Subtype.val hy)
  · rintro ⟨U, hU, _⟩ i j x y
    rw [← hU i x, ← hU j y]
    exact U.inner_map_map _ _

end Family

section FamilyAdjoint

variable {ι : Type*} {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
variable [∀ i, FiniteDimensional 𝕜 (V i)]
variable [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 W']

local instance (i : ι) : CompleteSpace (V i) := FiniteDimensional.complete 𝕜 (V i)
local instance : CompleteSpace W := FiniteDimensional.complete 𝕜 W
local instance : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'

/-- The `(i,j)` block of the cross-Gram packet of a family. -/
def crossGram (T : ∀ i, V i →L[𝕜] W) (i j : ι) : V j →L[𝕜] V i :=
  (T i)† ∘L T j

/-- Equality of cross-Gram blocks is equivalent to equality of every cross inner product. -/
theorem crossGram_eq_iff_crossInner_eq (T : ∀ i, V i →L[𝕜] W)
    (S : ∀ i, V i →L[𝕜] W') :
    (∀ i j, crossGram T i j = crossGram S i j) ↔
      ∀ i j x y, ⟪T i x, T j y⟫_𝕜 = ⟪S i x, S j y⟫_𝕜 := by
  constructor
  · intro h i j x y
    rw [← (T i).adjoint_inner_right x (T j y), ← (S i).adjoint_inner_right x (S j y)]
    change ⟪x, crossGram T i j y⟫_𝕜 = ⟪x, crossGram S i j y⟫_𝕜
    rw [h]
  · intro h i j
    ext y
    apply ext_inner_left 𝕜
    intro x
    change ⟪x, crossGram T i j y⟫_𝕜 = ⟪x, crossGram S i j y⟫_𝕜
    rw [(T i).adjoint_inner_right, (S i).adjoint_inner_right, h]

/-- Full adjoint cross-Gram packets reconstruct a family up to one common active-range
isometry. -/
theorem crossGramPacket_eq_iff_existsUnique_commonRangeIsometry
    (T : ∀ i, V i →L[𝕜] W) (S : ∀ i, V i →L[𝕜] W') :
    (∀ i j, crossGram T i j = crossGram S i j) ↔
      ∃! U :
          LinearMap.range (synthesis fun i ↦ (T i).toLinearMap) ≃ₗᵢ[𝕜]
            LinearMap.range (synthesis fun i ↦ (S i).toLinearMap),
        ∀ i x,
          ((U ⟨T i x, by
              exact ⟨DirectSum.lof 𝕜 ι V i x, synthesis_lof (fun i ↦ (T i).toLinearMap) i x⟩⟩ :
            LinearMap.range (synthesis fun i ↦ (S i).toLinearMap)) : W') = S i x := by
  rw [crossGram_eq_iff_crossInner_eq]
  exact crossInner_eq_iff_existsUnique_commonRangeIsometry
    (fun i ↦ (T i).toLinearMap) (fun i ↦ (S i).toLinearMap)

/-- If both families jointly span their codomains, equality of full cross-Gram packets gives a
unique unitary equivalence carrying every leg of one family to the corresponding leg of the other. -/
theorem crossGramPacket_eq_iff_existsUnique_codomainIsometry_of_jointly_surjective
    (T : ∀ i, V i →L[𝕜] W) (S : ∀ i, V i →L[𝕜] W')
    (hT : Function.Surjective (synthesis fun i ↦ (T i).toLinearMap))
    (hS : Function.Surjective (synthesis fun i ↦ (S i).toLinearMap)) :
    (∀ i j, crossGram T i j = crossGram S i j) ↔
      ∃! U : W ≃ₗᵢ[𝕜] W', ∀ i x, U (T i x) = S i x := by
  rw [crossGram_eq_iff_crossInner_eq]
  constructor
  · intro h
    let hs := synthesis_inner_eq_of_crossInner_eq
      (fun i ↦ (T i).toLinearMap) (fun i ↦ (S i).toLinearMap) h
    let U := codomainIsometryEquivOfInnerEq
      (synthesis fun i ↦ (T i).toLinearMap)
      (synthesis fun i ↦ (S i).toLinearMap) hs hT hS
    refine ⟨U, ?_, ?_⟩
    · intro i x
      simpa only [synthesis_lof] using codomainIsometryEquivOfInnerEq_apply
        (synthesis fun i ↦ (T i).toLinearMap)
        (synthesis fun i ↦ (S i).toLinearMap) hs hT hS (DirectSum.lof 𝕜 ι V i x)
    · intro U' hU'
      apply codomainIsometryEquivOfInnerEq_unique
        (synthesis fun i ↦ (T i).toLinearMap)
        (synthesis fun i ↦ (S i).toLinearMap) hs hT hS U'
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i x => simpa only [← DirectSum.lof_eq_of, synthesis_lof] using hU' i x
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · rintro ⟨U, hU, _⟩ i j x y
    rw [← hU i x, ← hU j y]
    exact U.inner_map_map _ _

end FamilyAdjoint

/-- Two scalar legs can have identical individual Gram shadows and opposite cross-Gram phase. -/
theorem scalar_relative_phase_counterexample :
    let T₁ : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    let T₂ : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    let S₁ : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    let S₂ : ℂ →ₗ[ℂ] ℂ := -LinearMap.id
    (∀ z, ⟪T₁ z, T₁ z⟫_ℂ = ⟪S₁ z, S₁ z⟫_ℂ) ∧
      (∀ z, ⟪T₂ z, T₂ z⟫_ℂ = ⟪S₂ z, S₂ z⟫_ℂ) ∧
      ⟪T₁ 1, T₂ 1⟫_ℂ ≠ ⟪S₁ 1, S₂ 1⟫_ℂ ∧
      ¬ ∃ U : ℂ ≃ₗᵢ[ℂ] ℂ, (U (T₁ 1) = S₁ 1 ∧ U (T₂ 1) = S₂ 1) := by
  dsimp
  constructor
  · simp
  constructor
  · intro z
    simp
  constructor
  · simp
  · rintro ⟨U, h₁, h₂⟩
    exact one_ne_neg_one (h₁.symm.trans h₂)

end HilbertMetric.NomologicalCrossGram
