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

open scoped DirectSum InnerProduct InnerProductSpace
open Module

variable {𝕜 D W W' : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
variable [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']

section ActiveRange

variable [AddCommGroup D] [Module 𝕜 D]

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
    change ‖activeRangeLinearEquiv T S h ⟨T x, LinearMap.mem_range_self T x⟩‖ =
      ‖(⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range T)‖
    rw [Submodule.coe_norm, Submodule.coe_norm, activeRangeLinearEquiv_apply]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜) (S x),
      norm_sq_eq_re_inner (𝕜 := 𝕜) (T x), ← h x x]

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
    change ⟪(⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range T),
        ⟨T y, LinearMap.mem_range_self T y⟩⟫_𝕜 =
      ⟪U ⟨T x, LinearMap.mem_range_self T x⟩,
        U ⟨T y, LinearMap.mem_range_self T y⟩⟫_𝕜
    exact (U.inner_map_map _ _).symm

/-- A surjective map's active range is canonically isometric to its codomain. -/
noncomputable def rangeIsometryEquivOfSurjective (T : D →ₗ[𝕜] W)
    (hT : Function.Surjective T) : LinearMap.range T ≃ₗᵢ[𝕜] W where
  toFun z := z.1
  invFun w := ⟨w, (LinearMap.range_eq_top.mpr hT).symm ▸ Submodule.mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

/-- When both maps span their codomains, the active-range isometry is a unitary equivalence of the
whole codomains. -/
noncomputable def codomainIsometryEquivOfInnerEq (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S) : W ≃ₗᵢ[𝕜] W' :=
  (rangeIsometryEquivOfSurjective T hT).symm |>.trans
    ((activeRangeIsometryEquiv T S h).trans (rangeIsometryEquivOfSurjective S hS))

@[simp]
theorem codomainIsometryEquivOfInnerEq_apply (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S) (x : D) :
    codomainIsometryEquivOfInnerEq T S h hT hS (T x) = S x := by
  change ((activeRangeIsometryEquiv T S h)
    ⟨T x, (LinearMap.range_eq_top.mpr hT).symm ▸ Submodule.mem_top⟩ :
    LinearMap.range S) = S x
  exact activeRangeLinearEquiv_apply T S h x

/-- A codomain isometry carrying a surjective map to another one is unique. -/
theorem codomainIsometryEquivOfInnerEq_unique (T : D →ₗ[𝕜] W) (S : D →ₗ[𝕜] W')
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜)
    (hT : Function.Surjective T) (hS : Function.Surjective S)
    (U : W ≃ₗᵢ[𝕜] W') (hU : ∀ x, U (T x) = S x) :
    U = codomainIsometryEquivOfInnerEq T S h hT hS := by
  ext w
  rcases hT w with ⟨x, rfl⟩
  rw [hU, codomainIsometryEquivOfInnerEq_apply]

section SameFiniteCodomain

variable [FiniteDimensional 𝕜 W]

/-- The active-range isometry for two maps into the same finite-dimensional codomain, regarded as
an isometry into that codomain. -/
noncomputable def activeRangeIsometryInto (T S : D →ₗ[𝕜] W)
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) :
    LinearMap.range T →ₗᵢ[𝕜] W :=
  (LinearMap.range S).subtypeₗᵢ.comp
    (activeRangeIsometryEquiv T S h).toLinearIsometry

omit [FiniteDimensional 𝕜 W] in
@[simp]
theorem activeRangeIsometryInto_apply (T S : D →ₗ[𝕜] W)
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) (x : D) :
    activeRangeIsometryInto T S h ⟨T x, LinearMap.mem_range_self T x⟩ = S x :=
  activeRangeIsometryEquiv_apply T S h x

/-- An isometry endomorphism of a finite-dimensional space is surjective. -/
theorem finiteDimensional_linearIsometry_surjective (U : W →ₗᵢ[𝕜] W) :
    Function.Surjective U :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp U.injective

/-- Extend the canonical active-range isometry to a unitary of the whole common codomain. -/
noncomputable def codomainUnitaryOfInnerEq (T S : D →ₗ[𝕜] W)
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) : W ≃ₗᵢ[𝕜] W :=
  let U := (activeRangeIsometryInto T S h).extend
  LinearIsometryEquiv.ofSurjective U (finiteDimensional_linearIsometry_surjective U)

@[simp]
theorem codomainUnitaryOfInnerEq_apply (T S : D →ₗ[𝕜] W)
    (h : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) (x : D) :
    codomainUnitaryOfInnerEq T S h (T x) = S x := by
  change (activeRangeIsometryInto T S h).extend (T x) = S x
  calc
    (activeRangeIsometryInto T S h).extend (T x) =
        activeRangeIsometryInto T S h ⟨T x, LinearMap.mem_range_self T x⟩ :=
      LinearIsometry.extend_apply (activeRangeIsometryInto T S h)
        ⟨T x, LinearMap.mem_range_self T x⟩
    _ = S x := activeRangeIsometryInto_apply T S h x

/-- Same-codomain polar fibre classification in inner-product form. -/
theorem innerKernel_eq_iff_exists_codomainUnitary (T S : D →ₗ[𝕜] W) :
    (∀ x y, ⟪T x, T y⟫_𝕜 = ⟪S x, S y⟫_𝕜) ↔
      ∃ U : W ≃ₗᵢ[𝕜] W, ∀ x, U (T x) = S x := by
  constructor
  · intro h
    exact ⟨codomainUnitaryOfInnerEq T S h, codomainUnitaryOfInnerEq_apply T S h⟩
  · rintro ⟨U, hU⟩ x y
    rw [← hU x, ← hU y]
    exact (U.inner_map_map _ _).symm

end SameFiniteCodomain

end ActiveRange

section Adjoint

variable [NormedAddCommGroup D] [InnerProductSpace 𝕜 D]
variable [FiniteDimensional 𝕜 D] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 W']

local instance nomologicalCrossGramLocalInst1 : CompleteSpace D := FiniteDimensional.complete 𝕜 D
local instance nomologicalCrossGramLocalInst2 : CompleteSpace W := FiniteDimensional.complete 𝕜 W
local instance nomologicalCrossGramLocalInst3 : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'

/-- The positive Gram operator of a continuous linear map. -/
noncomputable def gram (T : D →L[𝕜] W) : D →L[𝕜] D := T† ∘L T

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
    change ⟪x, ContinuousLinearMap.adjoint T (T y)⟫_𝕜 =
      ⟪x, ContinuousLinearMap.adjoint S (S y)⟫_𝕜
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

/-- Theorem 5.1 of the leading formal-law card: equality of two Gram operators into the same
finite-dimensional Hermitian codomain is exactly left multiplication by a codomain unitary. -/
theorem gram_eq_iff_exists_codomainUnitary (T S : D →L[𝕜] W) :
    gram T = gram S ↔ ∃ U : W ≃ₗᵢ[𝕜] W, ∀ x, U (T x) = S x := by
  rw [gram_eq_iff_inner_eq]
  exact innerKernel_eq_iff_exists_codomainUnitary T.toLinearMap S.toLinearMap

/-- The Gram operator has exactly the same kernel as the original map. -/
theorem ker_gram (T : D →L[𝕜] W) : LinearMap.ker (gram T).toLinearMap = T.ker := by
  simpa [gram] using T.ker_adjoint_comp_self

/-- The Gram operator has the same finite rank as the original map. -/
theorem finrank_range_gram (T : D →L[𝕜] W) :
    finrank 𝕜 (LinearMap.range (gram T).toLinearMap) = finrank 𝕜 T.range := by
  have hg := LinearMap.finrank_range_add_finrank_ker (gram T).toLinearMap
  have hT := LinearMap.finrank_range_add_finrank_ker T.toLinearMap
  rw [ker_gram T] at hg
  omega

/-- Every singular value squared is an eigenvalue of the Gram operator. -/
theorem gram_hasEigenvalue_sq_singularValues (T : D →L[𝕜] W) {n : ℕ}
    (hn : n < finrank 𝕜 D) :
    Module.End.HasEigenvalue (gram T).toLinearMap (T.toLinearMap.singularValues n ^ 2) := by
  simpa only [gram, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.adjoint_toLinearMap] using
      T.toLinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues hn

/-- The nonzero singular-value indices are exactly the indices below the rank of the map. -/
theorem support_singularValues_eq_range_rank (T : D →L[𝕜] W) :
    T.toLinearMap.singularValues.support = Finset.range (finrank 𝕜 T.range) :=
  T.toLinearMap.support_singularValues

end Adjoint

section Family

variable {ι : Type*} {V : ι → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

noncomputable local instance : DecidableEq ι := Classical.decEq ι

/-- Algebraic synthesis map for a family with possibly different source spaces. -/
noncomputable def synthesis (T : ∀ i, V i →ₗ[𝕜] W) : (⨁ i, V i) →ₗ[𝕜] W :=
  DirectSum.toModule 𝕜 ι W T

@[simp]
theorem synthesis_of (T : ∀ i, V i →ₗ[𝕜] W) (i : ι) (x : V i) :
    synthesis T (DirectSum.of V i x) = T i x :=
  DirectSum.toAddMonoid_of (fun i ↦ (T i).toAddMonoidHom) i x

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
      | of j y => simpa using h i j x y
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
              exact ⟨DirectSum.of V i x, synthesis_of T i x⟩⟩ :
            LinearMap.range (synthesis S)) : W') = S i x := by
  constructor
  · intro h
    let hs := synthesis_inner_eq_of_crossInner_eq T S h
    refine ⟨activeRangeIsometryEquiv (synthesis T) (synthesis S) hs, ?_, ?_⟩
    · intro i x
      simpa only [synthesis_of] using
        activeRangeIsometryEquiv_apply (synthesis T) (synthesis S) hs
          (DirectSum.of V i x)
    · intro U hU
      apply activeRangeIsometryEquiv_unique (synthesis T) (synthesis S) hs U
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i x => simpa only [synthesis_of] using hU i x
      | add x y hx hy =>
          have hxy :
              (⟨synthesis T (x + y), LinearMap.mem_range_self (synthesis T) (x + y)⟩ :
                  LinearMap.range (synthesis T)) =
                ⟨synthesis T x, LinearMap.mem_range_self (synthesis T) x⟩ +
                  ⟨synthesis T y, LinearMap.mem_range_self (synthesis T) y⟩ := by
            ext
            exact map_add (synthesis T) x y
          rw [hxy, map_add]
          simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  · rintro ⟨U, hU, _⟩ i j x y
    rw [← hU i x, ← hU j y]
    change ⟪(⟨T i x, by exact ⟨DirectSum.of V i x, synthesis_of T i x⟩⟩ :
        LinearMap.range (synthesis T)),
      ⟨T j y, by exact ⟨DirectSum.of V j y, synthesis_of T j y⟩⟩⟫_𝕜 =
      ⟪U ⟨T i x, by exact ⟨DirectSum.of V i x, synthesis_of T i x⟩⟩,
        U ⟨T j y, by exact ⟨DirectSum.of V j y, synthesis_of T j y⟩⟩⟫_𝕜
    exact (U.inner_map_map _ _).symm

end Family

section FamilyAdjoint

variable {ι : Type*} {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
variable [∀ i, FiniteDimensional 𝕜 (V i)]
variable [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 W']

noncomputable local instance : DecidableEq ι := Classical.decEq ι

local instance (i : ι) : CompleteSpace (V i) := FiniteDimensional.complete 𝕜 (V i)
local instance nomologicalCrossGramLocalInst4 : CompleteSpace W := FiniteDimensional.complete 𝕜 W
local instance nomologicalCrossGramLocalInst5 : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'

/-- The `(i,j)` block of the cross-Gram packet of a family. -/
noncomputable def crossGram (T : ∀ i, V i →L[𝕜] W) (i j : ι) : V j →L[𝕜] V i :=
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
    change ⟪x, ContinuousLinearMap.adjoint (T i) (T j y)⟫_𝕜 =
      ⟪x, ContinuousLinearMap.adjoint (S i) (S j y)⟫_𝕜
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
              exact ⟨DirectSum.of V i x, synthesis_of (fun i ↦ (T i).toLinearMap) i x⟩⟩ :
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
      change codomainIsometryEquivOfInnerEq
        (synthesis fun i ↦ (T i).toLinearMap)
        (synthesis fun i ↦ (S i).toLinearMap) hs hT hS (T i x) = S i x
      simpa using codomainIsometryEquivOfInnerEq_apply
        (synthesis fun i ↦ (T i).toLinearMap)
        (synthesis fun i ↦ (S i).toLinearMap) hs hT hS (DirectSum.of V i x)
    · intro U' hU'
      apply codomainIsometryEquivOfInnerEq_unique
        (synthesis fun i ↦ (T i).toLinearMap)
        (synthesis fun i ↦ (S i).toLinearMap) hs hT hS U'
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of i x => simpa using hU' i x
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · rintro ⟨U, hU, _⟩ i j x y
    rw [← hU i x, ← hU j y]
    exact (U.inner_map_map _ _).symm

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
  · norm_num
  · rintro ⟨U, h₁, h₂⟩
    have h : (1 : ℂ) = -1 := h₁.symm.trans h₂
    norm_num at h

end HilbertMetric.NomologicalCrossGram
