import Mathlib

/-!
# Matrix operators on `ℓ²(I)`

A bounded operator `T` on `ℓ²(I)` *has matrix* `K` when `(T e_j)_i = K i j` for the standard
basis vectors `e_j`.  Every column of such a matrix is square summable, so a single
non-square-summable column rules out every bounded realization.  Bounded operators are
determined by their matrices.  Rank-one operators `z ↦ ⟪y, z⟫ x` have matrix
`x_i \overline{y_j}` and are compact; their finite combinations have range inside the span of
the left vectors.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*}

theorem summable_norm_sq_lp (f : lp (fun _ : I => ℂ) 2) :
    Summable (fun i => ‖(f : I → ℂ) i‖ ^ 2) := by
  have h := (lp.memℓp f).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
  refine h.congr fun i => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two]

/-- A square-summable real sequence as an `ℓ²` vector. -/
def lpOfReal (f : I → ℝ) (hf : Summable (fun i => f i ^ 2)) : lp (fun _ : I => ℂ) 2 :=
  ⟨fun i => (f i : ℂ), by
    refine memℓp_gen (hf.congr fun i => ?_)
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]⟩

@[simp] theorem lpOfReal_apply (f : I → ℝ) (hf : Summable (fun i => f i ^ 2)) (i : I) :
    (lpOfReal f hf : I → ℂ) i = (f i : ℂ) := rfl

variable [DecidableEq I]


/-- The standard basis vector `e_j` of `ℓ²(I)`. -/
def lpBasisVec (j : I) : lp (fun _ : I => ℂ) 2 := lp.single 2 j (1 : ℂ)

/-- `T` has matrix `K` in the standard basis: `(T e_j)_i = K i j`. -/
def HasLpMatrix (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (K : I → I → ℂ) : Prop :=
  ∀ i j, (T (lpBasisVec j) : I → ℂ) i = K i j

/-- Every column of a bounded operator's matrix is square summable. -/
theorem HasLpMatrix.summable_col {T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K : I → I → ℂ} (h : HasLpMatrix T K) (j : I) : Summable (fun i => ‖K i j‖ ^ 2) :=
  (summable_norm_sq_lp (T (lpBasisVec j))).congr fun i => by rw [h i j]

/-- **Column obstruction.** A matrix with one non-square-summable column is the matrix of no
bounded operator. -/
theorem not_exists_hasLpMatrix_of_col {K : I → I → ℂ} {j : I}
    (hj : ¬ Summable (fun i => ‖K i j‖ ^ 2)) :
    ¬ ∃ T, HasLpMatrix T K := fun ⟨_, hT⟩ => hj (hT.summable_col j)

/-- A bounded operator is determined by its matrix. -/
theorem HasLpMatrix.ext {T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K : I → I → ℂ} (hT : HasLpMatrix T K) (hS : HasLpMatrix S K) : T = S := by
  ext1 f
  have hsum := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by norm_num) f
  have hcol : ∀ i, T (lp.single 2 i ((f : I → ℂ) i)) = S (lp.single 2 i ((f : I → ℂ) i)) := by
    intro i
    have hsingle : lp.single 2 i ((f : I → ℂ) i) = ((f : I → ℂ) i) • lpBasisVec i := by
      rw [lpBasisVec, ← lp.single_smul, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, map_smul]
    congr 1
    ext k
    rw [hT k i, hS k i]
  have h1 := hsum.mapL T
  have h2 := hsum.mapL S
  simp only [hcol] at h1
  exact h1.unique h2

theorem HasLpMatrix.add {T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K L : I → I → ℂ} (hT : HasLpMatrix T K) (hS : HasLpMatrix S L) :
    HasLpMatrix (T + S) (fun i j => K i j + L i j) := by
  intro i j
  simp [hT i j, hS i j]

theorem HasLpMatrix.sub {T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K L : I → I → ℂ} (hT : HasLpMatrix T K) (hS : HasLpMatrix S L) :
    HasLpMatrix (T - S) (fun i j => K i j - L i j) := by
  intro i j
  simp [hT i j, hS i j]

theorem HasLpMatrix.smul {T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K : I → I → ℂ} (hT : HasLpMatrix T K) (c : ℂ) :
    HasLpMatrix (c • T) (fun i j => c * K i j) := by
  intro i j
  simp [hT i j]

theorem HasLpMatrix.congr {T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2}
    {K L : I → I → ℂ} (hT : HasLpMatrix T K) (h : ∀ i j, K i j = L i j) : HasLpMatrix T L :=
  fun i j => (hT i j).trans (h i j)

theorem inner_lpBasisVec_right (y : lp (fun _ : I => ℂ) 2) (j : I) :
    ⟪y, lpBasisVec j⟫_ℂ = conj ((y : I → ℂ) j) := by
  rw [lpBasisVec, lp.inner_single_right]
  simp

/-- The rank-one operator `z ↦ ⟪y, z⟫ x` has matrix `x_i \overline{y_j}`. -/
theorem hasLpMatrix_rankOne (x y : lp (fun _ : I => ℂ) 2) :
    HasLpMatrix (rankOne ℂ x y) (fun i j => (x : I → ℂ) i * conj ((y : I → ℂ) j)) := by
  intro i j
  rw [rankOne_apply, inner_lpBasisVec_right, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Rank-one operators on a complex Hilbert space are compact. -/
theorem isCompactOperator_innerRankOne {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x : E) (y : F) :
    IsCompactOperator (rankOne ℂ x y) := by
  have h1 : IsCompactOperator (innerSL ℂ y) := isCompactOperator_of_locallyCompactSpace_dom _
  have h2 := h1.clm_comp ((1 : ℂ →L[ℂ] ℂ).smulRight x)
  have heq : (rankOne ℂ x y : F → E) = ((1 : ℂ →L[ℂ] ℂ).smulRight x) ∘ (innerSL ℂ y) := by
    funext z
    simp [rankOne_apply]
  rw [heq]
  exact h2

theorem range_rankOne_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x : E) (y : F) :
    LinearMap.range ((rankOne ℂ x y : F →L[ℂ] E) : F →ₗ[ℂ] E) ≤ Submodule.span ℂ {x} := by
  rintro _ ⟨z, rfl⟩
  rw [ContinuousLinearMap.coe_coe, rankOne_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- The antisymmetric wedge `x ∧ y = |x⟩⟨y| - |y⟩⟨x|`. -/
def lpWedge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) : E →L[ℂ] E :=
  rankOne ℂ x y - rankOne ℂ y x

theorem isCompactOperator_lpWedge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) : IsCompactOperator (lpWedge x y) :=
  (isCompactOperator_innerRankOne x y).sub (isCompactOperator_innerRankOne y x)

theorem range_lpWedge_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    LinearMap.range ((lpWedge x y : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤ Submodule.span ℂ {x, y} := by
  rintro _ ⟨z, rfl⟩
  simp only [lpWedge, ContinuousLinearMap.coe_coe, FunLike.coe_sub, Pi.sub_apply,
    rankOne_apply]
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    (Submodule.smul_mem _ _ (Submodule.subset_span ?_)) <;> simp

/-- An operator whose range lies in a span of two vectors has rank at most two. -/
theorem finrank_range_le_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →L[ℂ] E} {x y : E} (h : LinearMap.range ((T : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤ Submodule.span ℂ {x, y}) :
    Module.finrank ℂ (LinearMap.range ((T : E →L[ℂ] E) : E →ₗ[ℂ] E)) ≤ 2 := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ({x, y} : Set E)) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  calc Module.finrank ℂ (LinearMap.range ((T : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ Module.finrank ℂ (Submodule.span ℂ ({x, y} : Set E)) := Submodule.finrank_mono h
    _ ≤ ({x, y} : Finset E).card := by
        have := finrank_span_finset_le_card (R := ℂ) ({x, y} : Finset E)
        rw [Set.finrank, Finset.coe_pair] at this
        exact this
    _ ≤ 2 := Finset.card_le_two

/-- Bounded two-sided transport preserves compactness. -/
theorem isCompactOperator_transport {E F G H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G]
    [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : F →L[ℂ] G} (hK : IsCompactOperator K) (L : G →L[ℂ] H) (R : E →L[ℂ] F) :
    IsCompactOperator (L ∘L K ∘L R) :=
  (hK.comp_clm R).clm_comp L

end

end GaloisForLFunctions.HTGeometry
