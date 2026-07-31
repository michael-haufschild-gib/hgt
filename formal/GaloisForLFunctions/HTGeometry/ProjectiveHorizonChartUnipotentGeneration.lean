import GaloisForLFunctions.HTGeometry.SpecialLinearTransvectionGeneration
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Chart-unipotent generation of a projective horizon stabiliser

Fix a coordinate splitting `V = K^ι ⊕ K^κ` and read `K^κ` as the transverse subspace `W = S^⊥`
cut out by the covectors `e_i^*`, `i ∈ ι`.  The projective observer group attached to `S` is the
group of unimodular maps fixing `W` pointwise; in block form it is exactly

`[ A 0 ]`
`[ C 1 ]`,   `det A = 1`.

The chart translations of the affine charts with infinity hyperplane `ker e_i^*` contribute the
elementary transvections whose column index lies in `ι`.  This file proves that those
transvections generate the whole transverse stabiliser: the shear block `C` is cleared by the
transverse transvections, and the remaining `SL(K^ι)` factor is a product of transvections inside
`ι` by the general transvection-generation theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {K : Type*} [Field K]

/-! ## The transverse stabiliser -/

/-- The subgroup of unimodular maps of `K^(ι ⊕ κ)` fixing the transverse subspace `K^κ`
pointwise, i.e. whose transverse columns are the standard ones. -/
def transverseStabilizer (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Type*) [Field K] : Subgroup (SpecialLinearGroup (ι ⊕ κ) K) where
  carrier := {g | ∀ (k : κ) (x : ι ⊕ κ),
    (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x (Sum.inr k) =
      (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x (Sum.inr k)}
  one_mem' := by
    intro k x
    rw [Matrix.SpecialLinearGroup.coe_one]
  mul_mem' := by
    intro a b ha hb k x
    have hmul : ((a * b : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K) =
        (a : Matrix (ι ⊕ κ) (ι ⊕ κ) K) * (b : Matrix (ι ⊕ κ) (ι ⊕ κ) K) :=
      Matrix.SpecialLinearGroup.coe_mul a b
    rw [hmul, Matrix.mul_apply]
    have hrow : ∀ y, (a : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x y *
        (b : Matrix (ι ⊕ κ) (ι ⊕ κ) K) y (Sum.inr k) =
        (a : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x y * (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) y (Sum.inr k) :=
      fun y => by rw [hb k y]
    rw [Finset.sum_congr rfl fun y _ => hrow y, ← Matrix.mul_apply, Matrix.mul_one]
    exact ha k x
  inv_mem' := by
    intro a ha k x
    have hinv : ((a⁻¹ : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K) *
        (a : Matrix (ι ⊕ κ) (ι ⊕ κ) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h1 : (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x (Sum.inr k) =
        ∑ y, ((a⁻¹ : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K) x y *
          (a : Matrix (ι ⊕ κ) (ι ⊕ κ) K) y (Sum.inr k) := by
      rw [← Matrix.mul_apply, hinv]
    rw [h1, Finset.sum_congr rfl fun y _ => by rw [ha k y], ← Matrix.mul_apply, Matrix.mul_one]

/-- A unimodular map fixing the transverse subspace pointwise is the block matrix formed by its
own chart and shear blocks. -/
theorem coe_eq_fromBlocks_of_mem_transverseStabilizer {g : SpecialLinearGroup (ι ⊕ κ) K}
    (hg : g ∈ transverseStabilizer ι κ K) :
    (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) =
      Matrix.fromBlocks (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₁₁ 0
        (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₂₁ 1 := by
  have h12 : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₁₂ = 0 := by
    ext i k
    rw [Matrix.toBlocks₁₂]
    simpa using hg k (Sum.inl i)
  have h22 : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₂₂ = 1 := by
    ext k' k
    rw [Matrix.toBlocks₂₂]
    simpa [Matrix.one_apply] using hg k (Sum.inr k')
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K)]
  rw [h12, h22]

theorem mem_transverseStabilizer_of_coe_eq_fromBlocks {g : SpecialLinearGroup (ι ⊕ κ) K}
    {A : Matrix ι ι K} {C : Matrix κ ι K}
    (hACg : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) = Matrix.fromBlocks A 0 C 1) :
    g ∈ transverseStabilizer ι κ K := by
  intro k x
  rw [hACg]
  cases x <;> simp [Matrix.one_apply]

theorem mem_transverseStabilizer_iff {g : SpecialLinearGroup (ι ⊕ κ) K} :
    g ∈ transverseStabilizer ι κ K ↔
      ∃ (A : Matrix ι ι K) (C : Matrix κ ι K),
        (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) = Matrix.fromBlocks A 0 C 1 :=
  ⟨fun hg => ⟨_, _, coe_eq_fromBlocks_of_mem_transverseStabilizer hg⟩,
    fun ⟨_, _, hACg⟩ => mem_transverseStabilizer_of_coe_eq_fromBlocks hACg⟩

theorem det_toBlocks₁₁_of_mem_transverseStabilizer {g : SpecialLinearGroup (ι ⊕ κ) K}
    {A : Matrix ι ι K} {C : Matrix κ ι K}
    (hACg : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) = Matrix.fromBlocks A 0 C 1) :
    A.det = 1 := by
  have hdet : (Matrix.fromBlocks A 0 C (1 : Matrix κ κ K)).det = 1 := by
    rw [← hACg]; exact g.2
  rwa [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one] at hdet

/-! ## Chart transvections -/

/-- An elementary transvection whose column index is one of the chart directions `ι`.  These are
exactly the infinitesimal chart translations of the affine charts with infinity hyperplane
`ker e_i^*`. -/
structure ChartTransvection (ι κ K : Type*) where
  /-- Row index moved by the transvection. -/
  row : ι ⊕ κ
  /-- Chart direction whose covector the transvection uses. -/
  col : ι
  /-- The transvection is not a dilation. -/
  hne : row ≠ Sum.inl col
  /-- Transvection coefficient. -/
  coeff : K

/-- The matrix of a chart transvection. -/
def ChartTransvection.toMatrix (t : ChartTransvection ι κ K) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) K :=
  Matrix.transvection t.row (Sum.inl t.col) t.coeff

/-- The chart transvection as a unimodular matrix. -/
def ChartTransvection.toSL (t : ChartTransvection ι κ K) :
    SpecialLinearGroup (ι ⊕ κ) K :=
  ⟨t.toMatrix, Matrix.det_transvection_of_ne _ _ t.hne _⟩

/-- The set of chart transvections inside the special linear group. -/
def chartTransvectionSet (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Type*) [Field K] : Set (SpecialLinearGroup (ι ⊕ κ) K) :=
  Set.range (ChartTransvection.toSL : ChartTransvection ι κ K → SpecialLinearGroup (ι ⊕ κ) K)

/-- A matrix is a *chart-transvection product* when it is a finite product of chart
transvections. -/
def IsChartProduct (M : Matrix (ι ⊕ κ) (ι ⊕ κ) K) : Prop :=
  ∃ L : List (ChartTransvection ι κ K), M = (L.map ChartTransvection.toMatrix).prod

namespace IsChartProduct

theorem one : IsChartProduct (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) K) :=
  ⟨[], by simp⟩

theorem mul {A B : Matrix (ι ⊕ κ) (ι ⊕ κ) K}
    (hA : IsChartProduct A) (hB : IsChartProduct B) : IsChartProduct (A * B) := by
  obtain ⟨LA, rfl⟩ := hA
  obtain ⟨LB, rfl⟩ := hB
  exact ⟨LA ++ LB, by simp [List.prod_append]⟩

theorem single (t : ChartTransvection ι κ K) : IsChartProduct t.toMatrix :=
  ⟨[t], by simp⟩

end IsChartProduct

/-! ## Block identities -/

theorem fromBlocks_shear_mul (C C' : Matrix κ ι K) :
    (Matrix.fromBlocks (1 : Matrix ι ι K) 0 C (1 : Matrix κ κ K)) *
        (Matrix.fromBlocks (1 : Matrix ι ι K) 0 C' (1 : Matrix κ κ K)) =
      Matrix.fromBlocks (1 : Matrix ι ι K) 0 (C + C') (1 : Matrix κ κ K) := by
  rw [Matrix.fromBlocks_multiply]
  simp [add_comm]

omit [DecidableEq ι] in
theorem fromBlocks_block_mul (A A' : Matrix ι ι K) :
    (Matrix.fromBlocks A 0 0 (1 : Matrix κ κ K)) *
        (Matrix.fromBlocks A' 0 0 (1 : Matrix κ κ K)) =
      Matrix.fromBlocks (A * A') 0 0 (1 : Matrix κ κ K) := by
  rw [Matrix.fromBlocks_multiply]
  simp

omit [Fintype ι] [Fintype κ] in
theorem fromBlocks_shear_single (k : κ) (i : ι) (c : K) :
    Matrix.fromBlocks (1 : Matrix ι ι K) 0 (Matrix.single k i c) (1 : Matrix κ κ K) =
      Matrix.transvection (Sum.inr k : ι ⊕ κ) (Sum.inl i) c := by
  ext x y
  rw [Matrix.transvection]
  cases x <;> cases y <;> simp [Matrix.single_apply, Matrix.one_apply]

omit [Fintype ι] [Fintype κ] in
theorem fromBlocks_block_transvection (i j : ι) (c : K) :
    Matrix.fromBlocks (Matrix.transvection i j c) 0 0 (1 : Matrix κ κ K) =
      Matrix.transvection (Sum.inl i : ι ⊕ κ) (Sum.inl j) c := by
  ext x y
  rw [Matrix.transvection, Matrix.transvection]
  cases x <;> cases y <;> simp [Matrix.single_apply, Matrix.one_apply]

/-- The shear block is cleared by right division by the chart block. -/
theorem fromBlocks_eq_shear_mul_block (A : Matrix ι ι K) (C : Matrix κ ι K) (hA : A.det = 1) :
    Matrix.fromBlocks A 0 C (1 : Matrix κ κ K) =
      Matrix.fromBlocks (1 : Matrix ι ι K) 0 (C * A⁻¹) 1 *
        Matrix.fromBlocks A 0 0 (1 : Matrix κ κ K) := by
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hA]; exact isUnit_one)
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, hinv]

/-! ## Generation -/

/-- Every transverse shear is a product of chart transvections. -/
theorem isChartProduct_shear (C : Matrix κ ι K) :
    IsChartProduct (Matrix.fromBlocks (1 : Matrix ι ι K) 0 C 1) := by
  have key : ∀ t : Finset (κ × ι),
      IsChartProduct (Matrix.fromBlocks (1 : Matrix ι ι K) 0
        (∑ p ∈ t, Matrix.single p.1 p.2 (C p.1 p.2)) 1) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using IsChartProduct.one
    | insert p t hp ih =>
        rw [Finset.sum_insert hp, ← fromBlocks_shear_mul, fromBlocks_shear_single]
        exact (IsChartProduct.single ⟨Sum.inr p.1, p.2, by simp, C p.1 p.2⟩).mul ih
  have hC : (∑ p : κ × ι, Matrix.single p.1 p.2 (C p.1 p.2)) = C :=
    (Fintype.sum_prod_type _).trans (Matrix.matrix_eq_sum_single C).symm
  have h := key Finset.univ
  rwa [hC] at h

/-- Every unimodular chart block is a product of chart transvections. -/
theorem isChartProduct_block (A : Matrix ι ι K) (hA : A.det = 1) :
    IsChartProduct (Matrix.fromBlocks A 0 0 (1 : Matrix κ κ K)) := by
  obtain ⟨L, hL⟩ := isTransvectionProduct_of_det_eq_one A hA
  rw [hL]
  clear hL hA
  induction L with
  | nil => simpa using IsChartProduct.one
  | cons t L ih =>
      rw [List.map_cons, List.prod_cons, ← fromBlocks_block_mul,
        Matrix.TransvectionStruct.toMatrix, fromBlocks_block_transvection]
      exact (IsChartProduct.single
        ⟨Sum.inl t.i, t.j, by simpa using t.hij, t.c⟩).mul ih

/-- **Chart-unipotent generation, block form.**  Every unimodular map fixing the transverse
subspace pointwise is a product of chart transvections. -/
theorem isChartProduct_of_fromBlocks (A : Matrix ι ι K) (C : Matrix κ ι K) (hA : A.det = 1) :
    IsChartProduct (Matrix.fromBlocks A 0 C (1 : Matrix κ κ K)) := by
  rw [fromBlocks_eq_shear_mul_block A C hA]
  exact (isChartProduct_shear _).mul (isChartProduct_block A hA)

theorem mem_closure_of_chartListProd :
    ∀ (L : List (ChartTransvection ι κ K)) (g : SpecialLinearGroup (ι ⊕ κ) K),
      (g : Matrix (ι ⊕ κ) (ι ⊕ κ) K) = (L.map ChartTransvection.toMatrix).prod →
      g ∈ Subgroup.closure (chartTransvectionSet ι κ K) := by
  intro L
  induction L with
  | nil =>
      intro g hg
      have hg1 : g = 1 := Subtype.ext (by simpa using hg)
      rw [hg1]
      exact one_mem _
  | cons t L ih =>
      intro g hg
      have hinv : ((t.toSL⁻¹ : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K) *
          t.toMatrix = 1 := by
        rw [show t.toMatrix = (t.toSL : Matrix (ι ⊕ κ) (ι ⊕ κ) K) from rfl,
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      have hg' : ((t.toSL⁻¹ * g : SpecialLinearGroup (ι ⊕ κ) K) :
          Matrix (ι ⊕ κ) (ι ⊕ κ) K) = (L.map ChartTransvection.toMatrix).prod := by
        rw [Matrix.SpecialLinearGroup.coe_mul, hg, List.map_cons, List.prod_cons,
          ← mul_assoc, hinv, one_mul]
      have hmem := ih _ hg'
      have hgeq : g = t.toSL * (t.toSL⁻¹ * g) := (mul_inv_cancel_left t.toSL g).symm
      rw [hgeq]
      exact mul_mem (Subgroup.subset_closure ⟨t, rfl⟩) hmem

/-- **Chart-unipotent generation.**  The transvections attached to the chart directions `ι`
generate exactly the group of unimodular maps fixing the transverse subspace `K^κ` pointwise. -/
theorem closure_chartTransvectionSet_eq_transverseStabilizer :
    Subgroup.closure (chartTransvectionSet ι κ K) = transverseStabilizer ι κ K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩ k x
    show Matrix.transvection t.row (Sum.inl t.col) t.coeff x (Sum.inr k) = _
    rw [Matrix.transvection]
    simp
  · intro g hg
    obtain ⟨A, C, hACg⟩ := mem_transverseStabilizer_iff.1 hg
    have hA : A.det = 1 := det_toBlocks₁₁_of_mem_transverseStabilizer hACg
    obtain ⟨L, hL⟩ := isChartProduct_of_fromBlocks A C hA
    exact mem_closure_of_chartListProd L g (by rw [hACg, hL])


/-! ## Block parametrisation of the transverse stabiliser -/

/-- The chart block of a transverse-stabilising map, as a unimodular matrix. -/
def transverseChartBlock (g : transverseStabilizer ι κ K) : SpecialLinearGroup ι K :=
  ⟨((g : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₁₁,
    det_toBlocks₁₁_of_mem_transverseStabilizer
      (coe_eq_fromBlocks_of_mem_transverseStabilizer g.2)⟩

/-- The transverse shear block of a transverse-stabilising map. -/
def transverseShearBlock (g : transverseStabilizer ι κ K) : Matrix κ ι K :=
  ((g : SpecialLinearGroup (ι ⊕ κ) K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K).toBlocks₂₁

/-- The transverse-stabilising map assembled from a unimodular chart block and an arbitrary
transverse shear. -/
def transverseOfBlocks (A : SpecialLinearGroup ι K) (C : Matrix κ ι K) :
    transverseStabilizer ι κ K :=
  ⟨⟨Matrix.fromBlocks (A : Matrix ι ι K) 0 C 1, by
      rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]; exact A.2⟩,
    mem_transverseStabilizer_of_coe_eq_fromBlocks rfl⟩

/-- **Block parametrisation of the projective observer group.**  Fixing the transverse subspace
pointwise is exactly the data of a unimodular chart block together with an arbitrary transverse
shear, so the stabiliser is `SL(K^ι) × Hom(K^ι, K^κ)` as a set. -/
def transverseStabilizerEquiv :
    transverseStabilizer ι κ K ≃ SpecialLinearGroup ι K × Matrix κ ι K where
  toFun g := (transverseChartBlock g, transverseShearBlock g)
  invFun p := transverseOfBlocks p.1 p.2
  left_inv g :=
    Subtype.ext (Subtype.ext (coe_eq_fromBlocks_of_mem_transverseStabilizer g.2).symm)
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · show (Matrix.fromBlocks (p.1 : Matrix ι ι K) 0 p.2 1).toBlocks₁₁ = _
      rw [Matrix.toBlocks_fromBlocks₁₁]
    · show (Matrix.fromBlocks (p.1 : Matrix ι ι K) 0 p.2 1).toBlocks₂₁ = _
      rw [Matrix.toBlocks_fromBlocks₂₁]

/-- **Semidirect-product law.**  Composition of transverse stabilisers multiplies chart blocks and
twists the shear by the second chart block: `(A,C)·(A',C') = (A A', C A' + C')`. -/
theorem transverseOfBlocks_mul (A A' : SpecialLinearGroup ι K) (C C' : Matrix κ ι K) :
    transverseOfBlocks A C * transverseOfBlocks A' C' =
      transverseOfBlocks (A * A') (C * (A' : Matrix ι ι K) + C') := by
  refine Subtype.ext (Subtype.ext ?_)
  show Matrix.fromBlocks (A : Matrix ι ι K) 0 C 1 *
      Matrix.fromBlocks (A' : Matrix ι ι K) 0 C' 1 = _
  rw [Matrix.fromBlocks_multiply]
  show _ = Matrix.fromBlocks ((A : Matrix ι ι K) * (A' : Matrix ι ι K)) 0
    (C * (A' : Matrix ι ι K) + C') 1
  simp

end GaloisForLFunctions.HTGeometry
