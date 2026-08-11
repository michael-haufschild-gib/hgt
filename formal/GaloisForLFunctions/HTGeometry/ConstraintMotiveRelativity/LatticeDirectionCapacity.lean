import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CapacityPolarHorizon
import Mathlib

/-!
# Finite lattice-direction capacity and its vertical fibre

A baseline positive metric perturbed by finitely many marked rank-one directions with
nondecreasing nonnegative weights,

`G_n = A₀ + ∑_i c_i(n) · a_i ⊗ a_i`,

is an increasing capacity chart.  Its bounded-capacity sector is the orthogonal complement of the
span of the directions whose weights diverge, so the kernel of the limiting cometric is exactly
that span:

`ker Q_∞ = span_ℝ {a_i : c_i(n) → ∞}`.

The proof is direct: `⟪G_n x, x⟫ = ⟪A₀ x, x⟫ + ∑_i c_i(n) ⟪a_i, x⟫²` is bounded in `n` exactly
when `⟪a_i, x⟫ = 0` for every divergent index, because a nondecreasing real sequence is either
bounded or divergent.
-/

open Filter
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section LatticeDirections

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The rank-one operator `a ⊗ a`, `x ↦ ⟪a, x⟫ • a`. -/
noncomputable def rankOne (a : Y) : Y →ₗ[ℝ] Y where
  toFun x := ⟪a, x⟫ • a
  map_add' x y := by rw [inner_add_right, add_smul]
  map_smul' t x := by
    simp only [real_inner_smul_right, smul_smul, RingHom.id_apply]

omit [FiniteDimensional ℝ Y] in
@[simp] theorem rankOne_apply (a x : Y) : rankOne a x = ⟪a, x⟫ • a := rfl

omit [FiniteDimensional ℝ Y] in
theorem inner_rankOne (a x : Y) : ⟪rankOne a x, x⟫ = ⟪a, x⟫ ^ 2 := by
  rw [rankOne_apply, real_inner_smul_left]
  ring

omit [FiniteDimensional ℝ Y] in
theorem rankOne_smul (c : ℝ) (a : Y) : rankOne (c • a) = (c ^ 2) • rankOne a := by
  ext x
  simp only [rankOne_apply, LinearMap.smul_apply, real_inner_smul_left, smul_smul]
  ring_nf

omit [FiniteDimensional ℝ Y] in
theorem rankOne_symm (a x y : Y) : ⟪rankOne a x, y⟫ = ⟪x, rankOne a y⟫ := by
  rw [rankOne_apply, rankOne_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x a]
  ring

/-- The data of a finite marked lattice-direction capacity family. -/
structure LatticeDirectionData (Y : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (r : ℕ) where
  /-- The positive baseline metric. -/
  base : Y →ₗ[ℝ] Y
  /-- The baseline is symmetric. -/
  base_symm : ∀ x y, ⟪base x, y⟫ = ⟪x, base y⟫
  /-- The baseline is positive definite. -/
  base_pos : ∀ x, x ≠ 0 → 0 < ⟪base x, x⟫
  /-- The marked directions. -/
  dir : Fin r → Y
  /-- The capacity weights. -/
  weight : Fin r → ℕ → ℝ
  /-- The weights are nonnegative. -/
  weight_nonneg : ∀ i n, 0 ≤ weight i n
  /-- The weights are nondecreasing. -/
  weight_mono : ∀ i, Monotone (weight i)

namespace LatticeDirectionData

variable {r : ℕ} (L : LatticeDirectionData Y r)

/-- The Gram operator of stage `n`. -/
noncomputable def gram (n : ℕ) : Y →ₗ[ℝ] Y :=
  L.base + ∑ i, L.weight i n • rankOne (L.dir i)

theorem inner_gram (n : ℕ) (x : Y) :
    ⟪L.gram n x, x⟫ = ⟪L.base x, x⟫ + ∑ i, L.weight i n * ⟪L.dir i, x⟫ ^ 2 := by
  simp only [gram, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, inner_add_left, sum_inner, real_inner_smul_left, inner_rankOne]

theorem gram_symm (n : ℕ) (x y : Y) : ⟪L.gram n x, y⟫ = ⟪x, L.gram n y⟫ := by
  simp only [gram, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, L.base_symm, rankOne_symm]

theorem gram_pos (n : ℕ) (x : Y) (hx : x ≠ 0) : 0 < ⟪L.gram n x, x⟫ := by
  rw [L.inner_gram]
  have hbase := L.base_pos x hx
  have hsum : 0 ≤ ∑ i, L.weight i n * ⟪L.dir i, x⟫ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (L.weight_nonneg i n) (sq_nonneg _)
  linarith

theorem gram_mono (x : Y) : Monotone fun n => ⟪L.gram n x, x⟫ := by
  intro m n hmn
  show ⟪L.gram m x, x⟫ ≤ ⟪L.gram n x, x⟫
  rw [L.inner_gram, L.inner_gram]
  have : ∀ i : Fin r, L.weight i m * ⟪L.dir i, x⟫ ^ 2 ≤ L.weight i n * ⟪L.dir i, x⟫ ^ 2 :=
    fun i => mul_le_mul_of_nonneg_right (L.weight_mono i hmn) (sq_nonneg _)
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
  linarith

/-- The capacity chart of a finite marked lattice-direction family. -/
noncomputable def chart : CapacityChart Y where
  gram := L.gram
  gram_symm := L.gram_symm
  gram_pos := L.gram_pos
  gram_mono := L.gram_mono

@[simp] theorem chart_gram (n : ℕ) : L.chart.gram n = L.gram n := rfl

/-- The marked directions whose capacity weights diverge. -/
def divergentIndices : Set (Fin r) := {i | Tendsto (L.weight i) atTop atTop}

/-- The real span of the divergent marked directions. -/
noncomputable def divergentSpan : Submodule ℝ Y :=
  Submodule.span ℝ (L.dir '' L.divergentIndices)

theorem weight_bddAbove_of_not_divergent {i : Fin r} (hi : i ∉ L.divergentIndices) :
    ∃ M, ∀ n, L.weight i n ≤ M := by
  by_contra hcon
  push Not at hcon
  refine hi ?_
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨n, hn⟩ := hcon b
  exact ⟨n, fun m hm => le_trans hn.le (L.weight_mono i hm)⟩

/-- **The bounded-capacity sector is the polar of the divergent directions.** -/
theorem boundedCapacity_eq_orthogonal :
    L.chart.boundedCapacity = ((L.divergentSpan)ᗮ : Set Y) := by
  ext x
  constructor
  · rintro ⟨M, hM⟩
    have hbound : ∀ n, ⟪L.gram n x, x⟫ ≤ M := fun n => hM (Set.mem_range_self n)
    have hzero : ∀ i ∈ L.divergentIndices, ⟪L.dir i, x⟫ = 0 := by
      intro i hi
      by_contra hne
      have hsq : 0 < ⟪L.dir i, x⟫ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      have hbase : ∀ n, L.weight i n * ⟪L.dir i, x⟫ ^ 2 ≤ M - ⟪L.base x, x⟫ := by
        intro n
        have hg := hbound n
        rw [L.inner_gram] at hg
        have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, L.weight j n * ⟪L.dir j, x⟫ ^ 2 :=
          Finset.sum_nonneg fun j _ => mul_nonneg (L.weight_nonneg j n) (sq_nonneg _)
        have hsplit : ∑ j, L.weight j n * ⟪L.dir j, x⟫ ^ 2
            = L.weight i n * ⟪L.dir i, x⟫ ^ 2
              + ∑ j ∈ Finset.univ.erase i, L.weight j n * ⟪L.dir j, x⟫ ^ 2 :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        rw [hsplit] at hg
        linarith
      have hdiv : Tendsto (fun n => L.weight i n * ⟪L.dir i, x⟫ ^ 2) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hsq hi
      obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop (M - ⟪L.base x, x⟫)).exists
      exact absurd (hbase n) (not_le.mpr hn)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun v _ => ⟪v, x⟫ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, hi, rfl⟩
      exact hzero i hi
    · exact inner_zero_left x
    · intro v w _ _ hv hw
      rw [inner_add_left, hv, hw, add_zero]
    · intro t v _ hv
      rw [real_inner_smul_left, hv, mul_zero]
  · intro hx
    rw [SetLike.mem_coe, Submodule.mem_orthogonal] at hx
    have hzero : ∀ i ∈ L.divergentIndices, ⟪L.dir i, x⟫ = 0 := fun i hi =>
      hx (L.dir i) (Submodule.subset_span ⟨i, hi, rfl⟩)
    classical
    choose M hM using fun i (hi : i ∉ L.divergentIndices) => L.weight_bddAbove_of_not_divergent hi
    set B : ℝ := ⟪L.base x, x⟫
      + ∑ i, (if hi : i ∈ L.divergentIndices then 0 else M i hi * ⟪L.dir i, x⟫ ^ 2) with hB
    refine ⟨B, ?_⟩
    rintro s ⟨n, rfl⟩
    show ⟪L.gram n x, x⟫ ≤ B
    rw [L.inner_gram, hB]
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : i ∈ L.divergentIndices
    · rw [dif_pos hi, hzero i hi]
      simp
    · rw [dif_neg hi]
      exact mul_le_mul_of_nonneg_right (hM i hi n) (sq_nonneg _)

/-- **Finite lattice-direction rationality.**  The kernel of the limiting cometric is exactly the
span of the marked directions whose capacities diverge. -/
theorem ker_cometricLimit_eq_divergentSpan :
    LinearMap.ker L.chart.cometricLimit = L.divergentSpan := by
  have h := L.chart.boundedCapacity_eq_orthogonal
  rw [L.boundedCapacity_eq_orthogonal] at h
  have h2 : ((L.divergentSpan)ᗮ : Set Y) = ((LinearMap.ker L.chart.cometricLimit)ᗮ : Set Y) := h
  have h3 : (L.divergentSpan)ᗮ = (LinearMap.ker L.chart.cometricLimit)ᗮ :=
    SetLike.coe_injective h2
  have h4 := congrArg (fun S : Submodule ℝ Y => Sᗮ) h3
  simpa [Submodule.orthogonal_orthogonal] using h4.symm

end LatticeDirectionData

end LatticeDirections

end HTGeometry.ConstraintMotiveRelativity
