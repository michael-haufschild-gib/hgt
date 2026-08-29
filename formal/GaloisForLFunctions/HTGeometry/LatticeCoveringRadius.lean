import Mathlib

/-!
# The covering radius of a full lattice

Rounding each coordinate of a vector in the basis of a full lattice moves it by at most half a basis
vector in each direction, so the `ℤ`-span of a real basis is `(1/2)∑‖bᵢ‖`-dense.

This is the replacement, over a ring of integers `𝒪_F`, for the "size reduction to `|·| ≤ 1/2`" step
of Siegel reduction over `ℤ`: what the descent actually uses is not the constant `1/2` but the mere
boundedness of the covering radius of the lattice inside `F ⊗ ℝ`.

* `exists_intCombination_dist_le` — the rounding bound;
* `zspan_dense_of_basis` — the `ℤ`-span of a basis is `R`-dense for `R = (1/2)∑‖bᵢ‖`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- **Rounding in a basis.**  Every vector is within `(1/2)∑‖bᵢ‖` of an integral combination of the
basis. -/
theorem exists_intCombination_dist_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (x : V) :
    ∃ n : ι → ℤ, ‖x - ∑ i, (n i : ℝ) • b i‖ ≤ (1 / 2) * ∑ i, ‖b i‖ := by
  classical
  refine ⟨fun i => round (b.repr x i), ?_⟩
  have hx : x = ∑ i, (b.repr x i) • b i := (b.sum_repr x).symm
  have hdiff : x - ∑ i, ((round (b.repr x i) : ℤ) : ℝ) • b i
      = ∑ i, ((b.repr x i) - ((round (b.repr x i) : ℤ) : ℝ)) • b i := by
    have hsplit : ∑ i, ((b.repr x i) - ((round (b.repr x i) : ℤ) : ℝ)) • b i
        = (∑ i, (b.repr x i) • b i) - ∑ i, ((round (b.repr x i) : ℤ) : ℝ) • b i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => sub_smul _ _ _
    rw [hsplit, ← hx]
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact abs_sub_round (b.repr x i)

/-- **The `ℤ`-span of a real basis is dense with an explicit radius.** -/
theorem zspan_dense_of_basis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (x : V) :
    ∃ y ∈ Submodule.span ℤ (Set.range (b : ι → V)), ‖x - y‖ ≤ (1 / 2) * ∑ i, ‖b i‖ := by
  classical
  obtain ⟨n, hn⟩ := exists_intCombination_dist_le b x
  refine ⟨∑ i, (n i : ℝ) • b i, ?_, hn⟩
  refine Submodule.sum_mem _ fun i _ => ?_
  have hmem : (b i) ∈ Submodule.span ℤ (Set.range (b : ι → V)) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hz : ((n i : ℝ)) • b i = (n i) • b i := Int.cast_smul_eq_zsmul ℝ (n i) (b i)
  rw [hz]
  exact Submodule.smul_mem _ _ hmem

/-- **The covering radius exists.**  A single constant works for every vector. -/
theorem exists_coveringRadius {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : V, ∃ y ∈ Submodule.span ℤ (Set.range (b : ι → V)), ‖x - y‖ ≤ R := by
  refine ⟨(1 / 2) * ∑ i, ‖b i‖, by positivity, fun x => zspan_dense_of_basis b x⟩

-- The number-field instantiation is `NumberField.mixedEmbedding.latticeBasis` together with
-- `NumberField.mixedEmbedding.span_latticeBasis`, once a norm is fixed on the mixed space: the
-- `ℤ`-span of that basis *is* the image of the ring of integers, so the ring of integers is
-- `R`-dense in the mixed space with `R = (1/2)∑‖bᵢ‖`.  That boundedness — not the constant `1/2` —
-- is what the Siegel descent over `𝒪_F` needs in place of size reduction over `ℤ`.

end GaloisForLFunctions.HTGeometry
