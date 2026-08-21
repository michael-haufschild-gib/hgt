import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Index

/-!
# Total measure of a group in terms of a finite-index subgroup

For a left-invariant measure `μ` on an additive group `G` and a measurable subgroup `H` of finite
index,

```
μ (univ) = [G : H] · μ H .
```

The group is the disjoint union of the `[G : H]` cosets of `H`, and each coset has the same measure
as `H` by left invariance.  mathlib has the fundamental-domain machinery but no statement in this
form.

This is the structure of equations `(5.1)` and `(5.2)` in Suzuki, *Duality invariance of Faltings
heights, Hodge line bundles and global periods* (arXiv:2504.04993):

```
∫_{A(ℝ)} dz₁ ∧ … ∧ dz_g = #π₀(A(ℝ)) · ∫_{A(ℝ)⁰} dz₁ ∧ … ∧ dz_g ,
```

the real period being the number of connected components times the period of the identity
component.
-/

namespace GaloisForLFunctions.HTGeometry.HaarIndex

open MeasureTheory

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]

/-- **The total measure is the index times the measure of the subgroup.** -/
theorem measure_univ_eq_index_mul (H : AddSubgroup G) (hm : MeasurableSet (H : Set G))
    (μ : Measure G) [μ.IsAddLeftInvariant] [Finite (G ⧸ H)] :
    μ Set.univ = H.index * μ (H : Set G) := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  choose rep hrep using fun q : G ⧸ H => QuotientAddGroup.mk_surjective (s := H) q
  set f : (G ⧸ H) → Set G := fun q => (fun h => -(rep q) + h) ⁻¹' (H : Set G) with hf
  have hmem : ∀ (q : G ⧸ H) (g : G), g ∈ f q ↔ (QuotientAddGroup.mk g : G ⧸ H) = q := by
    intro q g
    have h1 : g ∈ f q ↔ -(rep q) + g ∈ H := Iff.rfl
    rw [h1, ← QuotientAddGroup.eq, hrep q]
    exact eq_comm
  have hmeas : ∀ q, MeasurableSet (f q) := fun q => hm.preimage (measurable_const_add _)
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    exact hqq' (((hmem q g).mp hg).symm.trans ((hmem q' g).mp hg'))
  have hcover : (⋃ q, f q) = Set.univ := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨QuotientAddGroup.mk g, (hmem _ g).mpr rfl⟩
  have hcard : ∀ q, μ (f q) = μ (H : Set G) := fun q => measure_preimage_add μ (-(rep q)) _
  calc μ Set.univ = μ (⋃ q, f q) := by rw [hcover]
    _ = ∑' q : (G ⧸ H), μ (f q) := measure_iUnion hdisj hmeas
    _ = ∑ q : (G ⧸ H), μ (f q) := tsum_fintype _
    _ = H.index * μ (H : Set G) := by
        simp only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [AddSubgroup.index, Nat.card_eq_fintype_card]

end GaloisForLFunctions.HTGeometry.HaarIndex
