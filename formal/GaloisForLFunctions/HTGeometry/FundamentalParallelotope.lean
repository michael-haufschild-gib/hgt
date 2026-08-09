import Mathlib

/-!
# The fundamental parallelotope of a lattice basis

Every point of a finite-dimensional real vector space is congruent, modulo the integer span of a
basis, to a point of the compact unit parallelotope of that basis.  This is the geometric input of
every "cover a fundamental domain by finitely many charts" argument: the parallelotope is compact,
so any open cover of it has a finite subcover, and periodicity carries the resulting estimates to
the whole space.

* **`isCompact_parallelotope`**;
* **`exists_intCombination_sub_mem_parallelotope`** — the reduction of an arbitrary point into the
  parallelotope by subtracting an integer combination of the basis, the integers being the floors
  of the coordinates.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

/-- The unit parallelotope of a family of vectors. -/
def parallelotope (b : Fin d → E) : Set E :=
  (fun t : Fin d → ℝ => ∑ i, t i • b i) '' (Set.Icc 0 1)

theorem continuous_parallelotopeMap (b : Fin d → E) :
    Continuous fun t : Fin d → ℝ => ∑ i, t i • b i := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

/-- **The unit parallelotope is compact.** -/
theorem isCompact_parallelotope (b : Fin d → E) : IsCompact (parallelotope b) :=
  isCompact_Icc.image (continuous_parallelotopeMap b)

/-- **Reduction into the parallelotope.**  Subtracting the integer parts of the coordinates lands
any point in the unit parallelotope of the basis. -/
theorem exists_intCombination_sub_mem_parallelotope
    (b : Module.Basis (Fin d) ℝ E) (z : E) :
    ∃ m : Fin d → ℤ, z - ∑ i, (m i : ℝ) • b i ∈ parallelotope (fun i => b i) := by
  classical
  refine ⟨fun i => ⌊b.repr z i⌋, ?_⟩
  refine ⟨fun i => Int.fract (b.repr z i), ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · exact Int.fract_nonneg _
    · exact (Int.fract_lt_one _).le
  · have hrepr : ∑ i, (b.repr z i) • b i = z := b.sum_repr z
    have hsplit : ∑ i, Int.fract (b.repr z i) • b i
        = (∑ i, (b.repr z i) • b i) - ∑ i, ((⌊b.repr z i⌋ : ℝ)) • b i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul]
      congr 1
    show ∑ i, Int.fract (b.repr z i) • b i = z - ∑ i, ((⌊b.repr z i⌋ : ℝ)) • b i
    rw [hsplit, hrepr]

end GaloisForLFunctions.HTGeometry
