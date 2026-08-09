import GaloisForLFunctions.HTGeometry.CompactQuotientSpan
import GaloisForLFunctions.HTGeometry.FundamentalParallelotope

/-!
# A compact fundamental set, and its finite cover

A subgroup with compact quotient contains a basis, and the unit parallelotope of that basis is a
compact fundamental set: every point of the space is congruent to one of its points.  Compactness
then supplies a finite cover by balls of any prescribed radius.

* **`exists_fundamental_compact_of_compactSpace_quotient`**;
* **`exists_finite_centres_of_compactSpace_quotient`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A compact fundamental set for a subgroup with compact quotient.** -/
theorem exists_fundamental_compact_of_compactSpace_quotient {P : AddSubgroup E}
    (h : CompactSpace (E ⧸ P)) :
    ∃ K : Set E, IsCompact K ∧ K.Nonempty ∧ ∀ z : E, ∃ p ∈ P, z - p ∈ K := by
  classical
  obtain ⟨t, hts, hli, hspan⟩ :=
    exists_linearIndependent_span_top_subset_of_compactSpace_quotient h
  have htfin : t.Finite := hli.setFinite
  haveI : Fintype t := htfin.fintype
  set b : Module.Basis t ℝ E := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan]) with hb
  have hbval : ∀ i : t, b i = (i : E) := by
    intro i
    rw [hb, Module.Basis.mk_apply]
  refine ⟨parallelotope (fun i : t => (b i : E)), isCompact_parallelotope _, ?_, ?_⟩
  · refine ⟨0, ⟨0, ⟨le_refl _, ?_⟩, by simp⟩⟩
    intro i
    exact zero_le_one
  · intro z
    obtain ⟨m, hm⟩ := exists_intCombination_sub_mem_parallelotope b z
    refine ⟨∑ i, (m i : ℝ) • b i, ?_, hm⟩
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have hzs : ((m i : ℝ)) • (b i) = (m i : ℤ) • (b i) := by
      rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [hzs]
    exact P.zsmul_mem (by rw [hbval i]; exact hts i.2) _

/-- **A finite set of centres whose `r`-balls cover a fundamental set.** -/
theorem exists_finite_centres_of_compactSpace_quotient {P : AddSubgroup E}
    (h : CompactSpace (E ⧸ P)) {r : ℝ} (hr : 0 < r) :
    ∃ (K : Set E) (s : Set E), IsCompact K ∧ K.Nonempty ∧
      (∀ z : E, ∃ p ∈ P, z - p ∈ K) ∧ s.Finite ∧
      ∀ z ∈ K, ∃ c ∈ s, ‖z - c‖ ≤ r := by
  obtain ⟨K, hKcomp, hKne, hfund⟩ := exists_fundamental_compact_of_compactSpace_quotient h
  obtain ⟨s, -, hsfin, hcov⟩ := hKcomp.finite_cover_balls hr
  refine ⟨K, s, hKcomp, hKne, hfund, hsfin, ?_⟩
  intro z hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hcov hz)
  refine ⟨c, hc, ?_⟩
  have := Metric.mem_ball.mp hzc
  rw [dist_eq_norm] at this
  exact this.le

end GaloisForLFunctions.HTGeometry
