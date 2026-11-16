import GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
import GaloisForLFunctions.RHTower.XiSchwartzMetricSupport
import Mathlib.Tactic

/-!
# Transverse directional supports on the two-dimensional torus

Two nonparallel affine lines have countably many intersections after quotienting
by the integer lattice. The same holds for two countable families of parallel
lines. Hence their intersection carries only countably concentrated measures;
a measure vanishing on singletons assigns it zero mass.

This is the geometric mechanism behind the two-direction spectral rigidity
in Robinson–Şahin, arXiv:2611.10761, Example 6.3. The quotient is the same one
used by the corpus's integer-lattice Fourier theory.
-/

noncomputable section

open Set MeasureTheory
open GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A real affine line wrapped around the unit torus. -/
def wrappedLine (p v : Fin 2 → ℝ) : Set (UnitAddTorus (Fin 2)) :=
  Set.range fun t : ℝ => torusProjection (p + t • v)

/-- A countable union of parallel wrapped lines. -/
def wrappedLineFamily (v : Fin 2 → ℝ) (p : ℕ → Fin 2 → ℝ) :
    Set (UnitAddTorus (Fin 2)) := ⋃ k, wrappedLine (p k) v

/-- The oriented area distinguishing transverse from parallel directions. -/
def directionArea (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

private theorem quotient_fiber {x y : Fin 2 → ℝ}
    (h : torusProjection x = torusProjection y) :
    ∃ n : Fin 2 → ℤ, ∀ i, (n i : ℝ) = x i - y i := by
  have hi (i : Fin 2) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    have hh := QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h i)
    simpa only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one] using hh
  choose n hn using hi
  exact ⟨n, hn⟩

private theorem wrappedLine_inter_countable (p q v w : Fin 2 → ℝ)
    (hvw : directionArea v w ≠ 0) : (wrappedLine p v ∩ wrappedLine q w).Countable := by
  let parameter (n : Fin 2 → ℤ) : ℝ :=
    (((n 0 : ℝ) + q 0 - p 0) * w 1 - ((n 1 : ℝ) + q 1 - p 1) * w 0) /
      directionArea v w
  apply (Set.countable_range (fun n : Fin 2 → ℤ =>
    torusProjection (p + parameter n • v))).mono
  rintro z ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
  obtain ⟨n, hn⟩ := quotient_fiber (ht.trans hu.symm)
  refine ⟨n, ?_⟩
  have h0 := hn 0
  have h1 := hn 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
  have hp : parameter n = t := by
    apply (div_eq_iff hvw).mpr
    dsimp only [directionArea]
    linear_combination w 1 * h0 - w 0 * h1
  change torusProjection (p + parameter n • v) = z
  rw [hp]
  exact ht

/-- Transverse wrapped lines have countable intersection; parallelism is the
only possible exception. This includes rational and irrational directions. -/
theorem wrappedLine_inter_countable_or_parallel (p q v w : Fin 2 → ℝ) :
    (wrappedLine p v ∩ wrappedLine q w).Countable ∨ directionArea v w = 0 := by
  by_cases h : directionArea v w = 0
  · exact Or.inr h
  · exact Or.inl (wrappedLine_inter_countable p q v w h)

/-- Countable directional families retain the same transverse rigidity. -/
theorem wrappedLineFamily_inter_countable_or_parallel
    (v w : Fin 2 → ℝ) (p q : ℕ → Fin 2 → ℝ) :
    (wrappedLineFamily v p ∩ wrappedLineFamily w q).Countable ∨
      directionArea v w = 0 := by
  by_cases h : directionArea v w = 0
  · exact Or.inr h
  · left
    have hc : (⋃ k, ⋃ l, wrappedLine (p k) v ∩ wrappedLine (q l) w).Countable :=
      Set.countable_iUnion fun k => Set.countable_iUnion fun l =>
        wrappedLine_inter_countable (p k) (q l) v w h
    apply hc.mono
    rintro z ⟨hp, hq⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨l, hk, hl⟩⟩

/-- The part of any measure lying in two transverse directional families is
concentrated on a countable set. No assumption on the original measure is needed. -/
theorem restricted_directional_measure_countable_or_parallel
    (μ : Measure (UnitAddTorus (Fin 2)))
    (v w : Fin 2 → ℝ) (p q : ℕ → Fin 2 → ℝ) :
    (∃ S : Set (UnitAddTorus (Fin 2)), S.Countable ∧
      (μ.restrict (wrappedLineFamily v p ∩ wrappedLineFamily w q)) Sᶜ = 0) ∨
      directionArea v w = 0 := by
  rcases wrappedLineFamily_inter_countable_or_parallel v w p q with h | h
  · left
    refine ⟨_, h, ?_⟩
    rw [Measure.restrict_apply h.measurableSet.compl, Set.compl_inter_self, measure_empty]
  · exact Or.inr h

/-- The common part of two transverse directional supports is exactly a sum
of point masses, using the corpus's countable-support measure decomposition. -/
theorem directionalRestriction_atomic_or_parallel
    (μ : Measure (UnitAddTorus (Fin 2)))
    (v w : Fin 2 → ℝ) (p q : ℕ → Fin 2 → ℝ) :
    μ.restrict (wrappedLineFamily v p ∩ wrappedLineFamily w q) =
      Measure.sum (fun z : ↥(wrappedLineFamily v p ∩ wrappedLineFamily w q) =>
        μ {(z : UnitAddTorus (Fin 2))} • Measure.dirac (z : UnitAddTorus (Fin 2))) ∨
      directionArea v w = 0 := by
  rcases wrappedLineFamily_inter_countable_or_parallel v w p q with h | h
  · left
    refine (RHTower.measure_eq_sum_smul_dirac_of_countable_ae
      (μ.restrict (wrappedLineFamily v p ∩ wrappedLineFamily w q))
      h.measurableSet h (ae_restrict_mem h.measurableSet)).trans ?_
    apply congrArg Measure.sum
    funext z
    rw [Measure.restrict_apply (measurableSet_singleton _),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr z.property)]
  · exact Or.inr h

end GaloisForLFunctions.BiarithmeticGeometry
