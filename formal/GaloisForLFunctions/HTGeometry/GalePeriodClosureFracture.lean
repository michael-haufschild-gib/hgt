import GaloisForLFunctions.HTGeometry.DiscretePeriodGaugeClassification
import GaloisForLFunctions.HTGeometry.RankThreePeriodNonHausdorff
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Sign.Basic

/-!
# Oriented Gale data does not determine the period-closure phase

Two labelled triples can have identical rank-two chirotopes while their integer period spans lie
on opposite sides of the discrete/nondiscrete effectivity wall. Thus even oriented linear matroid
data cannot recover the topological period closure. A source invariant intended to control both
differential-annihilator geometry and global fixed gauges must retain a separate closure or
Pontryagin-character component.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A redundant triple contained in the standard complex period lattice. -/
def latticePeriodTriple : Fin 3 → ℂ := ![1, Complex.I, 1 + Complex.I]

/-- A triple with the same real orientation signs but irrational integral period rank three. -/
def irrationalPeriodTriple : Fin 3 → ℂ :=
  ![1, Complex.I, (Real.sqrt 2 : ℂ) + Complex.I]

/-- The real oriented area of a labelled pair of complex periods. -/
def realOrientation (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

/-- The rank-two chirotope of a labelled complex period triple. -/
def periodChirotope (v : Fin 3 → ℂ) (i j : Fin 3) : SignType :=
  SignType.sign (realOrientation (v i) (v j))

/-- The lattice and irrational triples have exactly the same labelled chirotope. -/
theorem periodChirotope_lattice_eq_irrational :
    periodChirotope latticePeriodTriple = periodChirotope irrationalPeriodTriple := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodChirotope, realOrientation, latticePeriodTriple, irrationalPeriodTriple,
      Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]

/-- Irrationality of `sqrt 2` makes the second period triple rationally independent. -/
theorem irrationalPeriodTriple_linearIndependent :
    LinearIndependent ℚ irrationalPeriodTriple := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [Fin.sum_univ_succ, irrationalPeriodTriple] at hre him
  change (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 at hre
  have hg2 : g 2 = 0 := by
    by_contra hg2
    apply irrational_sqrt_two.ne_rat (-(g 0) / g 2)
    have hg2r : ((g 2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hg2
    push_cast
    apply (eq_div_iff hg2r).2
    linarith
  have hg0 : g 0 = 0 := by
    rw [hg2] at hre
    simpa using hre
  have hg1 : g 1 = 0 := by
    rw [hg2] at him
    simpa using him
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- The integer span of the redundant triple in the standard lattice. -/
def latticePeriodGroup : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range latticePeriodTriple)

/-- The integer span of the irrational rank-three triple. -/
def irrationalPeriodGroup : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range irrationalPeriodTriple)

/-- The redundant triple generates a discrete period group. -/
theorem latticePeriodGroup_discrete : DiscreteTopology latticePeriodGroup := by
  change DiscreteTopology (Submodule.span ℤ (Set.range latticePeriodTriple))
  letI : Countable (Submodule.span ℤ (Set.range latticePeriodTriple)) := inferInstance
  have hsubset : Set.range latticePeriodTriple ⊆
      (Submodule.span ℤ (Set.range Complex.basisOneI) : Set ℂ) := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, by simp [latticePeriodTriple, Complex.coe_basisOneI]⟩
    · exact Submodule.subset_span ⟨1, by simp [latticePeriodTriple, Complex.coe_basisOneI]⟩
    · exact add_mem
        (Submodule.subset_span ⟨0, by simp [Complex.coe_basisOneI]⟩)
        (Submodule.subset_span ⟨1, by simp [Complex.coe_basisOneI]⟩)
  apply discrete_of_countable_isClosed_intSubmodule
  exact isClosed_intSpan_of_subset_realBasis latticePeriodTriple Complex.basisOneI hsubset

/-- The irrational triple generates a nondiscrete period group. -/
theorem irrationalPeriodGroup_not_discrete : ¬ DiscreteTopology irrationalPeriodGroup :=
  not_discrete_intSpan_fin_three irrationalPeriodTriple
    irrationalPeriodTriple_linearIndependent

/-- **Gale/period-closure fracture.** Identical labelled chirotopes can have opposite global
period-effectivity phases. By the exact gauge-classification theorem, they consequently also
have opposite nonconstant-fixed-gauge phases. -/
theorem same_chirotope_opposite_period_effectivity :
    periodChirotope latticePeriodTriple = periodChirotope irrationalPeriodTriple ∧
      (periodIncidenceMultiplier latticePeriodGroup).HasLeftInverse ∧
      ¬(periodIncidenceMultiplier irrationalPeriodGroup).HasLeftInverse := by
  refine ⟨periodChirotope_lattice_eq_irrational, ?_, ?_⟩
  · exact (periodIncidenceMultiplier_hasLeftInverse_iff_discrete latticePeriodGroup).2
      latticePeriodGroup_discrete
  · exact (periodIncidenceMultiplier_hasLeftInverse_iff_discrete irrationalPeriodGroup).not.mpr
      irrationalPeriodGroup_not_discrete

end

end GaloisForLFunctions.HTGeometry
