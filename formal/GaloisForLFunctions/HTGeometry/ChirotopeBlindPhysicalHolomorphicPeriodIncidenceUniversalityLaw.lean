import GaloisForLFunctions.HTGeometry.GalePeriodClosureFracture
import GaloisForLFunctions.HTGeometry.HolomorphicPeriodIncidenceExclusion
import GaloisForLFunctions.HTGeometry.PhysicalOsculationEffectivityFracture

/-!
# Chirotope-blind physical/holomorphic period-incidence fracture

A discrete lattice triple and a rationally independent conic source can have identical labelled
rank-two chirotopes.  Nevertheless the lattice realization has an effective global incidence
multiplier, while the conic realization has exact physical contact orders two and three together
with global incidence ineffectivity and bounded-holomorphic all-power blindness.
-/

open Filter
open scoped Topology ENNReal Matrix

namespace GaloisForLFunctions

noncomputable section

/-- Positive oriented lattice comparator for the conic source. -/
def positiveLatticePeriodTriple : Fin 3 → ℂ :=
  ![1, 1 + Complex.I, 1 + 2 * Complex.I]

/-- Degree-four parameter producing three rationally independent conic periods. -/
def irrationalConicParameter : ℂ := (Real.sqrt 2 : ℂ) + Complex.I

def positiveLatticePeriodGroup : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range positiveLatticePeriodTriple)

def irrationalConicPeriodGroup : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range (conicRankThreeSource irrationalConicParameter))

theorem positiveLatticePeriodGroup_discrete :
    DiscreteTopology positiveLatticePeriodGroup := by
  change DiscreteTopology (Submodule.span ℤ (Set.range positiveLatticePeriodTriple))
  letI : Countable (Submodule.span ℤ (Set.range positiveLatticePeriodTriple)) := inferInstance
  have hsubset : Set.range positiveLatticePeriodTriple ⊆
      (Submodule.span ℤ (Set.range Complex.basisOneI) : Set ℂ) := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · change (1 : ℂ) ∈ Submodule.span ℤ (Set.range Complex.basisOneI)
      exact Submodule.subset_span ⟨0, by simp [Complex.coe_basisOneI]⟩
    · change (1 + Complex.I : ℂ) ∈
        Submodule.span ℤ (Set.range Complex.basisOneI)
      exact add_mem
        (Submodule.subset_span ⟨0, by simp [Complex.coe_basisOneI]⟩)
        (Submodule.subset_span ⟨1, by simp [Complex.coe_basisOneI]⟩)
    · change (1 + 2 * Complex.I : ℂ) ∈
        Submodule.span ℤ (Set.range Complex.basisOneI)
      apply add_mem
      · exact Submodule.subset_span ⟨0, by simp [Complex.coe_basisOneI]⟩
      · have hi : Complex.I ∈
            Submodule.span ℤ (Set.range Complex.basisOneI) :=
          Submodule.subset_span ⟨1, by simp [Complex.coe_basisOneI]⟩
        simpa using zsmul_mem hi 2
  apply discrete_of_countable_isClosed_intSubmodule
  exact isClosed_intSpan_of_subset_realBasis positiveLatticePeriodTriple Complex.basisOneI hsubset

theorem irrationalConicParameter_sq :
    irrationalConicParameter ^ 2 =
      1 + ((2 * Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [irrationalConicParameter, pow_two]
    norm_num
  · simp [irrationalConicParameter, pow_two]
    ring

theorem irrationalConicSource_linearIndependent :
    LinearIndependent ℚ (conicRankThreeSource irrationalConicParameter) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp only [Fin.sum_univ_succ, conicRankThreeSource] at hre him
  rw [irrationalConicParameter_sq] at hre him
  simp [irrationalConicParameter] at hre him
  simp only [Rat.smul_def] at hre him
  change ((g 0 : ℚ) : ℝ) +
      (((g 1 : ℚ) : ℝ) * Real.sqrt 2 + ((g 2 : ℚ) : ℝ)) = 0 at hre
  change ((g 1 : ℚ) : ℝ) +
      ((g 2 : ℚ) : ℝ) * (2 * Real.sqrt 2) = 0 at him
  have hg2 : g 2 = 0 := by
    by_contra hg2
    apply irrational_sqrt_two.ne_rat (-(g 1) / (2 * g 2))
    have hg2r : ((g 2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hg2
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num) hg2r)).2
    nlinarith [him]
  have hg1 : g 1 = 0 := by
    rw [hg2] at him
    simpa using him
  have hg0 : g 0 = 0 := by
    rw [hg1, hg2] at hre
    simpa using hre
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

theorem positiveLattice_chirotope_eq_irrationalConic :
    HTGeometry.periodChirotope positiveLatticePeriodTriple =
      HTGeometry.periodChirotope (conicRankThreeSource irrationalConicParameter) := by
  have hsource : conicRankThreeSource irrationalConicParameter =
      ![1, irrationalConicParameter,
        1 + ((2 * Real.sqrt 2 : ℝ) : ℂ) * Complex.I] := by
    funext i
    fin_cases i <;> simp [conicRankThreeSource, irrationalConicParameter_sq]
  rw [hsource]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [HTGeometry.periodChirotope, HTGeometry.realOrientation,
      positiveLatticePeriodTriple, irrationalConicParameter,
      Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2)] <;> ring_nf
  all_goals
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    norm_num

/-- **Chirotope-blind physical/holomorphic period-incidence fracture law.**  Identical local
oriented-matroid data admits both an effective lattice realization and a conic realization with
exact physical contact but no effective or nonzero bounded-holomorphic all-power incidence
class. -/
theorem chirotopeBlind_physicalHolomorphicPeriodIncidence_fracture
    (f : ℂ → ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R)) :
    HTGeometry.periodChirotope positiveLatticePeriodTriple =
        HTGeometry.periodChirotope (conicRankThreeSource irrationalConicParameter) ∧
      (periodIncidenceMultiplier positiveLatticePeriodGroup).HasLeftInverse ∧
      analyticOrderAt (rankThreeTransversePhysicalPullback irrationalConicParameter) 0 = 2 ∧
      analyticOrderAt (conicPhysicalPullback irrationalConicParameter) 0 = 3 ∧
      ¬ (periodIncidenceMultiplier irrationalConicPeriodGroup).HasLeftInverse ∧
      (periodHolomorphicEvaluation irrationalConicPeriodGroup f R hmap ∈
            closure (Set.range (periodIncidenceMultiplier irrationalConicPeriodGroup)) ↔
        periodHolomorphicEvaluation irrationalConicPeriodGroup f R hmap ∈
            Set.range (periodIncidenceMultiplier irrationalConicPeriodGroup)) ∧
      ((∀ r : ℕ,
          periodHolomorphicEvaluation irrationalConicPeriodGroup f R hmap ∈
            Set.range (poweredPeriodIncidenceMultiplier irrationalConicPeriodGroup r)) →
        periodHolomorphicEvaluation irrationalConicPeriodGroup f R hmap = 0) := by
  have hphysical := rankThreePhysicalOsculation_effectivity_fracture
    irrationalConicParameter irrationalConicSource_linearIndependent
  have hno : ¬ (periodIncidenceMultiplier irrationalConicPeriodGroup).HasLeftInverse := by
    simpa [irrationalConicPeriodGroup] using hphysical.2.2
  have hnondiscrete : ¬ DiscreteTopology irrationalConicPeriodGroup := by
    intro hdiscrete
    exact hno ((periodIncidenceMultiplier_hasLeftInverse_iff_discrete
      irrationalConicPeriodGroup).2 hdiscrete)
  have hholomorphic := holomorphic_period_incidence_exclusion
    irrationalConicPeriodGroup hnondiscrete f R hf hmap
  exact ⟨positiveLattice_chirotope_eq_irrationalConic,
    (periodIncidenceMultiplier_hasLeftInverse_iff_discrete positiveLatticePeriodGroup).2
      positiveLatticePeriodGroup_discrete,
    hphysical.1, hphysical.2.1, hno, hholomorphic.1, hholomorphic.2⟩

end

end GaloisForLFunctions
