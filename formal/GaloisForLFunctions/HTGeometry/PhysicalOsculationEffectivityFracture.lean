import GaloisForLFunctions.HTGeometry.PeriodIncidenceUniformEffectivity
import GaloisForLFunctions.HTGeometry.QuadraticPhysicalCharacterOsculation

/-!
# Physical osculation and global effectivity are independent source axes

The same rationally independent rank-three source supports quadratic physical-character
constraints of exact contact orders two and three while its period-incidence representation has no
continuous left inverse.  Thus local physical osculation is not determined by the global
effectivity phase.  Any unified source object must retain both axes.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A quadratic constraint on the conic rank-three source which is transverse at source height
two. -/
def rankThreeTransversePhysicalPullback (α : ℂ) : ℂ → ℂ :=
  quadraticBinomialPhysicalPullback 1 α (α ^ (2 : ℕ)) 1

theorem analyticOrderAt_rankThreeTransversePhysicalPullback_eq_two
    (α : ℂ) (hlin : LinearIndependent ℚ (conicRankThreeSource α)) :
    analyticOrderAt (rankThreeTransversePhysicalPullback α) 0 = 2 := by
  apply analyticOrderAt_quadraticBinomialPhysicalPullback_eq_two
  intro hprod
  have hα0 : α ≠ 0 := by
    simpa [conicRankThreeSource] using hlin.ne_zero (1 : Fin 3)
  have hα1 : α ≠ 1 := by
    intro hα1
    have h01 : (0 : Fin 3) = 1 := hlin.injective (by simp [conicRankThreeSource, hα1])
    norm_num at h01
  have hfix : α ^ (2 : ℕ) = α := by simpa [mul_comm] using hprod.symm
  have hfactor : α * (α - 1) = 0 := by
    calc
      α * (α - 1) = α ^ (2 : ℕ) - α := by ring
      _ = 0 := by rw [hfix, sub_self]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact hα0 hzero
  · exact hα1 (sub_eq_zero.mp hone)

/-- **Osculation/effectivity fracture witness.**  One rationally independent rank-three source has
no continuous global incidence inverse, yet supports quadratic physical constraints of exact
contact orders two and three.  Hence global effectivity does not determine local osculation. -/
theorem rankThreePhysicalOsculation_effectivity_fracture
    (α : ℂ) (hlin : LinearIndependent ℚ (conicRankThreeSource α)) :
    analyticOrderAt (rankThreeTransversePhysicalPullback α) 0 = 2 ∧
    analyticOrderAt (conicPhysicalPullback α) 0 = 3 ∧
    ¬ (periodIncidenceMultiplier
      (Submodule.span ℤ (Set.range (conicRankThreeSource α)))).HasLeftInverse := by
  exact ⟨analyticOrderAt_rankThreeTransversePhysicalPullback_eq_two α hlin,
    analyticOrderAt_conicPhysicalPullback_eq_three_of_rankThree α hlin,
    rankThreePeriodIncidenceMultiplier_not_hasLeftInverse (conicRankThreeSource α) hlin⟩

end

end GaloisForLFunctions
