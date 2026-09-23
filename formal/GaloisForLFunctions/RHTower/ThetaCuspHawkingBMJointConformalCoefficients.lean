import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformalWeightJets

/-! Exact principal-symbol, first-derivative, and zeroth-order identities of the actual joint chart. -/
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section

def ellipticCoefficient (p : Point3) (i : Fin 3) : ℝ :=
  ![1,warp (p 0)^(2 : ℕ)*(p 2)^(2 : ℕ),warp (p 0)^(2 : ℕ)*(p 2)^(2 : ℕ)] i

def firstRatio (p : Point3) (i : Fin 3) : ℝ :=
  ![-radialUnit (p 0)/2,0,1/(2*p 2)] i

def secondRatio (p : Point3) (i : Fin 3) : ℝ :=
  ![warp (p 0)^(2 : ℕ)/2+radialUnit (p 0)^(2 : ℕ)/4,0,-1/(4*(p 2)^(2 : ℕ))] i

theorem weightFirst_ratio (p : Point3) (i : Fin 3) :
    weightFirst p i = weight p*(firstRatio p i:ℂ) := by
  fin_cases i <;> dsimp [weightFirst,firstRatio] <;> push_cast <;> ring

theorem weightSecond_ratio (p : Point3) (i : Fin 3) :
    weightSecond p i = weight p*(secondRatio p i:ℂ) := by
  fin_cases i <;> dsimp [weightSecond,secondRatio] <;> push_cast <;> ring

/-- The full joint principal symbol becomes the Euclidean identity multiplied by Y². -/
theorem chart_principalSymbol (p : Point3) (j k : Fin 3) :
    (∑ i : Fin 3, ellipticCoefficient p i*chartFirst p i j*chartFirst p i k) =
      (chart p 1)^(2 : ℕ)*(if j = k then 1 else 0) := by
  fin_cases j <;> fin_cases k <;>
    norm_num [Fin.sum_univ_succ,ellipticCoefficient,chartFirst,chart]
  all_goals first | solve | ring | linear_combination (p 2)^(2 : ℕ)*warp (p 0)^(2 : ℕ)*(warp_relation (p 0))

/-- Every first derivative cancels after the actual field-weight conjugation. -/
theorem chart_driftCancellation (p : Point3) (hp : 0 < p 2) (j : Fin 3) :
    (∑ i : Fin 3, ellipticCoefficient p i*(chartSecond p i j+
      2*firstRatio p i*chartFirst p i j)) = 0 := by
  have hy : p 2 ≠ 0 := ne_of_gt hp
  fin_cases j <;> norm_num [Fin.sum_univ_succ,ellipticCoefficient,chartFirst,chartSecond,firstRatio]
  all_goals field_simp
  all_goals first | solve | ring | linear_combination (p 2)*warp (p 0)*(warp_relation (p 0))

/-- The entire zeroth-order correction is the fixed coefficient one quarter. -/
theorem chart_potential (p : Point3) (hp : 0 < p 2) :
    (∑ i : Fin 3, ellipticCoefficient p i*secondRatio p i) = 1/4 := by
  have hy : p 2 ≠ 0 := ne_of_gt hp
  norm_num [Fin.sum_univ_succ,ellipticCoefficient,secondRatio]
  field_simp
  linear_combination 2*(warp_relation (p 0))

end
end RHTower.D4BMJointConformal
