import GaloisForLFunctions.RHTower.RouteEWeightedHallANOVA
import GaloisForLFunctions.RHTower.FrankensteinPrimitiveXiMixedBurnolSchurGap
import GaloisForLFunctions.RHTower.XiWardCubicScalarSourceBohrSquaringWall
import GaloisForLFunctions.RHTower.RoutePPrimitiveDepthSquareModularDefect

/-!
# Route E/P cubic Hellinger--Pluecker load bridge

Route E measures physical column imbalance by chi-square.  Route P measures separation of two
cubic Cauchy source columns by the complement of their squared normalized coherence.  These had
been treated as different obstructions.  On a balanced two-column packet they are the same
projective coordinate through one exact cubic transform.

For positive source rates `a,b`, put

`chi = ((a-b)/(a+b))^(2 : ℕ)`.

The Route-P squared coherence at equal ordinate is `(1-chi)^(3 : ℕ)`, hence its normalized Pluecker
defect is

`1 - coherenceSq = chi * (3 - 3*chi + chi^(2 : ℕ))`.

Consequently the cubic Pluecker defect lies between `chi` and `3*chi`.  This is a quantitative
identification, not only a common vanishing locus: physical load dispersion and source Gram area
are equivalent at every scale.

The canonical Route-P depth-square operation provides a source-only finite witness.  Iterating it
twice multiplies every primitive log-frequency by four.  The resulting balanced chi-square is
`9/25`; the normalized quadratic coefficient of the unit-diagonal two-column cubic Gram is
`11529/62500`, strictly above both `1/6` and the uniform-Boolean ceiling `13/98`.  Thus the
unit-diagonal cubic Gamma/Hellinger metric clears the first SP-E degree-two obstruction without
using a Xi zero or a Xi Taylor coefficient.  Source-faithful diagonal transport and cofinal
coefficient equality remain separate gates.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Exact balanced two-column Route-E load -/

/-- Balanced physical target with one unit source and two equal-capacity columns. -/
def routeETwoColumnBalancedData : RouteEHallANOVAData Unit Bool where
  sourceLaw := fun _ => 1
  targetLaw := fun _ => 1 / 2
  source_pos := by intro; norm_num
  target_pos := by intro; norm_num
  source_sum := by simp
  target_sum := by simp

/-- Row kernel that sends source mass to the two physical columns in proportions `a:b`. -/
def routeETwoColumnLoadKernel (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    RouteERowKernel Unit Bool where
  transition := fun _ t => if t then a / (a + b) else b / (a + b)
  transition_nonneg := by
    intro _ t
    split <;> positivity
  row_sum := by
    intro _
    simp only [Fintype.sum_bool]
    simp
    field_simp [(add_pos ha hb).ne']

/-- Projective two-column load coordinate. -/
def routeETwoColumnLoadChiSquare (a b : ℝ) : ℝ :=
  ((a - b) / (a + b)) ^ (2 : ℕ)

/-- Route E's normalized physical chi-square is exactly the projective rate gap. -/
theorem routeETwoColumnBalanced_chiSquare_eq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routeETwoColumnBalancedData.chiSquare
        (routeETwoColumnLoadKernel a b ha hb) =
      routeETwoColumnLoadChiSquare a b := by
  classical
  unfold RouteEHallANOVAData.chiSquare RouteEHallANOVAData.density
    RouteEHallANOVAData.output routeETwoColumnBalancedData
    routeETwoColumnLoadKernel routeETwoColumnLoadChiSquare
  simp only [Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton]
  simp
  field_simp [(add_pos ha hb).ne']
  ring

theorem routeETwoColumnLoadChiSquare_lt_one
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routeETwoColumnLoadChiSquare a b < 1 := by
  unfold routeETwoColumnLoadChiSquare
  have hden : 0 < a + b := add_pos ha hb
  have hhigh : (a - b) / (a + b) < 1 :=
    (div_lt_one hden).2 (by linarith)
  have hlow : -1 < (a - b) / (a + b) :=
    (lt_div_iff₀ hden).2 (by linarith)
  have hprod : 0 <
      (1 - (a - b) / (a + b)) *
        (1 + (a - b) / (a + b)) :=
    mul_pos (sub_pos.mpr hhigh) (by linarith)
  nlinarith

/-! ## Cubic Cauchy Pluecker defect as Route-E load -/

/-- **Cubic load--Pluecker identity.**  The complement of Route P's squared normalized Cauchy
coherence is the cubic transform of the balanced Route-E column chi-square. -/
theorem routePBaseCauchyCubic_coherence_defect_eq_loadChiSquare
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - routePBaseCauchyCubicNormalizedCoherenceSq a b 0 =
      routeETwoColumnLoadChiSquare a b *
        (3 - 3 * routeETwoColumnLoadChiSquare a b +
          routeETwoColumnLoadChiSquare a b ^ (2 : ℕ)) := by
  unfold routePBaseCauchyCubicNormalizedCoherenceSq
    routeETwoColumnLoadChiSquare
  field_simp [(add_pos ha hb).ne']
  ring

/-- Physical chi-square is a lower bound for cubic Pluecker separation. -/
theorem routeETwoColumnLoadChiSquare_le_coherence_defect
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routeETwoColumnLoadChiSquare a b ≤
      1 - routePBaseCauchyCubicNormalizedCoherenceSq a b 0 := by
  rw [routePBaseCauchyCubic_coherence_defect_eq_loadChiSquare ha hb]
  have hchi0 : 0 ≤ routeETwoColumnLoadChiSquare a b := sq_nonneg _
  have hchi1 : routeETwoColumnLoadChiSquare a b ≤ 1 :=
    (routeETwoColumnLoadChiSquare_lt_one ha hb).le
  calc
    routeETwoColumnLoadChiSquare a b ≤
        routeETwoColumnLoadChiSquare a b +
          routeETwoColumnLoadChiSquare a b *
            (1 - routeETwoColumnLoadChiSquare a b) *
              (2 - routeETwoColumnLoadChiSquare a b) :=
      le_add_of_nonneg_right
        (mul_nonneg
          (mul_nonneg hchi0 (sub_nonneg.mpr hchi1)) (by linarith))
    _ = _ := by ring

/-- Cubic Pluecker separation costs at most three times physical chi-square. -/
theorem routePBaseCauchyCubic_coherence_defect_le_three_loadChiSquare
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - routePBaseCauchyCubicNormalizedCoherenceSq a b 0 ≤
      3 * routeETwoColumnLoadChiSquare a b := by
  rw [routePBaseCauchyCubic_coherence_defect_eq_loadChiSquare ha hb]
  have hchi0 : 0 ≤ routeETwoColumnLoadChiSquare a b := sq_nonneg _
  have hchi1 : routeETwoColumnLoadChiSquare a b ≤ 1 :=
    (routeETwoColumnLoadChiSquare_lt_one ha hb).le
  calc
    routeETwoColumnLoadChiSquare a b *
          (3 - 3 * routeETwoColumnLoadChiSquare a b +
            routeETwoColumnLoadChiSquare a b ^ (2 : ℕ)) =
        3 * routeETwoColumnLoadChiSquare a b -
          routeETwoColumnLoadChiSquare a b ^ (2 : ℕ) *
            (3 - routeETwoColumnLoadChiSquare a b) := by ring
    _ ≤ 3 * routeETwoColumnLoadChiSquare a b :=
      sub_le_self _ (mul_nonneg (sq_nonneg _) (by linarith))

/-- The unnormalized two-node Route-P Gram determinant is the same load curvature times its
diagonal scale. -/
theorem routePBaseCauchyCubicTwoNodeGramDet_eq_loadChiSquare
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    routePBaseCauchyCubicTwoNodeGramDet a b 0 =
      (1 / (16 * a ^ (3 : ℕ) * b ^ (3 : ℕ))) *
        routeETwoColumnLoadChiSquare a b *
          (3 - 3 * routeETwoColumnLoadChiSquare a b +
            routeETwoColumnLoadChiSquare a b ^ (2 : ℕ)) := by
  rw [routePBaseCauchyCubicTwoNodeGramDet]
  rw [normSq_routePBaseCauchyCubicKernel ha hb]
  rw [show (((a + b) ^ (2 : ℕ) + 0 ^ (2 : ℕ)) ^ (3 : ℕ)) = (a + b) ^ (6 : ℕ) by ring]
  unfold routeETwoColumnLoadChiSquare
  field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
  ring

/-- Distinct primitive Euler cells have strictly positive cubic Pluecker separation. -/
theorem routePPrimitivePair_cubicPluckerDefect_pos
    {pe tau : Nat.Primes × ℕ} (hne : pe ≠ tau) :
    0 < 1 - routePBaseCauchyCubicNormalizedCoherenceSq
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiGammaEulerPrimitiveLogFrequency tau) 0 := by
  apply sub_pos.mpr
  apply routePBaseCauchyCubicNormalizedCoherenceSq_lt_one
    (xiGammaEulerPrimitiveLogFrequency_pos pe)
    (xiGammaEulerPrimitiveLogFrequency_pos tau)
  exact Or.inl (xiGammaEulerPrimitiveLogFrequency_injective.ne hne)

/-! ## Canonical source pair clearing the SP-E quadratic floor -/

/-- Two iterations of Route P's primitive depth-square map. -/
def routePPrimitiveFourthDepth (pe : Nat.Primes × ℕ) : Nat.Primes × ℕ :=
  routePPrimitiveDepthSquare (routePPrimitiveDepthSquare pe)

theorem xiGammaEulerPrimitiveLogFrequency_routePPrimitiveFourthDepth
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe) =
      4 * xiGammaEulerPrimitiveLogFrequency pe := by
  rw [routePPrimitiveFourthDepth,
    xiGammaEulerPrimitiveLogFrequency_routePPrimitiveDepthSquare,
    xiGammaEulerPrimitiveLogFrequency_routePPrimitiveDepthSquare]
  ring

/-- Every primitive cell and its fourth-depth partner have exact balanced load `9/25`. -/
theorem routeETwoColumnLoadChiSquare_primitiveFourthDepth
    (pe : Nat.Primes × ℕ) :
    routeETwoColumnLoadChiSquare
        (xiGammaEulerPrimitiveLogFrequency pe)
        (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) =
      9 / 25 := by
  rw [xiGammaEulerPrimitiveLogFrequency_routePPrimitiveFourthDepth]
  unfold routeETwoColumnLoadChiSquare
  have hfrequency := xiGammaEulerPrimitiveLogFrequency_pos pe
  field_simp [hfrequency.ne']
  ring

/-- Scale-free quadratic coefficient of a unit-diagonal two-column cubic Cauchy Gram. -/
def routeEPCubicNormalizedPairGramRatio (a b : ℝ) : ℝ :=
  (1 - routePBaseCauchyCubicNormalizedCoherenceSq a b 0) / 4

/-- Exact source-only cubic Gram ratio on the canonical fourth-depth pair. -/
theorem routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth
    (pe : Nat.Primes × ℕ) :
    routeEPCubicNormalizedPairGramRatio
        (xiGammaEulerPrimitiveLogFrequency pe)
        (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) =
      11529 / 62500 := by
  rw [routeEPCubicNormalizedPairGramRatio,
    routePBaseCauchyCubic_coherence_defect_eq_loadChiSquare
      (xiGammaEulerPrimitiveLogFrequency_pos pe)
      (xiGammaEulerPrimitiveLogFrequency_pos
        (routePPrimitiveFourthDepth pe)),
    routeETwoColumnLoadChiSquare_primitiveFourthDepth]
  norm_num

/-- The canonical unit-diagonal metric clears the theta moment-log-convexity floor `1/6`. -/
theorem one_div_six_lt_routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth
    (pe : Nat.Primes × ℕ) :
    1 / 6 < routeEPCubicNormalizedPairGramRatio
        (xiGammaEulerPrimitiveLogFrequency pe)
        (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) := by
  rw [routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth]
  norm_num

/-- It also strictly exceeds the exact `13/98` ceiling of the uniform Boolean SP-E metric. -/
theorem thirteen_div_ninetyEight_lt_routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth
    (pe : Nat.Primes × ℕ) :
    13 / 98 < routeEPCubicNormalizedPairGramRatio
        (xiGammaEulerPrimitiveLogFrequency pe)
        (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) := by
  rw [routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth]
  norm_num

end


end RHTower
