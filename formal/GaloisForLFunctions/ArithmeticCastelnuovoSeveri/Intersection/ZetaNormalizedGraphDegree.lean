import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheTheoremOfTheSquareIsFree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ZetaReflectionEnergyBalance

/-!
# Reflection energy and arithmetic normalized graph degree

The formal normalized graph on the arithmetic scaling surface has twice
its horizontal degree equal to the actual Weil form. Its degree is therefore
half the difference between square mass and reflection defect. The graph
identities alone give a two-sided mass bound; nonnegative degree requires
exactly the stronger comparison of defect with mass.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticCorrespondencePositivity ArithmeticPositivityTheory SquareRootThreshold
open _root_.Zeta23

/-- Horizontal intersection degree of the formal normalized arithmetic graph. -/
def zetaNormalizedGraphDegree (x : ScalingCycle) : ℝ :=
  scalingSurface.pair (normGraph scalingSurface x) scalingSurface.H

/-- Twice the graph degree plus reflection defect is exactly the positive square mass. -/
theorem zeta_normalizedGraph_degree_energy (x : ScalingCycle) :
    2 * zetaNormalizedGraphDegree x +
        configurationReflectionDefect zetaZeroConfig (cx x.2.2) =
      configurationSquareMass zetaZeroConfig (cx x.2.2) := by
  have hw := zeta_squareMass_sub_re_W_eq_reflectionDefect
    (cx_contDiff x.2.2.property.1) (cx_hasCompactSupport x.2.2.property.2)
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed
    (cx_contDiff x.2.2.property.1) (cx_hasCompactSupport x.2.2.property.2)
    (cx_contDiff x.2.2.property.1) (cx_hasCompactSupport x.2.2.property.2)] at hw
  rw [zetaNormalizedGraphDegree, normGraph_degree_scalingSurface, weilPair]
  linarith only [hw]

/-- The formal graph degree lies between minus and plus half the square mass. -/
theorem zeta_normalizedGraph_degree_bounds (x : ScalingCycle) :
    -configurationSquareMass zetaZeroConfig (cx x.2.2) / 2 ≤
        zetaNormalizedGraphDegree x ∧
      zetaNormalizedGraphDegree x ≤ configurationSquareMass zetaZeroConfig (cx x.2.2) / 2 := by
  have hb := actualZeta_weil_squareMass_bounds
    (cx_contDiff x.2.2.property.1) (cx_hasCompactSupport x.2.2.property.2)
  rw [zetaNormalizedGraphDegree, normGraph_degree_scalingSurface, weilPair]
  constructor <;> linarith only [hb.1, hb.2]

/-- Nonnegative formal graph degree is equivalent to defect being bounded by mass. -/
theorem zeta_normalizedGraph_degree_nonneg_iff (x : ScalingCycle) :
    0 ≤ zetaNormalizedGraphDegree x ↔
      configurationReflectionDefect zetaZeroConfig (cx x.2.2) ≤
        configurationSquareMass zetaZeroConfig (cx x.2.2) := by
  have he := zeta_normalizedGraph_degree_energy x
  constructor <;> intro h <;> linarith only [he, h]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
