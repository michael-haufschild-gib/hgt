import GaloisForLFunctions.HTGeometry.WittenAsymptoticExpansion

/-!
# Finite-order mapping-torus WRT calibration

Andersen, *The Witten--Reshetikhin--Turaev invariants of finite order mapping tori I*,
Remark 1.1, records the exact `SU(2)` WRT value `Zₖ(T²₋Id) = k + 1`.  This file formalizes the
right-hand side and its exact Chern--Simons expansion.  It does not yet derive that formula from
a Lean construction of the non-abelian RT TQFT; that construction is the open infrastructure gap.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Published exact level formula for the `SU(2)` WRT invariant of the finite-order torus
mapping-torus calibration case. -/
def su2MinusIdentityTorusMappingTorusWRTFormula (k : ℕ) : ℂ :=
  (k : ℂ) + 1

/-- Its unique phase has constant and linear amplitudes. -/
def su2MinusIdentityTorusMappingTorusCoefficient (_ : Fin 1) (j : ℕ) : ℂ :=
  if j = 0 then 1 else if j = 1 then 1 else 0

/-- The published finite-order mapping-torus formula is an exact one-phase degree-one expansion. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion :
    HasExactFinitePhasePolynomialExpansion su2MinusIdentityTorusMappingTorusWRTFormula
      Finset.univ (fun _ : Fin 1 => 1)
      su2MinusIdentityTorusMappingTorusCoefficient 1 := by
  funext k
  simp [su2MinusIdentityTorusMappingTorusWRTFormula, finitePhasePolynomial,
    su2MinusIdentityTorusMappingTorusCoefficient]
  norm_num [Finset.sum_range_succ]
  ring

/-- This finite-order mapping-torus formula has zero remainder at every inverse-power order. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_hasAllOrdersRemainder :
    HasAllOrdersFinitePhasePolynomialRemainder su2MinusIdentityTorusMappingTorusWRTFormula
      Finset.univ (fun _ : Fin 1 => 1)
      su2MinusIdentityTorusMappingTorusCoefficient 1 :=
  su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion.hasAllOrdersRemainder

/-- The calibration formula satisfies the degree-one polynomial bound predicted by the
finite-order mapping-torus theorem. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_isBigO :
    su2MinusIdentityTorusMappingTorusWRTFormula =O[atTop] fun k : ℕ => (k : ℂ) := by
  simpa using su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion.isBigO
    (fun _ _ => norm_one)

end GaloisForLFunctions.HTGeometry
