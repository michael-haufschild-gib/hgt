import GaloisForLFunctions.RHTower.SoninPrincipalShellResidual
import GaloisForLFunctions.RHTower.SoninTropicalCalkinPathUniversalityLaw

/-!
# Tropical Sonin paths are Calkin-separated from principal residual channels

Canonical one-scale principal-shell residuals and their positive energies are compact.  Genuine
finite Sonin Gram paths are never compact.  Compact-congruence invariance therefore places these
two mechanisms in disjoint Calkin phases.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- **Sonin tropical-path/principal-residual Calkin separation.**  Every principal residual and
its positive energy vanish modulo compacts, whereas every genuine finite Gram path represents a
nonzero Calkin class; hence no path is compactly equivalent to either residual channel. -/
theorem soninTropicalPath_principalResidual_calkinSeparationUniversality
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (P : SoninScalePath) :
    IsCompactOperator (evenSoninPrincipalShellResidual a p hp) ∧
    IsCompactOperator (evenSoninPrincipalShellEnergy a p hp) ∧
    (∀ x : evenSubspace,
      0 ≤ Complex.re
        (inner Complex x (evenSoninPrincipalShellEnergy a p hp x))) ∧
    ¬ P.operator a =ₖ evenSoninPrincipalShellResidual a p hp ∧
    ¬ P.operator a =ₖ evenSoninPrincipalShellEnergy a p hp := by
  have hresidual :
      IsCompactOperator (evenSoninPrincipalShellResidual a p hp) :=
    evenSoninPrincipalShellResidual_isCompactOperator a p ha hp
  have henergy :
      IsCompactOperator (evenSoninPrincipalShellEnergy a p hp) :=
    evenSoninPrincipalShellEnergy_isCompactOperator a p ha hp
  have hpath : ¬ IsCompactOperator (P.operator a) :=
    P.operator_not_isCompactOperator a ha
  refine ⟨hresidual, henergy,
    evenSoninPrincipalShellEnergy_re_inner_nonneg a p hp, ?_, ?_⟩
  · intro hcompactEq
    exact hpath
      (RHTower.IsCompactOperator.compactEq_left hresidual hcompactEq)
  · intro hcompactEq
    exact hpath
      (RHTower.IsCompactOperator.compactEq_left henergy hcompactEq)

end

end RHTower
