import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.DeningerMeyerPaugamHasse

/-!
# Meyer--Paugam two-jet Hasse family

A generalized zeta-zero jet and its reciprocal reflection are treated as two spectral places.
Their evaluations jointly separate Meyer cohomology modulo the common invisible sector.  This
packages an exact two-coordinate endpoint without claiming that the common kernel vanishes.
-/

namespace RHTower

noncomputable section

/-- A Meyer zero jet and its reciprocal reflection jointly determine cohomology modulo their
common invisible sector. -/
def deningerMeyerPaugamTwoJetHasseFamily (d : DeningerMeyerZetaZeroJetDatum) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (DeningerMeyerStrongLogCohomology ⧸
        (LinearMap.ker d.evaluationLM ⊓ LinearMap.ker d.reflectedEvaluationLM))
      (Fin 2) where
  Local := fun _ => ℂ
  profile := fun q i => Fin.cases
    (deningerMeyerPaugamHasseQuotientEquivRealizedProfiles d q).1.1
    (fun _ => (deningerMeyerPaugamHasseQuotientEquivRealizedProfiles d q).1.2) i
  profile_injective := by
    intro q r hqr
    apply (deningerMeyerPaugamHasseQuotientEquivRealizedProfiles d).injective
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun hqr 0
    · exact congrFun hqr 1

end
end RHTower
