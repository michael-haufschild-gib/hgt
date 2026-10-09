import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ObstructionDomains
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LaurentDerivationTransport
import GaloisForLFunctions.HTGeometry.PaperWeightedInitialBridge

/-!
# Domain and prime-ideal certificates for the actual degeneration

The quadric domain proof and the injective Laurent presentation prove that
the literal graded degeneration is a domain. Transport through the proved
associated-graded equivalence gives the same certificate for the Rees special
fibre and for the corpus's signed initial-ideal quotient.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate Obstruction AssociatedGradedPresentation

instance paperDegenerationIsDomain : IsDomain (G ℂ) :=
  Function.Injective.isDomain (LaurentPresentation.toLaurentBase ℂ).toRingHom
    LaurentDerivationTransport.toLaurentBase_injective

instance paperAssociatedGradedIsDomain : IsDomain (associatedGraded ℂ) :=
  Function.Injective.isDomain (associatedGradedEquiv ℂ).symm.toRingHom
    (associatedGradedEquiv ℂ).symm.injective

theorem paperDegenerationIdeal_isPrime : (idealG ℂ).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp paperDegenerationIsDomain

theorem paperHighestRelation_prime : Prime (Hstar ℂ) :=
  (Ideal.span_singleton_prime (GradedRelationSanity.Hstar_ne_zero ℂ)).mp
    paperDegenerationIdeal_isPrime

theorem paperNativeInitialIdeal_isPrime :
    (initialIdeal (-presentationWeight) (idealA ℂ)).IsPrime := by
  rw [paperNativeInitialIdeal_sourceRelation]
  exact paperDegenerationIdeal_isPrime

instance paperNativeInitialQuotientIsDomain :
    IsDomain (P ℂ 5 ⧸ initialIdeal (-presentationWeight) (idealA ℂ)) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr paperNativeInitialIdeal_isPrime

end GaloisForLFunctions.HTGeometry
