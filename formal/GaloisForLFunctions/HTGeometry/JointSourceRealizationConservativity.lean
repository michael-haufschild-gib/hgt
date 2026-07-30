import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.GammaFactorialObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.GammaCofinalReconstructionDefect

/-!
# Joint source-realization conservativity

A source boundary reconstructs a primitive only modulo the common fixed gauge of the source
automorphisms.  A family of genuinely separate additive realization maps is jointly conservative
exactly when their common kernel kills that residual gauge.  This is the exact algebraic gate that
any analytic/monodromy/spectral/Hermitian/integral reconstruction package must instantiate.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The complete additive source boundary together with a labelled family of realization maps. -/
def CommutingDifferenceDifferentialField.familyRealizedBoundaryFingerprint
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →+ A) (x : K) : (ι → K) × (ρ → A) :=
  (S.boundaryFingerprint x, fun r => realization r x)

/-- Equality in every realization has exactly the residual source-gauge kernel predicted by the
source boundary. -/
theorem CommutingDifferenceDifferentialField.familyRealizedBoundaryFingerprint_eq_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →+ A) (x y : K) :
    S.familyRealizedBoundaryFingerprint realization x =
        S.familyRealizedBoundaryFingerprint realization y ↔
      JointFixed S (x - y) ∧ ∀ r, realization r (x - y) = 0 := by
  constructor
  · intro h
    have hboundary := congrArg Prod.fst h
    have hrealization := congrArg Prod.snd h
    refine ⟨S.boundaryFingerprint_eq_iff_sub_jointFixed x y |>.mp hboundary, ?_⟩
    intro r
    have hr := congrFun hrealization r
    simpa [familyRealizedBoundaryFingerprint] using sub_eq_zero.mpr hr
  · rintro ⟨hfixed, hrealization⟩
    apply Prod.ext
    · exact S.boundaryFingerprint_eq_iff_sub_jointFixed x y |>.mpr hfixed
    · funext r
      exact sub_eq_zero.mp (by simpa using! hrealization r)

/-- Exact joint-conservativity criterion: the family reconstructs every primitive together with
its source boundary if and only if no nonzero joint-fixed gauge is invisible in every realization.
-/
theorem CommutingDifferenceDifferentialField.familyRealizedBoundaryFingerprint_injective_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →+ A) :
    Function.Injective (S.familyRealizedBoundaryFingerprint realization) ↔
      ∀ z, JointFixed S z → (∀ r, realization r z = 0) → z = 0 := by
  constructor
  · intro hinjective z hfixed hinvisible
    apply hinjective
    apply S.familyRealizedBoundaryFingerprint_eq_iff realization z 0 |>.mpr
    simpa using And.intro hfixed hinvisible
  · intro hseparates x y hxy
    have hkernel :=
      S.familyRealizedBoundaryFingerprint_eq_iff realization x y |>.mp hxy
    exact sub_eq_zero.mp (hseparates (x - y) hkernel.1 hkernel.2)

/-- A nonzero source-fixed gauge invisible in every realization is an explicit obstruction to
joint conservativity. -/
theorem CommutingDifferenceDifferentialField.familyRealizedBoundaryFingerprint_not_injective
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →+ A) (z : K)
    (hfixed : JointFixed S z) (hinvisible : ∀ r, realization r z = 0) (hz : z ≠ 0) :
    ¬ Function.Injective (S.familyRealizedBoundaryFingerprint realization) := by
  intro hinjective
  exact hz
    ((S.familyRealizedBoundaryFingerprint_injective_iff realization).mp hinjective
      z hfixed hinvisible)

end

end GaloisForLFunctions
