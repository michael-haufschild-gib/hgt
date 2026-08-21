import GaloisForLFunctions.RHTower.DeningerArithmeticRealArakelovEndpoint
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient form of the real Arakelov endpoint

The graph of principal finite-plus-archimedean divisors is the kernel of total degree.
Consequently, its cokernel is canonically the orientation line.  This is the quotient form of
the finite-place/archimedean reciprocity endpoint and has no arithmetic or analytic premise.
-/

namespace GaloisForLFunctions.RHTower

section ArakelovEndpoint

variable {P R : Type*} [CommRing R]

/-- Modulo principal graph divisors, a finite-place divisor profile with an archimedean coordinate
is measured exactly by its total Arakelov degree. -/
noncomputable def deningerArakelovDegreeQuotientEquiv
    (weight : P → R) :
    (((P →₀ R) × R) ⧸ LinearMap.range (deningerArakelovPrincipalLinear weight)) ≃ₗ[R] R :=
  (deningerArakelov_exact_principal_degree weight).linearEquivOfSurjective
    (deningerArakelovDegreeLinear_surjective weight)

/-- The quotient equivalence evaluates a divisor class by its total degree. -/
theorem deningerArakelovDegreeQuotientEquiv_mk
    (weight : P → R) (x : (P →₀ R) × R) :
    deningerArakelovDegreeQuotientEquiv weight (Submodule.Quotient.mk x) =
      deningerArakelovDegreeLinear weight x :=
  rfl

end ArakelovEndpoint

end GaloisForLFunctions.RHTower
