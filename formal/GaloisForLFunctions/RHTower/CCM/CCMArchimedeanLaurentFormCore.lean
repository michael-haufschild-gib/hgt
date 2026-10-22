import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFormDomainEquivalence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogLaurentFormCore

/-!
# Laurent-polynomial core for the literal CCM archimedean form domain

Connes--Consani's form-core lemma is first proved in the equivalent logarithmic weighted space in
`SuzukiHlogLaurentFormCore`.  The exact shifted Riemann--Siegel weight is globally equivalent to
that logarithmic weight.  This file transports the finite Laurent submodule through the resulting
continuous linear equivalence and records the source theorem on the literal CCM form domain.
-/

open Set Topology

noncomputable section

namespace RHTower

/-- Finite Laurent polynomials in the aperture character, realized in the literal shifted
Riemann--Siegel form domain. -/
def ccmArchimedeanLaurentSubmodule (a : SuzukiPositiveAperture) :
    Submodule ℂ (CCMArchimedeanFormDomain a) :=
  (suzukiHlogLaurentSubmodule a).map
    (ccmArchimedeanLogFormDomainEquiv a).toLinearEquiv.toLinearMap

theorem ccmLogFormToArchimedean_integerMode_mem_laurentSubmodule
    (a : SuzukiPositiveAperture) (k : ℤ) :
    ccmLogFormToArchimedean a
        (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1)) ∈
      ccmArchimedeanLaurentSubmodule a := by
  exact ⟨_, suzukiIntegerApertureModeFormVector_mem_laurentSubmodule a k, rfl⟩

/-- The exact form-domain equivalence carries the logarithmic Laurent algebra onto the literal
CCM Laurent algebra. -/
theorem coe_ccmArchimedeanLaurentSubmodule (a : SuzukiPositiveAperture) :
    (ccmArchimedeanLaurentSubmodule a : Set (CCMArchimedeanFormDomain a)) =
      ccmLogFormToArchimedean a ''
        (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a)) := by
  ext q
  simp [ccmArchimedeanLaurentSubmodule,
    ccmArchimedeanLogFormDomainEquiv]

/-- **Connes--Consani (2021), Lemma `core`, literal CCM formulation.**

Finite Laurent polynomials in `U(x) = exp (pi*i*x/a)` are dense in the complete form domain of
the exact shifted Riemann--Siegel archimedean quadratic form restricted to `[-a,a]`.
-/
theorem dense_ccmArchimedeanLaurentSubmodule (a : SuzukiPositiveAperture) :
    Dense (ccmArchimedeanLaurentSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  rw [coe_ccmArchimedeanLaurentSubmodule]
  exact (ccmArchimedeanLogFormDomainEquiv a).surjective.denseRange.dense_image
    (ccmLogFormToArchimedean a).continuous
    (dense_suzukiHlogLaurentSubmodule a)

/-- Source-language closure statement: `ℂ[U,U⁻¹]` is a core for the literal CCM form. -/
theorem ccmArchimedeanLaurentPolynomials_formCore (a : SuzukiPositiveAperture) :
    closure
        (ccmArchimedeanLaurentSubmodule a : Set (CCMArchimedeanFormDomain a)) =
      Set.univ :=
  dense_iff_closure_eq.mp (dense_ccmArchimedeanLaurentSubmodule a)

end RHTower

end
