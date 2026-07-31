import GaloisForLFunctions.RHTower.XiDepthSuccessorStokesNormalLayer
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport

/-!
# Outer/inner weld for the Xi depth successor and Möbius--Gamma source graph

The singular squarefree Möbius--Gamma graph reconstructs the outer completed Xi
logarithmic current on its safe Euler domain. The balanced two-endpoint depth
successor supplies the inner moving-zero normal layer. This file proves that the
two charts carry exactly the same multiplicity-weighted centered residue.

This closes source-to-divisor normalization. It does not prove the remaining
same-fibre inverse/adjoint identification and therefore does not prove RH.
-/

open Complex Filter Set
open scoped Topology BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- On the Euler domain, balanced affine Xi current is exactly scaled output
of singular Möbius--Gamma graph plus strict-right correction. Scale
`(s - 1/2) / 2` is forced by coefficient-two graph normalization. -/
theorem xiExceptionalAffineDivisorCurrent_eq_scaled_mobiusGammaGraph
    {sigma epsilon u : ℂ}
    (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re)
    (hepsilon : epsilon ≠ 0) :
    xiExceptionalAffineDivisorCurrent (sigma + u * epsilon) =
      ((sigma + u * epsilon - 1 / 2) / 2) *
        (squarefreeMobiusGammaCurrentTransportV sigma epsilon
            (squarefreeFisherScore sigma epsilon) u +
          4 * infinitePrimeFlux (2 * (sigma + u * epsilon))) := by
  rw [squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
    hsigma hshift hepsilon]
  rw [← completedXi_sub_completedSquarefree_eq_four_mul_infinitePrimeFlux_two
    hshift]
  simp only [xiExceptionalAffineDivisorCurrent,
    exceptionalAffineDivisorCurrent, seamFluxCochain]
  ring

/-- Outer charge of the rational nearby cycle and residue of the continued
balanced source current are one invariant. First component is inner chart at
`z = ∞` in inverse coordinate; second is outer chart at divisor point. -/
theorem xiDepthNearby_outerCharge_and_affineResidue_match
    (rho : ℂ) :
    let m := (analyticOrderAt xi rho).toNat
    Tendsto
        (fun w : ℂ =>
          w⁻¹ *
            (depthSuccessorNearbyCycle (rho - 1 / 2) m w⁻¹ - 1))
        (𝓝[≠] 0)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      Tendsto
        (fun s : ℂ =>
          (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) := by
  dsimp only
  constructor
  · simpa [mul_comm] using
      GaloisForLFunctions.HTGeometry.tendsto_depthSuccessorNearbyCycle_outerCharge
        (rho - 1 / 2) (analyticOrderAt xi rho).toNat
  · have hxi : AnalyticAt ℂ xi rho :=
      xi_analyticOnNhd_univ rho (Set.mem_univ rho)
    have hfinite : analyticOrderAt xi rho ≠ ⊤ :=
      xi_order_ne_top rho
    have horder :
        analyticOrderAt xi rho =
          (((analyticOrderAt xi rho).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    have hmeromorphicOrder :
        meromorphicOrderAt xi rho =
          (((analyticOrderAt xi rho).toNat : ℕ) : ℤ) := by
      rw [hxi.meromorphicOrderAt_eq, horder]
      simp
    have hres :=
      xiExceptionalAffineDivisorCurrent_residue hmeromorphicOrder
    simpa using hres

end RHTower
