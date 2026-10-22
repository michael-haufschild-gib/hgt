import GaloisForLFunctions.RHTower.EulerAffineGammaXiWardTransport
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature

/-!
# Euler-affine Ward curvature bridge

This is a literal pre-divisor source law, not a selected-residue statement.
At the fixed safe source point `s = 2`, the first affine Euler Fisher Ward response is the
positive von Mangoldt logarithmic moment.  The same response is exactly the Euler contribution to
the Hedenmalm pole-unit transverse curvature.  Its unfrozen affine family transports through the
fixed Gamma completion to `continuedPrimeArchSourceRelativeTrace`.

Thus one source family discharges two shared gates together:

* `ORD`: its Ward curvature has strictly positive real part;
* `LAND`: every safe affine member lands in the completed Xi source trace.

No Xi zero, divisor, or source-selected scalar occurs in the definitions or proofs.  This does
not supply the still-missing critical-boundary/cofinal extension, so it is not an RH proof.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The fixed safe affine Ward curvature is twice the positive derivative of the prime flux. -/
theorem eulerAffineFisherScore_deriv_two_one_zero :
    deriv (eulerAffineFisherScore (2 : ℂ) 1) 0 =
      -2 * deriv infinitePrimeFlux 2 := by
  have hflux : DifferentiableAt ℂ infinitePrimeFlux 2 := by
    unfold infinitePrimeFlux
    rw [show (fun z => -logDeriv riemannZeta z) =
        fun z => -deriv riemannZeta z / riemannZeta z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := (2 : ℂ)) (by norm_num)
  have hshift : HasDerivAt (fun u : ℂ => infinitePrimeFlux (2 + u))
      (deriv infinitePrimeFlux 2) 0 := by
    apply HasDerivAt.comp_const_add (2 : ℂ) 0
    simpa using hflux.hasDerivAt
  have hdiff : HasDerivAt
      (fun u : ℂ => infinitePrimeFlux 2 - infinitePrimeFlux (2 + u))
      (-deriv infinitePrimeFlux 2) 0 := by
    exact HasDerivAt.const_sub (infinitePrimeFlux 2) hshift
  have hzeta : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hoverlap : DifferentiableAt ℂ
      (eulerAffineBoundaryOverlap (2 : ℂ) 1) 0 := by
    have hzetaDeriv : HasDerivAt riemannZeta (deriv riemannZeta 2) ((2 : ℂ) + 0) := by
      simpa using
        (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).hasDerivAt
    have hq :=
      (HasDerivAt.comp_const_add (2 : ℂ) 0 hzetaDeriv).div_const
        (riemannZeta 2)
    have heq : eulerAffineBoundaryOverlap (2 : ℂ) 1 =
        fun u : ℂ => riemannZeta ((2 : ℂ) + u) / riemannZeta 2 := by
      funext u
      simp [eulerAffineBoundaryOverlap]
    rw [heq]
    exact hq.differentiableAt
  have hg : HasDerivAt
      (fun u : ℂ => 2 * (eulerAffineBoundaryOverlap (2 : ℂ) 1 u *
        (infinitePrimeFlux 2 - infinitePrimeFlux (2 + u))))
      (-2 * deriv infinitePrimeFlux 2) 0 := by
    have hmul := hoverlap.hasDerivAt.mul hdiff
    have hzero : infinitePrimeFlux 2 - infinitePrimeFlux (2 + (0 : ℂ)) = 0 := by ring
    have hone : eulerAffineBoundaryOverlap (2 : ℂ) 1 0 = 1 := by
      simp [eulerAffineBoundaryOverlap, hzeta]
    have hscaled := hmul.const_mul (2 : ℂ)
    have hderiv : -2 * deriv infinitePrimeFlux 2 =
        2 * (deriv (eulerAffineBoundaryOverlap (2 : ℂ) 1) 0 *
          (infinitePrimeFlux 2 - infinitePrimeFlux (2 + 0)) +
          eulerAffineBoundaryOverlap (2 : ℂ) 1 0 * -deriv infinitePrimeFlux 2) := by
      rw [hzero, hone]
      ring
    rw [hderiv]
    exact hscaled
  have hopen : IsOpen {u : ℂ | 1 < ((2 : ℂ) + u).re} :=
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have heq : eulerAffineFisherScore (2 : ℂ) 1 =ᶠ[nhds 0]
      fun u : ℂ => 2 * (eulerAffineBoundaryOverlap (2 : ℂ) 1 u *
        (infinitePrimeFlux 2 - infinitePrimeFlux (2 + u))) := by
    filter_upwards [hopen.mem_nhds (by norm_num : 1 < ((2 : ℂ) + 0).re)] with u hu
    rw [eulerAffineFisherScore_eq_current_difference
      (sigma := (2 : ℂ)) (epsilon := 1) (u := u) (by norm_num) (by simpa using hu)]
    ring
  rw [heq.deriv_eq]
  exact hg.deriv

/-- The source Ward curvature is strictly ordered by the positive prime-power logarithmic moment. -/
theorem eulerAffineFisherScore_deriv_two_one_zero_re_pos :
    0 < (deriv (eulerAffineFisherScore (2 : ℂ) 1) 0).re := by
  rw [eulerAffineFisherScore_deriv_two_one_zero]
  have h := neg_deriv_infinitePrimeFlux_two_re_pos
  norm_num [Complex.mul_re] at h ⊢
  linarith

namespace HedenmalmThetaSource

/-- Exact cross-route identification of the source Ward curvature inside the pole-unit curvature. -/
theorem deriv_squarefreeMobiusCriticalRegularCurrent_one_eq_pole_add_eulerAffineFisherWard :
    deriv squarefreeMobiusCriticalRegularCurrent 1 =
      -deriv (logDeriv zetaResidueUnit) 1 +
        2 * deriv (eulerAffineFisherScore (2 : ℂ) 1) 0 := by
  rw [deriv_squarefreeMobiusCriticalRegularCurrent_eq_pole_curvature_add_euler_curvature,
    eulerAffineFisherScore_deriv_two_one_zero]
  ring

end HedenmalmThetaSource

/-- **`ORD + LAND` source producer.**  Strict pre-divisor Ward order, its exact Hedenmalm
curvature incidence, and safe completed-Xi landing come from the same unselected Euler family. -/
theorem eulerAffineHedenmalmWardOrderLanding_producer :
    (0 < (deriv (eulerAffineFisherScore (2 : ℂ) 1) 0).re) ∧
      (deriv HedenmalmThetaSource.squarefreeMobiusCriticalRegularCurrent 1 =
        -deriv (logDeriv zetaResidueUnit) 1 +
          2 * deriv (eulerAffineFisherScore (2 : ℂ) 1) 0) ∧
      (∀ u : ℂ, 1 < ((2 : ℂ) + u * 1).re →
        eulerAffineGammaXiWardTransportV (2 : ℂ) 1
            (eulerAffineFisherScore (2 : ℂ) 1) u =
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate ((2 : ℂ) + u * 1))) := by
  refine ⟨eulerAffineFisherScore_deriv_two_one_zero_re_pos,
    HedenmalmThetaSource.deriv_squarefreeMobiusCriticalRegularCurrent_one_eq_pole_add_eulerAffineFisherWard,
    ?_⟩
  intro u hu
  exact eulerAffineGammaXiWardTransportV_eq_continuedSource
    (sigma := (2 : ℂ)) (epsilon := 1) (u := u)
    (by norm_num) hu (by norm_num)

end

end RHTower
