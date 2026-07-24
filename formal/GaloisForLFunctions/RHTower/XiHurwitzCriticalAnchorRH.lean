import GaloisForLFunctions.RHTower.XiHurwitzHardyAnchor
import GaloisForLFunctions.RHTower.XiHurwitzOrientationUniversalityLaw
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# RH supplies the Hurwitz critical anchor chamber

The corpus already proves that RH makes every anchored two-node Hurwitz Vandermonde real.  The
infinite Xi divisor supplies an actual anchor, and RH places that anchor on the critical line.
This discharges the universal anchored-reality interface under RH and packages the exact remaining
content as existence of one critical anchor together with the universal reality chamber.
-/

open Complex Set

namespace RHTower

noncomputable section

open scoped Classical

/-- RH and the unconditional infinite Xi divisor supply an actual critical-line anchor. -/
theorem exists_xiHurwitzCriticalLineAnchor_of_rh
    (hRH : RiemannHypothesis) :
    ∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2 := by
  letI : Infinite XiDivisorSupport :=
    Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  let τ : XiDivisorSupport := Classical.choice
    (inferInstance : Nonempty XiDivisorSupport)
  exact ⟨τ, xi_divisor_support_re_eq_half_of_rh hRH τ⟩

/-- RH discharges reality of every critical-anchor Hurwitz pair separator. -/
theorem xiHurwitzEveryCriticalAnchorPairVandermondeReal_of_rh
    (hRH : RiemannHypothesis) :
    XiHurwitzEveryCriticalAnchorPairVandermondeReal := by
  intro τ _hτ
  exact xiHurwitzAnchoredPairVandermondeReal_of_rh hRH τ

/-- One actual critical anchor together with the universal anchored-reality interface is exactly
RH. -/
theorem exists_criticalAnchor_and_everyPairVandermondeReal_iff_rh :
    (∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2) ∧
        XiHurwitzEveryCriticalAnchorPairVandermondeReal ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hreal⟩
    exact (riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal
      τ hτ).mpr (hreal τ hτ)
  · intro hRH
    exact ⟨exists_xiHurwitzCriticalLineAnchor_of_rh hRH,
      xiHurwitzEveryCriticalAnchorPairVandermondeReal_of_rh hRH⟩

/-- RH discharges the full critical-anchor rigidity interface. -/
theorem xiHurwitzAllCriticalAnchorsRigid_of_rh
    (hRH : RiemannHypothesis) :
    XiHurwitzAllCriticalAnchorsRigid := by
  intro τ hτ
  exact ⟨
    (riemannHypothesis_iff_xiHurwitzAnchoredPairOrientationEnergy_eq_zero
      τ hτ).1 hRH,
    xiHurwitzAnchoredPairVandermondeReal_of_rh hRH τ⟩

/-- Existence of one critical anchor together with universal anchored rigidity is exactly RH. -/
theorem exists_criticalAnchor_and_allCriticalAnchorsRigid_iff_rh :
    (∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2) ∧
        XiHurwitzAllCriticalAnchorsRigid ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hrigid⟩
    exact
      (riemannHypothesis_iff_xiHurwitzAnchoredPairOrientationEnergy_eq_zero
        τ hτ).2 (hrigid τ hτ).1
  · intro hRH
    exact ⟨exists_xiHurwitzCriticalLineAnchor_of_rh hRH,
      xiHurwitzAllCriticalAnchorsRigid_of_rh hRH⟩

end

end RHTower
