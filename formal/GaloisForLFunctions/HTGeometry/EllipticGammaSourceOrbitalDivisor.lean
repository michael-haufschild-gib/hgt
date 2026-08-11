import GaloisForLFunctions.HTGeometry.EllipticGammaConeSource
import GaloisForLFunctions.HTGeometry.EllipticGammaConeOrder
import GaloisForLFunctions.HTGeometry.TripticSourceDivisor

/-!
# The additive orbital divisor of the elliptic gamma source

The elliptic gamma source is the logarithmic derivative of the elliptic gamma function, so the
order-`-1` coefficients of its `b`-difference along an orbit are exactly the shift orders of the
gamma function there.  Summing them gives the multiplicative orbital charge, which is `1` on the
orbit of the translation point and `0` on every orbit outside the period group.

The additive source therefore realizes an arbitrary single class of the additive orbital divisor —
the input the normal form needs to reduce a general mixed-constraint source to one of vanishing
divisor.

* `additiveOrbitalDivisor_ellipticGammaSourceTranslate` — the unit class;
* `additiveOrbitalDivisor_ellipticGammaSource_of_notMem` — nothing on any other class.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The additive orbital divisor of a source at order `-1` along the `σ`-orbit through `p`. -/
def additiveOrbitalDivisor (F : ℂ → ℂ) (σ p : ℂ) : ℂ :=
  ∑ᶠ m : ℤ, laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) (-1)

/-- The additive orbital divisor of a logarithmic derivative is the multiplicative orbital
charge. -/
theorem additiveOrbitalDivisor_logDeriv {Y : ℂ → ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ))
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (σ p : ℂ) :
    additiveOrbitalDivisor (logDeriv Y) σ p = ((tripticOrbitCharge Y σ p : ℤ) : ℂ) := by
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
        = ((shiftOrder Y σ (p + (m : ℂ) * σ) : ℤ) : ℂ) := fun m ↦
    laurentCoeff_shiftDiff_logDeriv hY hfin σ _
  rw [additiveOrbitalDivisor, finsum_congr hterm, ← intCast_finsum]
  rfl

/-- **The elliptic gamma source realizes the unit class.**  Its additive orbital divisor is `1` on
the orbit through the translation point. -/
theorem additiveOrbitalDivisor_ellipticGammaSourceTranslate {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) (hindep : IndepPeriods a b) (g : ℂ) :
    additiveOrbitalDivisor (logDeriv (ellipticGammaConeTranslate a b g)) b g = 1 := by
  rw [additiveOrbitalDivisor_logDeriv (meromorphicOn_ellipticGammaConeTranslate ha hb g)
    (meromorphicOrderAt_ellipticGammaConeTranslate_ne_top ha hb g) b g,
    tripticOrbitCharge_ellipticGammaConeTranslate ha hb hindep g]
  norm_num

/-- **The elliptic gamma source carries no charge off the period group.** -/
theorem additiveOrbitalDivisor_ellipticGammaSource_of_notMem {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) {p : ℂ} (hp : ¬ PeriodGroupMem a b p) :
    additiveOrbitalDivisor (logDeriv (ellipticGammaCone a b)) b p = 0 := by
  rw [additiveOrbitalDivisor_logDeriv (meromorphicOn_ellipticGammaCone ha hb)
    (meromorphicOrderAt_ellipticGammaCone_ne_top ha hb) b p,
    tripticOrbitCharge_ellipticGammaCone_of_notMem ha hb hp]
  norm_num

/-- The elliptic gamma source of the card is the logarithmic derivative of the cone product
quotient, so its additive orbital divisor is the multiplicative charge. -/
theorem additiveOrbitalDivisor_ellipticGammaSource {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) :
    additiveOrbitalDivisor (ellipticGammaSource a b) b 0 = 1 := by
  rw [ellipticGammaSource, additiveOrbitalDivisor_logDeriv (meromorphicOn_ellipticGammaCone ha hb)
    (meromorphicOrderAt_ellipticGammaCone_ne_top ha hb) b 0,
    tripticOrbitCharge_ellipticGammaCone ha hb hindep]
  norm_num

end

end GaloisForLFunctions.HTGeometry
