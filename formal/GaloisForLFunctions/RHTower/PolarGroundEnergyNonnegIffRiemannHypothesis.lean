import GaloisForLFunctions.RHTower.WeilPrimeMeasureRigidityFinite
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarBombieriYoshida
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityPrimeTwo

/-!
# Pole-vanishing Weil positivity at every aperture is exactly the Riemann hypothesis

The restricted-Weil route asks for nonnegativity of the pole-vanishing ground energy `μ₀(a)` at
every aperture `a`.  Bombieri–Yoshida gives the hard direction (nonnegativity at all apertures
implies RH).  Conversely, under RH the unconstrained ground energy is nonnegative at every aperture,
and the pole-vanishing ground energy dominates it.  This is the route's receiver (a two-sided
equivalence), not an obstruction to any producer.

What is unconditional is positivity on a bounded range of apertures: the pole-vanishing ground
energy is at least `1/20` for every aperture `a ≤ ½ (log 2 + 1/50)`.
-/

namespace RHTower

/-- **The restricted-Weil open step is equivalent to RH** (Bombieri–Yoshida and its converse). -/
theorem riemannHypothesis_iff_forall_polarGroundEnergy_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilPolarGroundEnergy a :=
  ⟨fun hRH a => (WeilDeletion.ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a).trans
      (ccmRestrictedWeilGroundEnergy_le_polar a),
    riemannHypothesis_of_polarGroundEnergy_nonneg⟩

/-- **The unconditional range.**  On apertures `a ≤ ½ (log 2 + 1/50)` the pole-vanishing ground
energy is at least `1/20`; RH is equivalent to nonnegativity on all remaining apertures. -/
theorem riemannHypothesis_iff_polarGroundEnergy_nonneg_beyond_primeTwo :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, (Real.log 2 + 1 / 50) / 2 < a.1 →
      0 ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  rw [riemannHypothesis_iff_forall_polarGroundEnergy_nonneg]
  constructor
  · exact fun h a _ => h a
  · intro h a
    by_cases ha : a.1 ≤ (Real.log 2 + 1 / 50) / 2
    · exact le_trans (by norm_num)
        (one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo a ha)
    · exact h a (lt_of_not_ge ha)

end RHTower
