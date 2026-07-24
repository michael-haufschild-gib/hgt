import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.SeamApexReflection
import GaloisForLFunctions.RHTower.SeamChargeStratum

/-!
# Xi apex-charge critical-half-strip confinement universality

The level-one additive Xi ladder charge was already known to be independent of every torsion
reading of the prime-flux lattice and, on the right half-plane, to obstruct RH. Euler-product
far-field zero-freeness supplies the missing spatial boundary: a nonzero apex bit cannot survive
past `Re ρ = 1`.
-/

open Complex

namespace GaloisForLFunctions
namespace RHTower

/-- A nonzero Xi apex bit right of the critical line is confined to the critical half-strip,
is invisible to every prime-flux torsion reading, and refutes RH. -/
structure XiApexChargeCriticalHalfStripCertificate (ρ : ℂ) : Prop where
  lower : 1 / 2 < ρ.re
  upper : ρ.re ≤ 1
  primeFluxBlind :
    ∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod 2)
      (c : Nat.Primes →₀ ℤ),
      φ (primeFluxHom c) ≠
        _root_.RHTower.wCharge 2
          ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ)
  notRH : ¬ _root_.RiemannHypothesis

/-- **Xi apex-charge critical-half-strip confinement law.** Every nonzero level-one Xi apex
charge on the right side is forced into `1/2 < Re ρ ≤ 1`; there it lies outside every prime-flux
torsion reading and is a pointwise obstruction to RH. -/
theorem xiApexCharge_criticalHalfStripConfinementUniversality
    {ρ : ℂ} (hρ : ρ ∈ _root_.RHTower.rightHalf)
    (hcharge :
      _root_.RHTower.wCharge 2
        ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) ≠ 0) :
    XiApexChargeCriticalHalfStripCertificate ρ := by
  have hlower : 1 / 2 < ρ.re := by
    exact _root_.RHTower.mem_rightHalf.mp hρ
  have hupper : ρ.re ≤ 1 := by
    by_contra hnot
    have hfar : 1 < ρ.re := lt_of_not_ge hnot
    have hxi : _root_.RHTower.xi ρ ≠ 0 :=
      _root_.RHTower.xi_ne_zero_of_one_lt_re hfar
    have horder :
        analyticOrderAt _root_.RHTower.xi ρ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hxi)
    apply hcharge
    rw [horder]
    simp
  refine ⟨hlower, hupper, ?_, ?_⟩
  · intro φ c
    exact nontrivial_wCharge_ne_primeFlux_charge φ hcharge c
  · apply _root_.RHTower.xiDeckParity_ne_zero_imp_not_rh hρ
    rw [xiDeckParity_eq_wCharge_two]
    exact hcharge

end RHTower
end GaloisForLFunctions
