import GaloisForLFunctions.RHTower.XiApexChargeCompleteStratumUniversalityLaw
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# Xi apex-charge confined complete-stratum universality

The finite-family Xi apex-charge stratum is locally prime-flux blind, globally conserved, and
quadratically unrefinable.  Euler-product far-field zero-freeness supplies its missing spatial
boundary: every nonzero charge in the family is confined to the critical half-strip.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-- Complete pointwise classification of a nonzero level-one Xi apex charge. -/
structure XiApexChargeConfinedStratumPointCertificate (ρ : ℂ) : Prop where
  lower : 1 / 2 < ρ.re
  upper : ρ.re ≤ 1
  primeFluxBlind :
    ∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod 2)
      (c : Nat.Primes →₀ ℤ),
      φ (primeFluxHom c) ≠
        _root_.RHTower.wCharge 2
          ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ)
  notRH : ¬ _root_.RiemannHypothesis

/-- Family-level certificate joining pointwise critical-half-strip confinement to global charge
conservation and Arf-density collapse. -/
structure XiApexChargeConfinedCompleteStratumCertificate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι) : Prop where
  pointwise :
    ∀ i ∈ s,
      _root_.RHTower.wCharge 2
          ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) ≠ 0 →
        XiApexChargeConfinedStratumPointCertificate (ρ i)
  conserved :
    ∑ i ∈ s,
      _root_.RHTower.wCharge 2
        ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) = 0
  arfCollapse :
    ∀ i ∈ s,
      _root_.RHTower.xiDeckParity (ρ i) *
          _root_.RHTower.xiDeckParity (ρ (σ i)) =
        _root_.RHTower.xiDeckParity (ρ i)

/-- **Xi apex-charge confined complete-stratum universality law.** On every fixed-point-free,
conjugation-closed finite right-half Xi family, each nonzero level-one charge is confined to
`1/2 < Re ρ ≤ 1`, is invisible to every prime-flux torsion reading, and refutes RH; the family
charge still sums to zero and its quadratic Arf density collapses to the same linear charge. -/
theorem xiApexCharge_confinedCompleteStratumUniversality
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i))
    (hR : ∀ i ∈ s, ρ i ∈ _root_.RHTower.rightHalf) :
    XiApexChargeConfinedCompleteStratumCertificate s ρ σ := by
  have hcomplete :=
    xi_apex_complete_charge_stratum s ρ σ hσs hσσ hfix hconj hR
  refine ⟨?_, hcomplete.2.1, hcomplete.2.2⟩
  intro i hi hcharge
  have hlocal := hcomplete.1 i hi hcharge
  have hlower : 1 / 2 < (ρ i).re :=
    _root_.RHTower.mem_rightHalf.mp (hR i hi)
  have hupper : (ρ i).re ≤ 1 := by
    by_contra hnot
    have hfar : 1 < (ρ i).re := lt_of_not_ge hnot
    have hxi : _root_.RHTower.xi (ρ i) ≠ 0 :=
      _root_.RHTower.xi_ne_zero_of_one_lt_re hfar
    have horder :
        analyticOrderAt _root_.RHTower.xi (ρ i) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hxi)
    apply hcharge
    rw [horder]
    simp
  exact ⟨hlower, hupper, hlocal.1, hlocal.2⟩

end RHTower
end GaloisForLFunctions
