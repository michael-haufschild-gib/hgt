import GaloisForLFunctions.RHTower.SeamApexReflection
import GaloisForLFunctions.RHTower.SeamChargeStratum

/-!
# Xi apex-charge complete-stratum universality law

Two terminal seam laws give complementary readings of the same level-one Xi deck parity.  Apex
reflection proves local prime-flux independence plus global conservation.  Charge stratification
proves Arf collapse plus pointwise RH refutation on the right half-plane.  Together they completely
classify a nonzero apex bit: locally inaccessible to every prime-flux torsion reading, globally
conserved to zero over a reflection family, quadratically unrefinable, and individually fatal to RH.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-- **Xi apex-charge complete-stratum universality law.**  On any fixed-point-free,
conjugation-closed finite family of right-half Xi points, every nonzero level-one apex charge is
simultaneously prime-flux independent and an RH obstruction; all charges still sum to zero, and
the quadratic Arf density collapses to the same linear charge. -/
theorem xi_apex_complete_charge_stratum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ρ : ι → ℂ) (σ : ι → ι)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i)
    (hconj : ∀ i ∈ s, ρ (σ i) = (starRingEnd ℂ) (ρ i))
    (hR : ∀ i ∈ s, ρ i ∈ _root_.RHTower.rightHalf) :
    (∀ i ∈ s,
      _root_.RHTower.wCharge 2
          ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) ≠ 0 →
        (∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod 2)
          (c : Nat.Primes →₀ ℤ),
          φ (primeFluxHom c) ≠
            _root_.RHTower.wCharge 2
              ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ)) ∧
        ¬ _root_.RiemannHypothesis) ∧
      (∑ i ∈ s,
        _root_.RHTower.wCharge 2
          ((analyticOrderAt _root_.RHTower.xi (ρ i)).toNat : ℤ) = 0) ∧
      (∀ i ∈ s,
        _root_.RHTower.xiDeckParity (ρ i) *
            _root_.RHTower.xiDeckParity (ρ (σ i)) =
          _root_.RHTower.xiDeckParity (ρ i)) := by
  have hapex := xi_apex_local_seam_global s ρ σ hσs hσσ hfix hconj
  have hstratum := _root_.RHTower.xi_charge_stratum
    s ρ σ hσs hσσ hfix hconj hR
  refine ⟨?_, hapex.2, hstratum.2.1⟩
  intro i hi hnz
  refine ⟨hapex.1 i hi hnz, ?_⟩
  apply hstratum.2.2 i hi
  rw [xiDeckParity_eq_wCharge_two]
  exact hnz

end RHTower
end GaloisForLFunctions
