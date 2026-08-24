import GaloisForLFunctions.HTGeometry.HeisenbergHorizonRepresentation

/-!
# Hasse detection for Heisenberg commutator symbols

The faithful operator realization of derivations preserves not only maximal commutator rank but
the entire exterior-symbol kernel.  Hence equality and vanishing of global derivation
commutator symbols can be checked after passage to the Heisenberg operator algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

/-- Heisenberg operator observations distinguish exactly the same exterior symbols as the source
derivation commutator law. -/
theorem heisenbergLawCommutatorMap_congr_hasse_iff
    (ρ : V →ₗ[K] Derivation K L L) (z z' : ⋀[K]^2 V) :
    heisenbergLawCommutatorMap ρ z = heisenbergLawCommutatorMap ρ z' ↔
      derivationCommutatorMap ρ z = derivationCommutatorMap ρ z' := by
  change derivationEndomorphism (derivationCommutatorMap ρ z) =
      derivationEndomorphism (derivationCommutatorMap ρ z') ↔ _
  exact (derivationEndomorphism_injective (K := K) (L := L)).eq_iff

/-- A Heisenberg exterior commutator observation vanishes exactly when its source derivation
symbol vanishes. -/
theorem heisenbergLawCommutatorMap_eq_zero_hasse_iff
    (ρ : V →ₗ[K] Derivation K L L) (z : ⋀[K]^2 V) :
    heisenbergLawCommutatorMap ρ z = 0 ↔ derivationCommutatorMap ρ z = 0 := by
  simpa using heisenbergLawCommutatorMap_congr_hasse_iff ρ z 0

/-- Faithful operator realization preserves the full obstruction kernel, not merely whether that
kernel is trivial. -/
theorem heisenbergLawCommutatorMap_ker_eq
    (ρ : V →ₗ[K] Derivation K L L) :
    LinearMap.ker (heisenbergLawCommutatorMap ρ) =
      LinearMap.ker (derivationCommutatorMap ρ) := by
  ext z
  simp only [LinearMap.mem_ker, heisenbergLawCommutatorMap_eq_zero_hasse_iff]

end


end GaloisForLFunctions.HTGeometry
