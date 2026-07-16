import GaloisForLFunctions.HTGeometry.CommutingKaehlerPrincipalSymbol

/-!
# Horizon chord geometry detects noncommutativity

For a linear law map from an arbitrary vector space into field derivations, two dependence-horizon
directions whose derivations commute generate an entire projective line of dependence directions.
Consequently, a chord with dependent endpoints and one hypertranscendental interior direction is
an unconditional witness that the endpoint derivations do not commute.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [Field L] [Algebra K L] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- The ordinary jet of `x` along one direction in an arbitrary linear space of derivation laws. -/
def linearDerivationLawJet
    (ρ : V →ₗ[K] Derivation K L L) (x : L) (v : V) (n : ℕ) : L :=
  (((ρ v : Derivation K L L) : L → L)^[n]) x

/-- Directions along which the complete ordinary jet of `x` is algebraically dependent. -/
def linearDerivationDependenceHorizon
    (ρ : V →ₗ[K] Derivation K L L) (x : L) : Set V :=
  {v | ¬ AlgebraicIndependent K (linearDerivationLawJet ρ x v)}

/-- **Commuting-chord theorem.**  Two horizon directions whose derivations commute span only
horizon directions. -/
theorem commuting_horizon_chord
    (ρ : V →ₗ[K] Derivation K L L) (x : L) {v w : V}
    (hv : v ∈ linearDerivationDependenceHorizon ρ x)
    (hw : w ∈ linearDerivationDependenceHorizon ρ x)
    (hcomm : Function.Commute (ρ v) (ρ w)) :
    ∀ a b : K, a • v + b • w ∈ linearDerivationDependenceHorizon ρ x := by
  intro a b
  change ¬ AlgebraicIndependent K
    (fun r : ℕ ↦ (((ρ (a • v + b • w) : Derivation K L L) : L → L)^[r]) x)
  rw [map_add, map_smul, map_smul]
  exact commutingDerivations_superposition (ρ v) (ρ w) x hcomm hv hw a b

/-- **Horizon curvature witness.**  If a chord has dependent endpoints but contains one
hypertranscendental direction, the endpoint derivations cannot commute. -/
theorem hypertranscendental_chord_forces_noncommute
    (ρ : V →ₗ[K] Derivation K L L) (x : L) {v w : V}
    (hv : v ∈ linearDerivationDependenceHorizon ρ x)
    (hw : w ∈ linearDerivationDependenceHorizon ρ x)
    {a b : K}
    (hHT : AlgebraicIndependent K
      (linearDerivationLawJet ρ x (a • v + b • w))) :
    ¬ Function.Commute (ρ v) (ρ w) := by
  intro hcomm
  exact (commuting_horizon_chord ρ x hv hw hcomm a b) hHT

/-- On a pairwise commuting law subspace, the dependence horizon is closed under every binary
linear combination. -/
theorem commutingSubspace_horizon_linearCombination
    (ρ : V →ₗ[K] Derivation K L L) (x : L) (W : Submodule K V)
    (hcomm : ∀ v ∈ W, ∀ w ∈ W, Function.Commute (ρ v) (ρ w))
    {v w : V} (hvW : v ∈ W) (hwW : w ∈ W)
    (hv : v ∈ linearDerivationDependenceHorizon ρ x)
    (hw : w ∈ linearDerivationDependenceHorizon ρ x) :
    ∀ a b : K, a • v + b • w ∈ linearDerivationDependenceHorizon ρ x :=
  commuting_horizon_chord ρ x hv hw (hcomm v hvW w hwW)

end

end GaloisForLFunctions.HTGeometry
