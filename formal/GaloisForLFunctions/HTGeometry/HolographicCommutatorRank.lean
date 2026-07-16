import GaloisForLFunctions.HTGeometry.HorizonCommutatorGeometry
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Derivation.Lie

/-!
# Holographic horizon secants force commutator rank

The Lie bracket of a linear space of derivation laws is a linear map out of its second exterior
power.  An escaping chord of the complete differential-algebraic horizon is a decomposable symbol
outside this map's kernel.  Consequently, any geometric theorem forcing an escaping horizon
secant into every exterior subspace of codimension below `r` gives an unconditional rank-`r`
lower bound on the commutator map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [Field L] [Algebra K L] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- The Lie bracket of a linear derivation law as an alternating two-symbol. -/
def derivationCommutatorAlternatingMap
    (ρ : V →ₗ[K] Derivation K L L) :
    V [⋀^Fin 2]→ₗ[K] Derivation K L L where
  toFun f := ⁅ρ (f 0), ρ (f 1)⁆
  map_update_add' f i x y := by
    fin_cases i <;> simp
  map_update_smul' f i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' f i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all

/-- The commutator symbol as a linear map from the second exterior power of law space. -/
def derivationCommutatorMap
    (ρ : V →ₗ[K] Derivation K L L) :
    (⋀[K]^2 V) →ₗ[K] Derivation K L L :=
  exteriorPower.alternatingMapLinearEquiv (derivationCommutatorAlternatingMap ρ)

omit [CharZero K] in
@[simp]
theorem derivationCommutatorMap_wedge
    (ρ : V →ₗ[K] Derivation K L L) (v w : V) :
    derivationCommutatorMap ρ (exteriorPower.ιMulti K 2 ![v, w]) =
      ⁅ρ v, ρ w⁆ := by
  simp [derivationCommutatorMap, derivationCommutatorAlternatingMap]

omit [CharZero K] in
theorem derivation_commute_iff_commutator_eq_zero
    (D E : Derivation K L L) :
    Function.Commute D E ↔ ⁅D, E⁆ = 0 := by
  constructor
  · intro h
    ext z
    simpa [Derivation.commutator_apply] using sub_eq_zero.mpr (h z)
  · intro h z
    have hz := DFunLike.congr_fun h z
    simpa [Derivation.commutator_apply] using sub_eq_zero.mp hz

/-- An escaping hypertranscendental chord gives a decomposable exterior symbol outside the
commutator kernel. -/
theorem horizonSecant_not_mem_derivationCommutatorMap_ker
    (ρ : V →ₗ[K] Derivation K L L) (x : L) {v w : V}
    (hv : v ∈ linearDerivationDependenceHorizon ρ x)
    (hw : w ∈ linearDerivationDependenceHorizon ρ x)
    {a b : K}
    (hHT : AlgebraicIndependent K
      (linearDerivationLawJet ρ x (a • v + b • w))) :
    exteriorPower.ιMulti K 2 ![v, w] ∉ (derivationCommutatorMap ρ).ker := by
  intro hker
  have hzero : ⁅ρ v, ρ w⁆ = 0 := by
    simpa using hker
  exact (hypertranscendental_chord_forces_noncommute ρ x hv hw hHT)
    ((derivation_commute_iff_commutator_eq_zero (ρ v) (ρ w)).2 hzero)

/-- **Abstract holographic commutator-rank theorem.**  If every exterior subspace whose
codimension is smaller than `r` contains an escaping horizon secant, then the commutator symbol
has rank at least `r`. -/
theorem finrank_derivationCommutatorMap_range_ge_of_horizonSecant_avoidance
    [FiniteDimensional K V]
    (ρ : V →ₗ[K] Derivation K L L) (x : L) (r : ℕ)
    (hsecant : ∀ U : Submodule K (⋀[K]^2 V),
      Module.finrank K U + r > Module.finrank K (⋀[K]^2 V) →
      ∃ v w : V, ∃ a b : K,
        v ∈ linearDerivationDependenceHorizon ρ x ∧
        w ∈ linearDerivationDependenceHorizon ρ x ∧
        exteriorPower.ιMulti K 2 ![v, w] ∈ U ∧
        AlgebraicIndependent K
          (linearDerivationLawJet ρ x (a • v + b • w))) :
    r ≤ Module.finrank K (derivationCommutatorMap ρ).range := by
  by_contra hrank
  have hrank' : Module.finrank K (derivationCommutatorMap ρ).range < r :=
    Nat.lt_of_not_ge hrank
  have hnullity := LinearMap.finrank_range_add_finrank_ker
    (derivationCommutatorMap ρ)
  have hlarge : Module.finrank K (derivationCommutatorMap ρ).ker + r >
      Module.finrank K (⋀[K]^2 V) := by
    omega
  obtain ⟨v, w, a, b, hv, hw, hker, hHT⟩ :=
    hsecant (derivationCommutatorMap ρ).ker hlarge
  exact (horizonSecant_not_mem_derivationCommutatorMap_ker ρ x hv hw hHT) hker

end

end GaloisForLFunctions.HTGeometry
