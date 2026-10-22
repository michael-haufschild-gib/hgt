import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeMultiplicativeAutomorphismComparison
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

/-!
# Pointwise topology on multiplicative prime-fibre automorphisms

This module equips every finite cyclotomic-stage automorphism group with the discrete topology
and the compatible tower with its product/subtype topology.  The full group
`DeningerPrimeArithmeticMulAut p` receives the topology induced by simultaneous restriction.

The algebraic packet comparison is then proved to be a homeomorphism of topological groups.
Consequently the literal multiplicative automorphism group is compact, Hausdorff, and totally
disconnected in its pointwise prime-power-root topology.  No topology is transported from the
packet merely to make the conclusion true.
-/

namespace RHTower

noncomputable section

open Topology

/-- Finite cyclotomic-stage automorphism groups carry their natural discrete topology. -/
instance deningerPrimeArithmeticRootsMulAutTopologicalSpace
    (p l : Nat.Primes) (k : ℕ) :
    TopologicalSpace (MulAut (DeningerPrimeArithmeticRoots p l k)) :=
  ⊥

instance deningerPrimeArithmeticRootsMulAutDiscreteTopology
    (p l : Nat.Primes) (k : ℕ) :
    DiscreteTopology (MulAut (DeningerPrimeArithmeticRoots p l k)) :=
  ⟨rfl⟩

/-- Pointwise topology on full multiplicative automorphisms, induced by simultaneous restriction
to all compatible away-prime-power cyclotomic stages. -/
noncomputable instance deningerPrimeArithmeticMulAutTopologicalSpace
    (p : Nat.Primes) :
    TopologicalSpace (DeningerPrimeArithmeticMulAut p) :=
  TopologicalSpace.induced
    (deningerPrimeArithmeticMulAutTowerRestriction p) inferInstance

theorem deningerPrimeArithmeticMulAutTowerRestriction_isInducing
    (p : Nat.Primes) :
    IsInducing (deningerPrimeArithmeticMulAutTowerRestriction p) :=
  ⟨rfl⟩

theorem deningerPrimeArithmeticMulAutTowerRestriction_continuous
    (p : Nat.Primes) :
    Continuous (deningerPrimeArithmeticMulAutTowerRestriction p) :=
  continuous_induced_dom

noncomputable instance deningerPrimeArithmeticMulAutT2Space
    (p : Nat.Primes) :
    T2Space (DeningerPrimeArithmeticMulAut p) :=
  T2Space.of_injective_continuous
    (deningerPrimeArithmeticMulAutTowerRestriction_injective p)
    (deningerPrimeArithmeticMulAutTowerRestriction_continuous p)

noncomputable instance deningerPrimeArithmeticMulAutIsTopologicalGroup
    (p : Nat.Primes) :
    IsTopologicalGroup (DeningerPrimeArithmeticMulAut p) :=
  topologicalGroup_induced
    (deningerPrimeArithmeticMulAutTowerRestriction p)

theorem deningerPrimePacketCyclotomicStageAction_continuous
    (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    Continuous (deningerPrimePacketCyclotomicStageAction p l k) := by
  change Continuous (fun u =>
    deningerFiniteCyclicUnitActionOfCardEq _
      ((l.1 : ℕ) ^ k) (deningerPrimeArithmeticRoots_card p l k)
        (deningerPacketCoordinateReduction p l k u))
  exact continuous_of_discreteTopology.comp
    (deningerPacketCoordinateReduction_continuous p l k)

theorem deningerPrimePacketCompatibleCyclotomicTowerAction_continuous
    (p : Nat.Primes) :
    Continuous (deningerPrimePacketCompatibleCyclotomicTowerAction p) := by
  exact (continuous_pi fun l =>
    continuous_pi fun k =>
      deningerPrimePacketCyclotomicStageAction_continuous p l k).subtype_mk _

theorem deningerPrimePacketArithmeticMulAutMulEquiv_continuous
    (p : Nat.Primes) :
    Continuous (deningerPrimePacketArithmeticMulAutMulEquiv p) := by
  rw [continuous_induced_rng]
  exact
    (deningerPrimePacketCompatibleCyclotomicTowerAction_continuous p).congr
      (fun u =>
        (deningerPrimePacketArithmeticMulAutMulEquiv_restriction p u).symm)

/-- **Pointwise profinite comparison.**  Packet units are homeomorphic, as a topological group,
to all multiplicative automorphisms of the algebraic-closure units with the pointwise
prime-power-root topology. -/
noncomputable def deningerPrimePacketArithmeticMulAutContinuousMulEquiv
    (p : Nat.Primes) :
    DeningerPacketUnits p ≃ₜ* DeningerPrimeArithmeticMulAut p := by
  let E := deningerPrimePacketArithmeticMulAutMulEquiv p
  have hE : Continuous E :=
    deningerPrimePacketArithmeticMulAutMulEquiv_continuous p
  have hhome : IsHomeomorph E :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨hE, E.bijective⟩
  exact ContinuousMulEquiv.mk' (hhome.homeomorph E) (by
    intro x y
    change E (x * y) = E x * E y
    exact map_mul E x y)

@[simp] theorem deningerPrimePacketArithmeticMulAutContinuousMulEquiv_apply
    (p : Nat.Primes) (u : DeningerPacketUnits p) :
    deningerPrimePacketArithmeticMulAutContinuousMulEquiv p u =
      deningerPrimePacketArithmeticMulAutMulEquiv p u :=
  rfl

/-- Full multiplicative automorphisms commute: after restriction, multiplication is coordinatewise
in the product of away-prime local unit groups.  The unbundled instance avoids replacing the
canonical `MulAut` group structure. -/
noncomputable instance deningerPrimeArithmeticMulAutIsMulCommutative
    (p : Nat.Primes) :
    IsMulCommutative (DeningerPrimeArithmeticMulAut p) where
  is_comm := ⟨by
    intro f g
    apply
      (deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).symm.injective
    simpa only [map_mul] using
      mul_comm
        ((deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).symm f)
        ((deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).symm g)⟩

noncomputable instance deningerPrimeArithmeticMulAutCompactSpace
    (p : Nat.Primes) :
    CompactSpace (DeningerPrimeArithmeticMulAut p) :=
  (deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).toHomeomorph.compactSpace

noncomputable instance deningerPrimeArithmeticMulAutTotallyDisconnectedSpace
    (p : Nat.Primes) :
    TotallyDisconnectedSpace (DeningerPrimeArithmeticMulAut p) :=
  deningerTotallyDisconnected_of_injective
    (deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).symm.continuous
    (deningerPrimePacketArithmeticMulAutContinuousMulEquiv p).symm.injective

end

end RHTower
