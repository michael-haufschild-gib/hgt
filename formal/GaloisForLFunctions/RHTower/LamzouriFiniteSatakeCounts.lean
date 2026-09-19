import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.RHTower.SatakeReality

open Finset
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions

open HilbertMetric

noncomputable section

/-- A finite Satake packet completed by adjoining the conjugate of every parameter. -/
def finiteSatakeSymmetricPacket {n : ℕ} (f : Fin n → ℂ) : Multiset ℂ :=
  univ.val.map f + (univ.val.map f).map (starRingEnd ℂ)

def finiteSatakeSymmetricSupport {n : ℕ} (f : Fin n → ℂ) : Finset ℂ :=
  (finiteSatakeSymmetricPacket f).toFinset

def finiteSatakeSymmetricMultiplicity {n : ℕ} (f : Fin n → ℂ) (z : ℂ) : ℕ :=
  (finiteSatakeSymmetricPacket f).count z

def finiteSatakeSymmetricCollisionMass {n : ℕ} (f : Fin n → ℂ) : ℝ :=
  finiteMultiplicityCollisionMass (finiteSatakeSymmetricSupport f)
    (finiteSatakeSymmetricMultiplicity f)

def finiteSatakeSymmetricSimpleSupport {n : ℕ} (f : Fin n → ℂ) : Finset ℂ :=
  finiteSimpleMultiplicitySupport (finiteSatakeSymmetricSupport f)
    (finiteSatakeSymmetricMultiplicity f)

theorem finiteSatakeSymmetricPacket_conj_closed {n : ℕ} (f : Fin n → ℂ) :
    (finiteSatakeSymmetricPacket f).map (starRingEnd ℂ) =
      finiteSatakeSymmetricPacket f := by
  unfold finiteSatakeSymmetricPacket
  rw [Multiset.map_add]
  have hdouble :
      ((univ.val.map f).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
        univ.val.map f := by
    simp only [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i hi
    simp [Function.comp_def]
  rw [hdouble]
  exact add_comm _ _

/-- Every power-sum moment of the conjugation-completed packet is real. -/
theorem finiteSatakeSymmetricPacket_moment_real {n : ℕ}
    (f : Fin n → ℂ) (k : ℕ) :
    (starRingEnd ℂ)
        (((finiteSatakeSymmetricPacket f).map fun z => z ^ k).sum) =
      ((finiteSatakeSymmetricPacket f).map fun z => z ^ k).sum :=
  selfDual_moment_real _ (finiteSatakeSymmetricPacket_conj_closed f) k

theorem finiteSatakeSymmetricMultiplicityMass_eq {n : ℕ} (f : Fin n → ℂ) :
    finiteMultiplicityMass (finiteSatakeSymmetricSupport f)
        (finiteSatakeSymmetricMultiplicity f) = (2 * n : ℕ) := by
  have hnat :
      (∑ z ∈ finiteSatakeSymmetricSupport f,
          finiteSatakeSymmetricMultiplicity f z) =
        (finiteSatakeSymmetricPacket f).card := by
    apply Multiset.sum_count_eq_card
    intro z hz
    exact Multiset.mem_toFinset.mpr hz
  unfold finiteMultiplicityMass
  rw [← Nat.cast_sum, hnat]
  simp [finiteSatakeSymmetricPacket]
  ring

/-- Lamzouri's first multiplicity inequality for a finite self-dual Satake packet. -/
theorem finiteSatakeSymmetricSimpleSupport_lower {n : ℕ} (f : Fin n → ℂ) :
    2 * (2 * n : ℕ) - finiteSatakeSymmetricCollisionMass f ≤
      ((finiteSatakeSymmetricSimpleSupport f).card : ℝ) := by
  have h := finiteSimpleMultiplicitySupport_lower
    (finiteSatakeSymmetricSupport f) (finiteSatakeSymmetricMultiplicity f)
  rw [finiteSatakeSymmetricMultiplicityMass_eq] at h
  exact h

/-- Lamzouri's distinctness inequality for a finite self-dual Satake packet. -/
theorem finiteSatakeSymmetricDistinctSupport_lower {n : ℕ} (f : Fin n → ℂ) :
    (3 / 2 : ℝ) * (2 * n : ℕ) -
        (1 / 2 : ℝ) * finiteSatakeSymmetricCollisionMass f ≤
      ((finiteSatakeSymmetricSupport f).card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower
    (finiteSatakeSymmetricSupport f) (finiteSatakeSymmetricMultiplicity f)
  have hs : finitePositiveMultiplicitySupport
      (finiteSatakeSymmetricSupport f) (finiteSatakeSymmetricMultiplicity f) =
      finiteSatakeSymmetricSupport f := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    apply Multiset.count_pos.mpr
    exact Multiset.mem_toFinset.mp hz
  rw [hs, finiteSatakeSymmetricMultiplicityMass_eq] at h
  exact h

end

end GaloisForLFunctions
