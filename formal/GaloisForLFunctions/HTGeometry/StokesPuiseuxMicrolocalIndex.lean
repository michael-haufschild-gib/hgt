import GaloisForLFunctions.HTGeometry.StokesCellularMicrolocalSheaf
import GaloisForLFunctions.HTGeometry.StokesPuiseuxOrbitCoarea

/-!
# Puiseux contact as a directed microlocal Morse index

The cellular exponential sheaf for a branch difference of numerator degree `k` has `2k` singular
conormals and `k` directed decay conormals.  Tensoring by a root-space fiber multiplies every
microstalk rank by the root-space dimension.  Summing over branch orbits and normalizing by the
common cover degree recovers mixed Hom irregularity exactly.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

open CellularMicrolocal

namespace FinitePuiseuxFamily

variable {m K N : ℕ}

/-- Total directed-decay Morse multiplicity of one ordered branch pair. -/
def directedPairMorseMass (p : FinitePuiseuxFamily m K N)
    (fiberRank : Fin m → ℕ) (a b : Fin m) : ℕ :=
  ∑ wall : Fin (p.contactNumerator a b),
    microRank (fiberRank a * fiberRank b)
      (decayWall (p.contactNumerator a b) wall)
      (activeConormalSide (decayWall (p.contactNumerator a b) wall))

/-- Directed Morse multiplicity is contact numerator times root-space dimension. -/
theorem directedPairMorseMass_eq (p : FinitePuiseuxFamily m K N)
    (fiberRank : Fin m → ℕ) (a b : Fin m) :
    p.directedPairMorseMass fiberRank a b =
      p.contactNumerator a b * (fiberRank a * fiberRank b) := by
  exact directedDecayMicroRank_sum _ _

/-- Total characteristic-cycle multiplicity over all conormal rays of one ordered pair. -/
def fullPairCharacteristicMass (p : FinitePuiseuxFamily m K N)
    (fiberRank : Fin m → ℕ) (a b : Fin m) : ℕ :=
  ∑ wall : StokesWall (p.contactNumerator a b),
    microRank (fiberRank a * fiberRank b) wall (activeConormalSide wall)

/-- Full characteristic cycle has twice the directed-decay multiplicity. -/
theorem fullPairCharacteristicMass_eq (p : FinitePuiseuxFamily m K N)
    (fiberRank : Fin m → ℕ) (a b : Fin m) :
    p.fullPairCharacteristicMass fiberRank a b =
      2 * p.contactNumerator a b * (fiberRank a * fiberRank b) := by
  exact fullCharacteristicMultiplicity_sum _ _

end FinitePuiseuxFamily

namespace PuiseuxOrbitCoareaDatum

variable {n m K N : ℕ}

/-- Root-space rank pulled from irregular classes to Puiseux branches. -/
def branchFiberRank (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (a : Fin m) : ℕ :=
  fiberRank (d.orbit a)

/-- Orbit-summed directed Morse multiplicity, normalized by common-cover degree. -/
def normalizedMicrolocalHomMass (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (i j : Fin n) : ℝ :=
  d.toOrbitCoareaDatum.fiberSum i fun a =>
    d.toOrbitCoareaDatum.fiberSum j fun b =>
      (d.branches.directedPairMorseMass (d.branchFiberRank fiberRank) a b : ℝ) / N

/-- **Directed microlocal Hom index.** Normalized directed microstalk multiplicity is exactly
mixed Hom irregularity times the root-space dimension. -/
theorem normalizedMicrolocalHomMass_eq
    (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (i j : Fin n) :
    d.normalizedMicrolocalHomMass fiberRank i j =
      d.toOrbitCoareaDatum.homIrregularity i j *
        ((fiberRank i : ℝ) * fiberRank j) := by
  simp only [normalizedMicrolocalHomMass, OrbitCoareaDatum.fiberSum,
    FinitePuiseuxFamily.directedPairMorseMass_eq, branchFiberRank]
  rw [d.homIrregularity_eq_normalizedCoefficientSum]
  simp only [normalizedHomIrregularity]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_filter] at ha
  have ha' : d.orbit a = i := by simpa [toOrbitCoareaDatum] using ha.2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_filter] at hb
  have hb' : d.orbit b = j := by simpa [toOrbitCoareaDatum] using hb.2
  rw [ha', hb']
  push_cast
  ring

end PuiseuxOrbitCoareaDatum
end
end IrregularStokes
end GaloisForLFunctions
