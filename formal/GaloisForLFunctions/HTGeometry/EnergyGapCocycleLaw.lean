import GaloisForLFunctions.HTGeometry.LocalSpectralConnectedClusterDecomposition

/-!
# Energy gaps as an exact cocycle

Observable energy data are relational.  The pair field `Eᵢ - Eⱼ` obeys an
exact cocycle law; conversely, every pair field obeying that law comes from an
energy potential, unique up to one common translation.  Boolean interaction
packet projection commutes exactly with formation of this cocycle.

This is the algebraic joint between projective observer time and the local
connected-packet filtration.
-/

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- Relational pair field obtained from an energy potential. -/
def energyGapCocycle
    {I G : Type*} [AddCommGroup G]
    (energy : I → G) (i j : I) : G :=
  energy i - energy j

/-- Triangle-additive pair fields are precisely energy-gap cocycles. -/
def IsEnergyGapCocycle
    {I G : Type*} [AddCommGroup G]
    (gap : I → I → G) : Prop :=
  ∀ i j k, gap i j + gap j k = gap i k

theorem energyGapCocycle_isEnergyGapCocycle
    {I G : Type*} [AddCommGroup G]
    (energy : I → G) :
    IsEnergyGapCocycle (energyGapCocycle energy) := by
  intro i j k
  simp [energyGapCocycle]

/-- **Exact relational reconstruction.**  Every energy-gap cocycle comes from
an energy potential.  No finiteness or topology is required. -/
theorem isEnergyGapCocycle_iff_exists_energy
    {I G : Type*} [Nonempty I] [AddCommGroup G]
    (gap : I → I → G) :
    IsEnergyGapCocycle gap ↔
      ∃ energy : I → G, gap = energyGapCocycle energy := by
  constructor
  · intro hgap
    let base : I := Classical.choice ‹Nonempty I›
    refine ⟨fun i => gap i base, ?_⟩
    funext i j
    exact (eq_sub_iff_add_eq).2 (hgap i j base)
  · rintro ⟨energy, rfl⟩
    exact energyGapCocycle_isEnergyGapCocycle energy

/-- Two energy potentials generate the same complete relational field exactly
when they differ by one common energy-origin translation. -/
theorem energyGapCocycle_eq_iff_exists_translation
    {I G : Type*} [Nonempty I] [AddCommGroup G]
    (energy energy' : I → G) :
    energyGapCocycle energy = energyGapCocycle energy' ↔
      ∃ c : G, ∀ i, energy' i = energy i + c := by
  constructor
  · intro h
    let base : I := Classical.choice ‹Nonempty I›
    refine ⟨energy' base - energy base, ?_⟩
    intro i
    have hi := congrFun (congrFun h i) base
    unfold energyGapCocycle at hi
    calc
      energy' i = (energy' i - energy' base) + energy' base := by
        simp
      _ = (energy i - energy base) + energy' base := by
        rw [← hi]
      _ = energy i + (energy' base - energy base) := by
        abel
  · rintro ⟨c, hc⟩
    funext i j
    simp only [energyGapCocycle, hc]
    abel

theorem energyGapCocycle_translate
    {I G : Type*} [AddCommGroup G]
    (energy : I → G) (c : G) :
    energyGapCocycle (fun i => energy i + c) =
      energyGapCocycle energy := by
  funext i j
  simp [energyGapCocycle]

/-- **Packet--cocycle commutation law.**  Every Boolean control-packet sector
of a gap is exactly the difference of the corresponding packet sectors of
its endpoint energies.  Thus connected control filtration descends
canonically from energies to relational observer time. -/
theorem spectralPacketResponse_energyGapCocycle
    {E I : Type*} [DecidableEq E]
    (energy : (E → ℂ) → I → ℂ)
    (packet : Finset E) (z : E → ℂ) (i j : I) :
    spectralPacketResponse
        (fun coupling => energyGapCocycle (energy coupling) i j)
        packet z =
      spectralPacketResponse (fun coupling => energy coupling i)
          packet z -
        spectralPacketResponse (fun coupling => energy coupling j)
          packet z := by
  unfold spectralPacketResponse energyGapCocycle finsetMobiusResponse
  simp only [mul_sub, Finset.sum_sub_distrib]

end GaloisForLFunctions.HTGeometry
