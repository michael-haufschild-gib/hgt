import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization

/-!
# Thermal return, replica purity, and exact degeneracy

The thermofield return amplitude is the partition function at complex inverse
temperature divided by the real partition function. Its completed-time squared
return has a strictly positive floor `Z(2β) / Z(β)^2`. Equality holds precisely
when the energies are distinct; degeneracies increase the plateau.

This connects the finite Gibbs, complex partition, and replica-collision APIs
to the discrete-spectrum mechanism in section 3 of Maldacena,
*Eternal black holes in Anti-de-Sitter*, arXiv:hep-th/0106112.
-/

open scoped BigOperators Interval Topology
open Filter

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- Thermal return is the normalized partition function at complex temperature. -/
theorem survival_eq_partition_ratio (β : ℝ) (E : α → ℝ) (t : ℝ) :
    finiteSpectralSurvivalAmplitude (finiteGibbsStateWeight β E) E t =
      finiteComplexGibbsPartition E ((β : ℂ) - (t : ℂ) * Complex.I) /
        (finiteGibbsPartition β E : ℂ) := by
  rw [finiteSpectralSurvivalAmplitude, finiteComplexGibbsPartition, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hexp :
      Complex.exp (-(E a : ℂ) * ((β : ℂ) - (t : ℂ) * Complex.I)) =
        (Real.exp (-β * E a) : ℂ) *
          Complex.exp (((E a * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, finiteGibbsStateWeight, Complex.ofReal_div]
  ring

omit [Nonempty α] in
/-- At one replica, energy rigidity is exactly absence of degenerate levels. -/
theorem replicaRigidAt_one_iff_injective (E : α → ℝ) :
    ReplicaRigidAt E 1 ↔ Function.Injective E := by
  classical
  constructor
  · intro h i j hij
    let p : α → ℕ := fun k => if k = i then 1 else 0
    let q : α → ℕ := fun k => if k = j then 1 else 0
    have hp : p ∈ Finset.univ.piAntidiag 1 := by
      simp [p, Finset.mem_piAntidiag]
    have hq : q ∈ Finset.univ.piAntidiag 1 := by
      simp [q, Finset.mem_piAntidiag]
    have henergy : replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q := by
      simpa [replicaMultiplicityEnergy, p, q] using hij
    have heq := congrFun (h p hp q hq henergy) i
    by_contra hne
    simp [p, q, hne] at heq
  · intro h p hp q hq henergy
    rw [piAntidiag_one_eq_image_single, Finset.mem_image] at hp hq
    obtain ⟨i, _, rfl⟩ := hp
    obtain ⟨j, _, rfl⟩ := hq
    have hij : E i = E j := by simpa [replicaMultiplicityEnergy] using henergy
    rw [h hij]

/-- The exact thermal completed-time return mass, including all degeneracies. -/
def returnPlateau (β : ℝ) (E : α → ℝ) : ℝ :=
  fidelityReplicaCollisionMass (finiteGibbsStateWeight β E) E 1

/-- Canonical purity is the unavoidable diagonal contribution to thermal return. -/
theorem purity_le_returnPlateau (β : ℝ) (E : α → ℝ) :
    finiteGibbsPurity β E ≤ returnPlateau β E := by
  have h := fidelityReplicaCollisionMass_floor_le (finiteGibbsStateWeight_pos β E) E 1
  simpa only [fidelityReplicaPermutationFloor_one_eq_sum_sq, finiteGibbsPurity,
    returnPlateau] using h

theorem partition_ratio_le_returnPlateau (β : ℝ) (E : α → ℝ) :
    finiteGibbsPartition (2 * β) E / finiteGibbsPartition β E ^ 2 ≤
      returnPlateau β E := by
  rw [← finiteGibbsPurity_eq_partitionRatio]
  exact purity_le_returnPlateau β E

theorem returnPlateau_pos (β : ℝ) (E : α → ℝ) :
    0 < returnPlateau β E :=
  (finiteGibbsPurity_pos β E).trans_le (purity_le_returnPlateau β E)

/-- The purity floor is sharp exactly for a nondegenerate spectrum.
No rational independence of gaps is required. -/
theorem returnPlateau_eq_purity_iff (β : ℝ) (E : α → ℝ) :
    returnPlateau β E = finiteGibbsPurity β E ↔ Function.Injective E := by
  have h := fidelityReplicaCollisionMass_eq_floor_iff
    (finiteGibbsStateWeight_pos β E) E 1
  simpa only [returnPlateau, fidelityReplicaPermutationFloor_one_eq_sum_sq,
    finiteGibbsPurity, replicaRigidAt_one_iff_injective] using h

/-- Any repeated energy makes the thermal plateau strictly exceed Gibbs purity. -/
theorem purity_lt_returnPlateau_iff (β : ℝ) (E : α → ℝ) :
    finiteGibbsPurity β E < returnPlateau β E ↔ ¬ Function.Injective E := by
  rw [← returnPlateau_eq_purity_iff β E]
  exact lt_iff_le_and_ne.trans (by
    simp only [purity_le_returnPlateau β E, true_and, ne_eq, eq_comm])

/-- Time average of the actual normalized complex-temperature partition function. -/
def partitionReturnMean (β : ℝ) (E : α → ℝ) (T : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ * ∫ t : ℝ in -T..T,
    (Complex.normSq (finiteComplexGibbsPartition E
      ((β : ℂ) - (t : ℂ) * Complex.I) / (finiteGibbsPartition β E : ℂ)) : ℂ)

omit [Nonempty α] in
/-- The exact mean-return limit exists for every finite Gibbs spectrum. -/
theorem partitionReturnMean_tendsto (β : ℝ) (E : α → ℝ) :
    Tendsto (partitionReturnMean β E) atTop (𝓝 (returnPlateau β E : ℂ)) := by
  have heq : partitionReturnMean β E =
      finiteSpectralSurvivalFidelityMean (finiteGibbsStateWeight β E) E 1 := by
    funext T
    simp only [partitionReturnMean, finiteSpectralSurvivalFidelityMean,
      finiteSpectralSurvivalFidelity, survival_eq_partition_ratio, pow_one]
  rw [heq]
  exact finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
    (finiteGibbsStateWeight β E) E 1

/-- Finite thermal spectra cannot lose all mean return at late times. -/
theorem partitionReturnMean_not_tendsto_zero (β : ℝ) (E : α → ℝ) :
    ¬ Tendsto (partitionReturnMean β E) atTop (𝓝 0) := by
  intro h
  have heq := tendsto_nhds_unique (partitionReturnMean_tendsto β E) h
  have hz : returnPlateau β E = 0 := Complex.ofReal_eq_zero.mp heq
  exact (returnPlateau_pos β E).ne' hz

/-- Independent thermal systems contribute the product of their purity floors,
even when sums of their energies create new resonances. -/
theorem tensor_purity_le_returnPlateau
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (β : ℝ) (E : α → ℝ) (F : γ → ℝ) :
    finiteGibbsPurity β E * finiteGibbsPurity β F ≤
      returnPlateau β (finiteTensorEnergy E F) := by
  rw [← finiteGibbsPurity_tensor]
  exact purity_le_returnPlateau β _

end

end GaloisForLFunctions.HTGeometry.Thermofield

#print axioms GaloisForLFunctions.HTGeometry.Thermofield.survival_eq_partition_ratio
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.replicaRigidAt_one_iff_injective
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.purity_le_returnPlateau
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.partition_ratio_le_returnPlateau
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.returnPlateau_pos
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.returnPlateau_eq_purity_iff
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.purity_lt_returnPlateau_iff
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.partitionReturnMean_tendsto
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.partitionReturnMean_not_tendsto_zero
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.tensor_purity_le_returnPlateau
