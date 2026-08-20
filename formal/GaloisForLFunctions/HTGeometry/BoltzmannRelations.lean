import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization
import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy
import GaloisForLFunctions.HTGeometry.ThermodynamicCycleAffinity

/-!
# Finite Boltzmann relations

For a nonempty finite state space, microcanonical entropy is the logarithm of
the zero-inverse-temperature partition function.  This identifies the uniform
Gibbs population, Wightman kernel, replica purity, energy moments, and
independent-system tensor product with exact exponential entropy factors.

At zero inverse temperature every Gibbs population affinity and every induced
walk affinity vanishes.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The microcanonical entropy is the logarithm of the canonical partition at zero inverse
temperature. -/
theorem finiteMicrocanonicalEntropy_eq_log_finiteGibbsPartition_zero
    (I : Type*) [Fintype I] (energy : I → ℝ) :
    finiteMicrocanonicalEntropy I =
      Real.log (HTGeometry.finiteGibbsPartition 0 energy) := by
  rw [HTGeometry.finiteGibbsPartition_zero]
  rfl

/-- The zero-inverse-temperature partition is the exponential of microcanonical entropy. -/
theorem finiteGibbsPartition_zero_eq_exp_finiteMicrocanonicalEntropy
    (I : Type*) [Fintype I] [Nonempty I] (energy : I → ℝ) :
    HTGeometry.finiteGibbsPartition 0 energy =
      Real.exp (finiteMicrocanonicalEntropy I) := by
  rw [HTGeometry.finiteGibbsPartition_zero, finiteMicrocanonicalEntropy,
    Real.exp_log]
  positivity

/-- At zero inverse temperature every Gibbs population is the uniform microcanonical weight. -/
theorem finiteGibbsStateWeight_zero_eq_microcanonicalWeight
    {I : Type*} [Fintype I] (energy : I → ℝ) (i : I) :
    HTGeometry.finiteGibbsStateWeight 0 energy i = microcanonicalWeight I i := by
  rw [HTGeometry.finiteGibbsStateWeight, HTGeometry.finiteGibbsPartition_zero]
  simp [microcanonicalWeight]

/-- Each zero-inverse-temperature Gibbs population is the inverse Boltzmann multiplicity. -/
theorem finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy
    {I : Type*} [Fintype I] (energy : I → ℝ) (i : I) :
    HTGeometry.finiteGibbsStateWeight 0 energy i =
      Real.exp (-finiteMicrocanonicalEntropy I) := by
  letI : Nonempty I := ⟨i⟩
  rw [finiteGibbsStateWeight_zero_eq_microcanonicalWeight]
  simpa [microcanonicalWeight] using
    (exp_neg_finiteMicrocanonicalEntropy_eq_card_inv I).symm

/-- The zero-inverse-temperature Wightman kernel is the uniform microcanonical weight. -/
theorem finiteKMSWightmanWeight_zero_eq_microcanonicalWeight
    {I : Type*} [Fintype I] (energy : I → ℝ) (i j : I) :
    HTGeometry.finiteKMSWightmanWeight 0 energy i j = microcanonicalWeight I i := by
  rw [HTGeometry.finiteKMSWightmanWeight, HTGeometry.finiteGibbsPartition_zero]
  simp [microcanonicalWeight]

/-- Every zero-inverse-temperature Wightman kernel entry is the inverse Boltzmann
multiplicity. -/
theorem finiteKMSWightmanWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy
    {I : Type*} [Fintype I] (energy : I → ℝ) (i j : I) :
    HTGeometry.finiteKMSWightmanWeight 0 energy i j =
      Real.exp (-finiteMicrocanonicalEntropy I) := by
  letI : Nonempty I := ⟨i⟩
  rw [finiteKMSWightmanWeight_zero_eq_microcanonicalWeight]
  simpa [microcanonicalWeight] using
    (exp_neg_finiteMicrocanonicalEntropy_eq_card_inv I).symm

/-- Zero-temperature Gibbs purity is the inverse Boltzmann multiplicity. -/
theorem finiteGibbsPurity_zero_eq_exp_neg_finiteMicrocanonicalEntropy
    {I : Type*} [Fintype I] [Nonempty I] (energy : I → ℝ) :
    HTGeometry.finiteGibbsPurity 0 energy =
      Real.exp (-finiteMicrocanonicalEntropy I) := by
  rw [HTGeometry.finiteGibbsPurity_zero,
    exp_neg_finiteMicrocanonicalEntropy_eq_card_inv]
  simp [one_div]

/-- The diagonal squared mass of the zero-inverse-temperature thermofield kernel is the inverse
Boltzmann multiplicity. -/
theorem sum_sq_diag_finiteKMSWightmanWeight_zero_eq_exp_neg_entropy
    {I : Type*} [Fintype I] [Nonempty I] (energy : I → ℝ) :
    ∑ i, HTGeometry.finiteKMSWightmanWeight 0 energy i i ^ 2 =
      Real.exp (-finiteMicrocanonicalEntropy I) := by
  rw [HTGeometry.sum_sq_diag_finiteKMSWightmanWeight_eq_purity,
    finiteGibbsPurity_zero_eq_exp_neg_finiteMicrocanonicalEntropy]

/-- The off-diagonal squared thermofield mass at zero inverse temperature is one minus the
inverse Boltzmann multiplicity. -/
theorem sum_offDiagonal_sq_finiteKMSWightmanWeight_zero_eq_one_sub_exp_neg_entropy
    {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] (energy : I → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        HTGeometry.finiteKMSWightmanWeight 0 energy i j ^ 2) =
      1 - Real.exp (-finiteMicrocanonicalEntropy I) := by
  rw [HTGeometry.sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity,
    finiteGibbsPurity_zero_eq_exp_neg_finiteMicrocanonicalEntropy]

/-- Microcanonical entropy is additive for independent finite state spaces. -/
theorem finiteMicrocanonicalEntropy_prod
    (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] :
    finiteMicrocanonicalEntropy (I × J) =
      finiteMicrocanonicalEntropy I + finiteMicrocanonicalEntropy J := by
  have hI : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hJ : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [finiteMicrocanonicalEntropy, Fintype.card_prod,
    Nat.cast_mul, Real.log_mul hI hJ]
  rfl

/-- The zero-inverse-temperature partition of an independent product is the exponential of the
sum of its microcanonical entropies. -/
theorem finiteGibbsPartition_zero_tensor_eq_exp_entropy_add
    (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (energyI : I → ℝ) (energyJ : J → ℝ) :
    HTGeometry.finiteGibbsPartition 0
        (HTGeometry.finiteTensorEnergy energyI energyJ) =
      Real.exp (finiteMicrocanonicalEntropy I + finiteMicrocanonicalEntropy J) := by
  rw [finiteGibbsPartition_zero_eq_exp_finiteMicrocanonicalEntropy,
    finiteMicrocanonicalEntropy_prod]

/-- A zero-inverse-temperature product Gibbs population is the inverse exponential of the sum
of the component microcanonical entropies. -/
theorem finiteGibbsStateWeight_zero_tensor_eq_exp_neg_entropy_add
    {I J : Type*} [Fintype I] [Fintype J]
    (energyI : I → ℝ) (energyJ : J → ℝ) (i : I) (j : J) :
    HTGeometry.finiteGibbsStateWeight 0
        (HTGeometry.finiteTensorEnergy energyI energyJ) (i, j) =
      Real.exp (-(finiteMicrocanonicalEntropy I + finiteMicrocanonicalEntropy J)) := by
  letI : Nonempty I := ⟨i⟩
  letI : Nonempty J := ⟨j⟩
  rw [finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy,
    finiteMicrocanonicalEntropy_prod]

/-- Uniform Gibbs weights of independent systems factor into their microcanonical weights. -/
theorem finiteGibbsStateWeight_zero_tensor_eq_mul
    {I J : Type*} [Fintype I] [Fintype J]
    (energyI : I → ℝ) (energyJ : J → ℝ) (i : I) (j : J) :
    HTGeometry.finiteGibbsStateWeight 0
        (HTGeometry.finiteTensorEnergy energyI energyJ) (i, j) =
      microcanonicalWeight I i * microcanonicalWeight J j := by
  rw [finiteGibbsStateWeight_zero_eq_microcanonicalWeight]
  simp only [microcanonicalWeight, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- The zero-inverse-temperature mean energy is the microcanonical average expressed through
the inverse Boltzmann multiplicity. -/
theorem finiteGibbsEnergyMean_zero_eq_exp_neg_entropy_mul_sum
    {I : Type*} [Fintype I] [Nonempty I] (energy : I → ℝ) :
    HTGeometry.finiteGibbsEnergyMean 0 energy =
      Real.exp (-finiteMicrocanonicalEntropy I) * ∑ i, energy i := by
  unfold HTGeometry.finiteGibbsEnergyMean
  simp_rw [finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy]
  rw [Finset.mul_sum]

/-- The zero-inverse-temperature energy variance has the corresponding uniform Boltzmann
normalization. -/
theorem finiteGibbsEnergyVariance_zero_eq_entropy_weighted
    {I : Type*} [Fintype I] [Nonempty I] (energy : I → ℝ) :
    HTGeometry.finiteGibbsEnergyVariance 0 energy =
      Real.exp (-finiteMicrocanonicalEntropy I) * ∑ i, energy i ^ 2 -
        (Real.exp (-finiteMicrocanonicalEntropy I) * ∑ i, energy i) ^ 2 := by
  unfold HTGeometry.finiteGibbsEnergyVariance HTGeometry.finiteGibbsEnergyMean
  simp_rw [finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy]
  rw [Finset.mul_sum, Finset.mul_sum]

/-- The product Gibbs law has the squared inverse multiplicity at zero inverse temperature. -/
theorem finiteGibbsProductGapIntensity_zero_eq_exp_neg_two_entropy
    {I : Type*} [Fintype I] (energy : I → ℝ) (i j : I) :
    HTGeometry.finiteGibbsProductGapIntensity 0 energy i j =
      Real.exp (-2 * finiteMicrocanonicalEntropy I) := by
  unfold HTGeometry.finiteGibbsProductGapIntensity
  rw [finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy,
    finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy,
    ← Real.exp_add]
  congr 1
  ring

/-- Every unsymmetrized Gibbs transition intensity at zero inverse temperature carries the
common inverse Boltzmann multiplicity. -/
theorem finiteGibbsTransitionIntensity_zero_eq_exp_neg_entropy_mul_normSq
    {I : Type*} [Fintype I] (energy : I → ℝ) (amplitude : I → I → ℂ) (i j : I) :
    HTGeometry.finiteGibbsTransitionIntensity 0 energy amplitude i j =
      Real.exp (-finiteMicrocanonicalEntropy I) * Complex.normSq (amplitude i j) := by
  unfold HTGeometry.finiteGibbsTransitionIntensity
  rw [finiteGibbsStateWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy]

/-- Every symmetric Wightman transition intensity at zero inverse temperature carries the common
inverse Boltzmann multiplicity. -/
theorem finiteKMSWightmanTransitionIntensity_zero_eq_exp_neg_entropy_mul_normSq
    {I : Type*} [Fintype I] (energy : I → ℝ) (amplitude : I → I → ℂ) (i j : I) :
    HTGeometry.finiteKMSWightmanTransitionIntensity 0 energy amplitude i j =
      Real.exp (-finiteMicrocanonicalEntropy I) * Complex.normSq (amplitude i j) := by
  unfold HTGeometry.finiteKMSWightmanTransitionIntensity
  unfold HTGeometry.wightmanTransitionIntensity
  rw [finiteKMSWightmanWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy]

/-- Squared zero-inverse-temperature Wightman weights have the squared inverse multiplicity. -/
theorem finiteKMSWightmanWeight_sq_zero_eq_exp_neg_two_entropy
    {I : Type*} [Fintype I] (energy : I → ℝ) (i j : I) :
    HTGeometry.finiteKMSWightmanWeight 0 energy i j ^ 2 =
      Real.exp (-2 * finiteMicrocanonicalEntropy I) := by
  rw [finiteKMSWightmanWeight_zero_eq_exp_neg_finiteMicrocanonicalEntropy,
    pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The second Gibbs gap moment at zero inverse temperature is twice the uniform
Boltzmann-normalized energy variance. -/
theorem thermalGapMoment_finiteGibbsProduct_two_zero_eq_entropy_weighted
    {I : Type*} [Fintype I] [Nonempty I] (energy : I → ℝ) :
    HTGeometry.thermalGapMoment (HTGeometry.finiteGibbsProductGapIntensity 0 energy) energy 2 =
      2 * (Real.exp (-finiteMicrocanonicalEntropy I) * ∑ i, energy i ^ 2 -
        (Real.exp (-finiteMicrocanonicalEntropy I) * ∑ i, energy i) ^ 2) := by
  rw [HTGeometry.thermalGapMoment_finiteGibbsProduct_two_eq_two_mul_energyVariance,
    finiteGibbsEnergyVariance_zero_eq_entropy_weighted]

/-- Gibbs population affinity vanishes at zero inverse temperature. -/
theorem thermodynamicAffinity_finiteGibbsStateWeight_zero
    {I : Type*} [Fintype I] (energy : I → ℝ) (i j : I) :
    thermodynamicAffinity
        (HTGeometry.finiteGibbsStateWeight 0 energy j)
        (HTGeometry.finiteGibbsStateWeight 0 energy i) = 0 := by
  rw [thermodynamicAffinity_finiteGibbsStateWeight]
  ring

/-- Every Gibbs population walk has zero affinity at zero inverse temperature. -/
theorem thermodynamicWalkAffinity_finiteGibbsStateWeight_zero
    {I : Type*} [Fintype I] {G : SimpleGraph I}
    (energy : I → ℝ) {i j : I} (p : G.Walk i j) :
    thermodynamicWalkAffinity
        (fun u _ => HTGeometry.finiteGibbsStateWeight 0 energy u) p = 0 := by
  rw [thermodynamicWalkAffinity_finiteGibbsStateWeight]
  ring

end

end GaloisForLFunctions.HTGeometry
