import GaloisForLFunctions.HTGeometry.ConservativeDissipativeConsensus
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

set_option autoImplicit false

/-!
# Adaptive thermalization of finite Gibbs and KMS states

The Schaffer–Exl energy mechanism (arXiv:2609.04530), instantiated on the
existing finite Gibbs reference, produces an actual positive, normalized
implicit trajectory from any finite Gibbs state to any target finite Gibbs
state. The constructed complete mixing admits arbitrary time- and
state-dependent raw coefficients and step parameters. Reference normalization
gives a one-third density oscillation factor. Populations, real observable
expectations, and Wightman half-density kernels converge to the existing
thermal objects. Finite probability relative entropy decreases to zero,
and its initial value equals total physical-plus-temporal entropy loss.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Logarithmic reference of the existing finite Gibbs state. -/
def gibbsTransportReference (β : ℝ) (energy : ι → ℝ) (i : ι) : ℝ :=
  Real.log (_root_.HTGeometry.finiteGibbsStateWeight β energy i)

/-- The transport reference reconstructs the existing Gibbs probability exactly. -/
theorem exp_gibbsTransportReference (β : ℝ) (energy : ι → ℝ) (i : ι) :
    Real.exp (gibbsTransportReference β energy i) = _root_.HTGeometry.finiteGibbsStateWeight β energy i :=
  Real.exp_log (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy i)

/-- Gibbs normalization fixes the transport reference mass to one. -/
theorem gibbsTransportReference_mass (β : ℝ) (energy : ι → ℝ) :
    transportReferenceMass (gibbsTransportReference β energy) = 1 := by
  simp only [transportReferenceMass, exp_gibbsTransportReference,
    _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one]

/-- Normalized Gibbs transport has a common one-third oscillation contraction factor. -/
theorem gibbsTransportReference_contraction (β : ℝ) (energy : ι → ℝ) :
    transportContraction (gibbsTransportReference β energy) = (3 : ℝ)⁻¹ := by
  rw [transportContraction, gibbsTransportReference_mass]
  ring

/-- Any initial finite Gibbs state is encoded relative to any target finite Gibbs state. -/
def gibbsTransportInput (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (i : ι) : ℝ :=
  gibbsTransportReference β₀ energy₀ i - gibbsTransportReference β energy i

/-- The constructed relative input has precisely the prescribed initial Gibbs populations. -/
theorem gibbsTransportInput_population (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (i : ι) :
    Real.exp (gibbsTransportReference β energy i + gibbsTransportInput β₀ β energy₀ energy i) =
      _root_.HTGeometry.finiteGibbsStateWeight β₀ energy₀ i := by
  rw [gibbsTransportInput, ← add_sub_assoc, add_sub_cancel_left, exp_gibbsTransportReference]

/-- Both Gibbs states have unit mass, so the conserved relative density average is one. -/
theorem gibbsTransportInput_average (β₀ β : ℝ) (energy₀ energy : ι → ℝ) :
    transportAverage (gibbsTransportReference β energy)
      (fun i => Real.exp (gibbsTransportInput β₀ β energy₀ energy i)) = 1 := by
  simp only [transportAverage, gibbsTransportReference_mass, div_one, ← Real.exp_add,
    gibbsTransportInput_population, _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one]

/-- Actual adaptive implicit populations connecting two arbitrary finite Gibbs states. -/
def gibbsThermalPopulation (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  Real.exp (gibbsTransportReference β energy i +
    consensusLogOrbit a (gibbsTransportReference β energy) u (gibbsTransportInput β₀ β energy₀ energy) n i)

omit [Nonempty ι] in
/-- Every actual thermalizing population remains strictly positive. -/
theorem gibbsThermalPopulation_pos (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) (i : ι) :
    0 < gibbsThermalPopulation a u β₀ β energy₀ energy n i := Real.exp_pos _

/-- The adaptive thermalization starts at the exact existing initial Gibbs state. -/
theorem gibbsThermalPopulation_zero (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (i : ι) :
    gibbsThermalPopulation a u β₀ β energy₀ energy 0 i =
      _root_.HTGeometry.finiteGibbsStateWeight β₀ energy₀ i :=
  gibbsTransportInput_population β₀ β energy₀ energy i

/-- All intermediate Gibbs-thermalizing states are normalized probability distributions. -/
theorem gibbsThermalPopulation_mass (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) :
    ∑ i, gibbsThermalPopulation a u β₀ β energy₀ energy n i = 1 := by
  simp only [gibbsThermalPopulation, consensusLogOrbit, implicitEntropyOrbit_mass,
    gibbsTransportInput_population, _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one]

/-- The actual adaptive process converges to the existing target Gibbs probability at each state. -/
theorem gibbsThermalPopulation_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (i : ι) :
    Filter.Tendsto (fun n => gibbsThermalPopulation a u β₀ β energy₀ energy n i) Filter.atTop
      (nhds (_root_.HTGeometry.finiteGibbsStateWeight β energy i)) := by
  simpa only [gibbsThermalPopulation, gibbsTransportInput_average, exp_gibbsTransportReference, mul_one] using
    consensusPopulation_tendsto a (gibbsTransportReference β energy) u
      (gibbsTransportInput β₀ β energy₀ energy) i

/-- Explicit one-third geometric error bound to the target Gibbs state. -/
theorem gibbsThermalPopulation_error_bound (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) (i : ι) :
    |gibbsThermalPopulation a u β₀ β energy₀ energy n i - _root_.HTGeometry.finiteGibbsStateWeight β energy i| ≤
      _root_.HTGeometry.finiteGibbsStateWeight β energy i * (3 : ℝ)⁻¹ ^ n *
        transportOscillation (fun j => Real.exp (gibbsTransportInput β₀ β energy₀ energy j)) := by
  have h := consensusDensity_error_bound a (gibbsTransportReference β energy) u
    (gibbsTransportInput β₀ β energy₀ energy) n i
  rw [gibbsTransportInput_average, gibbsTransportReference_contraction] at h
  have hm := mul_le_mul_of_nonneg_left h (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy i).le
  have he : gibbsThermalPopulation a u β₀ β energy₀ energy n i -
      _root_.HTGeometry.finiteGibbsStateWeight β energy i =
      _root_.HTGeometry.finiteGibbsStateWeight β energy i *
        (consensusDensity a (gibbsTransportReference β energy) u (gibbsTransportInput β₀ β energy₀ energy) n i - 1) := by
    rw [gibbsThermalPopulation, Real.exp_add, exp_gibbsTransportReference]
    change _ = _ * (Real.exp _ - 1)
    ring
  rw [he, abs_mul, abs_of_pos (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy i)]
  simpa only [mul_assoc] using hm

/-- Relative entropy to the normalized target Gibbs reference along the actual process. -/
def gibbsThermalEntropy (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) : ℝ :=
  relativeEntropyEnergy (gibbsTransportReference β energy)
    (consensusLogOrbit a (gibbsTransportReference β energy) u (gibbsTransportInput β₀ β energy₀ energy) n) + 1

/-- The normalized target has relative Boltzmann energy minus one. -/
theorem relativeEntropyEnergy_gibbs_zero (β : ℝ) (energy : ι → ℝ) :
    relativeEntropyEnergy (gibbsTransportReference β energy) 0 = -1 := by
  simp [relativeEntropyEnergy, exp_gibbsTransportReference, Finset.sum_neg_distrib,
    _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one]

/-- The finite Gibbs relative entropy is nonnegative along the actual adaptive trajectory. -/
theorem gibbsThermalEntropy_nonneg (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) :
    0 ≤ gibbsThermalEntropy a u β₀ β energy₀ energy n := by
  have h := relativeEntropyEnergy_lower_bound (gibbsTransportReference β energy)
    (consensusLogOrbit a (gibbsTransportReference β energy) u (gibbsTransportInput β₀ β energy₀ energy) n)
  change -(transportReferenceMass (gibbsTransportReference β energy)) ≤ _ at h
  rw [gibbsTransportReference_mass] at h
  unfold gibbsThermalEntropy
  linarith

/-- Relative entropy to the target Gibbs state tends to zero under arbitrary adaptive mixing. -/
theorem gibbsThermalEntropy_tendsto_zero (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (u : ℕ → (ι → ℝ) → ℝ)
    (β₀ β : ℝ) (energy₀ energy : ι → ℝ) :
    Filter.Tendsto (gibbsThermalEntropy a u β₀ β energy₀ energy) Filter.atTop (nhds 0) := by
  have h := consensusLogOrbit_energy_tendsto a (gibbsTransportReference β energy) u
    (gibbsTransportInput β₀ β energy₀ energy)
  simp only [gibbsTransportInput_average, Real.log_one] at h
  change Filter.Tendsto _ _ (nhds (relativeEntropyEnergy (gibbsTransportReference β energy) 0)) at h
  rw [relativeEntropyEnergy_gibbs_zero] at h
  unfold gibbsThermalEntropy
  simpa only [neg_add_cancel] using h.add_const 1

/-- The energy above its normalized minimum is exactly finite probability relative entropy. -/
theorem gibbsThermalEntropy_eq_relativeEntropy (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (n : ℕ) :
    gibbsThermalEntropy a u β₀ β energy₀ energy n =
      ∑ i, gibbsThermalPopulation a u β₀ β energy₀ energy n i *
        Real.log (gibbsThermalPopulation a u β₀ β energy₀ energy n i /
          _root_.HTGeometry.finiteGibbsStateWeight β energy i) := by
  have hi : ∀ i, Real.log (gibbsThermalPopulation a u β₀ β energy₀ energy n i /
      _root_.HTGeometry.finiteGibbsStateWeight β energy i) =
      consensusLogOrbit a (gibbsTransportReference β energy) u
        (gibbsTransportInput β₀ β energy₀ energy) n i := by
    intro i
    rw [gibbsThermalPopulation, ← exp_gibbsTransportReference β energy i,
      ← Real.exp_sub, add_sub_cancel_left, Real.log_exp]
  simp only [hi, gibbsThermalEntropy, relativeEntropyEnergy, mul_sub, mul_one,
    Finset.sum_sub_distrib]
  change (∑ i, gibbsThermalPopulation a u β₀ β energy₀ energy n i *
      consensusLogOrbit a (gibbsTransportReference β energy) u (gibbsTransportInput β₀ β energy₀ energy) n i) -
      (∑ i, gibbsThermalPopulation a u β₀ β energy₀ energy n i) + 1 = _
  rw [gibbsThermalPopulation_mass]
  ring

omit [Nonempty ι] in
/-- Relative entropy decreases along the entire adaptive thermalization. -/
theorem gibbsThermalEntropy_antitone (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy : ι → ℝ) :
    Antitone (gibbsThermalEntropy a u β₀ β energy₀ energy) := by
  intro m n hmn
  have h := implicitEntropyOrbit_energy_antitone
    (fun k y => mixingCoefficients (a k y)) (gibbsTransportReference β energy)
    (fun k y => mixingStep (u k y)) (gibbsTransportInput β₀ β energy₀ energy) hmn
  unfold gibbsThermalEntropy consensusLogOrbit
  linarith

/-- Every finite real observable converges to its target Gibbs expectation. -/
theorem gibbsThermalExpectation_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy observable : ι → ℝ) :
    Filter.Tendsto (fun n => ∑ i, gibbsThermalPopulation a u β₀ β energy₀ energy n i * observable i)
      Filter.atTop (nhds (∑ i, _root_.HTGeometry.finiteGibbsStateWeight β energy i * observable i)) := by
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (gibbsThermalPopulation_tendsto a u β₀ β energy₀ energy i).mul_const (observable i))

/-- Adaptive population thermalization also recovers the existing KMS Wightman half-density kernel. -/
theorem gibbsThermalHalfDensity_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy : ι → ℝ) (i j : ι) :
    Filter.Tendsto (fun n => Real.sqrt (gibbsThermalPopulation a u β₀ β energy₀ energy n i *
      gibbsThermalPopulation a u β₀ β energy₀ energy n j)) Filter.atTop
      (nhds (_root_.HTGeometry.finiteKMSWightmanWeight β energy i j)) := by
  have h := ((gibbsThermalPopulation_tendsto a u β₀ β energy₀ energy i).mul
    (gibbsThermalPopulation_tendsto a u β₀ β energy₀ energy j)).sqrt
  rw [← _root_.HTGeometry.finiteKMSWightmanWeight_sq β energy i j, Real.sqrt_sq_eq_abs,
    abs_of_pos (_root_.HTGeometry.finiteKMSWightmanWeight_pos β energy i j)] at h
  exact h

/-- Total physical and temporal entropy loss equals the initial relative entropy to the target Gibbs state. -/
theorem gibbsThermal_total_entropy_loss (a : ℕ → (ι → ℝ) → ι → ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (β₀ β : ℝ) (energy₀ energy : ι → ℝ) :
    ∑' n, implicitEntropyOrbitLoss (fun k y => mixingCoefficients (a k y))
      (gibbsTransportReference β energy) (fun k y => mixingStep (u k y))
      (gibbsTransportInput β₀ β energy₀ energy) n = gibbsThermalEntropy a u β₀ β energy₀ energy 0 := by
  have h := consensus_total_entropy_loss a (gibbsTransportReference β energy) u
    (gibbsTransportInput β₀ β energy₀ energy)
  simp only [gibbsTransportInput_average, Real.log_one] at h
  change (∑' n, implicitEntropyOrbitLoss _ _ _ _ n) =
    relativeEntropyEnergy (gibbsTransportReference β energy) (gibbsTransportInput β₀ β energy₀ energy) -
      relativeEntropyEnergy (gibbsTransportReference β energy) 0 at h
  rw [relativeEntropyEnergy_gibbs_zero] at h
  change _ = relativeEntropyEnergy (gibbsTransportReference β energy)
    (gibbsTransportInput β₀ β energy₀ energy) + 1
  linarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
