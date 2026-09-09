import GaloisForLFunctions.HTGeometry.ConservativeDissipativeEntropy

set_option autoImplicit false

/-!
# KMS entropy production as conservative–dissipative energy loss

The evolution mechanism from Schaffer–Exl (arXiv:2609.04530) connects the
constructed population transport to existing finite KMS fluctuation–dissipation.
Hermitian amplitudes are built from square roots of the transport conductances.
At Gibbs populations, Boltzmann energy loss is exactly half the negative total
KMS entropy production, including arbitrary signed inverse temperature.
Stationarity is classified by inactive edges, zero inverse temperature, and
equal-energy transitions; normalization introduces no additional condition.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*}

/-- Hermitian transition amplitudes whose squared norms are the raw transport conductances. -/
def entropyKMSAmplitude (a : ι → ι → ℝ) (i j : ι) : ℂ :=
  Real.sqrt (entropyConductance a i j)

theorem entropyKMSAmplitude_hermitian (a : ι → ι → ℝ) (i j : ι) :
    entropyKMSAmplitude a j i = star (entropyKMSAmplitude a i j) := by
  simp only [entropyKMSAmplitude, Complex.star_def, Complex.conj_ofReal,
    entropyConductance_symm a j i]

theorem entropyKMSAmplitude_normSq (a : ι → ι → ℝ) (i j : ι) :
    Complex.normSq (entropyKMSAmplitude a i j) = entropyConductance a i j := by
  simp only [entropyKMSAmplitude, Complex.normSq_ofReal,
    Real.mul_self_sqrt (entropyConductance_nonneg a i j)]

variable [Fintype ι]

/-- Gibbs populations in logarithmic coordinates, at arbitrary signed inverse temperature. -/
def entropyGibbsCoordinate (β : ℝ) (energy : ι → ℝ) (i : ι) : ℝ :=
  Real.log (_root_.HTGeometry.finiteGibbsStateWeight β energy i)

theorem exp_entropyGibbsCoordinate (β : ℝ) (energy : ι → ℝ) (i : ι) :
    Real.exp (entropyGibbsCoordinate β energy i) =
      _root_.HTGeometry.finiteGibbsStateWeight β energy i := by
  letI : Nonempty ι := ⟨i⟩
  exact Real.exp_log (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy i)

/-- Transport entropy production is precisely the existing KMS transition intensity. -/
theorem entropyKMSIntensity_eq_transport (a : ι → ι → ℝ) (β : ℝ) (energy : ι → ℝ) (i j : ι) :
    finiteKMSEntropyProductionTransitionIntensity β energy (entropyKMSAmplitude a) i j =
      entropyConductance a i j * entropyProductionValue
        (Real.exp (entropyGibbsCoordinate β energy i))
        (Real.exp (entropyGibbsCoordinate β energy j)) := by
  letI : Nonempty ι := ⟨i⟩
  rw [finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq
      β energy _ (entropyKMSAmplitude_hermitian a), entropyKMSAmplitude_normSq,
    exp_entropyGibbsCoordinate, exp_entropyGibbsCoordinate,
    entropyProductionValue_reverse (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy i)
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy j), mul_comm]

/-- The nonlinear Gibbs-state energy derivative equals minus half the total KMS entropy production. -/
theorem hasDerivAt_entropyKMS_energy (a : ι → ι → ℝ) (β : ℝ) (energy : ι → ℝ) :
    HasDerivAt (fun t : ℝ => entropyEnergy (fun i => entropyGibbsCoordinate β energy i +
      t * entropyField a (entropyGibbsCoordinate β energy) i))
      (-((2 : ℝ)⁻¹) * ∑ i, ∑ j,
        finiteKMSEntropyProductionTransitionIntensity β energy (entropyKMSAmplitude a) i j) 0 := by
  simpa only [entropyKMSIntensity_eq_transport] using
    hasDerivAt_entropyField_energy a (entropyGibbsCoordinate β energy)

/-- Signed-temperature fluctuation–dissipation form of the same exact derivative. -/
theorem hasDerivAt_entropyKMS_energy_dissipative (a : ι → ι → ℝ) (β : ℝ) (energy : ι → ℝ) :
    HasDerivAt (fun t : ℝ => entropyEnergy (fun i => entropyGibbsCoordinate β energy i +
      t * entropyField a (entropyGibbsCoordinate β energy) i))
      (-((2 : ℝ)⁻¹) * β * ∑ i, ∑ j,
        _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity β energy (entropyKMSAmplitude a) i j) 0 := by
  convert hasDerivAt_entropyKMS_energy a β energy using 1
  simp only [finiteKMSEntropyProductionTransitionIntensity_eq_beta_mul_dissipative
    β energy _ (entropyKMSAmplitude_hermitian a), ← Finset.mul_sum]
  ring

/-- Energy gaps, rather than normalization, determine logarithmic Gibbs differences. -/
theorem entropyGibbsCoordinate_sub (β : ℝ) (energy : ι → ℝ) (i j : ι) :
    entropyGibbsCoordinate β energy i - entropyGibbsCoordinate β energy j =
      β * (energy j - energy i) := by
  letI : Nonempty ι := ⟨i⟩
  simp only [entropyGibbsCoordinate, _root_.HTGeometry.finiteGibbsStateWeight,
    Real.log_div (Real.exp_ne_zero _) (_root_.HTGeometry.finiteGibbsPartition_pos β energy).ne',
    Real.log_exp]
  ring

/-- Complete Gibbs stationarity classification: inactive edges, zero inverse temperature, or equal energies. -/
theorem entropyKMS_stationary_iff (a : ι → ι → ℝ) (β : ℝ) (energy : ι → ℝ) :
    entropyField a (entropyGibbsCoordinate β energy) = 0 ↔
      ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ β = 0 ∨ energy i = energy j := by
  rw [entropyField_eq_zero_iff]
  have he (i j : ι) : entropyGibbsCoordinate β energy i = entropyGibbsCoordinate β energy j ↔
      β = 0 ∨ energy i = energy j := by
    rw [← sub_eq_zero, entropyGibbsCoordinate_sub, mul_eq_zero, sub_eq_zero, eq_comm (a := energy j)]
  simp only [he]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
