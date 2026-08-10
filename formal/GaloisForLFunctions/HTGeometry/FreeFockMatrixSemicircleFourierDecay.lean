import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleCoordinateLaw
import GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralDensityDecay
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Fourier decay for diagonal finite matrix semicircles

For a coefficient family whose matrix Dyson branch is diagonal, the exact vacuum spectral
calculus is the diagonal matrix of the coordinate spectral laws.  Absolute continuity converts
each entry to its Radon--Nikodym density, so Riemann--Lebesgue decay upgrades to matrix
operator-norm decay in finite dimension.
-/

open Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Complex-valued Radon--Nikodym density of a finite positive measure. -/
noncomputable def spectralMeasureDensity (mu : Measure ℝ) (x : ℝ) : ℂ :=
  ((mu.rnDeriv volume x).toReal : ℂ)

theorem spectralMeasureDensity_integrable
    (mu : Measure ℝ) [IsFiniteMeasure mu] (hmu : mu ≪ volume) :
    Integrable (spectralMeasureDensity mu) volume := by
  have hreal : Integrable (fun x ↦ (mu.rnDeriv volume x).toReal) volume :=
    by
      simpa only [smul_eq_mul, mul_one] using
        (MeasureTheory.integrable_rnDeriv_smul_iff
          (E := ℝ) hmu (f := fun _ ↦ (1 : ℝ))).mpr
          (integrable_const (μ := mu) (1 : ℝ))
  exact hreal.ofReal

theorem spectralDensityFourierAmplitude_spectralMeasureDensity
    (mu : Measure ℝ) [IsFiniteMeasure mu] (hmu : mu ≪ volume) (t : ℝ) :
    spectralDensityFourierAmplitude (spectralMeasureDensity mu) t =
      ∫ x : ℝ, Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I) ∂mu := by
  rw [spectralDensityFourierAmplitude]
  have hRN := MeasureTheory.integral_rnDeriv_smul
    (E := ℂ) hmu
    (f := fun x : ℝ ↦ Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I))
  rw [← hRN]
  apply integral_congr_ae
  filter_upwards with x
  simp only [spectralMeasureDensity, Complex.ofReal_mul]
  exact mul_comm _ _

/-- Exact diagonal coordinate spectral density of a monomial matrix semicircle. -/
noncomputable def freeFockDiagonalSpectralDensity
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i j : I) (x : ℝ) : ℂ :=
  if i = j then
    spectralMeasureDensity
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) x
  else 0

/-- Vacuum-compressed real-time propagator supplied by the exact compact coordinate spectral
laws.  Under the monomial-column hypothesis, all off-diagonal vacuum moments vanish, so this is
the full matrix spectral calculus in the internal basis. -/
noncomputable def freeFockDiagonalVacuumPropagator
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (t : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal fun i ↦
    ∫ x : ℝ, Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I)
      ∂(freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)

theorem freeFockPower_vacuumCoefficient_offdiag_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hmono : MatrixFamilyHasSubsingletonColumns A)
    {i j : I} (hij : i ≠ j) (n : ℕ) :
    freeFockPower A j n (i, []) = 0 := by
  rw [freeFockPower_vacuumCoefficient A hA]
  split
  · rw [matrixDysonFormalCoeff_diagonal_of_subsingletonColumns A hmono]
    simp [hij]
  · rfl

theorem freeFockDiagonalVacuumPropagator_apply
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (t : ℝ) (i j : I) :
    freeFockDiagonalVacuumPropagator A hA hker t i j =
      if i = j then
        ∫ x : ℝ, Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I)
          ∂(freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)
      else 0 := by
  simp [freeFockDiagonalVacuumPropagator, Matrix.diagonal_apply]

theorem freeFockDiagonalVacuumPropagator_eq_densityAmplitude
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hac : ∀ i, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume)
    (t : ℝ) :
    freeFockDiagonalVacuumPropagator A hA hker t =
      finiteMatrixSpectralDensityAmplitude
        (freeFockDiagonalSpectralDensity A hA hker) t := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [freeFockDiagonalVacuumPropagator_apply, if_pos rfl]
    have hdensity : freeFockDiagonalSpectralDensity A hA hker i i =
        spectralMeasureDensity
          (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) := by
      funext x
      simp [freeFockDiagonalSpectralDensity]
    rw [finiteMatrixSpectralDensityAmplitude, hdensity]
    exact (spectralDensityFourierAmplitude_spectralMeasureDensity _ (hac i) t).symm
  · rw [freeFockDiagonalVacuumPropagator_apply, if_neg hij]
    simp [finiteMatrixSpectralDensityAmplitude, freeFockDiagonalSpectralDensity, hij,
      spectralDensityFourierAmplitude]

theorem freeFockDiagonalVacuumPropagator_entry_tendsto_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hac : ∀ i, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume)
    (i j : I) :
    Tendsto (fun t ↦ freeFockDiagonalVacuumPropagator A hA hker t i j)
      (cocompact ℝ) (𝓝 0) := by
  refine (finiteMatrixSpectralDensityAmplitude_entry_tendsto_zero
    (freeFockDiagonalSpectralDensity A hA hker) i j).congr' ?_
  exact Filter.Eventually.of_forall fun t ↦ (congrFun
    (congrFun (freeFockDiagonalVacuumPropagator_eq_densityAmplitude
      A hA hker hac t) i) j).symm

theorem freeFockDiagonalVacuumPropagator_matrixCoefficient_tendsto_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hac : ∀ i, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume)
    (x y : I → ℂ) :
    Tendsto (fun t ↦ star x ⬝ᵥ
      (freeFockDiagonalVacuumPropagator A hA hker t *ᵥ y))
      (cocompact ℝ) (𝓝 0) := by
  simp only [dotProduct, mulVec]
  have hout : Tendsto
      (fun t ↦ ∑ i : I, star x i *
        ∑ j : I, freeFockDiagonalVacuumPropagator A hA hker t i j * y j)
      (cocompact ℝ) (𝓝 (∑ _i : I, (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro i hi
    have hrow : Tendsto
        (fun t ↦ ∑ j : I,
          freeFockDiagonalVacuumPropagator A hA hker t i j * y j)
        (cocompact ℝ) (𝓝 (∑ _j : I, (0 : ℂ))) := by
      apply tendsto_finsetSum
      intro j hj
      simpa using
        (freeFockDiagonalVacuumPropagator_entry_tendsto_zero
          A hA hker hac i j).mul tendsto_const_nhds
    simpa using tendsto_const_nhds.mul hrow
  simpa using hout

theorem freeFockDiagonalVacuumPropagator_operatorNorm_tendsto_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hac : ∀ i, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume) :
    Tendsto (fun t ↦ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I))
      (freeFockDiagonalVacuumPropagator A hA hker t)‖)
      (cocompact ℝ) (𝓝 0) := by
  refine (finiteMatrixSpectralDensityAmplitude_operatorNorm_tendsto_zero
    (freeFockDiagonalSpectralDensity A hA hker)).congr' ?_
  exact Filter.Eventually.of_forall fun t ↦ congrArg
    (fun M : Matrix I I ℂ ↦ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) M‖)
    (freeFockDiagonalVacuumPropagator_eq_densityAmplitude A hA hker hac t).symm

end

end GaloisForLFunctions.HTGeometry
