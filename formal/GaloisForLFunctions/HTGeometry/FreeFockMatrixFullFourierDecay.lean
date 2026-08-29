import GaloisForLFunctions.HTGeometry.FreeFockMatrixFullAnalyticLaw
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleFourierDecay

/-!
# Fourier decay for full finite matrix semicircles

Complex polarization of four positive vector spectral laws gives every entry of the
vacuum-compressed propagator.  When the polarized atom matrix vanishes at every energy, all four
measures are absolutely continuous; their Radon--Nikodym densities therefore give entrywise
Riemann--Lebesgue decay and finite-dimensional operator-norm decay.
-/

open Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Fourier transform of an arbitrary internal-vector spectral measure. -/
noncomputable def freeFockVectorFourierAmplitude
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (t : ℝ) : ℂ :=
  ∫ a : ℝ, Complex.exp (-((t * a : ℝ) : ℂ) * Complex.I)
    ∂(freeFockVectorSpectralMeasure A hA hker x)

/-- Full vacuum-compressed propagator reconstructed by complex polarization. -/
noncomputable def freeFockMatrixVacuumPropagator
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (t : ℝ) : Matrix I I ℂ :=
  fun i j =>
    (4 : ℂ)⁻¹ *
        (freeFockVectorFourierAmplitude A hA hker
            (freeFockInternalBasis i + freeFockInternalBasis j) t -
          freeFockVectorFourierAmplitude A hA hker
            (freeFockInternalBasis i - freeFockInternalBasis j) t) -
      Complex.I * (4 : ℂ)⁻¹ *
        (freeFockVectorFourierAmplitude A hA hker
            (freeFockInternalBasis i + Complex.I • freeFockInternalBasis j) t -
          freeFockVectorFourierAmplitude A hA hker
            (freeFockInternalBasis i - Complex.I • freeFockInternalBasis j) t)

/-- Full polarized Radon--Nikodym density matrix. -/
noncomputable def freeFockMatrixSpectralDensity
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i j : I) (a : ℝ) : ℂ :=
  (4 : ℂ)⁻¹ *
      (spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker
            (freeFockInternalBasis i + freeFockInternalBasis j)) a -
        spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker
            (freeFockInternalBasis i - freeFockInternalBasis j)) a) -
    Complex.I * (4 : ℂ)⁻¹ *
      (spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker
            (freeFockInternalBasis i + Complex.I • freeFockInternalBasis j)) a -
        spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker
            (freeFockInternalBasis i - Complex.I • freeFockInternalBasis j)) a)

theorem freeFockVectorFourierAmplitude_eq_densityAmplitude
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ)
    (hac : freeFockVectorSpectralMeasure A hA hker x ≪ volume) (t : ℝ) :
    freeFockVectorFourierAmplitude A hA hker x t =
      spectralDensityFourierAmplitude
        (spectralMeasureDensity (freeFockVectorSpectralMeasure A hA hker x)) t := by
  exact (spectralDensityFourierAmplitude_spectralMeasureDensity
    (freeFockVectorSpectralMeasure A hA hker x) hac t).symm

/-- The polarized propagator is exactly the Fourier amplitude of its full density matrix. -/
theorem freeFockMatrixVacuumPropagator_eq_densityAmplitude
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hatom : ∀ a : ℝ, freeFockMatrixAtomMass A hA hker a = 0)
    (t : ℝ) :
    freeFockMatrixVacuumPropagator A hA hker t =
      finiteMatrixSpectralDensityAmplitude
        (freeFockMatrixSpectralDensity A hA hker) t := by
  ext i j
  let e : I → I → ℂ := freeFockInternalBasis
  have hac (x : I → ℂ) : freeFockVectorSpectralMeasure A hA hker x ≪ volume :=
    freeFockVectorSpectralMeasure_absolutelyContinuous_of_matrixAtomMass_eq_zero
      A hA hker hatom x
  let phi : ℝ → ℂ := fun a => Complex.exp (-((t * a : ℝ) : ℂ) * Complex.I)
  have hphi : AEStronglyMeasurable phi volume := by
    apply Continuous.aestronglyMeasurable
    dsimp only [phi]
    fun_prop
  have hphiBound : ∀ᵐ a : ℝ ∂volume, ‖phi a‖ ≤ 1 :=
    Filter.Eventually.of_forall fun a => by
      have hnorm := Complex.norm_exp_ofReal_mul_I (-(t * a))
      simpa [phi] using hnorm.le
  have hint (x : I → ℂ) : Integrable (fun a => phi a *
      spectralMeasureDensity (freeFockVectorSpectralMeasure A hA hker x) a) volume :=
    (spectralMeasureDensity_integrable
      (freeFockVectorSpectralMeasure A hA hker x) (hac x)).bdd_mul hphi hphiBound
  have hblockOne : Integrable (fun a => (4 : ℂ)⁻¹ *
      (phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i + e j)) a -
        phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i - e j)) a)) volume :=
    ((hint (e i + e j)).sub (hint (e i - e j))).const_mul _
  have hblockTwo : Integrable (fun a => Complex.I * (4 : ℂ)⁻¹ *
      (phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i + Complex.I • e j)) a -
        phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i - Complex.I • e j)) a)) volume :=
    ((hint (e i + Complex.I • e j)).sub
      (hint (e i - Complex.I • e j))).const_mul _
  rw [show freeFockMatrixVacuumPropagator A hA hker t i j =
      (4 : ℂ)⁻¹ *
          (freeFockVectorFourierAmplitude A hA hker (e i + e j) t -
            freeFockVectorFourierAmplitude A hA hker (e i - e j) t) -
        Complex.I * (4 : ℂ)⁻¹ *
          (freeFockVectorFourierAmplitude A hA hker (e i + Complex.I • e j) t -
            freeFockVectorFourierAmplitude A hA hker (e i - Complex.I • e j) t) by rfl]
  rw [freeFockVectorFourierAmplitude_eq_densityAmplitude A hA hker _ (hac _) t,
    freeFockVectorFourierAmplitude_eq_densityAmplitude A hA hker _ (hac _) t,
    freeFockVectorFourierAmplitude_eq_densityAmplitude A hA hker _ (hac _) t,
    freeFockVectorFourierAmplitude_eq_densityAmplitude A hA hker _ (hac _) t]
  simp only [finiteMatrixSpectralDensityAmplitude, spectralDensityFourierAmplitude,
    freeFockMatrixSpectralDensity, e]
  change (4 : ℂ)⁻¹ *
      ((∫ a, phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i + e j)) a ∂volume) -
        ∫ a, phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i - e j)) a ∂volume) -
      Complex.I * (4 : ℂ)⁻¹ *
      ((∫ a, phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i + Complex.I • e j)) a ∂volume) -
        ∫ a, phi a * spectralMeasureDensity
          (freeFockVectorSpectralMeasure A hA hker (e i - Complex.I • e j)) a ∂volume) = _
  rw [← integral_sub (hint (e i + e j)) (hint (e i - e j)),
    ← integral_const_mul,
    ← integral_sub (hint (e i + Complex.I • e j))
      (hint (e i - Complex.I • e j)),
    ← integral_const_mul,
    ← integral_sub hblockOne hblockTwo]
  apply integral_congr_ae
  filter_upwards with a
  dsimp only [phi]
  ring

theorem freeFockMatrixVacuumPropagator_entry_tendsto_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hatom : ∀ a : ℝ, freeFockMatrixAtomMass A hA hker a = 0)
    (i j : I) :
    Tendsto (fun t => freeFockMatrixVacuumPropagator A hA hker t i j)
      (cocompact ℝ) (𝓝 0) := by
  refine (finiteMatrixSpectralDensityAmplitude_entry_tendsto_zero
    (freeFockMatrixSpectralDensity A hA hker) i j).congr' ?_
  exact Filter.Eventually.of_forall fun t => (congrFun
    (congrFun (freeFockMatrixVacuumPropagator_eq_densityAmplitude
      A hA hker hatom t) i) j).symm

/-- Full-matrix Riemann--Lebesgue theorem for a finite matrix semicircle with no matrix atoms. -/
theorem freeFockMatrixVacuumPropagator_operatorNorm_tendsto_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hatom : ∀ a : ℝ, freeFockMatrixAtomMass A hA hker a = 0) :
    Tendsto (fun t => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I))
      (freeFockMatrixVacuumPropagator A hA hker t)‖)
      (cocompact ℝ) (𝓝 0) := by
  refine (finiteMatrixSpectralDensityAmplitude_operatorNorm_tendsto_zero
    (freeFockMatrixSpectralDensity A hA hker)).congr' ?_
  exact Filter.Eventually.of_forall fun t => congrArg
    (fun M : Matrix I I ℂ => ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) M‖)
    (freeFockMatrixVacuumPropagator_eq_densityAmplitude A hA hker hatom t).symm

end

end GaloisForLFunctions.HTGeometry
