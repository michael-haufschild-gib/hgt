import GaloisForLFunctions.HTGeometry.FreeFockMatrixFullAnalyticLaw
import GaloisForLFunctions.HTGeometry.HallKrausRankNondecrease
import GaloisForLFunctions.HTGeometry.HermitianTraceNorm

/-!
# Zero-atom exclusion for full matrix semicircles

Regularized Ward limits convert Hall rank nondecrease of the Kraus covariance into exclusion of
the atom at zero.  This is the zero-energy core of the full matrix-semicircle atomlessness theorem.
-/

open Filter Matrix Set Topology
open scoped BigOperators Matrix ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

omit [DecidableEq I] [DecidableEq K] in
/-- The finite Kraus covariance is continuous in its matrix argument. -/
theorem continuous_matrixSemicircleCovariance (A : K → Matrix I I ℂ) :
    Continuous (matrixSemicircleCovariance A) := by
  unfold matrixSemicircleCovariance
  fun_prop

/-- The positive imaginary-axis profile converges to the atom matrix at zero from above. -/
theorem freeFockMatrixImaginaryAxisProfile_tendsto_atomMass_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    Tendsto (freeFockMatrixImaginaryAxisProfile A hA hker)
      (𝓝[>] (0 : ℝ))
      (𝓝 (freeFockMatrixAtomMass A hA hker 0)) := by
  have hright_le : 𝓝[>] (0 : ℝ) ≤ nhdsWithin 0 {0}ᶜ := by
    apply nhdsWithin_mono
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hy)
  have hPoisson :=
    (freeFockMatrixPoissonProfile_tendsto_atomMass A hA hker 0).mono_left hright_le
  apply hPoisson.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa [freeFockMatrixPoissonProfile] using
    (freeFockMatrixImaginaryAxisProfile_eq_smul_hermitianImaginaryPart
      A hA hker y hy).symm

private def shiftedInverseTrace (P H : Matrix I I ℂ) (ε : ℝ) : ℝ :=
  ((P * (H + (ε : ℂ) • (1 : Matrix I I ℂ))⁻¹).trace).re

private theorem shiftedInverseTrace_mono
    {P H : Matrix I I ℂ} (hP : P.PosSemidef) (hH : H.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    shiftedInverseTrace P H b ≤ shiftedInverseTrace P H a :=
  re_trace_mul_shiftedPosSemidef_inv_le hH hP ha hab

private def imaginaryAxisCutoffCovarianceSource
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y δ : ℝ) : Matrix I I ℂ :=
  matrixSemicircleCovariance A
    (finiteMatrixResolventCutoff
        (freeFockMatrixImaginaryAxisProfile A hA hker y) δ *
      freeFockMatrixImaginaryAxisProfile A hA hker y)

private def imaginaryAxisRegularizedCovarianceTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y δ ε : ℝ) : ℝ :=
  shiftedInverseTrace
    (imaginaryAxisCutoffCovarianceSource A hA hker y δ)
    (matrixSemicircleCovariance A
      (freeFockMatrixImaginaryAxisProfile A hA hker y)) ε

private def imaginaryAxisScaledCovarianceTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y δ : ℝ) : ℝ :=
  ((imaginaryAxisCutoffCovarianceSource A hA hker y δ *
    freeFockMatrixImaginaryAxisScaledProfile A hA hker y).trace).re

private def imaginaryAxisCutoffWardTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y δ : ℝ) : ℝ :=
  ((finiteMatrixResolventCutoff
        (freeFockMatrixImaginaryAxisProfile A hA hker y) δ *
      ((1 : Matrix I I ℂ) -
        freeFockMatrixImaginaryAxisProfile A hA hker y)).trace).re

private theorem imaginaryAxisCutoffCovarianceSource_posSemidef
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    (imaginaryAxisCutoffCovarianceSource A hA hker y δ).PosSemidef := by
  apply matrixSemicircleCovariance_posSemidef
  apply finiteMatrixResolventCutoff_mul_posSemidef
  · exact (freeFockMatrixImaginaryAxisProfile_posDef A hA hker y hy).posSemidef
  · exact hδ

private theorem imaginaryAxisCovariance_posSemidef
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {y : ℝ} (hy : 0 < y) :
    (matrixSemicircleCovariance A
      (freeFockMatrixImaginaryAxisProfile A hA hker y)).PosSemidef :=
  matrixSemicircleCovariance_posSemidef A
    (freeFockMatrixImaginaryAxisProfile_posDef A hA hker y hy).posSemidef

/-- Increasing the covariance regularization decreases its positive trace pairing. -/
private theorem imaginaryAxisRegularizedCovarianceTrace_mono
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    {y δ ε : ℝ} (hy : 0 < y) (hδ : 0 < δ) (hyε : y ^ (2 : ℕ) ≤ ε) :
    imaginaryAxisRegularizedCovarianceTrace A hA hker y δ ε ≤
      imaginaryAxisRegularizedCovarianceTrace A hA hker y δ (y ^ (2 : ℕ)) := by
  exact shiftedInverseTrace_mono
    (imaginaryAxisCutoffCovarianceSource_posSemidef A hA hker hy hδ)
    (imaginaryAxisCovariance_posSemidef A hA hker hy)
    (sq_pos_of_pos hy) hyε

/-- The Dyson inverse identifies the `y²`-regularized trace with the scaled-profile pairing. -/
private theorem imaginaryAxisRegularizedCovarianceTrace_sq_eq_scaled
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {y δ : ℝ} (hy : 0 < y) :
    imaginaryAxisRegularizedCovarianceTrace A hA hker y δ (y ^ (2 : ℕ)) =
      imaginaryAxisScaledCovarianceTrace A hA hker y δ := by
  unfold imaginaryAxisRegularizedCovarianceTrace shiftedInverseTrace
  unfold imaginaryAxisScaledCovarianceTrace
  have hy2 : ((y ^ (2 : ℕ) : ℝ) : ℂ) = (y : ℂ) ^ (2 : ℕ) := by norm_cast
  rw [hy2]
  rw [← freeFockMatrixImaginaryAxisScaledProfile_eq_inv A hA hker y hy]

/-- The exact Ward trace transfers the scaled covariance pairing to the cutoff complement. -/
private theorem imaginaryAxisScaledCovarianceTrace_eq_ward
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {y δ : ℝ} (hy : 0 < y) :
    imaginaryAxisScaledCovarianceTrace A hA hker y δ =
      imaginaryAxisCutoffWardTrace A hA hker y δ := by
  unfold imaginaryAxisScaledCovarianceTrace imaginaryAxisCutoffCovarianceSource
  unfold imaginaryAxisCutoffWardTrace
  exact congrArg Complex.re
    (freeFockMatrixImaginaryAxis_cutoff_trace_identity A hA hker y δ hy).symm

private theorem imaginaryAxisRegularizedCovarianceTrace_sq_eq_ward
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {y δ : ℝ} (hy : 0 < y) :
    imaginaryAxisRegularizedCovarianceTrace A hA hker y δ (y ^ (2 : ℕ)) =
      imaginaryAxisCutoffWardTrace A hA hker y δ :=
  (imaginaryAxisRegularizedCovarianceTrace_sq_eq_scaled A hA hker hy).trans
    (imaginaryAxisScaledCovarianceTrace_eq_ward A hA hker hy)

/-- At positive height, antitonicity and the exact Ward identity bound the regularized covariance
trace by the cutoff complement trace. -/
theorem freeFockMatrixImaginaryAxis_regularized_trace_le
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    {y δ ε : ℝ} (hy : 0 < y) (hδ : 0 < δ) (hyε : y ^ (2 : ℕ) ≤ ε) :
    imaginaryAxisRegularizedCovarianceTrace A hA hker y δ ε ≤
      imaginaryAxisCutoffWardTrace A hA hker y δ :=
  (imaginaryAxisRegularizedCovarianceTrace_mono A hA hker hy hδ hyε).trans_eq
    (imaginaryAxisRegularizedCovarianceTrace_sq_eq_ward A hA hker hy)

private theorem tendsto_shiftedInverseTrace
    {α : Type*} [TopologicalSpace α] {l : Filter α}
    {P H : α → Matrix I I ℂ} {P₀ H₀ : Matrix I I ℂ}
    (hP : Tendsto P l (𝓝 P₀)) (hH : Tendsto H l (𝓝 H₀))
    (hH₀ : H₀.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => shiftedInverseTrace (P x) (H x) ε) l
      (𝓝 (shiftedInverseTrace P₀ H₀ ε)) := by
  have hinv : Tendsto
      (fun x => (H x + (ε : ℂ) • (1 : Matrix I I ℂ))⁻¹) l
      (𝓝 ((H₀ + (ε : ℂ) • (1 : Matrix I I ℂ))⁻¹)) :=
    (continuousAt_shiftedPosSemidef_inv hH₀ hε).tendsto.comp hH
  have htrace : Continuous (fun X : Matrix I I ℂ => X.trace.re) := by
    fun_prop
  unfold shiftedInverseTrace
  exact htrace.continuousAt.tendsto.comp (hP.mul hinv)

private theorem le_of_tendsto_of_eventually_le
    {α : Type*} {l : Filter α} [l.NeBot] {f g : α → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b))
    (hfg : ∀ᶠ x in l, f x ≤ g x) : a ≤ b := by
  have hsub : Tendsto (fun x => f x - g x) l (𝓝 (a - b)) := hf.sub hg
  have hnonpos : a - b ≤ 0 :=
    le_of_tendsto hsub (hfg.mono fun _ hx => sub_nonpos.mpr hx)
  linarith

private def freeFockMatrixZeroAtomMass
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) : Matrix I I ℂ :=
  freeFockMatrixAtomMass A hA hker 0

private def zeroAtomCutoffCovarianceSource
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (δ : ℝ) : Matrix I I ℂ :=
  matrixSemicircleCovariance A
    (finiteMatrixResolventCutoff (freeFockMatrixZeroAtomMass A hA hker) δ *
      freeFockMatrixZeroAtomMass A hA hker)

private def zeroAtomRegularizedCovarianceTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (δ ε : ℝ) : ℝ :=
  shiftedInverseTrace (zeroAtomCutoffCovarianceSource A hA hker δ)
    (matrixSemicircleCovariance A (freeFockMatrixZeroAtomMass A hA hker)) ε

private def zeroAtomCutoffWardTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (δ : ℝ) : ℝ :=
  ((finiteMatrixResolventCutoff (freeFockMatrixZeroAtomMass A hA hker) δ *
    ((1 : Matrix I I ℂ) - freeFockMatrixZeroAtomMass A hA hker)).trace).re

private theorem tendsto_imaginaryAxisCutoffCovarianceSource
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => imaginaryAxisCutoffCovarianceSource A hA hker y δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (zeroAtomCutoffCovarianceSource A hA hker δ)) := by
  have hX := freeFockMatrixImaginaryAxisProfile_tendsto_atomMass_zero A hA hker
  have hM : (freeFockMatrixZeroAtomMass A hA hker).PosSemidef := by
    exact freeFockMatrixAtomMass_posSemidef A hA hker 0
  have hR := tendsto_finiteMatrixResolventCutoff_comp hX hM hδ
  have hRX := hR.mul hX
  have hcov :=
    (continuous_matrixSemicircleCovariance A).continuousAt.tendsto.comp hRX
  simpa only [Function.comp_def, imaginaryAxisCutoffCovarianceSource,
    zeroAtomCutoffCovarianceSource, freeFockMatrixZeroAtomMass] using hcov

private theorem tendsto_imaginaryAxisCovariance
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    Tendsto (fun y => matrixSemicircleCovariance A
        (freeFockMatrixImaginaryAxisProfile A hA hker y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (matrixSemicircleCovariance A (freeFockMatrixZeroAtomMass A hA hker))) := by
  exact (continuous_matrixSemicircleCovariance A).continuousAt.tendsto.comp
    (freeFockMatrixImaginaryAxisProfile_tendsto_atomMass_zero A hA hker)

private theorem tendsto_imaginaryAxisRegularizedCovarianceTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun y => imaginaryAxisRegularizedCovarianceTrace A hA hker y δ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (zeroAtomRegularizedCovarianceTrace A hA hker δ ε)) := by
  have hηM : (matrixSemicircleCovariance A
      (freeFockMatrixZeroAtomMass A hA hker)).PosSemidef :=
    matrixSemicircleCovariance_posSemidef A
      (freeFockMatrixAtomMass_posSemidef A hA hker 0)
  exact tendsto_shiftedInverseTrace
    (tendsto_imaginaryAxisCutoffCovarianceSource A hA hker hδ)
    (tendsto_imaginaryAxisCovariance A hA hker) hηM hε

private theorem tendsto_imaginaryAxisCutoffWardTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => imaginaryAxisCutoffWardTrace A hA hker y δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (zeroAtomCutoffWardTrace A hA hker δ)) := by
  have hX := freeFockMatrixImaginaryAxisProfile_tendsto_atomMass_zero A hA hker
  have hM : (freeFockMatrixZeroAtomMass A hA hker).PosSemidef :=
    freeFockMatrixAtomMass_posSemidef A hA hker 0
  have hR := tendsto_finiteMatrixResolventCutoff_comp hX hM hδ
  have hcomp : Tendsto
      (fun y => (1 : Matrix I I ℂ) - freeFockMatrixImaginaryAxisProfile A hA hker y)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 : Matrix I I ℂ) - freeFockMatrixZeroAtomMass A hA hker)) :=
    tendsto_const_nhds.sub hX
  have htrace : Continuous (fun X : Matrix I I ℂ => X.trace.re) := by
    fun_prop
  unfold imaginaryAxisCutoffWardTrace zeroAtomCutoffWardTrace
  exact htrace.continuousAt.tendsto.comp (hR.mul hcomp)

/-- First Ward limit: fixed cutoff and covariance regularizations survive `y ↓ 0`. -/
private theorem zeroAtomRegularizedCovarianceTrace_le_cutoffWardTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    zeroAtomRegularizedCovarianceTrace A hA hker δ ε ≤
      zeroAtomCutoffWardTrace A hA hker δ := by
  have hsq : Tendsto (fun y : ℝ => y ^ (2 : ℕ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto (fun y : ℝ => y ^ (2 : ℕ)) (𝓝 0) (𝓝 (0 ^ (2 : ℕ))) :=
      (show ContinuousAt (fun y : ℝ => y ^ (2 : ℕ)) 0 by fun_prop).tendsto
    have hrestrict := hfull.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa using hrestrict
  have hsquare : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y ^ (2 : ℕ) ≤ ε :=
    ((tendsto_order.1 hsq).2 ε hε).mono fun _ hy => hy.le
  have hle : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      imaginaryAxisRegularizedCovarianceTrace A hA hker y δ ε ≤
        imaginaryAxisCutoffWardTrace A hA hker y δ := by
    filter_upwards [self_mem_nhdsWithin, hsquare] with y hy hyε
    exact freeFockMatrixImaginaryAxis_regularized_trace_le A hA hker hy hδ hyε
  exact le_of_tendsto_of_eventually_le
    (tendsto_imaginaryAxisRegularizedCovarianceTrace A hA hker hδ hε)
    (tendsto_imaginaryAxisCutoffWardTrace A hA hker hδ) hle

private def zeroAtomCovarianceCutoffTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (ε : ℝ) : ℝ :=
  let H := matrixSemicircleCovariance A (freeFockMatrixZeroAtomMass A hA hker)
  shiftedInverseTrace H H ε

private theorem tendsto_zeroAtomCutoffCovarianceSource
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    Tendsto (fun δ => zeroAtomCutoffCovarianceSource A hA hker δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (matrixSemicircleCovariance A (freeFockMatrixZeroAtomMass A hA hker))) := by
  have hM : (freeFockMatrixZeroAtomMass A hA hker).PosSemidef :=
    freeFockMatrixAtomMass_posSemidef A hA hker 0
  have hmul := tendsto_finiteMatrixResolventCutoff_mul hM
  have hcov :=
    (continuous_matrixSemicircleCovariance A).continuousAt.tendsto.comp hmul
  simpa only [Function.comp_def, zeroAtomCutoffCovarianceSource] using hcov

private theorem tendsto_zeroAtomRegularizedCovarianceTrace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ => zeroAtomRegularizedCovarianceTrace A hA hker δ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (zeroAtomCovarianceCutoffTrace A hA hker ε)) := by
  have hηM : (matrixSemicircleCovariance A
      (freeFockMatrixZeroAtomMass A hA hker)).PosSemidef :=
    matrixSemicircleCovariance_posSemidef A
      (freeFockMatrixAtomMass_posSemidef A hA hker 0)
  exact tendsto_shiftedInverseTrace
    (tendsto_zeroAtomCutoffCovarianceSource A hA hker)
    tendsto_const_nhds hηM hε

private theorem tendsto_zeroAtomCutoffWardTrace_rank_sub_trace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    Tendsto (zeroAtomCutoffWardTrace A hA hker)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((freeFockMatrixZeroAtomMass A hA hker).rank -
        (freeFockMatrixZeroAtomMass A hA hker).trace.re)) := by
  let M := freeFockMatrixZeroAtomMass A hA hker
  have hM : M.PosSemidef := freeFockMatrixAtomMass_posSemidef A hA hker 0
  have hcutoff := tendsto_finiteMatrixResolventCutoff_trace_re_rank hM
  have hmul := tendsto_finiteMatrixResolventCutoff_mul hM
  have htrace : Continuous (fun X : Matrix I I ℂ => X.trace.re) := by
    fun_prop
  have hmulTrace : Tendsto
      (fun δ => (finiteMatrixResolventCutoff M δ * M).trace.re)
      (𝓝[>] (0 : ℝ)) (𝓝 M.trace.re) :=
    htrace.continuousAt.tendsto.comp hmul
  have hsub := hcutoff.sub hmulTrace
  change Tendsto (zeroAtomCutoffWardTrace A hA hker)
    (𝓝[>] (0 : ℝ)) (𝓝 ((M.rank : ℝ) - M.trace.re))
  convert hsub using 1
  funext δ
  unfold zeroAtomCutoffWardTrace
  change ((finiteMatrixResolventCutoff M δ * ((1 : Matrix I I ℂ) - M)).trace).re =
    (finiteMatrixResolventCutoff M δ).trace.re -
      (finiteMatrixResolventCutoff M δ * M).trace.re
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
  rfl

/-- Second Ward limit: covariance cutoff trace is bounded by atom rank minus atom trace. -/
private theorem zeroAtomCovarianceCutoffTrace_le_rank_sub_trace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) {ε : ℝ} (hε : 0 < ε) :
    zeroAtomCovarianceCutoffTrace A hA hker ε ≤
      (freeFockMatrixZeroAtomMass A hA hker).rank -
        (freeFockMatrixZeroAtomMass A hA hker).trace.re := by
  have hle : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      zeroAtomRegularizedCovarianceTrace A hA hker δ ε ≤
        zeroAtomCutoffWardTrace A hA hker δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact zeroAtomRegularizedCovarianceTrace_le_cutoffWardTrace
      A hA hker hδ hε
  exact le_of_tendsto_of_eventually_le
    (tendsto_zeroAtomRegularizedCovarianceTrace A hA hker hε)
    (tendsto_zeroAtomCutoffWardTrace_rank_sub_trace A hA hker) hle

private theorem tendsto_zeroAtomCovarianceCutoffTrace_rank
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    Tendsto (zeroAtomCovarianceCutoffTrace A hA hker)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((matrixSemicircleCovariance A
        (freeFockMatrixZeroAtomMass A hA hker)).rank : ℝ)) := by
  let H := matrixSemicircleCovariance A (freeFockMatrixZeroAtomMass A hA hker)
  have hH : H.PosSemidef := matrixSemicircleCovariance_posSemidef A
    (freeFockMatrixAtomMass_posSemidef A hA hker 0)
  have hcutoff := tendsto_finiteMatrixResolventCutoff_trace_re_rank hH
  change Tendsto (zeroAtomCovarianceCutoffTrace A hA hker)
    (𝓝[>] (0 : ℝ)) (𝓝 (H.rank : ℝ))
  convert hcutoff using 1
  funext ε
  unfold zeroAtomCovarianceCutoffTrace shiftedInverseTrace
  change ((H * (H + (ε : ℂ) • (1 : Matrix I I ℂ))⁻¹).trace).re = _
  rfl

/-- Triple Ward limit: covariance rank cannot exceed atom rank minus its positive trace. -/
theorem rank_matrixSemicircleCovariance_zeroAtom_le_rank_sub_trace
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    ((matrixSemicircleCovariance A
      (freeFockMatrixAtomMass A hA hker 0)).rank : ℝ) ≤
      (freeFockMatrixAtomMass A hA hker 0).rank -
        (freeFockMatrixAtomMass A hA hker 0).trace.re := by
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      zeroAtomCovarianceCutoffTrace A hA hker ε ≤
        (freeFockMatrixZeroAtomMass A hA hker).rank -
          (freeFockMatrixZeroAtomMass A hA hker).trace.re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact zeroAtomCovarianceCutoffTrace_le_rank_sub_trace A hA hker hε
  have hconst : Tendsto (fun _ε : ℝ =>
      (freeFockMatrixZeroAtomMass A hA hker).rank -
        (freeFockMatrixZeroAtomMass A hA hker).trace.re)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((freeFockMatrixZeroAtomMass A hA hker).rank -
        (freeFockMatrixZeroAtomMass A hA hker).trace.re)) := tendsto_const_nhds
  simpa [freeFockMatrixZeroAtomMass] using le_of_tendsto_of_eventually_le
    (tendsto_zeroAtomCovarianceCutoffTrace_rank A hA hker) hconst hle

/-- A nonzero positive-semidefinite finite matrix has strictly positive real trace. -/
theorem posSemidef_trace_re_pos_of_ne_zero
    {M : Matrix I I ℂ} (hM : M.PosSemidef) (hM0 : M ≠ 0) :
    0 < M.trace.re := by
  rw [trace_re_eq_sum_eigenvalues hM.isHermitian]
  apply lt_of_le_of_ne
  · exact Finset.sum_nonneg fun i _hi => hM.eigenvalues_nonneg i
  · intro hsum
    have heig : ∀ i, hM.isHermitian.eigenvalues i = 0 := by
      intro i
      apply le_antisymm
      · have hi := Finset.single_le_sum
          (fun j _hj => hM.eigenvalues_nonneg j) (Finset.mem_univ i)
        rw [← hsum] at hi
        exact hi
      · exact hM.eigenvalues_nonneg i
    have hspec := isHermitian_eq_conj_diagonal hM.isHermitian
    apply hM0
    simpa [heig, Matrix.star_eq_conjTranspose] using hspec

/-- Hall rank nondecrease excludes the zero atom of a full matrix semicircle. -/
theorem freeFockMatrixAtomMass_zero_eq_zero_of_hall
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hHall : LinearFamilyHall fun k => (A k).mulVecLin) :
    freeFockMatrixAtomMass A hA hker 0 = 0 := by
  let M := freeFockMatrixAtomMass A hA hker 0
  have hM : M.PosSemidef := freeFockMatrixAtomMass_posSemidef A hA hker 0
  have hlowerNat : M.rank ≤ (matrixSemicircleCovariance A M).rank := by
    simpa [matrixSemicircleCovariance] using
      rank_le_rank_krausSum_of_hall A hHall hM
  have hlower : (M.rank : ℝ) ≤ (matrixSemicircleCovariance A M).rank := by
    exact_mod_cast hlowerNat
  have hupper : ((matrixSemicircleCovariance A M).rank : ℝ) ≤
      M.rank - M.trace.re := by
    simpa [M] using rank_matrixSemicircleCovariance_zeroAtom_le_rank_sub_trace
      A hA hker
  by_contra hM0
  have htrace : 0 < M.trace.re := posSemidef_trace_re_pos_of_ne_zero hM hM0
  linarith

end

end GaloisForLFunctions.HTGeometry
