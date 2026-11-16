import GaloisForLFunctions.HilbertMetric.Correlation.DopplerClusterKernel
import GaloisForLFunctions.HilbertMetric.Correlation.FiniteGramPrediction
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Finite noisy prediction from Gaussian cluster correlations

The actual Doppler kernel and independent observation noise define a Hilbert
Gram realization. Prediction uses its finite observation map, with no
invertibility requirement: repeated sampling times and zero noise are allowed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate ComplexOrder
open GaloisForLFunctions.HTGeometry
namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]

private theorem dopplerClusterKernel_neg (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) :
    dopplerClusterKernel w mean variance (-t) = conj (dopplerClusterKernel w mean variance t) := by
  simp only [dopplerClusterKernel_eq_charFun_sum, charFun_neg, map_sum, map_mul,
    Complex.conj_ofReal]

/-- The finite Doppler Gram at arbitrary, possibly repeated sampling times. -/
theorem dopplerGram_posSemidef (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) {n : ℕ} (t : Fin n → ℝ) :
    (Matrix.of fun i j => dopplerClusterKernel w mean variance (t j - t i)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def]
    rw [← dopplerClusterKernel_neg, neg_sub]
  · intro c
    obtain ⟨r, hr, he⟩ := dopplerClusterKernel_positiveDefinite w mean variance n t c
    have hform : star c ⬝ᵥ (Matrix.of fun i j =>
        dopplerClusterKernel w mean variance (t j - t i)).mulVec c = (r : ℂ) := by
      simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        Finset.mul_sum, mul_assoc] using he
    rw [hform]
    exact Complex.zero_le_real.mpr hr

/-- The continuous Doppler kernel in the corpus's Hilbert Gram convention. -/
theorem dopplerClusterKernel_isPSDKernel (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) :
    IsPSDKernel (fun s t => dopplerClusterKernel w mean variance (s - t)) := by
  apply isPSDKernel_of_forall_posSemidef
  · intro s t
    rw [← dopplerClusterKernel_neg, neg_sub]
  · intro n t
    exact (dopplerGram_posSemidef w mean variance t).transpose

private theorem independentNoise_isPSDKernel {X : Type*} [Fintype X] [DecidableEq X]
    (noise : X → NNReal) :
    IsPSDKernel (fun x y => if x = y then (noise x : ℂ) else 0) := by
  classical
  apply isPSDKernel_of_forall_posSemidef
  · intro x y
    by_cases h : x = y
    · subst y; simp only [if_true, Complex.conj_ofReal]
    · simp only [if_neg h, if_neg (Ne.symm h), map_zero]
  · intro n f
    have h : (Matrix.diagonal (fun x => (noise x : ℂ))).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun x => Complex.zero_le_real.mpr (noise x).coe_nonneg)
    simpa only [Matrix.submatrix, Matrix.diagonal_apply] using h.submatrix f

/-- Joint target-and-pilot covariance, with target noise fixed to zero. -/
def dopplerObservationKernel (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal)
    (i j : Option (Fin n)) : ℂ :=
  dopplerClusterKernel w mean variance (i.elim target time - j.elim target time) +
    if i = j then ((i.elim (0 : NNReal) noise : NNReal) : ℂ) else 0

instance dopplerObservationKernel_psd (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal) :
    Fact (IsPSDKernel (dopplerObservationKernel w mean variance time target noise)) := by
  exact ⟨((dopplerClusterKernel_isPSDKernel w mean variance).comp
    (fun i : Option (Fin n) => i.elim target time)).add
      (independentNoise_isPSDKernel (fun i : Option (Fin n) => i.elim 0 noise))⟩

/-- Finite observation synthesis in the genuine Hilbert realization of the noisy covariance. -/
def dopplerObservationMap (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal) :
    EuclideanSpace ℂ (Fin n) →L[ℂ]
      KernelHilbert (dopplerObservationKernel w mean variance time target noise) :=
  LinearMap.toContinuousLinearMap
    { toFun c := ∑ i, c i • KernelHilbert.vector
        (dopplerObservationKernel w mean variance time target noise) (some i)
      map_add' c d := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' a c := by
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- Optimal finite pilot coefficients, including all singular cases. -/
def dopplerPredictionCoefficients (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal) :
    EuclideanSpace ℂ (Fin n) :=
  finitePredictionCoefficients (dopplerObservationMap w mean variance time target noise)
    (KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) none)

private theorem dopplerObservationMap_single (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) {n : ℕ} (time : Fin n → ℝ) (target : ℝ)
    (noise : Fin n → NNReal) (i : Fin n) :
    dopplerObservationMap w mean variance time target noise (EuclideanSpace.single i 1) =
      KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) (some i) := by
  change (∑ j, (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin n)) j •
    KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) (some j)) = _
  simp

/-- The optimal coefficients solve the literal Doppler-and-noise covariance equations. -/
theorem dopplerPrediction_normal_eq (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) {n : ℕ} (time : Fin n → ℝ) (target : ℝ)
    (noise : Fin n → NNReal) (i : Fin n) :
    (∑ j, (dopplerClusterKernel w mean variance (time j - time i) +
      if j = i then (noise j : ℂ) else 0) *
        dopplerPredictionCoefficients w mean variance time target noise j) =
      dopplerClusterKernel w mean variance (target - time i) := by
  have h := finitePrediction_orthogonal
    (dopplerObservationMap w mean variance time target noise)
    (KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) none)
    (EuclideanSpace.single i 1)
  rw [dopplerObservationMap_single] at h
  have h' := inner_eq_zero_symm.mp h
  change ⟪KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) (some i),
    KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) none -
      ∑ j, dopplerPredictionCoefficients w mean variance time target noise j •
        KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) (some j)⟫_ℂ = 0 at h'
  rw [inner_sub_right, inner_sum] at h'
  simp only [inner_smul_right, KernelHilbert.inner_vector, dopplerObservationKernel,
    Option.elim_some, Option.elim_none, Option.some.injEq, reduceCtorEq, if_false, add_zero] at h'
  simpa only [mul_comm] using (sub_eq_zero.mp h').symm

/-- The prediction error in the covariance Hilbert space. -/
def dopplerFiniteRisk (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal)
    (c : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ‖KernelHilbert.vector (dopplerObservationKernel w mean variance time target noise) none -
    dopplerObservationMap w mean variance time target noise c‖ ^ 2

/-- Exact finite-pilot prediction, without a hidden nonsingularity assumption. -/
theorem dopplerFiniteRisk_decomposition (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) {n : ℕ} (time : Fin n → ℝ) (target : ℝ)
    (noise : Fin n → NNReal) (c : EuclideanSpace ℂ (Fin n)) :
    dopplerFiniteRisk w mean variance time target noise c =
      dopplerFiniteRisk w mean variance time target noise
        (dopplerPredictionCoefficients w mean variance time target noise) +
      ‖dopplerObservationMap w mean variance time target noise
        (c - dopplerPredictionCoefficients w mean variance time target noise)‖ ^ 2 :=
  finitePrediction_error_decomposition _ _ _

/-- Every optimal predictor has exactly the same synthesized observation. -/
theorem dopplerFiniteRisk_minimizer_iff (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) {n : ℕ} (time : Fin n → ℝ) (target : ℝ)
    (noise : Fin n → NNReal) (c : EuclideanSpace ℂ (Fin n)) :
    (∀ d, dopplerFiniteRisk w mean variance time target noise c ≤
      dopplerFiniteRisk w mean variance time target noise d) ↔
    dopplerObservationMap w mean variance time target noise
      (c - dopplerPredictionCoefficients w mean variance time target noise) = 0 :=
  finitePrediction_minimizer_iff _ _ _

end HilbertMetric.Correlation

