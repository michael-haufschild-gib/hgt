import GaloisForLFunctions.HTGeometry.LpBoundedSmulMultiplier
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Bounded Fourier multipliers on Hilbert-space-valued `L²`

The Plancherel transform is a linear isometry equivalence of `L²(E; F)` for every complex Hilbert
space `F`.  Conjugating scalar multiplication by a bounded measurable symbol through it produces the
*vector-valued Fourier multiplier* with that symbol, again of operator norm at most the symbol
bound.

A nonnegative real symbol gives an accretive multiplier: the `L²` inner product of a function with
its multiple is the integral of the symbol against the pointwise squared norm.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped FourierTransform ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## The vector-valued Plancherel transform -/

variable (E F) in
/-- The Fourier transform on `L²(E;F)`, as a continuous linear map. -/
def vectorFourierL2 : Lp (α := E) F 2 →L[ℂ] Lp (α := E) F 2 :=
  (Lp.fourierTransformₗᵢ E F).toLinearIsometry.toContinuousLinearMap

variable (E F) in
/-- The inverse Fourier transform on `L²(E;F)`, as a continuous linear map. -/
def vectorFourierL2inv : Lp (α := E) F 2 →L[ℂ] Lp (α := E) F 2 :=
  (Lp.fourierTransformₗᵢ E F).symm.toLinearIsometry.toContinuousLinearMap

theorem norm_vectorFourierL2_apply (f : Lp (α := E) F 2) :
    ‖vectorFourierL2 E F f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).norm_map f

theorem norm_vectorFourierL2inv_apply (f : Lp (α := E) F 2) :
    ‖vectorFourierL2inv E F f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).symm.norm_map f

@[simp] theorem vectorFourierL2inv_vectorFourierL2 (f : Lp (α := E) F 2) :
    vectorFourierL2inv E F (vectorFourierL2 E F f) = f :=
  (Lp.fourierTransformₗᵢ E F).symm_apply_apply f

@[simp] theorem vectorFourierL2_vectorFourierL2inv (f : Lp (α := E) F 2) :
    vectorFourierL2 E F (vectorFourierL2inv E F f) = f :=
  (Lp.fourierTransformₗᵢ E F).apply_symm_apply f

/-! ## The multiplier -/

/-- **The vector-valued Fourier multiplier with a bounded measurable symbol.** -/
def vectorFourierMulCLM {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) : Lp (α := E) F 2 →L[ℂ] Lp (α := E) F 2 :=
  (vectorFourierL2inv E F).comp
    ((lpBoundedSmulCLM (p := 2) (μ := (volume : Measure E)) (H := F) hφ hC0 hC).comp
      (vectorFourierL2 E F))

theorem vectorFourierMulCLM_apply {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (f : Lp (α := E) F 2) :
    vectorFourierMulCLM (F := F) hφ hC0 hC f
      = vectorFourierL2inv E F
          (lpBoundedSmulCLM (p := 2) (μ := (volume : Measure E)) (H := F) hφ hC0 hC
            (vectorFourierL2 E F f)) := rfl

/-- **The multiplier obeys the bound of its symbol.** -/
theorem norm_vectorFourierMulCLM_le {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) : ‖vectorFourierMulCLM (F := F) hφ hC0 hC‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun f => ?_
  rw [vectorFourierMulCLM_apply, norm_vectorFourierL2inv_apply]
  refine le_trans (ContinuousLinearMap.le_of_opNorm_le _
    (norm_lpBoundedSmulCLM_le (p := 2) (μ := (volume : Measure E)) (H := F) hφ hC0 hC) _) ?_
  rw [norm_vectorFourierL2_apply]

/-! ## Accretivity of a nonnegative symbol -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

omit [CompleteSpace F] in
/-- The pointwise inner product against a scalar multiple. -/
theorem inner_smul_self_eq (c : ℂ) (v : F) :
    (inner ℂ (c • v) v : ℂ) = (starRingEnd ℂ) c * (‖v‖ : ℂ) ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  rfl

omit [CompleteSpace F] in
/-- **A nonnegative real symbol gives an accretive multiplier on `L²`.**  The inner product of a
function with its multiple is the integral of the symbol against the pointwise squared norm. -/
theorem re_inner_lpBoundedSmulCLM_nonneg {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hnn : ∀ x, ∃ v : ℝ, 0 ≤ v ∧ φ x = (v : ℂ))
    (f : Lp F 2 μ) :
    0 ≤ (inner ℂ (lpBoundedSmulCLM (p := 2) (μ := μ) (H := F) hφ hC0 hC f) f : ℂ).re := by
  have hrepr : (inner ℂ (lpBoundedSmulCLM (p := 2) (μ := μ) (H := F) hφ hC0 hC f) f : ℂ)
      = ∫ x, (inner ℂ (φ x • (f : α → F) x) ((f : α → F) x) : ℂ) ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [lpBoundedSmulCLM_coeFn (p := 2) (μ := μ) (H := F) hφ hC0 hC f] with x h1
    rw [h1]
  have hpt : ∀ x : α, (inner ℂ (φ x • (f : α → F) x) ((f : α → F) x) : ℂ).re
      ≥ 0 := by
    intro x
    obtain ⟨v, hv0, hveq⟩ := hnn x
    rw [inner_smul_self_eq, hveq]
    simp only [Complex.conj_ofReal]
    have : ((v : ℂ) * ((‖(f : α → F) x‖ : ℂ)) ^ 2).re = v * ‖(f : α → F) x‖ ^ 2 := by
      simp [pow_two]
    rw [this]
    positivity
  rw [hrepr]
  by_cases hint : Integrable (fun x => (inner ℂ (φ x • (f : α → F) x) ((f : α → F) x) : ℂ)) μ
  · have hcomm := Complex.reCLM.integral_comp_comm hint
    have hre : (∫ x, (inner ℂ (φ x • (f : α → F) x) ((f : α → F) x) : ℂ) ∂μ).re
        = ∫ x, (inner ℂ (φ x • (f : α → F) x) ((f : α → F) x) : ℂ).re ∂μ := hcomm.symm
    rw [hre]
    exact integral_nonneg fun x => hpt x
  · rw [integral_undef hint]
    simp

end GaloisForLFunctions.HTGeometry
