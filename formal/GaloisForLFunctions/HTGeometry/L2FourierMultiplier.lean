import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Bounded Fourier multipliers on `L²`

A bounded measurable symbol acts on `L²` by multiplication with operator norm at most its bound.
Conjugating that action by the Plancherel transform gives the *Fourier multiplier* with that symbol,
again of operator norm at most the bound. This is the operator-theoretic form of a constant-
coefficient evolution: the propagator of a linear equation with constant coefficients is a Fourier
multiplier, and its bound is read off from the symbol.

The first half of the file supplies the algebra of multiplication operators — the composite of two
is the multiplier of the product, a symbol that is almost everywhere `1` gives the identity, and a
symbol that is almost everywhere a sum gives the sum. The second half transports all of it through
Plancherel.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

section MulAlgebra

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The composite of two multiplication operators is the multiplier of the product symbol.** -/
theorem lpBoundedMulCLM_comp {φ ψ χ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ x, ‖ψ x‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ x, ‖χ x‖ ≤ B)
    (hae : ∀ᵐ x ∂μ, χ x = φ x * ψ x) :
    (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC).comp
        (lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD)
      = lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC
      (lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD f),
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hψ hD0 hD f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hχ hB0 hB f, hae] with x h1 h2 h3 h4
  show ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC
      (lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD f) : Lp 𝕜 p μ) : α → 𝕜) x = _
  rw [h1, h2, h3, h4, mul_assoc]

/-- A symbol that is almost everywhere `1` induces the identity. -/
theorem lpBoundedMulCLM_eq_id {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hae : ∀ᵐ x ∂μ, φ x = 1) :
    lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC = ContinuousLinearMap.id 𝕜 (Lp 𝕜 p μ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f, hae] with x h1 h2
  rw [h1, h2, one_mul]
  rfl

/-- **A symbol that is almost everywhere a sum induces the sum of the multipliers.** -/
theorem lpBoundedMulCLM_add {φ ψ χ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ x, ‖ψ x‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ x, ‖χ x‖ ≤ B)
    (hae : ∀ᵐ x ∂μ, χ x = φ x + ψ x) :
    lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB
      = lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC
        + lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hχ hB0 hB f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hψ hD0 hD f,
    Lp.coeFn_add (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f)
      (lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD f), hae] with x h1 h2 h3 h4 h5
  show ((lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB f : Lp 𝕜 p μ) : α → 𝕜) x = _
  rw [h1, h5, add_apply, h4, Pi.add_apply, h2, h3, add_mul]

/-- A symbol that is almost everywhere `0` induces the zero operator. -/
theorem lpBoundedMulCLM_eq_zero {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hae : ∀ᵐ x ∂μ, φ x = 0) :
    lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC = 0 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f, hae,
    Lp.coeFn_zero 𝕜 p μ] with x h1 h2 h3
  rw [h1, h2, zero_mul]
  show (0 : 𝕜) = ((0 : Lp 𝕜 p μ) : α → 𝕜) x
  rw [h3]
  rfl

/-- A symbol that is almost everywhere a negative induces the negative of the multiplier. -/
theorem lpBoundedMulCLM_neg {φ ψ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ x, ‖ψ x‖ ≤ D)
    (hae : ∀ᵐ x ∂μ, ψ x = -φ x) :
    lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD
      = -lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hψ hD0 hD f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    Lp.coeFn_neg (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f), hae] with x h1 h2 h3 h4
  show ((lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD f : Lp 𝕜 p μ) : α → 𝕜) x = _
  rw [h1, h4, neg_apply, h3, Pi.neg_apply, h2, neg_mul]

/-- A symbol that is almost everywhere a difference induces the difference of the multipliers. -/
theorem lpBoundedMulCLM_sub {φ ψ χ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ x, ‖ψ x‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ x, ‖χ x‖ ≤ B)
    (hae : ∀ᵐ x ∂μ, χ x = φ x - ψ x) :
    lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB
      = lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC
        - lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hχ hB0 hB f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hψ hD0 hD f,
    Lp.coeFn_sub (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f)
      (lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD f), hae] with x h1 h2 h3 h4 h5
  show ((lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB f : Lp 𝕜 p μ) : α → 𝕜) x = _
  rw [h1, h5, sub_apply, h4, Pi.sub_apply, h2, h3, sub_mul]

/-- A symbol that is almost everywhere a scalar multiple induces the scalar multiple of the
multiplier. -/
theorem lpBoundedMulCLM_smul {φ χ : α → 𝕜} (hφ : Measurable φ) (hχ : Measurable χ)
    {C B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hB0 : 0 ≤ B) (hB : ∀ x, ‖χ x‖ ≤ B)
    (c : 𝕜) (hae : ∀ᵐ x ∂μ, χ x = c * φ x) :
    lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB
      = c • lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hχ hB0 hB f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    Lp.coeFn_smul c (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f), hae] with x h1 h2 h3 h4
  show ((lpBoundedMulCLM (p := p) (μ := μ) hχ hB0 hB f : Lp 𝕜 p μ) : α → 𝕜) x = _
  rw [h1, h4, smul_apply, h3, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]

end MulAlgebra

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The Plancherel transform as a continuous linear map -/

variable (E) in
/-- The Fourier transform on `L²`, as a continuous linear map. -/
def fourierL2 : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  (Lp.fourierTransformₗᵢ E ℂ).toLinearIsometry.toContinuousLinearMap

variable (E) in
/-- The inverse Fourier transform on `L²`, as a continuous linear map. -/
def fourierL2inv : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.toLinearIsometry.toContinuousLinearMap

theorem norm_fourierL2_apply (f : Lp (α := E) ℂ 2) : ‖fourierL2 E f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E ℂ).norm_map f

theorem norm_fourierL2inv_apply (f : Lp (α := E) ℂ 2) : ‖fourierL2inv E f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.norm_map f

theorem norm_fourierL2_le : ‖fourierL2 E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul, norm_fourierL2_apply]

theorem norm_fourierL2inv_le : ‖fourierL2inv E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul, norm_fourierL2inv_apply]

@[simp] theorem fourierL2inv_fourierL2 (f : Lp (α := E) ℂ 2) :
    fourierL2inv E (fourierL2 E f) = f :=
  (Lp.fourierTransformₗᵢ E ℂ).symm_apply_apply f

@[simp] theorem fourierL2_fourierL2inv (f : Lp (α := E) ℂ 2) :
    fourierL2 E (fourierL2inv E f) = f :=
  (Lp.fourierTransformₗᵢ E ℂ).apply_symm_apply f

/-! ## The multiplier -/

/-- **The Fourier multiplier with a bounded measurable symbol.** -/
def fourierMulCLM {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  (fourierL2inv E).comp
    ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC).comp (fourierL2 E))

theorem fourierMulCLM_apply {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (f : Lp (α := E) ℂ 2) :
    fourierMulCLM hφ hC0 hC f
      = fourierL2inv E (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
          (fourierL2 E f)) := rfl

/-- **The multiplier obeys the bound of its symbol.** -/
theorem norm_fourierMulCLM_le {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) : ‖fourierMulCLM hφ hC0 hC‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun f => ?_
  rw [fourierMulCLM_apply, norm_fourierL2inv_apply]
  refine le_trans (ContinuousLinearMap.le_of_opNorm_le _
    (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure E)) hφ hC0 hC) _) ?_
  rw [norm_fourierL2_apply]

/-- **The composite of two Fourier multipliers is the multiplier of the product symbol.** -/
theorem fourierMulCLM_comp {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ᵐ ξ ∂(volume : Measure E), χ ξ = φ ξ * ψ ξ) :
    (fourierMulCLM hφ hC0 hC).comp (fourierMulCLM hψ hD0 hD) = fourierMulCLM hχ hB0 hB := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hcomp := lpBoundedMulCLM_comp (p := 2) (μ := (volume : Measure E)) hφ hψ hχ hC0 hC hD0 hD
    hB0 hB hae
  have hstep : (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC)
      ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hψ hD0 hD) (fourierL2 E f))
      = (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hχ hB0 hB) (fourierL2 E f) := by
    exact congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T (fourierL2 E f)) hcomp
  show fourierL2inv E ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC)
      (fourierL2 E (fourierL2inv E
        ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hψ hD0 hD) (fourierL2 E f)))))
    = _
  rw [fourierL2_fourierL2inv, hstep]
  rfl

/-- A symbol that is almost everywhere `1` gives the identity. -/
theorem fourierMulCLM_eq_id {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hae : ∀ᵐ ξ ∂(volume : Measure E), φ ξ = 1) :
    fourierMulCLM hφ hC0 hC = ContinuousLinearMap.id ℂ (Lp (α := E) ℂ 2) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply, lpBoundedMulCLM_eq_id (p := 2) (μ := (volume : Measure E)) hφ hC0 hC hae]
  simp

/-- A symbol that is almost everywhere a difference gives the difference of the multipliers. -/
theorem fourierMulCLM_sub {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ᵐ ξ ∂(volume : Measure E), χ ξ = φ ξ - ψ ξ) :
    fourierMulCLM hχ hB0 hB = fourierMulCLM hφ hC0 hC - fourierMulCLM hψ hD0 hD := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply, lpBoundedMulCLM_sub (p := 2) (μ := (volume : Measure E)) hφ hψ hχ
    hC0 hC hD0 hD hB0 hB hae]
  show fourierL2inv E ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
      (fourierL2 E f)) - (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hψ hD0 hD
      (fourierL2 E f))) = _
  rw [map_sub]
  rfl

/-- A symbol that is almost everywhere a scalar multiple gives the scalar multiple of the
multiplier. -/
theorem fourierMulCLM_smul {φ χ : E → ℂ} (hφ : Measurable φ) (hχ : Measurable χ)
    {C B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (c : ℂ) (hae : ∀ᵐ ξ ∂(volume : Measure E), χ ξ = c * φ ξ) :
    fourierMulCLM hχ hB0 hB = c • fourierMulCLM hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply, lpBoundedMulCLM_smul (p := 2) (μ := (volume : Measure E)) hφ hχ
    hC0 hC hB0 hB c hae]
  show fourierL2inv E (c • (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
      (fourierL2 E f))) = _
  rw [map_smul]
  rfl

/-- A symbol that is almost everywhere `0` gives the zero operator. -/
theorem fourierMulCLM_eq_zero {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hae : ∀ᵐ ξ ∂(volume : Measure E), φ ξ = 0) :
    fourierMulCLM hφ hC0 hC = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply,
    lpBoundedMulCLM_eq_zero (p := 2) (μ := (volume : Measure E)) hφ hC0 hC hae]
  simp

/-- A symbol that is almost everywhere a negative gives the negative of the multiplier. -/
theorem fourierMulCLM_neg {φ ψ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (hae : ∀ᵐ ξ ∂(volume : Measure E), ψ ξ = -φ ξ) :
    fourierMulCLM hψ hD0 hD = -fourierMulCLM hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply,
    lpBoundedMulCLM_neg (p := 2) (μ := (volume : Measure E)) hφ hψ hC0 hC hD0 hD hae]
  show fourierL2inv E (-(lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
      (fourierL2 E f))) = _
  rw [map_neg]
  rfl

/-- **A symbol that is almost everywhere a sum gives the sum of the multipliers.** -/
theorem fourierMulCLM_add {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ᵐ ξ ∂(volume : Measure E), χ ξ = φ ξ + ψ ξ) :
    fourierMulCLM hχ hB0 hB = fourierMulCLM hφ hC0 hC + fourierMulCLM hψ hD0 hD := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply, lpBoundedMulCLM_add (p := 2) (μ := (volume : Measure E)) hφ hψ hχ
    hC0 hC hD0 hD hB0 hB hae]
  show fourierL2inv E ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
      (fourierL2 E f)) + (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hψ hD0 hD
      (fourierL2 E f))) = _
  rw [map_add]
  rfl

end GaloisForLFunctions.HTGeometry
