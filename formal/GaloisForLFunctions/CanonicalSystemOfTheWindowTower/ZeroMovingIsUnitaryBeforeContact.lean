import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ThePrecontactWeilSpacesHaveEntireFourierCoordinates
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaSpectralEigenspace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unitary zero-moving in the completed Weil space

The symmetric derivative has dense shifted range in each Fourier evaluation kernel. Its shifts
by conjugate parameters have the same Gram form. Completion therefore gives an exact unitary
between the two kernels, preserving the aperture and the unshifted Weil norm.
-/

open Complex MeasureTheory Set Topology
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

open _root_.RHTower HTGeometry

variable (a : PrecontactAperture)

theorem denseRange_nativeSmoothCore : DenseRange (smoothCore a) := by
  apply (denseRange_smoothCore a).mono
  rintro x ⟨u, rfl⟩
  obtain ⟨v, rfl⟩ := (suzukiTaSmoothCoreEquivSource a.1).surjective u
  exact ⟨v, rfl⟩

/-- The derivative is symmetric for the literal, unshifted Weil form. -/
theorem smoothCore_derivative_symmetric (u v : SuzukiTaSmoothCore a.1) :
    inner ℂ (smoothCore a (suzukiTaSmoothCoreIDeriv a.1 u)) (smoothCore a v) =
      inner ℂ (smoothCore a u) (smoothCore a (suzukiTaSmoothCoreIDeriv a.1 v)) := by
  simp only [inner_eq_weil, toForm_smoothCore]
  exact ccmRestrictedWeilForm_suzukiTaSmoothCoreIDeriv a.1 u v

theorem eval_smoothCore_derivative (z : ℂ) (u : SuzukiTaSmoothCore a.1) :
    eval a z (smoothCore a (suzukiTaSmoothCoreIDeriv a.1 u)) =
      z * eval a z (smoothCore a u) := by
  rw [eval_smoothCore, eval_smoothCore]
  simpa only [star_star] using suzukiTaSpectralMoment_IDeriv a.1 (star z) u

/-- The closed subspace of entire transforms vanishing at one point. -/
abbrev evaluationKernel (z : ℂ) := LinearMap.ker (eval a z).toLinearMap

/-- Smooth shifted derivatives, regarded as vectors in their exact evaluation kernel. -/
def shiftFeature (κ : ℂ) (u : SuzukiTaSmoothCore a.1) : evaluationKernel a κ :=
  ⟨smoothCore a (suzukiTaSpectralCoreShift a.1 (star κ) u), by
    change eval a κ (smoothCore a (suzukiTaSpectralCoreShift a.1 (star κ) u)) = 0
    rw [eval_smoothCore]
    change suzukiTaSpectralMoment a.1 (star κ)
      (suzukiTaSpectralCoreShiftToHilbert a.1 (star κ) u) = 0
    exact suzukiTaSpectralMoment_shift_eq_zero a.1 (star κ) u⟩

theorem shiftFeature_coe (κ : ℂ) (u : SuzukiTaSmoothCore a.1) :
    (shiftFeature a κ u : WeilHilbertBeforeContact a) =
      smoothCore a (suzukiTaSmoothCoreIDeriv a.1 u) - κ • smoothCore a u := by
  simp only [shiftFeature, suzukiTaSpectralCoreShift, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, star_star, map_sub, map_smul]

/-- Linear shifted derivative with its evaluation constraint retained in the codomain. -/
def shiftToKernel (κ : ℂ) : SuzukiTaSmoothCore a.1 →ₗ[ℂ] evaluationKernel a κ where
  toFun := shiftFeature a κ
  map_add' u v := by
    apply Subtype.ext
    exact map_add ((smoothCore a).comp (suzukiTaSpectralCoreShift a.1 (star κ))) u v
  map_smul' c u := by
    apply Subtype.ext
    exact map_smul ((smoothCore a).comp (suzukiTaSpectralCoreShift a.1 (star κ))) c u

theorem eval_shiftFeature (κ z : ℂ) (u : SuzukiTaSmoothCore a.1) :
    eval a z (shiftFeature a κ u) = (z - κ) * eval a z (smoothCore a u) := by
  rw [shiftFeature_coe, map_sub, map_smul, eval_smoothCore_derivative, smul_eq_mul]
  ring

/-- Compact integration solves the shifted equation on the corrected dense smooth core. -/
theorem denseRange_shiftFeature (κ : ℂ) : DenseRange (shiftFeature a κ) := by
  let J := smoothCore a
  let φ := eval a κ
  let q := suzukiTaSpectralMomentNormalizer a.1 (star κ)
  have hq : φ (J q) = 1 := eval_normalizer a κ
  have hP := DenseCoreHyperplane.denseRange_projection_comp J φ q hq
    (denseRange_nativeSmoothCore a)
  apply hP.mono
  rintro y ⟨g, rfl⟩
  let g₀ := g - φ (J g) • q
  have hg₀ : φ (J g₀) = 0 := by
    simp only [g₀, map_sub, map_smul, hq, smul_eq_mul, mul_one, sub_self]
  have hzero : (∫ x : ℝ, suzukiTaSpectralWeightedCore (star κ) g₀ x) = 0 := by
    change (∫ x : ℝ, Complex.exp (I * star (star κ) * (x : ℂ)) * g₀ x) = 0
    rw [star_star, ← eval_smoothCore_eq_integral]
    exact hg₀
  refine ⟨suzukiTaSpectralShiftedPrimitiveSolution a.1 (star κ) g₀ hzero, ?_⟩
  apply Subtype.ext
  change J (suzukiTaSpectralCoreShift a.1 (star κ)
    (suzukiTaSpectralShiftedPrimitiveSolution a.1 (star κ) g₀ hzero)) = _
  rw [suzukiTaSpectralCoreShift_solution]
  change J g₀ = (DenseCoreHyperplane.projection J φ q hq (J g) : WeilHilbertBeforeContact a)
  rw [DenseCoreHyperplane.projection_coe_apply]
  exact (J.map_sub g (φ (J g) • q)).trans (by rw [map_smul])

/-- Conjugate shifts have the same polarized Gram form because the derivative is symmetric. -/
theorem shiftFeature_gram_conj (κ : ℂ) (u v : SuzukiTaSmoothCore a.1) :
    inner ℂ (shiftFeature a κ u) (shiftFeature a κ v) =
      inner ℂ (shiftFeature a (star κ) u) (shiftFeature a (star κ) v) := by
  change inner ℂ (shiftFeature a κ u : WeilHilbertBeforeContact a)
      (shiftFeature a κ v : WeilHilbertBeforeContact a) =
    inner ℂ (shiftFeature a (star κ) u : WeilHilbertBeforeContact a)
      (shiftFeature a (star κ) v : WeilHilbertBeforeContact a)
  simp only [shiftFeature_coe, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]
  rw [smoothCore_derivative_symmetric a u v]
  ring

theorem shiftFeature_norm_conj (κ : ℂ) (u : SuzukiTaSmoothCore a.1) :
    ‖shiftFeature a (star κ) u‖ = ‖shiftFeature a κ u‖ := by
  have hsq : ‖shiftFeature a (star κ) u‖ ^ 2 = ‖shiftFeature a κ u‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (shiftFeature_gram_conj a κ u u).symm
  exact le_antisymm
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq.ge)

/-- Exact unitary zero-moving between conjugate Fourier evaluation kernels. -/
def zeroMove (κ : ℂ) : evaluationKernel a κ ≃ₗᵢ[ℂ] evaluationKernel a (star κ) :=
  (LinearEquiv.refl ℂ (SuzukiTaSmoothCore a.1)).extendOfIsometry
    (shiftToKernel a κ) (shiftToKernel a (star κ))
    (denseRange_shiftFeature a κ) (denseRange_shiftFeature a (star κ))
    (shiftFeature_norm_conj a κ)

theorem zeroMove_shiftFeature (κ : ℂ) (u : SuzukiTaSmoothCore a.1) :
    zeroMove a κ (shiftFeature a κ u) = shiftFeature a (star κ) u :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

/-- The completed unitary has the exact entire-function zero-moving identity. -/
theorem zeroMove_fourier (κ z : ℂ) (x : evaluationKernel a κ) :
    (z - κ) * fourier a (zeroMove a κ x) z =
      (z - star κ) * fourier a x z := by
  have hf : Continuous (fun x : evaluationKernel a κ =>
      (z - κ) * eval a z (zeroMove a κ x)) :=
    continuous_const.mul (((eval a z).continuous.comp continuous_subtype_val).comp
      (zeroMove a κ).continuous)
  have hg : Continuous (fun x : evaluationKernel a κ =>
      (z - star κ) * eval a z x) :=
    continuous_const.mul ((eval a z).continuous.comp continuous_subtype_val)
  have heq := hf.ext_on (denseRange_shiftFeature a κ) hg (by
    rintro _ ⟨u, rfl⟩
    dsimp only
    rw [zeroMove_shiftFeature, eval_shiftFeature, eval_shiftFeature]
    ring)
  exact congrFun heq x

/-- Every completed Weil vector with a Fourier zero admits an aperture-preserving zero move. -/
theorem exists_zero_move (κ : ℂ) (x : WeilHilbertBeforeContact a)
    (hx : fourier a x κ = 0) :
    ∃ y : WeilHilbertBeforeContact a,
      fourier a y (star κ) = 0 ∧ ‖y‖ = ‖x‖ ∧
        ∀ z, (z - κ) * fourier a y z = (z - star κ) * fourier a x z := by
  let x₀ : evaluationKernel a κ := ⟨x, hx⟩
  refine ⟨zeroMove a κ x₀, (zeroMove a κ x₀).property, ?_, ?_⟩
  · exact (zeroMove a κ).norm_map x₀
  · exact fun z => zeroMove_fourier a κ z x₀

#print axioms denseRange_shiftFeature
#print axioms shiftFeature_gram_conj
#print axioms zeroMove
#print axioms zeroMove_shiftFeature
#print axioms exists_zero_move

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
