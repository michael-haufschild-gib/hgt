import GaloisForLFunctions.RHTower.CCMRationalClosedKappaLefschetzParityNoGo
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianLineWronskianGreenComparison
import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Clifford-corrected CCM product and the Xi Weil coefficient

The two opposite Clifford phases cancel in the product of literal closed CCM Lefschetz
correspondences.  On the multiplicity-exact Xi Hilbert carrier, the corresponding two-channel
Gram matrix is positive semidefinite and its Clifford-graded trace is exactly the Weil quadratic
coefficient.  The final theorem separates unconditional matrix positivity from scalar positivity:
the latter, on the full square-summable test domain, is equivalent to RH.
-/

noncomputable section

open CategoryTheory Complex
open scoped ComplexOrder

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
private abbrev RelativeKReal :=
  ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal

/-- Opposite Clifford phase on a literal closed CCM Lefschetz correspondence. -/
def ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression
    (c : Section) :
    CyclicModule.KRealAntiHom RelativeKReal RelativeKReal where
  toHom :=
    (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal c).toHom.smul (-Complex.I)
  real_antinaturality n x := by
    rw [CyclicModule.Hom.smul_degree_apply, map_smulₛₗ,
      (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal c).real_naturality,
      CyclicModule.Hom.smul_degree_apply]
    simp

@[simp]
theorem ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression_apply
    (c : Section) (n : ℕ) (x : Relative.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression c).toHom.simplicial.app
        (.op (.mk n)) x =
      (-Complex.I) •
        (ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk n)) x :=
  rfl

/-- Exact phase-cancellation/product law on the literal closed CCM quotient. -/
theorem ccmRationalAdelicClosedNonunitalStrongClifford_corrected_product_degree
    (c d : Section) (n : ℕ) (x : Relative.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression c).toHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicClosedNonunitalStrongCliffordTransgression d).toHom.simplicial.app
          (.op (.mk n)) x) =
      (ccmRationalAdelicClosedNonunitalStrongLefschetz (c * d)).simplicial.app
        (.op (.mk n)) x := by
  change (-Complex.I) •
      (ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
        (.op (.mk n))
        (Complex.I •
          (ccmRationalAdelicClosedNonunitalStrongLefschetz d).simplicial.app
            (.op (.mk n)) x) = _
  rw [map_smul, smul_smul,
    ccmRationalAdelicClosedNonunitalStrongLefschetz_mul_degree]
  simp

end GaloisForLFunctions.RHTower

namespace CliffordWeil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Real coefficient of an involutive isometry. -/
def quadratic (J : H →ₗᵢ[ℂ] H) (a : H) : ℝ :=
  (inner ℂ (J a) a).re

/-- An involutive linear isometry is self-adjoint. -/
theorem inner_map_left_eq_inner_map_right
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a b : H) :
    inner ℂ (J a) b = inner ℂ a (J b) := by
  calc
    inner ℂ (J a) b = inner ℂ (J (J a)) (J b) :=
      (J.inner_map_map (J a) b).symm
    _ = inner ℂ a (J b) := by rw [hJ a]

/-- The quadratic coefficient of an involutive isometry has no imaginary part. -/
theorem inner_map_self_eq_quadratic
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    inner ℂ (J a) a = (quadratic J a : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  calc
    (starRingEnd ℂ) (inner ℂ (J a) a) = inner ℂ a (J a) := inner_conj_symm a (J a)
    _ = inner ℂ (J a) a :=
      (inner_map_left_eq_inner_map_right J hJ a a).symm

/-- Two-channel Clifford packet attached to `a` and the reflected vector `Ja`. -/
def packet (J : H →ₗᵢ[ℂ] H) (a : H) : Fin 2 → H :=
  ![a, Complex.I • J a]

/-- Positive matrix lift of the indefinite quadratic coefficient. -/
def gram (J : H →ₗᵢ[ℂ] H) (a : H) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.gram ℂ (packet J a)

/-- Clifford grading extracting the reflected off-diagonal coefficient. -/
def grading : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, Complex.I; -Complex.I, 0]

/-- Normalized Clifford-graded trace of the positive matrix lift. -/
def coefficient (J : H →ₗᵢ[ℂ] H) (a : H) : ℂ :=
  (2 : ℂ)⁻¹ * Matrix.trace (grading * gram J a)

@[simp]
theorem gram_zero_zero
    (J : H →ₗᵢ[ℂ] H) (a : H) :
    gram J a 0 0 = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  simp [gram, packet, Matrix.gram_apply, inner_self_eq_norm_sq_to_K]

@[simp]
theorem gram_zero_one
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    gram J a 0 1 = Complex.I * (quadratic J a : ℂ) := by
  change inner ℂ a (Complex.I • J a) = _
  rw [inner_smul_right,
    ← inner_map_left_eq_inner_map_right J hJ a a,
    inner_map_self_eq_quadratic J hJ a]

@[simp]
theorem gram_one_zero
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    gram J a 1 0 = -Complex.I * (quadratic J a : ℂ) := by
  change inner ℂ (Complex.I • J a) a = _
  rw [inner_smul_left, inner_map_self_eq_quadratic J hJ a]
  simp

@[simp]
theorem gram_one_one
    (J : H →ₗᵢ[ℂ] H) (a : H) :
    gram J a 1 1 = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  change inner ℂ (Complex.I • J a) (Complex.I • J a) = _
  have hI : (starRingEnd ℂ) Complex.I * Complex.I = 1 := by
    rw [Complex.conj_I]
    simp [Complex.I_mul_I]
  rw [inner_smul_left, inner_smul_right, J.inner_map_map, ← mul_assoc, hI, one_mul]
  simp [inner_self_eq_norm_sq_to_K]

/-- Closed form of the Clifford Gram matrix. -/
theorem gram_eq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    gram J a =
      !![((‖a‖ ^ 2 : ℝ) : ℂ), Complex.I * (quadratic J a : ℂ);
        -Complex.I * (quadratic J a : ℂ), ((‖a‖ ^ 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram_zero_zero, gram_zero_one,
    gram_one_zero, gram_one_one, hJ]

/-- Matrix positivity is unconditional: it is Gram positivity, not Weil positivity. -/
theorem gram_posSemidef
    (J : H →ₗᵢ[ℂ] H) (a : H) :
    Matrix.PosSemidef (gram J a) :=
  Matrix.posSemidef_gram ℂ _

/-- The Clifford-graded coefficient of the positive lift is exactly the original quadratic form. -/
theorem coefficient_eq_quadratic
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    coefficient J a = (quadratic J a : ℂ) := by
  rw [coefficient, gram_eq J hJ a]
  simp [grading, Matrix.trace_fin_two]
  linear_combination (-(quadratic J a : ℂ)) * Complex.I_mul_I

/-- Positive-channel energy identity. -/
theorem plus_channel_energy_eq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    ‖a + J a‖ ^ 2 / 2 = ‖a‖ ^ 2 + quadratic J a := by
  have hinner : RCLike.re (inner ℂ a (J a)) = quadratic J a := by
    rw [← inner_map_left_eq_inner_map_right J hJ a a]
    rfl
  rw [norm_add_sq (𝕜 := ℂ), J.norm_map, hinner]
  ring

/-- Negative-channel energy identity. -/
theorem minus_channel_energy_eq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    ‖a - J a‖ ^ 2 / 2 = ‖a‖ ^ 2 - quadratic J a := by
  have hinner : RCLike.re (inner ℂ a (J a)) = quadratic J a := by
    rw [← inner_map_left_eq_inner_map_right J hJ a a]
    rfl
  rw [norm_sub_sq (𝕜 := ℂ), J.norm_map, hinner]
  ring

end CliffordWeil

namespace RHTower

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Critical-line reflection is an involution on the multiplicity-exact Xi Hilbert carrier. -/
theorem xiWeilLineConjLinearIsometry_involutive :
    Function.Involutive xiWeilLineConjLinearIsometry := by
  intro v
  apply Subtype.ext
  funext q
  simp [xiWeilLineConjLinearIsometry_apply, xiWeilLineConjLp_apply,
    DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply]

/-- Positive Clifford matrix attached to an Xi divisor evaluation vector. -/
def xiWeilCliffordGram (v : XiWeilCarrier) : Matrix (Fin 2) (Fin 2) ℂ :=
  CliffordWeil.gram xiWeilLineConjLinearIsometry v

/-- Clifford coefficient of the Xi positive matrix lift. -/
def xiWeilCliffordCoefficient (v : XiWeilCarrier) : ℂ :=
  CliffordWeil.coefficient xiWeilLineConjLinearIsometry v

/-- Polarized numerical pairing of critical-line reflection on the Xi Hilbert carrier. -/
def xiWeilCliffordPairing (v w : XiWeilCarrier) : ℂ :=
  inner ℂ (xiWeilLineConjLinearIsometry w) v

/-- The Xi Clifford matrix is positive without RH. -/
theorem xiWeilCliffordGram_posSemidef (v : XiWeilCarrier) :
    Matrix.PosSemidef (xiWeilCliffordGram v) :=
  CliffordWeil.gram_posSemidef xiWeilLineConjLinearIsometry v

/-- The polarized numerical pairing is exactly the multiplicity-exact Xi Weil form. -/
theorem xiWeilCliffordPairing_evaluation_eq_polarization
    (F G : ℂ → ℂ) (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    xiWeilCliffordPairing (xiWeilEvaluationLp F hF) (xiWeilEvaluationLp G hG) =
      xiWeilPolarization F G := by
  exact inner_xiWeilLineConjLp_evaluation_eq_polarization F G hF hG

/-- The Clifford coefficient on an evaluation vector is exactly the diagonal Xi Weil form. -/
theorem xiWeilCliffordCoefficient_evaluation_eq_polarization_re
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilCliffordCoefficient (xiWeilEvaluationLp F hF) =
      ((xiWeilPolarization F F).re : ℂ) := by
  rw [xiWeilCliffordCoefficient,
    CliffordWeil.coefficient_eq_quadratic
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive]
  change (xiWeilHilbertQuadratic (xiWeilEvaluationLp F hF) : ℂ) = _
  rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re]

/-- Hostile circularity certificate: positivity of the scalar Clifford coefficient on the full
Xi evaluation domain is exactly RH, despite unconditional positivity of the matrix lift. -/
theorem riemannHypothesis_iff_xiWeilCliffordCoefficient_nonneg :
    RiemannHypothesis ↔
      ∀ (F : ℂ → ℂ) (hF : XiWeilSquareSummable F),
        0 ≤ (xiWeilCliffordCoefficient (xiWeilEvaluationLp F hF)).re := by
  rw [riemannHypothesis_iff_xiWeilPolarization_nonneg]
  constructor
  · intro h F hF
    rw [xiWeilCliffordCoefficient_evaluation_eq_polarization_re F hF]
    simpa using h F hF
  · intro h F hF
    have h' := h F hF
    rw [xiWeilCliffordCoefficient_evaluation_eq_polarization_re F hF] at h'
    simpa using h'

end RHTower
