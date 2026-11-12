import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGrossencharacterFactorizesTheProbeCorrection
import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.MetaplecticMobiusDescent.TheDifferentNormalizesTheTraceCharacter
import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaWeightsArePrincipalIdealCharacters
import GaloisForLFunctions.HTGeometry.ParityGaussianPoisson
import GaloisForLFunctions.HTGeometry.MellinConjugate
import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Harmonic Gaussian Poisson summation gives Grossencharacter continuation

On the Euclidean plane `ℝ² ≅ ℂ`, every anti-holomorphic harmonic polynomial `(x₀ − i x₁)^m`
multiplied by `e^{−π t ‖x‖²}` is an eigenfunction of the Fourier transform up to scaling:

`(𝓕 ((x₀ − i x₁)^m e^{−π t ‖x‖²}))(ξ) = t⁻¹ (−i / t)^m (ξ₀ − i ξ₁)^m e^{−π (1/t) ‖ξ‖²}`.

Generating-function proof: for real `u`, `e^{u(x₀ − i x₁) − π t (x₀² + x₁²)}` factors into
two scalar quadratic exponentials whose Fourier transforms multiply to
`t⁻¹ e^{−π ‖ξ‖² / t + u (−i / t)(ξ₀ − i ξ₁)}` because `u² + (−i u)² = 0`; differentiating `m` times
in `u` at `u = 0` yields the `m`-th harmonic moment.

Applying affine Poisson summation on cosets of the primitive finite conductor `𝔣` of any ray class
character `ψ : HeckeCharacter 𝔪` over `K = ℚ(ω)` with harmonic weight `6k` (`k ≥ 1`) gives the
exact theta inversion formula

`Θ_{ψ, k}(1 / t) = ε(ψ, k) · t^{6k + 1} · conj(Θ_{ψ, k}(t))`,   `‖ε(ψ, k)‖ = 1`,

with vanishing constant terms at `0` and `∞`. Packaging `Θ_{ψ, k}` as a strong functional-equation
pair produces an entire completed `L`-function `grossenCompletedL 𝔪 ψ k` of order at most one with
functional equation `Λ(1 − w) = ε · conj(Λ(conj w))`, whose division by `α_𝔣^{−(w + 3k)} Γ(w + 3k)`
is holomorphic on `Re w > −3k`, equals the convergent primitive Euler product on `Re w > 1`, and
relates to `grossenEulerProductModS 𝔪 ψ k S` through the entire finite Euler product
`grossenDeletedFactors 𝔪 ψ k S` (nonvanishing on `Re w > 0`).
-/

noncomputable section

open Complex Filter MeasureTheory NumberField IsDedekindDomain Set
open scoped BigOperators Classical ComplexConjugate FourierTransform Topology nonZeroDivisors

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open HTGeometry HTGeometry.IntegerLatticePoisson

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

/-! ### Two-dimensional harmonic Gaussians and their Fourier transform -/

/-- The anti-holomorphic linear coordinate `x₀ − i x₁` on `ℝ²`. -/
def conjPlane (x : Plane2) : ℂ := (x 0 : ℂ) - Complex.I * (x 1 : ℂ)

theorem continuous_conjPlane : Continuous conjPlane := by
  unfold conjPlane
  fun_prop

theorem conjPlane_add (x y : Plane2) : conjPlane (x + y) = conjPlane x + conjPlane y := by
  simp only [conjPlane, PiLp.add_apply, Complex.ofReal_add]
  ring

theorem conjPlane_smul (r : ℝ) (x : Plane2) : conjPlane (r • x) = (r : ℂ) * conjPlane x := by
  simp only [conjPlane, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem norm_sq_plane2 (x : Plane2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Real.inner_apply, pow_two]

theorem norm_conjPlane (x : Plane2) : ‖conjPlane x‖ = ‖x‖ := by
  have hre : (conjPlane x).re = x 0 := by simp [conjPlane]
  have him : (conjPlane x).im = -(x 1) := by simp [conjPlane]
  have hsq : ‖conjPlane x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him, norm_sq_plane2]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The two-dimensional harmonic Gaussian `(x₀ − i x₁)^m e^{−π t ‖x‖²}`. -/
def harmonicGaussian (m : ℕ) (t : ℝ) (x : Plane2) : ℂ :=
  conjPlane x ^ m * gaussianKernel (Real.pi * t) x

theorem continuous_harmonicGaussian (m : ℕ) (t : ℝ) : Continuous (harmonicGaussian m t) :=
  (continuous_conjPlane.pow m).mul (continuous_gaussianKernel _)

theorem norm_harmonicGaussian (m : ℕ) (t : ℝ) (x : Plane2) :
    ‖harmonicGaussian m t x‖ = ‖x‖ ^ m * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2) := by
  rw [harmonicGaussian, norm_mul, norm_pow, norm_conjPlane,
    IntegerLatticePoisson.norm_gaussianKernel]

/-- Half the Gaussian decay rate absorbs the polynomial factor `‖x‖^m`. -/
theorem exists_harmonicGaussian_norm_bound (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Plane2,
      ‖harmonicGaussian m t x‖ ≤ C * ‖gaussianKernel (Real.pi * (t / 2)) x‖ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  refine ⟨Real.exp ((m : ℝ) ^ 2 / (2 * Real.pi)) / (Real.sqrt t) ^ m,
    div_pos (Real.exp_pos _) (pow_pos hs m), fun x => ?_⟩
  have hp := _root_.RHTower.pow_mul_exp_neg_half_pi_sq_le m (mul_nonneg hs.le (norm_nonneg x))
  have he : -(Real.pi / 2) * (Real.sqrt t * ‖x‖) ^ 2 = -(Real.pi * (t / 2)) * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    ring
  rw [he, mul_pow] at hp
  have hscaled : ‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) ≤
      Real.exp ((m : ℝ) ^ 2 / (2 * Real.pi)) / (Real.sqrt t) ^ m := by
    rw [le_div_iff₀ (pow_pos hs m)]
    nlinarith only [hp]
  rw [norm_harmonicGaussian, IntegerLatticePoisson.norm_gaussianKernel]
  calc ‖x‖ ^ m * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2)
      = (‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2)) *
          Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscaled (Real.exp_pos _).le

theorem integrable_harmonicGaussian (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (harmonicGaussian m t) := by
  obtain ⟨C, _, hb⟩ := exists_harmonicGaussian_norm_bound m ht
  exact ((integrable_gaussianKernel (mul_pos Real.pi_pos (half_pos ht))).norm.const_mul C).mono'
    (continuous_harmonicGaussian m t).aestronglyMeasurable (Eventually.of_forall hb)

/-- Scalar coordinate factors of the generating function `e^{u(x₀ − i x₁) − π t ‖x‖²}`. -/
private def harmonicGenCoord (t u : ℝ) : Fin 2 → ℝ → ℂ :=
  ![fun y => cexp ((u : ℂ) * (y : ℂ) - (Real.pi * t : ℂ) * (y : ℂ) ^ 2),
    fun y => cexp ((-Complex.I * (u : ℂ)) * (y : ℂ) - (Real.pi * t : ℂ) * (y : ℂ) ^ 2)]

private theorem coordinateProduct_harmonicGenCoord (t u : ℝ) (x : Plane2) :
    coordinateProduct (harmonicGenCoord t u) x =
      cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x := by
  rw [coordinateProduct, Fin.prod_univ_two]
  simp only [harmonicGenCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [gaussianKernel_eq_ofReal, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [norm_sq_plane2, conjPlane]
  push_cast
  ring

private theorem fourier_cexp_linear_gaussian {t : ℝ} (ht : 0 < t) (w : ℂ) (ξ₀ : ℝ) :
    (𝓕 (fun y : ℝ => cexp (w * (y : ℂ) - (Real.pi * t : ℂ) * (y : ℂ) ^ 2))) ξ₀ =
      (Real.sqrt (1 / t) : ℂ) *
        cexp ((((-2 * Real.pi * ξ₀ : ℝ) : ℂ) * Complex.I + w) ^ 2 /
          (4 * (Real.pi * t : ℂ))) := by
  have hb : (-(Real.pi * t : ℂ)).re < 0 := by
    have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
    simpa using hpt
  rw [Real.fourier_eq']
  simp_rw [smul_eq_mul]
  have heq : (fun y : ℝ => cexp ((-2 * Real.pi * inner ℝ y ξ₀ : ℝ) * Complex.I) *
        cexp (w * (y : ℂ) - (Real.pi * t : ℂ) * (y : ℂ) ^ 2)) =
      (fun y : ℝ => cexp (-(Real.pi * t : ℂ) * (y : ℂ) ^ 2 +
        (((-2 * Real.pi * ξ₀ : ℝ) : ℂ) * Complex.I + w) * (y : ℂ) + 0)) := by
    funext y
    rw [← Complex.exp_add, Real.inner_apply]
    congr 1
    push_cast
    ring
  rw [heq, _root_.integral_cexp_quadratic hb]
  have hpi : (Real.pi : ℂ) / - -(Real.pi * t : ℂ) = ((1 / t : ℝ) : ℂ) := by
    rw [neg_neg]
    push_cast
    field_simp [Real.pi_ne_zero, ht.ne']
  have hsqrt : (((1 / t : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt (1 / t) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hpi, hsqrt]
  congr 1
  congr 1
  ring

private theorem fourier_harmonicGen {t : ℝ} (ht : 0 < t) (u : ℝ) (ξ : Plane2) :
    (𝓕 (fun x : Plane2 => cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)) ξ =
      ((1 / t : ℝ) : ℂ) * gaussianKernel (Real.pi * (1 / t)) ξ *
        cexp ((u : ℂ) * ((-Complex.I / (t : ℂ)) * conjPlane ξ)) := by
  have hfun : (fun x : Plane2 => cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x) =
      coordinateProduct (harmonicGenCoord t u) :=
    funext fun x => (coordinateProduct_harmonicGenCoord t u x).symm
  rw [hfun, fourier_coordinateProduct, Fin.prod_univ_two]
  simp only [harmonicGenCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fourier_cexp_linear_gaussian ht (u : ℂ) (ξ 0),
    fourier_cexp_linear_gaussian ht (-Complex.I * (u : ℂ)) (ξ 1)]
  have hsq : (Real.sqrt (1 / t) : ℂ) * (Real.sqrt (1 / t) : ℂ) = ((1 / t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  calc
    _ = ((Real.sqrt (1 / t) : ℂ) * (Real.sqrt (1 / t) : ℂ)) *
        (cexp ((((-2 * Real.pi * ξ 0 : ℝ) : ℂ) * Complex.I + (u : ℂ)) ^ 2 /
          (4 * (Real.pi * t : ℂ))) *
        cexp ((((-2 * Real.pi * ξ 1 : ℝ) : ℂ) * Complex.I + (-Complex.I * (u : ℂ))) ^ 2 /
          (4 * (Real.pi * t : ℂ)))) := by ring
    _ = ((1 / t : ℝ) : ℂ) * gaussianKernel (Real.pi * (1 / t)) ξ *
        cexp ((u : ℂ) * ((-Complex.I / (t : ℂ)) * conjPlane ξ)) := by
      rw [hsq, ← Complex.exp_add, gaussianKernel_eq_ofReal, Complex.ofReal_exp]
      conv_rhs => rw [mul_assoc, ← Complex.exp_add]
      congr 2
      rw [norm_sq_plane2, conjPlane]
      push_cast
      field_simp [Real.pi_ne_zero, ht.ne']
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Generating moment integral in `u : ℝ` for the `m`-th harmonic Gaussian. -/
private def harmonicMoment (m : ℕ) (t : ℝ) (ξ : Plane2) (u : ℝ) : ℂ :=
  ∫ x : Plane2, cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
    (conjPlane x ^ m * cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)

private theorem norm_cexp_mul_conjPlane_gaussian_le (m : ℕ) {t : ℝ} (ht : 0 < t)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (u : ℝ), |u| ≤ M → ∀ x : Plane2,
      ‖conjPlane x ^ m * cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x‖ ≤
        K₀ * ‖gaussianKernel (Real.pi * (t / 2)) x‖ := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_harmonicGaussian_norm_bound m (half_pos ht)
  have hp : 0 < Real.pi * (t / 4) := by positivity
  refine ⟨C₁ * Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))), by positivity, fun u hu x => ?_⟩
  rw [norm_mul, norm_mul, norm_pow, norm_conjPlane, Complex.norm_exp,
    IntegerLatticePoisson.norm_gaussianKernel, IntegerLatticePoisson.norm_gaussianKernel]
  have hre : ((u : ℂ) * conjPlane x).re = u * x 0 := by simp [conjPlane]
  rw [hre]
  have hux : u * x 0 ≤ M * ‖x‖ := by
    calc u * x 0 ≤ |u * x 0| := le_abs_self _
      _ = |u| * |x 0| := abs_mul u (x 0)
      _ ≤ M * ‖x‖ := mul_le_mul hu (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
        (abs_nonneg _) hM
  have hquad : M * ‖x‖ - Real.pi * (t / 4) * ‖x‖ ^ 2 ≤ M ^ 2 / (4 * (Real.pi * (t / 4))) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * (Real.pi * (t / 4)) * ‖x‖ - M)]
  have hexp_split : Real.exp (u * x 0) * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2) ≤
      Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))) *
        Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) *
        Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hm_bound : ‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) ≤
      C₁ * Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2) := by
    have h1 := hb₁ x
    rw [norm_harmonicGaussian, IntegerLatticePoisson.norm_gaussianKernel,
      show t / 2 / 2 = t / 4 by ring] at h1
    exact h1
  calc ‖x‖ ^ m * Real.exp (u * x 0) * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2)
      = ‖x‖ ^ m * (Real.exp (u * x 0) * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2)) := by ring
    _ ≤ ‖x‖ ^ m * (Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))) *
          Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) *
          Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp_split (pow_nonneg (norm_nonneg x) m)
    _ = Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))) *
          (‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2)) *
          Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2) := by ring
    _ ≤ Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))) *
          (C₁ * Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2)) *
          Real.exp (-(Real.pi * (t / 4)) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm_bound (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = C₁ * Real.exp (M ^ 2 / (4 * (Real.pi * (t / 4)))) *
          Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]
        ring_nf

private theorem hasDerivAt_harmonicMoment (m : ℕ) {t : ℝ} (ht : 0 < t) (ξ : Plane2) (u₀ : ℝ) :
    HasDerivAt (harmonicMoment m t ξ) (harmonicMoment (m + 1) t ξ u₀) u₀ := by
  obtain ⟨K₀, _, hK₀⟩ := norm_cexp_mul_conjPlane_gaussian_le (m + 1) ht (|u₀| + 1) (by positivity)
  obtain ⟨K₁, _, hK₁⟩ := norm_cexp_mul_conjPlane_gaussian_le m ht (|u₀| + 1) (by positivity)
  have hc_phase : Continuous (fun x : Plane2 => cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_id.inner continuous_const))).mul
        continuous_const)
  have hF_meas : ∀ u : ℝ, AEStronglyMeasurable
      (fun x : Plane2 => cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        (conjPlane x ^ m * cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x))
      volume := fun u => by
    refine Continuous.aestronglyMeasurable ?_
    have hc2 : Continuous (fun x : Plane2 => cexp ((u : ℂ) * conjPlane x)) :=
      Complex.continuous_exp.comp (continuous_const.mul continuous_conjPlane)
    exact hc_phase.mul (((continuous_conjPlane.pow m).mul hc2).mul (continuous_gaussianKernel _))
  have hF_int : Integrable
      (fun x : Plane2 => cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        (conjPlane x ^ m * cexp ((u₀ : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)) := by
    refine ((integrable_gaussianKernel (mul_pos Real.pi_pos (half_pos ht))).norm.const_mul K₁).mono'
      (hF_meas u₀) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hK₁ u₀ (by linarith) x
  have hF'_meas : AEStronglyMeasurable
      (fun x : Plane2 => cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        (conjPlane x ^ (m + 1) * cexp ((u₀ : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x))
      volume := by
    refine Continuous.aestronglyMeasurable ?_
    have hc2 : Continuous (fun x : Plane2 => cexp ((u₀ : ℂ) * conjPlane x)) :=
      Complex.continuous_exp.comp (continuous_const.mul continuous_conjPlane)
    exact hc_phase.mul (((continuous_conjPlane.pow (m + 1)).mul hc2).mul (continuous_gaussianKernel _))
  have hbound : Integrable (fun x : Plane2 => K₀ * ‖gaussianKernel (Real.pi * (t / 2)) x‖) :=
    (integrable_gaussianKernel (mul_pos Real.pi_pos (half_pos ht))).norm.const_mul K₀
  have hle : ∀ᵐ x : Plane2, ∀ u ∈ Metric.ball u₀ 1,
      ‖cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        (conjPlane x ^ (m + 1) * cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)‖ ≤
        K₀ * ‖gaussianKernel (Real.pi * (t / 2)) x‖ := by
    filter_upwards with x u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    have hu_abs : |u| ≤ |u₀| + 1 := by linarith [abs_sub_abs_le_abs_sub u u₀]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hK₀ u hu_abs x
  have hdiff : ∀ᵐ x : Plane2, ∀ u ∈ Metric.ball u₀ 1,
      HasDerivAt (fun v : ℝ => cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        (conjPlane x ^ m * cexp ((v : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x))
        (cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
          (conjPlane x ^ (m + 1) * cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)) u := by
    filter_upwards with x u _
    have hd1 : HasDerivAt (fun v : ℝ => (v : ℂ) * conjPlane x) (conjPlane x) u := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (conjPlane x)
    have hd2 : HasDerivAt (fun v : ℝ => cexp ((v : ℂ) * conjPlane x))
        (cexp ((u : ℂ) * conjPlane x) * conjPlane x) u := hd1.cexp
    have hd3 := ((hd2.const_mul (conjPlane x ^ m)).mul_const (gaussianKernel (Real.pi * t) x)).const_mul
      (cexp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I))
    refine hd3.congr_deriv ?_
    rw [pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := Metric.ball u₀ 1) (Metric.ball_mem_nhds u₀ zero_lt_one)
    (Eventually.of_forall hF_meas) hF_int hF'_meas hle hbound hdiff).2

private theorem harmonicMoment_eq {t : ℝ} (ht : 0 < t) (ξ : Plane2) :
    ∀ (m : ℕ) (u : ℝ), harmonicMoment m t ξ u =
      ((1 / t : ℝ) : ℂ) * ((-Complex.I / (t : ℂ)) * conjPlane ξ) ^ m *
        gaussianKernel (Real.pi * (1 / t)) ξ *
        cexp ((u : ℂ) * ((-Complex.I / (t : ℂ)) * conjPlane ξ))
  | 0, u => by
    have h0 : harmonicMoment 0 t ξ u =
        (𝓕 (fun x : Plane2 => cexp ((u : ℂ) * conjPlane x) * gaussianKernel (Real.pi * t) x)) ξ := by
      rw [harmonicMoment, Real.fourier_eq']
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [pow_zero, one_mul])
    rw [h0, fourier_harmonicGen ht u ξ, pow_zero, mul_one]
  | m + 1, u => by
    have hrec := harmonicMoment_eq ht ξ m
    have hderiv_lhs := hasDerivAt_harmonicMoment m ht ξ u
    rw [funext hrec] at hderiv_lhs
    have hd1 : HasDerivAt (fun v : ℝ => (v : ℂ) * ((-Complex.I / (t : ℂ)) * conjPlane ξ))
        ((-Complex.I / (t : ℂ)) * conjPlane ξ) u := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const ((-Complex.I / (t : ℂ)) * conjPlane ξ)
    have hd_rhs := (hd1.cexp.const_mul (((1 / t : ℝ) : ℂ) *
      ((-Complex.I / (t : ℂ)) * conjPlane ξ) ^ m * gaussianKernel (Real.pi * (1 / t)) ξ))
    rw [hderiv_lhs.unique hd_rhs, pow_succ]
    ring

/-- **Exact 2D harmonic Gaussian Fourier transform.** -/
theorem fourier_harmonicGaussian (m : ℕ) {t : ℝ} (ht : 0 < t) (ξ : Plane2) :
    (𝓕 (harmonicGaussian m t)) ξ =
      ((1 / t : ℝ) : ℂ) * (-Complex.I / (t : ℂ)) ^ m * harmonicGaussian m (1 / t) ξ := by
  have h0 : (𝓕 (harmonicGaussian m t)) ξ = harmonicMoment m t ξ 0 := by
    rw [Real.fourier_eq', harmonicMoment]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp [harmonicGaussian])
  rw [h0, harmonicMoment_eq ht ξ m 0, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    mul_pow, harmonicGaussian]
  ring

theorem fourier_affine_harmonicGaussian (B : Plane2 ≃L[ℝ] Plane2) (m : ℕ) {t : ℝ} (ht : 0 < t)
    (v ξ : Plane2) :
    (𝓕 (fun x => harmonicGaussian m t (B x + v))) ξ =
      (latticeScale B : ℂ) * ((1 / t : ℝ) : ℂ) * (-Complex.I / (t : ℂ)) ^ m *
        (latticePhase v (inverseAdjoint B ξ) * harmonicGaussian m (1 / t) (inverseAdjoint B ξ)) := by
  have h := fourier_comp_linearEquiv (fun x => harmonicGaussian m t (x + v)) B ξ
  rw [fourier_comp_add, fourier_harmonicGaussian m ht] at h
  rw [h, latticePhase]
  simp only [Complex.real_smul]
  ring

theorem harmonicGaussian_summable_affine_translates (B : Plane2 ≃L[ℝ] Plane2) (m : ℕ)
    {t : ℝ} (ht : 0 < t) (v : Plane2) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u : (Fin 2 → ℤ) → ℝ, Summable u ∧ ∀ x : Fin 2 → ℝ, ‖x‖ ≤ R → ∀ k : Fin 2 → ℤ,
      ‖harmonicGaussian m t (B (WithLp.toLp 2 (x + integerPoint k)) + v)‖ ≤ u k := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicGaussian_norm_bound m ht
  obtain ⟨u, hu, hub⟩ := gaussian_summable_affine_translates B
    (mul_pos Real.pi_pos (half_pos ht)) v R hR
  exact ⟨fun k => C * u k, hu.mul_left C,
    fun x hx k => (hbound _).trans (mul_le_mul_of_nonneg_left (hub x hx k) hC.le)⟩

theorem summable_norm_harmonicGaussian_affine (B : Plane2 ≃L[ℝ] Plane2) (m : ℕ)
    {t : ℝ} (ht : 0 < t) (v : Plane2) :
    Summable fun k : Fin 2 → ℤ =>
      ‖harmonicGaussian m t (B (euclideanIntegerPoint k) + v)‖ := by
  obtain ⟨u, hu, hb⟩ := harmonicGaussian_summable_affine_translates B m ht v 0 le_rfl
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hu
  simpa only [zero_add, euclideanIntegerPoint] using hb 0 (by simp) k

/-- **Affine lattice Poisson summation for 2D harmonic Gaussians.** -/
theorem harmonic_gaussian_poisson_with_shift (B : Plane2 ≃L[ℝ] Plane2) (m : ℕ)
    {t : ℝ} (ht : 0 < t) (v : Plane2) :
    (∑' k : Fin 2 → ℤ, harmonicGaussian m t (B (euclideanIntegerPoint k) + v)) =
      (latticeScale B : ℂ) * ((1 / t : ℝ) : ℂ) * (-Complex.I / (t : ℂ)) ^ m *
        ∑' k : Fin 2 → ℤ, latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          harmonicGaussian m (1 / t) (inverseAdjoint B (euclideanIntegerPoint k)) := by
  have ht' : 0 < 1 / t := one_div_pos.mpr ht
  have hdual_norm : Summable fun k : Fin 2 → ℤ =>
      ‖latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
        harmonicGaussian m (1 / t) (inverseAdjoint B (euclideanIntegerPoint k))‖ := by
    simpa only [norm_mul, norm_latticePhase, one_mul, add_zero, inverseAdjointEquiv_apply] using
      summable_norm_harmonicGaussian_affine (inverseAdjointEquiv B) m ht' 0
  have hs : Summable fun k : Fin 2 → ℤ =>
      (𝓕 (fun x => harmonicGaussian m t (B x + v))) (euclideanIntegerPoint k) := by
    apply Summable.of_norm
    refine (hdual_norm.mul_left
      ‖(latticeScale B : ℂ) * ((1 / t : ℝ) : ℂ) * (-Complex.I / (t : ℂ)) ^ m‖).congr fun k => ?_
    rw [fourier_affine_harmonicGaussian B m ht v (euclideanIntegerPoint k)]
    simp only [norm_mul]
  have hc : Continuous (fun x => harmonicGaussian m t (B x + v)) :=
    (continuous_harmonicGaussian m t).comp (B.continuous.add continuous_const)
  have hi : Integrable (fun x => harmonicGaussian m t (B x + v)) :=
    integrable_comp_linearEquiv ((integrable_harmonicGaussian m ht).comp_add_right v) B
  rw [euclidean_poisson_of_summable_translates hc hi
    (harmonicGaussian_summable_affine_translates B m ht v) hs]
  simp_rw [fourier_affine_harmonicGaussian B m ht v]
  exact tsum_mul_left

/-! ### Eisenstein principal lattice geometry and trace duality -/

local instance : Countable O := Coordinates.coordinateEquiv.countable_iff.mpr inferInstance

local instance : Finite Oˣ :=
  Nat.finite_of_card_ne_zero (by rw [card_units_thirdCyclotomic K]; decide)

private theorem omega_sq_eq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem ringComplex_conjO_eq (x : O) : ringComplex (conjO x) = conj (ringComplex x) := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  have h3 : ringComplex omega ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : ringComplex omega ≠ 0 := fun h => by
    rw [h, zero_pow (by decide)] at h3; exact zero_ne_one h3
  have hznorm : ‖ringComplex omega‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h3 (by decide)
  have hstar : conj (ringComplex omega) = ringComplex omega ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc ringComplex omega * conj (ringComplex omega) = 1 := by
          rw [Complex.mul_conj', hznorm]; norm_num
      _ = ringComplex omega * ringComplex omega ^ 2 := by rw [← pow_succ', h3]
  simp only [map_add, map_mul, map_intCast, conjO_omega, map_pow, hstar]

theorem ringComplex_omega_sq_add : ringComplex omega ^ 2 + ringComplex omega + 1 = 0 := by
  have h := congrArg ringComplex omega_sq_eq
  simp only [map_pow, map_sub, map_neg, map_one] at h
  linear_combination h

theorem ringComplex_omega_re : (ringComplex omega).re = -1 / 2 := by
  have h1 := ringComplex_conjO_eq omega
  rw [conjO_omega, map_pow] at h1
  have hsum : ringComplex omega + conj (ringComplex omega) = -1 := by
    rw [← h1]
    linear_combination ringComplex_omega_sq_add
  have hre := congrArg Complex.re hsum
  simp only [add_re, conj_re, neg_re, one_re] at hre
  linarith

theorem ringComplex_omega_im_sq : (ringComplex omega).im ^ 2 = 3 / 4 := by
  have h3 : ringComplex omega ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hnorm : ‖ringComplex omega‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h3 (by decide)
  have hsq : (ringComplex omega).re ^ 2 + (ringComplex omega).im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq (ringComplex omega)
    rw [hnorm, one_pow, Complex.normSq_apply] at h
    nlinarith
  rw [ringComplex_omega_re] at hsq
  linarith

theorem ringComplex_omega_im_ne_zero : (ringComplex omega).im ≠ 0 := by
  intro h
  have hsq := ringComplex_omega_im_sq
  rw [h, zero_pow (by decide)] at hsq
  norm_num at hsq

theorem abs_ringComplex_omega_im : |(ringComplex omega).im| = Real.sqrt 3 / 2 := by
  have h1 : |(ringComplex omega).im| ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
    rw [sq_abs, ringComplex_omega_im_sq, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  exact (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp h1

theorem ringComplex_traceLambda_sq : ringComplex traceLambda ^ 2 = -3 := by
  have h : ringComplex traceLambda = 1 + 2 * ringComplex omega := by
    simp only [traceLambda, map_add, map_one, map_mul, map_ofNat]
  rw [h]
  linear_combination 4 * ringComplex_omega_sq_add

theorem norm_ringComplex_traceLambda_sq : ‖ringComplex traceLambda‖ ^ 2 = 3 := by
  have h := congrArg norm (ringComplex_traceLambda_sq)
  simpa only [norm_pow, norm_neg, Complex.norm_ofNat] using h

theorem norm_ringComplex_traceLambda : ‖ringComplex traceLambda‖ = Real.sqrt 3 := by
  have h : ‖ringComplex traceLambda‖ ^ 2 = Real.sqrt 3 ^ 2 := by
    rw [norm_ringComplex_traceLambda_sq, Real.sq_sqrt (by norm_num)]
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 3)).mp h

/-- Twice the real part of `ringComplex z` equals the rational field trace of `z : O`. -/
theorem two_mul_re_ringComplex_eq_trace (z : O) :
    2 * (ringComplex z).re = ((Algebra.trace ℚ K (algebraMap O K z) : ℚ) : ℝ) := by
  set a := (Coordinates.coords z).1
  set b := (Coordinates.coords z).2
  rw [← Coordinates.eval_coords z]
  change 2 * (ringComplex (Coordinates.eval a b)).re =
    ((Algebra.trace ℚ K (algebraMap O K (Coordinates.eval a b)) : ℚ) : ℝ)
  have hK : algebraMap O K (Coordinates.eval a b) =
      ((a : ℚ) : K) + ((b : ℚ) : K) * algebraMap O K omega := by
    simp [Coordinates.eval]
  rw [hK, Coordinates.trace_rational_coordinates]
  simp only [Coordinates.eval, map_add, map_mul, map_intCast, add_re, mul_re, intCast_re,
    intCast_im, zero_mul, sub_zero, ringComplex_omega_re, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_intCast]
  ring

/-- Twice the real part of `ringComplex z / ringComplex d` equals `Tr_{K/ℚ}(z / d)`. -/
theorem two_mul_re_ringComplex_div_eq_trace (z d : O) (hd : d ≠ 0) :
    2 * (ringComplex z / ringComplex d).re =
      ((Algebra.trace ℚ K (algebraMap O K z / algebraMap O K d) : ℚ) : ℝ) := by
  set a := (Coordinates.coords d).1
  set b := (Coordinates.coords d).2
  have hd_eq : d = Coordinates.eval a b := (Coordinates.eval_coords d).symm
  rw [hd_eq] at hd ⊢
  set N : ℤ := a ^ 2 - a * b + b ^ 2
  have hN_pos : 0 < N := Coordinates.coordinate_norm_pos a b hd
  have hmul : Coordinates.eval a b * conjO (Coordinates.eval a b) = (N : O) :=
    Coordinates.eval_mul_conj a b
  have hdC : ringComplex (Coordinates.eval a b) ≠ 0 :=
    fun h => hd (ringComplex_injective (by simpa using h))
  have hdK : algebraMap O K (Coordinates.eval a b) ≠ 0 :=
    fun h => hd (NumberField.RingOfIntegers.coe_injective h)
  have hdivC : ringComplex z / ringComplex (Coordinates.eval a b) =
      ringComplex (z * conjO (Coordinates.eval a b)) / (N : ℂ) := by
    have hNC : ringComplex (Coordinates.eval a b) *
        ringComplex (conjO (Coordinates.eval a b)) = (N : ℂ) := by
      simpa using congrArg ringComplex hmul
    have hNZ : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [div_eq_div_iff hdC hNZ, map_mul, ← hNC]
    ring
  have hdivK : algebraMap O K z / algebraMap O K (Coordinates.eval a b) =
      ((1 / (N : ℚ) : ℚ) : K) * algebraMap O K (z * conjO (Coordinates.eval a b)) := by
    have hNK : algebraMap O K (Coordinates.eval a b) *
        algebraMap O K (conjO (Coordinates.eval a b)) = (N : K) := by
      simpa using congrArg (algebraMap O K) hmul
    have hNQ : (N : K) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [div_eq_iff hdK, map_mul]
    push_cast
    field_simp [hNQ]
    linear_combination (algebraMap O K z) * hNK.symm
  rw [hdivC, hdivK]
  have hsmul : Algebra.trace ℚ K (((1 / (N : ℚ) : ℚ) : K) *
      algebraMap O K (z * conjO (Coordinates.eval a b))) =
      (1 / (N : ℚ)) * Algebra.trace ℚ K (algebraMap O K (z * conjO (Coordinates.eval a b))) := by
    simpa [Algebra.smul_def] using
      (Algebra.trace ℚ K).map_smul (1 / (N : ℚ)) (algebraMap O K (z * conjO (Coordinates.eval a b)))
  rw [hsmul, show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_re,
    mul_div_assoc', two_mul_re_ringComplex_eq_trace]
  push_cast
  ring

/-- ℝ-linear equivalence identifying `ℂ` with `Plane2 = EuclideanSpace ℝ (Fin 2)`. -/
def complexPlaneLinearEquiv : ℂ ≃ₗ[ℝ] Plane2 where
  toFun z := WithLp.toLp 2 ![z.re, z.im]
  map_add' z w := by ext i; fin_cases i <;> simp
  map_smul' r z := by ext i; fin_cases i <;> simp
  invFun x := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv x := by
    ext i; fin_cases i <;> simp

@[simp]
theorem conjPlane_complexPlaneLinearEquiv (z : ℂ) :
    conjPlane (complexPlaneLinearEquiv z) = conj z := by
  apply Complex.ext <;> simp [conjPlane, complexPlaneLinearEquiv]

@[simp]
theorem norm_complexPlaneLinearEquiv (z : ℂ) : ‖complexPlaneLinearEquiv z‖ = ‖z‖ := by
  rw [← norm_conjPlane, conjPlane_complexPlaneLinearEquiv, Complex.norm_conj]

theorem inner_complexPlaneLinearEquiv (z w : ℂ) :
    inner ℝ (complexPlaneLinearEquiv z) (complexPlaneLinearEquiv w) = (z * conj w).re := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [complexPlaneLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.inner_apply, mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add]

/-- ℝ-linear equivalence sending `(u₀, u₁) ∈ ℝ²` to `u₀ + u₁ ω ∈ ℂ`. -/
def omegaBasisLinearEquiv : Plane2 ≃ₗ[ℝ] ℂ where
  toFun u := (u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega
  map_add' u v := by simp only [PiLp.add_apply, Complex.ofReal_add]; ring
  map_smul' r u := by
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul,
      RingHom.id_apply]
    ring
  invFun z := WithLp.toLp 2 ![z.re + z.im / (2 * (ringComplex omega).im),
    z.im / (ringComplex omega).im]
  left_inv u := by
    have him0 := ringComplex_omega_im_ne_zero
    ext i
    fin_cases i
    · change (((u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega).re +
        ((u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega).im / (2 * (ringComplex omega).im)) = u 0
      simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero,
        ringComplex_omega_re, add_im, mul_im, zero_add]
      field_simp [him0]
      ring
    · change (((u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega).im / (ringComplex omega).im) = u 1
      simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
      field_simp [him0]
  right_inv z := by
    have him0 := ringComplex_omega_im_ne_zero
    apply Complex.ext
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, ringComplex_omega_re]
      field_simp [him0]
      ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
      field_simp [him0]

/-- Symmetric lattice scale `s(f₀) = √(2 / (√3 · |f₀|))` for a nonzero generator `f₀ : O`. -/
def grossenElemScale (f₀ : O) : ℝ :=
  Real.sqrt (2 / (Real.sqrt 3 * ‖ringComplex f₀‖))

theorem grossenElemScale_pos {f₀ : O} (hf₀ : f₀ ≠ 0) : 0 < grossenElemScale f₀ := by
  have hz : 0 < ‖ringComplex f₀‖ :=
    norm_pos_iff.mpr fun h => hf₀ (ringComplex_injective (by simpa using h))
  unfold grossenElemScale
  positivity

theorem grossenElemScale_sq {f₀ : O} (hf₀ : f₀ ≠ 0) :
    grossenElemScale f₀ ^ 2 = 2 / (Real.sqrt 3 * ‖ringComplex f₀‖) := by
  have hz : 0 < ‖ringComplex f₀‖ :=
    norm_pos_iff.mpr fun h => hf₀ (ringComplex_injective (by simpa using h))
  exact Real.sq_sqrt (by positivity)

/-- ℝ-linear multiplication on `ℂ` by a nonzero complex number `c`. -/
def complexMulLeftLinearEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := c * z
  map_add' z w := mul_add c z w
  map_smul' r z := by simp only [Complex.real_smul, RingHom.id_apply]; ring
  invFun z := c⁻¹ * z
  left_inv z := inv_mul_cancel_left₀ hc z
  right_inv z := mul_inv_cancel_left₀ hc z

/-- The continuous ℝ-linear equivalence parametrizing the scaled principal ideal `f₀ O` in `ℝ²`. -/
def eisensteinLatticeEquiv (f₀ : O) (hf₀ : f₀ ≠ 0) : Plane2 ≃L[ℝ] Plane2 :=
  (omegaBasisLinearEquiv.trans
    ((complexMulLeftLinearEquiv ((grossenElemScale f₀ : ℂ) * ringComplex f₀)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (grossenElemScale_pos hf₀).ne')
        (fun h => hf₀ (ringComplex_injective (by simpa using h))))).trans
      complexPlaneLinearEquiv)).toContinuousLinearEquiv

theorem eisensteinLatticeEquiv_apply (f₀ : O) (hf₀ : f₀ ≠ 0) (u : Plane2) :
    eisensteinLatticeEquiv f₀ hf₀ u =
      complexPlaneLinearEquiv ((grossenElemScale f₀ : ℂ) * ringComplex f₀ *
        ((u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega)) := by
  change complexPlaneLinearEquiv
      (((grossenElemScale f₀ : ℂ) * ringComplex f₀) *
        ((u 0 : ℂ) + (u 1 : ℂ) * ringComplex omega)) = _
  rw [mul_assoc]

theorem eisensteinLatticeEquiv_integerPoint (f₀ : O) (hf₀ : f₀ ≠ 0) (n : Fin 2 → ℤ) :
    eisensteinLatticeEquiv f₀ hf₀ (euclideanIntegerPoint n) =
      complexPlaneLinearEquiv ((grossenElemScale f₀ : ℂ) *
        ringComplex (f₀ * Coordinates.eval (n 0) (n 1))) := by
  rw [eisensteinLatticeEquiv_apply]
  simp only [euclideanIntegerPoint, integerPoint, Coordinates.eval, map_mul, map_add,
    map_intCast, Complex.ofReal_intCast, mul_assoc]

private def plane2Basis : Module.Basis (Fin 2) ℝ Plane2 :=
  (Pi.basisFun ℝ (Fin 2)).map (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

/-- The inverse covolume `|det B|⁻¹` of `eisensteinLatticeEquiv f₀ hf₀` is `‖ringComplex f₀‖⁻¹`. -/
theorem latticeScale_eisensteinLatticeEquiv (f₀ : O) (hf₀ : f₀ ≠ 0) :
    latticeScale (eisensteinLatticeEquiv f₀ hf₀) = ‖ringComplex f₀‖⁻¹ := by
  have hz : 0 < ‖ringComplex f₀‖ :=
    norm_pos_iff.mpr fun h => hf₀ (ringComplex_injective (by simpa using h))
  have hb0 : plane2Basis 0 = WithLp.toLp 2 ![1, 0] := by
    ext j; fin_cases j <;> simp [plane2Basis, Pi.basisFun_apply]
  have hb1 : plane2Basis 1 = WithLp.toLp 2 ![0, 1] := by
    ext j; fin_cases j <;> simp [plane2Basis, Pi.basisFun_apply]
  have hrepr : ∀ (v : Plane2) (i : Fin 2), plane2Basis.repr v i = v i := fun v i => by
    simp [plane2Basis, Module.Basis.map_repr, Pi.basisFun_repr]
  have he0 : (eisensteinLatticeEquiv f₀ hf₀ : Plane2 →ₗ[ℝ] Plane2) (plane2Basis 0) =
      WithLp.toLp 2 ![grossenElemScale f₀ * (ringComplex f₀).re,
        grossenElemScale f₀ * (ringComplex f₀).im] := by
    change eisensteinLatticeEquiv f₀ hf₀ (plane2Basis 0) = _
    rw [hb0, eisensteinLatticeEquiv_apply]
    ext j; fin_cases j <;> simp [complexPlaneLinearEquiv]
  have he1 : (eisensteinLatticeEquiv f₀ hf₀ : Plane2 →ₗ[ℝ] Plane2) (plane2Basis 1) =
      WithLp.toLp 2 ![grossenElemScale f₀ * (ringComplex f₀).re * (ringComplex omega).re -
          grossenElemScale f₀ * (ringComplex f₀).im * (ringComplex omega).im,
        grossenElemScale f₀ * (ringComplex f₀).re * (ringComplex omega).im +
          grossenElemScale f₀ * (ringComplex f₀).im * (ringComplex omega).re] := by
    change eisensteinLatticeEquiv f₀ hf₀ (plane2Basis 1) = _
    rw [hb1, eisensteinLatticeEquiv_apply]
    ext j; fin_cases j <;> simp [complexPlaneLinearEquiv]
  have hdet : LinearMap.det (eisensteinLatticeEquiv f₀ hf₀ : Plane2 →ₗ[ℝ] Plane2) =
      grossenElemScale f₀ ^ 2 * ‖ringComplex f₀‖ ^ 2 * (ringComplex omega).im := by
    rw [← LinearMap.det_toMatrix plane2Basis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, he0, he1, hrepr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hnorm_sq : (ringComplex f₀).re ^ 2 + (ringComplex f₀).im ^ 2 = ‖ringComplex f₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    linear_combination grossenElemScale f₀ ^ 2 * (ringComplex omega).im * hnorm_sq
  unfold latticeScale
  rw [hdet, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _),
    abs_ringComplex_omega_im, grossenElemScale_sq hf₀]
  congr 1
  have hs3 : (Real.sqrt 3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hs3, hz.ne']

/-- Bijection `(Fin 2 → ℤ) ≃ O` matching integer dual frequencies to `O` under `Tr(x y / (1+2ω))`. -/
def dualElemEquiv : (Fin 2 → ℤ) ≃ O where
  toFun m := Coordinates.eval (m 0 + m 1) (m 0)
  invFun a := ![(Coordinates.coords a).2, (Coordinates.coords a).1 - (Coordinates.coords a).2]
  left_inv m := by
    ext i
    have hc := Coordinates.coords_eval (m 0 + m 1) (m 0)
    have h1 : (Coordinates.coords (Coordinates.eval (m 0 + m 1) (m 0))).1 = m 0 + m 1 :=
      congrArg Prod.fst hc
    have h2 : (Coordinates.coords (Coordinates.eval (m 0 + m 1) (m 0))).2 = m 0 :=
      congrArg Prod.snd hc
    fin_cases i <;> simp [h1, h2]
  right_inv a := by
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa only [add_sub_cancel] using Coordinates.eval_coords a

theorem trace_eval_mul_dualElemEquiv (a b : ℤ) (m : Fin 2 → ℤ) :
    Algebra.trace ℚ K (algebraMap O K (Coordinates.eval a b * dualElemEquiv m) /
      algebraMap O K traceLambda) = (a * m 0 + b * m 1 : ℤ) := by
  have hprod : Coordinates.eval a b * dualElemEquiv m =
      Coordinates.eval (a * (m 0 + m 1) - b * m 0) (a * m 0 + b * m 1) := by
    simp only [dualElemEquiv, Equiv.coe_fn_mk, Coordinates.eval]
    have hsq := omega_sq_eq
    push_cast
    linear_combination (b : O) * (m 0 : O) * hsq
  have hK : algebraMap O K (Coordinates.eval (a * (m 0 + m 1) - b * m 0) (a * m 0 + b * m 1)) =
      (((a * (m 0 + m 1) - b * m 0 : ℤ) : ℚ) : K) +
        (((a * m 0 + b * m 1 : ℤ) : ℚ) : K) * algebraMap O K omega := by
    simp [Coordinates.eval]
  rw [hprod, hK, Coordinates.trace_div_traceLambda]

/-- Explicit formula for the dual lattice point `inverseAdjoint B (euclideanIntegerPoint m)`. -/
def eisensteinDualPoint (f₀ : O) (m : Fin 2 → ℤ) : Plane2 :=
  complexPlaneLinearEquiv (((2 / grossenElemScale f₀ : ℝ) : ℂ) *
    conj (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * f₀)))

theorem inverseAdjoint_eisensteinLatticeEquiv (f₀ : O) (hf₀ : f₀ ≠ 0) (m : Fin 2 → ℤ) :
    inverseAdjoint (eisensteinLatticeEquiv f₀ hf₀) (euclideanIntegerPoint m) =
      eisensteinDualPoint f₀ m := by
  have hs0 : grossenElemScale f₀ ≠ 0 := (grossenElemScale_pos hf₀).ne'
  have htf : traceLambda * f₀ ≠ 0 := mul_ne_zero traceLambda_ne_zero hf₀
  have hfK : algebraMap O K f₀ ≠ 0 := fun h => hf₀ (NumberField.RingOfIntegers.coe_injective h)
  have htK : algebraMap O K traceLambda ≠ 0 :=
    fun h => traceLambda_ne_zero (NumberField.RingOfIntegers.coe_injective h)
  have hbasis_inner : ∀ a b : ℤ,
      inner ℝ (complexPlaneLinearEquiv ((grossenElemScale f₀ : ℂ) *
        ringComplex (f₀ * Coordinates.eval a b))) (eisensteinDualPoint f₀ m) =
        (a * m 0 + b * m 1 : ℝ) := by
    intro a b
    rw [eisensteinDualPoint, inner_complexPlaneLinearEquiv]
    have hconj : conj (((2 / grossenElemScale f₀ : ℝ) : ℂ) *
        conj (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * f₀))) =
        ((2 / grossenElemScale f₀ : ℝ) : ℂ) *
          (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * f₀)) := by
      rw [map_mul, Complex.conj_ofReal, conj_conj]
    rw [hconj]
    have hcancel : (grossenElemScale f₀ : ℂ) * ringComplex (f₀ * Coordinates.eval a b) *
        (((2 / grossenElemScale f₀ : ℝ) : ℂ) *
          (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * f₀))) =
        (2 : ℂ) * (ringComplex (f₀ * Coordinates.eval a b * dualElemEquiv m) /
          ringComplex (traceLambda * f₀)) := by
      simp only [map_mul]
      push_cast
      field_simp [hs0]
    rw [hcancel]
    have hre2 : ((2 : ℂ) * (ringComplex (f₀ * Coordinates.eval a b * dualElemEquiv m) /
        ringComplex (traceLambda * f₀))).re =
        2 * (ringComplex (f₀ * Coordinates.eval a b * dualElemEquiv m) /
          ringComplex (traceLambda * f₀)).re := by simp
    rw [hre2, two_mul_re_ringComplex_div_eq_trace _ _ htf]
    have hK_cancel : algebraMap O K (f₀ * Coordinates.eval a b * dualElemEquiv m) /
        algebraMap O K (traceLambda * f₀) =
        algebraMap O K (Coordinates.eval a b * dualElemEquiv m) / algebraMap O K traceLambda := by
      simp only [map_mul]
      field_simp [hfK, htK]
    rw [hK_cancel, trace_eval_mul_dualElemEquiv]
    push_cast
    ring
  apply ext_inner_left ℝ
  intro y
  obtain ⟨u, rfl⟩ := (eisensteinLatticeEquiv f₀ hf₀).surjective y
  have h1 : inner ℝ (eisensteinLatticeEquiv f₀ hf₀ u)
      (inverseAdjoint (eisensteinLatticeEquiv f₀ hf₀) (euclideanIntegerPoint m)) =
      u 0 * (m 0 : ℝ) + u 1 * (m 1 : ℝ) := by
    rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ ((eisensteinLatticeEquiv f₀ hf₀).symm (eisensteinLatticeEquiv f₀ hf₀ u))
      (euclideanIntegerPoint m) = _
    rw [(eisensteinLatticeEquiv f₀ hf₀).symm_apply_apply, PiLp.inner_apply, Fin.sum_univ_two]
    simp [euclideanIntegerPoint, integerPoint, mul_comm]
  rw [h1]
  have hu_decomp : u = u 0 • euclideanIntegerPoint ![1, 0] +
      u 1 • euclideanIntegerPoint ![0, 1] := by
    ext i
    fin_cases i <;> simp [euclideanIntegerPoint, integerPoint]
  have hb0 := eisensteinLatticeEquiv_integerPoint f₀ hf₀ ![1, 0]
  have hb1 := eisensteinLatticeEquiv_integerPoint f₀ hf₀ ![0, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb0 hb1
  conv_rhs => rw [hu_decomp]
  rw [map_add, map_smul, map_smul, inner_add_left, inner_smul_left, inner_smul_left,
    hb0, hb1, hbasis_inner 1 0, hbasis_inner 0 1]
  simp

/-! ### Primitive finite conductor characters and the harmonic theta functional equation -/

/-- `K = ℚ(ω)` is totally imaginary: it has no real infinite places. -/
theorem isEmpty_isReal_infinitePlace :
    IsEmpty {w : InfinitePlace K // w.IsReal} := by
  refine ⟨fun w => ?_⟩
  let φ : K →+* ℝ := InfinitePlace.embedding_of_isReal w.2
  have hrel : (algebraMap O K omega) ^ 2 + algebraMap O K omega + 1 = 0 := by
    have h := congrArg (algebraMap O K) omega_sq_eq
    simp only [map_pow, map_sub, map_neg, map_one] at h
    linear_combination h
  have hreal := congrArg φ hrel
  simp only [map_add, map_pow, map_one, map_zero] at hreal
  nlinarith [sq_nonneg (φ (algebraMap O K omega) + 1 / 2)]

/-- Over `K = ℚ(ω)`, `integralHeckeWeight` agrees on all nonzero `a : O` with `heckeValue` on `(a)`. -/
theorem integralHeckeWeight_eq_heckeValue (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {a : O} (ha : a ≠ 0) :
    integralHeckeWeight 𝔪 ψ a = heckeValue 𝔪 ψ (Ideal.span {a}) := by
  have haK : algebraMap O K a ≠ 0 := fun h => ha (NumberField.RingOfIntegers.coe_injective h)
  have h := integralHeckeWeight_mul_parities_eq_heckeValue 𝔪 ψ a haK
  have hemp : IsEmpty 𝔪.inf := ⟨fun w => isEmpty_isReal_infinitePlace.false w.1⟩
  rw [Fintype.prod_empty, mul_one] at h
  exact h

/-- Every global unit `u : Oˣ` lies in the kernel of `heckePrimitiveFiniteCharacter 𝔪 ψ`. -/
theorem heckePrimitiveFiniteCharacter_globalUnit (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (u : Oˣ) :
    heckePrimitiveFiniteCharacter 𝔪 ψ
      (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (u : O)) = 1 := by
  let u_mod : (O ⧸ 𝔪.fin)ˣ := Units.map (Ideal.Quotient.mk 𝔪.fin).toMonoidHom u
  have hred : heckeConductorReduction 𝔪 ψ (u_mod : O ⧸ 𝔪.fin) =
      Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (u : O) := rfl
  rw [← hred, heckePrimitiveFiniteCharacter_unit 𝔪 ψ u_mod]
  change integralHeckeWeight 𝔪 ψ (u : O) = 1
  rw [integralHeckeWeight_eq_heckeValue 𝔪 ψ u.ne_zero,
    Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top, heckeValue_one]

/-- Every `MulChar` on a finite commutative ring has values of norm at most `1`. -/
theorem norm_mulChar_finite_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (x : R) : ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hpow : χ (u : R) ^ Fintype.card Rˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_pos.ne').le
  · rw [χ.map_nonunit hx, norm_zero]
    exact zero_le_one

/-- On a finite commutative ring, `χ⁻¹ x = conj (χ x)` holds for both units and nonunits. -/
theorem mulChar_finite_inv_eq_conj {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (x : R) : χ⁻¹ x = conj (χ x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hpow : χ (u : R) ^ Fintype.card Rˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have hnorm : ‖χ (u : R)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_pos.ne'
    have hprod1 : χ (u : R) * χ⁻¹ (u : R) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    have hprod2 : χ (u : R) * conj (χ (u : R)) = 1 := by
      rw [Complex.mul_conj', hnorm]
      norm_num
    have hne : χ (u : R) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hnorm; norm_num at hnorm
    exact mul_left_cancel₀ hne (hprod1.trans hprod2.symm)
  · rw [(χ⁻¹).map_nonunit hx, χ.map_nonunit hx, map_zero]

/-- Chosen generator of the primitive finite conductor `heckeFiniteConductor 𝔪 ψ`. -/
def conductorGen (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) : O :=
  Submodule.IsPrincipal.generator (heckeFiniteConductor 𝔪 ψ)

theorem span_conductorGen (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    Ideal.span {conductorGen 𝔪 ψ} = heckeFiniteConductor 𝔪 ψ :=
  Ideal.span_singleton_generator (heckeFiniteConductor 𝔪 ψ)

theorem conductorGen_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    conductorGen 𝔪 ψ ≠ 0 := by
  intro h
  apply heckeFiniteConductor_ne_bot 𝔪 ψ
  rw [← span_conductorGen 𝔪 ψ, h, Ideal.span_singleton_eq_bot]

theorem norm_ringComplex_conductorGen_sq (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    ‖ringComplex (conductorGen 𝔪 ψ)‖ ^ 2 =
      (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) := by
  set a := (Coordinates.coords (conductorGen 𝔪 ψ)).1
  set b := (Coordinates.coords (conductorGen 𝔪 ψ)).2
  have hab : conductorGen 𝔪 ψ = Coordinates.eval a b :=
    (Coordinates.eval_coords (conductorGen 𝔪 ψ)).symm
  rw [hab, Coordinates.complex_norm_eval_sq, ← span_conductorGen 𝔪 ψ, hab,
    Ideal.absNorm_span_singleton, Coordinates.norm_eval]
  have hpos := Coordinates.coordinate_norm_pos a b (hab ▸ conductorGen_ne_zero 𝔪 ψ)
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
  push_cast
  ring

local instance (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    Finite (O ⧸ heckeFiniteConductor 𝔪 ψ) :=
  (heckeFiniteConductor 𝔪 ψ).finiteQuotientOfFreeOfNeBot (heckeFiniteConductor_ne_bot 𝔪 ψ)

local instance (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    Fintype (O ⧸ heckeFiniteConductor 𝔪 ψ) :=
  Fintype.ofFinite (O ⧸ heckeFiniteConductor 𝔪 ψ)

/-- The primitive additive trace character on `O ⧸ heckeFiniteConductor 𝔪 ψ`. -/
def conductorTraceChar (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    AddChar (O ⧸ heckeFiniteConductor 𝔪 ψ) ℂ :=
  (principalTraceChar (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ)).compAddMonoidHom
    (Ideal.quotEquivOfEq (span_conductorGen 𝔪 ψ).symm).toAddMonoidHom

theorem conductorTraceChar_isPrimitive (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    (conductorTraceChar 𝔪 ψ).IsPrimitive :=
  ProductGauss.primitive_comp_ringEquiv _ _
    (principalTraceChar_primitive (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ))

theorem conductorTraceChar_apply (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (x : O) :
    conductorTraceChar 𝔪 ψ (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) x) =
      cexp ((Algebra.trace ℚ K ((algebraMap O K x) /
        (algebraMap O K traceLambda * algebraMap O K (conductorGen 𝔪 ψ))) : ℂ) *
          (2 * Real.pi * Complex.I)) := by
  simp only [conductorTraceChar, AddChar.compAddMonoidHom_apply,
    RingEquiv.toAddMonoidHom, RingHom.toAddMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe, Ideal.quotEquivOfEq_mk]
  exact principalTraceChar_apply _ _ x

/-- Canonical archimedean scale `α_𝔣 = 2π / (√3 · √N(𝔣))` of `heckeFiniteConductor 𝔪 ψ`. -/
def grossenAlpha (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) : ℝ :=
  2 * Real.pi / (Real.sqrt 3 * Real.sqrt (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ)))

theorem grossenAlpha_eq_pi_mul_scale_sq (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    grossenAlpha 𝔪 ψ = Real.pi * grossenElemScale (conductorGen 𝔪 ψ) ^ 2 := by
  have hnorm : Real.sqrt (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ)) =
      ‖ringComplex (conductorGen 𝔪 ψ)‖ := by
    rw [← norm_ringComplex_conductorGen_sq 𝔪 ψ, Real.sqrt_sq (norm_nonneg _)]
  rw [grossenAlpha, hnorm, grossenElemScale_sq (conductorGen_ne_zero 𝔪 ψ)]
  ring

theorem grossenAlpha_pos (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    0 < grossenAlpha 𝔪 ψ := by
  rw [grossenAlpha_eq_pi_mul_scale_sq]
  exact mul_pos Real.pi_pos (sq_pos_of_pos (grossenElemScale_pos (conductorGen_ne_zero 𝔪 ψ)))

/-- Summand of the harmonic Grossencharacter theta series at `a : O`. -/
def grossenThetaTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (t : ℝ) (a : O) : ℂ :=
  heckePrimitiveFiniteCharacter 𝔪 ψ (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) *
    conj (ringComplex a) ^ (6 * k) *
    ((Real.exp (-(grossenAlpha 𝔪 ψ * t) * ‖ringComplex a‖ ^ 2) : ℝ) : ℂ)

/-- Harmonic Grossencharacter theta series `Θ_{ψ, k}(t)` (`k ≥ 1`). -/
def grossenTheta (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (t : ℝ) : ℂ :=
  ∑' a : O, grossenThetaTerm 𝔪 ψ k t a

@[simp]
theorem grossenThetaTerm_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k)
    (t : ℝ) : grossenThetaTerm 𝔪 ψ k t 0 = 0 := by
  have hk0 : 6 * k ≠ 0 := by omega
  simp [grossenThetaTerm, zero_pow hk0]

/-- Coset-and-lattice parametrization `(O ⧸ 𝔣) × (Fin 2 → ℤ) ≃ O`. -/
private def conductorCosetEquiv (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    (O ⧸ heckeFiniteConductor 𝔪 ψ) × (Fin 2 → ℤ) ≃ O :=
  Equiv.ofBijective
    (fun p => Quotient.out p.1 + conductorGen 𝔪 ψ * Coordinates.eval (p.2 0) (p.2 1))
    ⟨by
      rintro ⟨q₁, n₁⟩ ⟨q₂, n₂⟩ h
      have hmk := congrArg (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ)) h
      have hgen0 : Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (conductorGen 𝔪 ψ) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by
          rw [← span_conductorGen 𝔪 ψ]
          exact Ideal.subset_span (mem_singleton _))
      simp only [map_add, map_mul, hgen0, zero_mul, add_zero, Ideal.Quotient.mk_out] at hmk
      subst hmk
      have heval : Coordinates.eval (n₁ 0) (n₁ 1) = Coordinates.eval (n₂ 0) (n₂ 1) :=
        mul_left_cancel₀ (conductorGen_ne_zero 𝔪 ψ) (add_left_cancel h)
      have hc := congrArg Coordinates.coords heval
      rw [Coordinates.coords_eval, Coordinates.coords_eval] at hc
      ext i
      · rfl
      · fin_cases i
        · exact congrArg Prod.fst hc
        · exact congrArg Prod.snd hc,
     by
      intro a
      let q := Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a
      have hmem : a - Quotient.out q ∈ Ideal.span {conductorGen 𝔪 ψ} := by
        rw [span_conductorGen, ← Ideal.Quotient.eq]
        exact (Ideal.Quotient.mk_out q).symm
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hmem
      obtain ⟨b₀, b₁, rfl⟩ := Coordinates.exists_coordinates z
      refine ⟨(q, ![b₀, b₁]), ?_⟩
      dsimp only [Coordinates.eval]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -hz⟩

/-- Expressing `grossenThetaTerm` on a coset `Quotient.out q + f₀ * eval (n 0) (n 1)` via
`harmonicGaussian`. -/
private theorem grossenThetaTerm_coset_eq (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (t : ℝ) (q : O ⧸ heckeFiniteConductor 𝔪 ψ) (n : Fin 2 → ℤ) :
    (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) *
      grossenThetaTerm 𝔪 ψ k t
        (Quotient.out q + conductorGen 𝔪 ψ * Coordinates.eval (n 0) (n 1)) =
      heckePrimitiveFiniteCharacter 𝔪 ψ q *
        harmonicGaussian (6 * k) t
          (eisensteinLatticeEquiv (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ)
            (euclideanIntegerPoint n) +
            complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
              ringComplex (Quotient.out q))) := by
  have hmk : Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ)
      (Quotient.out q + conductorGen 𝔪 ψ * Coordinates.eval (n 0) (n 1)) = q := by
    have hgen0 : Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (conductorGen 𝔪 ψ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by
        rw [← span_conductorGen 𝔪 ψ]; exact Ideal.subset_span (mem_singleton _))
    simp [hgen0, Ideal.Quotient.mk_out]
  have hvec : eisensteinLatticeEquiv (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ)
        (euclideanIntegerPoint n) +
      complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
        ringComplex (Quotient.out q)) =
      complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
        ringComplex (Quotient.out q + conductorGen 𝔪 ψ * Coordinates.eval (n 0) (n 1))) := by
    rw [eisensteinLatticeEquiv_integerPoint, ← map_add]
    congr 1
    simp only [map_add]
    ring
  rw [hvec, grossenThetaTerm, hmk, harmonicGaussian, conjPlane_complexPlaneLinearEquiv,
    gaussianKernel_eq_ofReal, norm_complexPlaneLinearEquiv, map_mul, Complex.conj_ofReal,
    mul_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (grossenElemScale_pos (conductorGen_ne_zero 𝔪 ψ)).le, mul_pow,
    grossenAlpha_eq_pi_mul_scale_sq]
  have hexp : Real.exp (-(Real.pi * grossenElemScale (conductorGen 𝔪 ψ) ^ 2 * t) *
      ‖ringComplex (Quotient.out q + conductorGen 𝔪 ψ * Coordinates.eval (n 0) (n 1))‖ ^ 2) =
      Real.exp (-(Real.pi * t) * (grossenElemScale (conductorGen 𝔪 ψ) ^ 2 *
        ‖ringComplex (Quotient.out q + conductorGen 𝔪 ψ * Coordinates.eval (n 0) (n 1))‖ ^ 2)) := by
    congr 1; ring
  rw [hexp]
  ring

theorem summable_norm_grossenThetaTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    Summable fun a : O => ‖grossenThetaTerm 𝔪 ψ k t a‖ := by
  have hs0 : 0 < grossenElemScale (conductorGen 𝔪 ψ) ^ (6 * k) :=
    pow_pos (grossenElemScale_pos (conductorGen_ne_zero 𝔪 ψ)) (6 * k)
  rw [← (conductorCosetEquiv 𝔪 ψ).summable_iff]
  have hprod : Summable fun p : (O ⧸ heckeFiniteConductor 𝔪 ψ) × (Fin 2 → ℤ) =>
      grossenElemScale (conductorGen 𝔪 ψ) ^ (6 * k) *
        ‖grossenThetaTerm 𝔪 ψ k t (conductorCosetEquiv 𝔪 ψ p)‖ := by
    refine (summable_prod_of_nonneg fun _ => by positivity).mpr ⟨fun q => ?_, ?_⟩
    · refine ((summable_norm_harmonicGaussian_affine
        (eisensteinLatticeEquiv (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ)) (6 * k) ht
        (complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
          ringComplex (Quotient.out q)))).mul_left
        ‖heckePrimitiveFiniteCharacter 𝔪 ψ q‖).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
      have heq := congrArg norm (grossenThetaTerm_coset_eq 𝔪 ψ k t q n)
      simp only [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (grossenElemScale_pos (conductorGen_ne_zero 𝔪 ψ)).le] at heq
      exact heq.le
    · exact (hasSum_fintype _).summable
  refine (hprod.mul_left (grossenElemScale (conductorGen 𝔪 ψ) ^ (6 * k))⁻¹).congr fun p => ?_
  simp only [Function.comp_apply, inv_mul_cancel_left₀ hs0.ne']

/-- Unit-modulus root number `ε(ψ, k)` of the harmonic Grossencharacter theta series. -/
def grossenRootNumber (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) : ℂ :=
  (latticeScale (eisensteinLatticeEquiv (conductorGen 𝔪 ψ) (conductorGen_ne_zero 𝔪 ψ)) : ℂ) *
    gaussSum (heckePrimitiveFiniteCharacter 𝔪 ψ) (conductorTraceChar 𝔪 ψ) *
    (-Complex.I) ^ (6 * k) *
    (((2 : ℂ) / ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ 2 *
      ringComplex (traceLambda * conductorGen 𝔪 ψ))) ^ (6 * k))

theorem norm_grossenRootNumber (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) :
    ‖grossenRootNumber 𝔪 ψ k‖ = 1 := by
  have hf₀ := conductorGen_ne_zero 𝔪 ψ
  have hz : 0 < ‖ringComplex (conductorGen 𝔪 ψ)‖ :=
    norm_pos_iff.mpr fun h => hf₀ (ringComplex_injective (by simpa using h))
  have hgauss_sq : ‖gaussSum (heckePrimitiveFiniteCharacter 𝔪 ψ) (conductorTraceChar 𝔪 ψ)‖ ^ 2 =
      ‖ringComplex (conductorGen 𝔪 ψ)‖ ^ 2 := by
    rw [FiniteRing.norm_gaussSum_sq (heckePrimitiveFiniteCharacter_isPrimitive 𝔪 ψ)
      (conductorTraceChar_isPrimitive 𝔪 ψ), norm_ringComplex_conductorGen_sq]
    simp [Nat.card_eq_fintype_card, Submodule.cardQuot_apply, Ideal.absNorm_apply]
  have hgauss : ‖gaussSum (heckePrimitiveFiniteCharacter 𝔪 ψ) (conductorTraceChar 𝔪 ψ)‖ =
      ‖ringComplex (conductorGen 𝔪 ψ)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hgauss_sq
  have hunit_base : ‖(2 : ℂ) / ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ 2 *
      ringComplex (traceLambda * conductorGen 𝔪 ψ))‖ = 1 := by
    rw [norm_div, Complex.norm_ofNat, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (grossenElemScale_pos hf₀).le, grossenElemScale_sq hf₀,
      map_mul, norm_mul, norm_ringComplex_traceLambda]
    have hs3 : (Real.sqrt 3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [hs3, hz.ne']
  unfold grossenRootNumber
  rw [norm_mul, norm_mul, norm_mul, latticeScale_eisensteinLatticeEquiv, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hz.le), hgauss, inv_mul_cancel₀ hz.ne', one_mul,
    norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, norm_pow, hunit_base, one_pow]

theorem grossenRootNumber_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) :
    grossenRootNumber 𝔪 ψ k ≠ 0 := by
  intro h
  have hn := norm_grossenRootNumber 𝔪 ψ k
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- **Exact Poisson inversion formula for `grossenTheta`.** -/
theorem grossenTheta_inv (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    grossenTheta 𝔪 ψ k (1 / t) =
      grossenRootNumber 𝔪 ψ k * (t : ℂ) ^ (6 * k + 1) * conj (grossenTheta 𝔪 ψ k t) := by
  have hf₀ := conductorGen_ne_zero 𝔪 ψ
  have hs_pos := grossenElemScale_pos hf₀
  have hs_pow_ne : ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k)) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs_pos.ne')
  have ht' : 0 < 1 / t := one_div_pos.mpr ht
  have htf : traceLambda * conductorGen 𝔪 ψ ≠ 0 := mul_ne_zero traceLambda_ne_zero hf₀
  set B := eisensteinLatticeEquiv (conductorGen 𝔪 ψ) hf₀
  -- Compute the dual harmonic Gaussian and trace phase at each `m : Fin 2 → ℤ`
  have hdual_gauss : ∀ m : Fin 2 → ℤ,
      harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m)) =
        (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) *
          (((2 : ℂ) / ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ 2 *
            ringComplex (traceLambda * conductorGen 𝔪 ψ))) ^ (6 * k)) *
          (ringComplex (dualElemEquiv m) ^ (6 * k) *
            ((Real.exp (-(grossenAlpha 𝔪 ψ * t) * ‖ringComplex (dualElemEquiv m)‖ ^ 2) : ℝ) : ℂ)) := by
    intro m
    rw [inverseAdjoint_eisensteinLatticeEquiv _ hf₀ m, eisensteinDualPoint, harmonicGaussian,
      conjPlane_complexPlaneLinearEquiv, gaussianKernel_eq_ofReal, norm_complexPlaneLinearEquiv,
      map_mul, Complex.conj_ofReal, conj_conj]
    have hconj_plane : (((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
          (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ))) ^ (6 * k) =
        (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) *
          (((2 : ℂ) / ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ 2 *
            ringComplex (traceLambda * conductorGen 𝔪 ψ))) ^ (6 * k)) *
          ringComplex (dualElemEquiv m) ^ (6 * k) := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      push_cast
      field_simp [hs_pos.ne']
    have hnorm_dual : Real.pi * t *
        ‖((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
          conj (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ))‖ ^ 2 =
        grossenAlpha 𝔪 ψ * t * ‖ringComplex (dualElemEquiv m)‖ ^ 2 := by
      have hs3 : (Real.sqrt 3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hz : ‖ringComplex (conductorGen 𝔪 ψ)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr fun h => hf₀ (ringComplex_injective (by simpa using h))
      have h2s : ‖((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ)‖ =
          2 / grossenElemScale (conductorGen 𝔪 ψ) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [norm_mul, h2s, Complex.norm_conj, norm_div, map_mul, norm_mul,
        norm_ringComplex_traceLambda, grossenAlpha_eq_pi_mul_scale_sq]
      field_simp [hs3, hz, hs_pos.ne']
      rw [Real.sq_sqrt (by norm_num),
        show grossenElemScale (conductorGen 𝔪 ψ) ^ 4 =
          (grossenElemScale (conductorGen 𝔪 ψ) ^ 2) ^ 2 by ring,
        grossenElemScale_sq hf₀]
      field_simp [hs3, hz]
      rw [Real.sq_sqrt (by norm_num)]
    rw [hconj_plane, ← neg_mul, ← neg_mul, neg_inj.symm]
    · simp only [← hnorm_dual, neg_mul]
      ring
  have hphase_eq : ∀ (q : O ⧸ heckeFiniteConductor 𝔪 ψ) (m : Fin 2 → ℤ),
      latticePhase (complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
        ringComplex (Quotient.out q))) (inverseAdjoint B (euclideanIntegerPoint m)) =
        (conductorTraceChar 𝔪 ψ).mulShift
          (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q := by
    intro q m
    rw [inverseAdjoint_eisensteinLatticeEquiv _ hf₀ m, eisensteinDualPoint, latticePhase,
      inner_complexPlaneLinearEquiv]
    have hconj2 : conj (((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
        conj (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ))) =
        ((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
          (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ)) := by
      rw [map_mul, Complex.conj_ofReal, conj_conj]
    have hprod_re : 2 * Real.pi * ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
        ringComplex (Quotient.out q) *
        (((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
          (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ)))).re =
        2 * Real.pi * ((Algebra.trace ℚ K (algebraMap O K (Quotient.out q * dualElemEquiv m) /
          algebraMap O K (traceLambda * conductorGen 𝔪 ψ)) : ℚ) : ℝ) := by
      congr 1
      have hc : (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) * ringComplex (Quotient.out q) *
          (((2 / grossenElemScale (conductorGen 𝔪 ψ) : ℝ) : ℂ) *
            (ringComplex (dualElemEquiv m) / ringComplex (traceLambda * conductorGen 𝔪 ψ))) =
          (2 : ℂ) * (ringComplex (Quotient.out q * dualElemEquiv m) /
            ringComplex (traceLambda * conductorGen 𝔪 ψ)) := by
        simp only [map_mul]
        push_cast
        field_simp [hs_pos.ne']
      rw [hc, show ((2 : ℂ) * (ringComplex (Quotient.out q * dualElemEquiv m) /
          ringComplex (traceLambda * conductorGen 𝔪 ψ))).re =
          2 * (ringComplex (Quotient.out q * dualElemEquiv m) /
            ringComplex (traceLambda * conductorGen 𝔪 ψ)).re by simp,
        two_mul_re_ringComplex_div_eq_trace _ _ htf]
    rw [hconj2, hprod_re, AddChar.mulShift_apply, mul_comm _ q]
    conv_rhs => rw [← Ideal.Quotient.mk_out q, ← RingHom.map_mul, conductorTraceChar_apply]
    congr 1
    simp only [map_mul]
    push_cast
    ring
  -- Sum over `q : O ⧸ 𝔣` and apply Poisson summation on each coset at scale `1 / t`
  apply mul_left_cancel₀ hs_pow_ne
  have hlhs : (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) * grossenTheta 𝔪 ψ k (1 / t) =
      ∑ q : O ⧸ heckeFiniteConductor 𝔪 ψ, heckePrimitiveFiniteCharacter 𝔪 ψ q *
        ∑' n : Fin 2 → ℤ, harmonicGaussian (6 * k) (1 / t)
          (B (euclideanIntegerPoint n) +
            complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
              ringComplex (Quotient.out q))) := by
    rw [grossenTheta, ← tsum_mul_left, ← (conductorCosetEquiv 𝔪 ψ).tsum_eq]
    have hsum_prod : Summable fun p : (O ⧸ heckeFiniteConductor 𝔪 ψ) × (Fin 2 → ℤ) =>
        (grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) *
          grossenThetaTerm 𝔪 ψ k (1 / t) (conductorCosetEquiv 𝔪 ψ p) :=
      (((conductorCosetEquiv 𝔪 ψ).summable_iff.mpr
        (summable_norm_grossenThetaTerm 𝔪 ψ k ht')).of_norm).mul_left _
    rw [hsum_prod.tsum_prod, tsum_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    calc
      _ = ∑' n : Fin 2 → ℤ, heckePrimitiveFiniteCharacter 𝔪 ψ q *
            harmonicGaussian (6 * k) (1 / t) (B (euclideanIntegerPoint n) +
              complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
                ringComplex (Quotient.out q))) :=
          tsum_congr fun n => grossenThetaTerm_coset_eq 𝔪 ψ k (1 / t) q n
      _ = _ := tsum_mul_left
  rw [hlhs]
  have hpoisson : ∀ q : O ⧸ heckeFiniteConductor 𝔪 ψ,
      (∑' n : Fin 2 → ℤ, harmonicGaussian (6 * k) (1 / t)
        (B (euclideanIntegerPoint n) +
          complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
            ringComplex (Quotient.out q)))) =
        (latticeScale B : ℂ) * (t : ℂ) * (-Complex.I * (t : ℂ)) ^ (6 * k) *
          ∑' m : Fin 2 → ℤ,
            (conductorTraceChar 𝔪 ψ).mulShift
              (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q *
              harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m)) := by
    intro q
    have hp := harmonic_gaussian_poisson_with_shift B (6 * k) ht'
      (complexPlaneLinearEquiv ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) *
        ringComplex (Quotient.out q)))
    rw [one_div_one_div] at hp
    rw [hp]
    have ht_inv : (-Complex.I / ((1 / t : ℝ) : ℂ)) = -Complex.I * (t : ℂ) := by
      push_cast; field_simp [ht.ne']
    rw [ht_inv]
    congr 1
    exact tsum_congr fun m => by rw [hphase_eq q m]
  simp_rw [hpoisson]
  have hsum_m : ∀ q : O ⧸ heckeFiniteConductor 𝔪 ψ, Summable fun m : Fin 2 → ℤ =>
      heckePrimitiveFiniteCharacter 𝔪 ψ q *
        ((conductorTraceChar 𝔪 ψ).mulShift
          (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q *
          harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m))) := by
    intro q
    apply Summable.of_norm
    refine ((summable_norm_harmonicGaussian_affine (inverseAdjointEquiv B) (6 * k) ht 0).mul_left
      ‖heckePrimitiveFiniteCharacter 𝔪 ψ q‖).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun m => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hph : ‖(conductorTraceChar 𝔪 ψ).mulShift
        (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q‖ = 1 := by
      rw [← hphase_eq q m, norm_latticePhase]
    rw [hph, one_mul, inverseAdjointEquiv_apply, add_zero]
  have hinterchange :
      (∑ q : O ⧸ heckeFiniteConductor 𝔪 ψ, heckePrimitiveFiniteCharacter 𝔪 ψ q *
        ((latticeScale B : ℂ) * (t : ℂ) * (-Complex.I * (t : ℂ)) ^ (6 * k) *
          ∑' m : Fin 2 → ℤ, (conductorTraceChar 𝔪 ψ).mulShift
            (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q *
            harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m)))) =
      (latticeScale B : ℂ) * (t : ℂ) * (-Complex.I * (t : ℂ)) ^ (6 * k) *
        ∑' m : Fin 2 → ℤ, (∑ q : O ⧸ heckeFiniteConductor 𝔪 ψ,
          heckePrimitiveFiniteCharacter 𝔪 ψ q *
            (conductorTraceChar 𝔪 ψ).mulShift
              (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q) *
          harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m)) := by
    calc
      _ = (latticeScale B : ℂ) * (t : ℂ) * (-Complex.I * (t : ℂ)) ^ (6 * k) *
            ∑ q ∈ Finset.univ, ∑' m : Fin 2 → ℤ,
              heckePrimitiveFiniteCharacter 𝔪 ψ q *
                ((conductorTraceChar 𝔪 ψ).mulShift
                  (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q *
                  harmonicGaussian (6 * k) t (inverseAdjoint B (euclideanIntegerPoint m))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← tsum_mul_left, ← tsum_mul_left]
          conv_rhs => rw [← tsum_mul_left]
          exact tsum_congr fun m => by ring
      _ = _ := by
          rw [← Summable.tsum_finsetSum (fun q _ => hsum_m q)]
          congr 1
          refine tsum_congr fun m => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => (mul_assoc _ _ _).symm
  rw [hinterchange]
  have hconj_theta : conj (grossenTheta 𝔪 ψ k t) =
      ∑' m : Fin 2 → ℤ, conj (heckePrimitiveFiniteCharacter 𝔪 ψ
          (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m))) *
        ringComplex (dualElemEquiv m) ^ (6 * k) *
        ((Real.exp (-(grossenAlpha 𝔪 ψ * t) * ‖ringComplex (dualElemEquiv m)‖ ^ 2) : ℝ) : ℂ) := by
    rw [grossenTheta, Complex.conj_tsum, ← dualElemEquiv.tsum_eq]
    refine tsum_congr fun m => ?_
    rw [grossenThetaTerm, map_mul, map_mul, map_pow, conj_conj, Complex.conj_ofReal]
  rw [hconj_theta]
  calc
    _ = ∑' m : Fin 2 → ℤ,
          ((grossenElemScale (conductorGen 𝔪 ψ) : ℂ) ^ (6 * k) *
            (grossenRootNumber 𝔪 ψ k * (t : ℂ) ^ (6 * k + 1))) *
          (conj (heckePrimitiveFiniteCharacter 𝔪 ψ
              (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m))) *
            ringComplex (dualElemEquiv m) ^ (6 * k) *
            ((Real.exp (-(grossenAlpha 𝔪 ψ * t) *
              ‖ringComplex (dualElemEquiv m)‖ ^ 2) : ℝ) : ℂ)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      have hg : (∑ q : O ⧸ heckeFiniteConductor 𝔪 ψ,
          heckePrimitiveFiniteCharacter 𝔪 ψ q *
            (conductorTraceChar 𝔪 ψ).mulShift
              (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m)) q) =
          conj (heckePrimitiveFiniteCharacter 𝔪 ψ
            (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (dualElemEquiv m))) *
            gaussSum (heckePrimitiveFiniteCharacter 𝔪 ψ) (conductorTraceChar 𝔪 ψ) := by
        change gaussSum (heckePrimitiveFiniteCharacter 𝔪 ψ)
            ((conductorTraceChar 𝔪 ψ).mulShift _) = _
        rw [FiniteRing.gaussSum_mulShift_eq_of_isPrimitive
          (heckePrimitiveFiniteCharacter_isPrimitive 𝔪 ψ), mulChar_finite_inv_eq_conj]
      rw [hg, hdual_gauss m, grossenRootNumber, mul_pow, pow_succ]
      ring
    _ = _ := by
      rw [tsum_mul_left]
      ring

/-! ### Exponential tail bounds, `WeakFEPair`, order-one envelope, and Euler product -/

/-- Grouping `grossenTheta` norms by `Algebra.norm ℤ a = n ≥ 1` gives `O(e^{−α_𝔣 t / 2})` decay on
`t ≥ 1`. -/
theorem exists_grossenTheta_exp_decay (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖grossenTheta 𝔪 ψ k t‖ ≤ C * Real.exp (-(grossenAlpha 𝔪 ψ / 2 * t)) := by
  have hα := grossenAlpha_pos 𝔪 ψ
  have hsum_half := summable_norm_grossenThetaTerm 𝔪 ψ k (half_pos one_pos)
  refine ⟨∑' a : O, ‖grossenThetaTerm 𝔪 ψ k (1 / 2) a‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hle_term : ∀ a : O, ‖grossenThetaTerm 𝔪 ψ k t a‖ ≤
      ‖grossenThetaTerm 𝔪 ψ k (1 / 2) a‖ * Real.exp (-(grossenAlpha 𝔪 ψ / 2 * t)) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp [grossenThetaTerm_zero 𝔪 ψ hk]
    · set c₀ := (Coordinates.coords a).1
      set c₁ := (Coordinates.coords a).2
      have hc : a = Coordinates.eval c₀ c₁ := (Coordinates.eval_coords a).symm
      have hnorm1 : (1 : ℝ) ≤ ‖ringComplex a‖ ^ 2 := by
        rw [hc, Coordinates.complex_norm_eval_sq]
        have hpos := Coordinates.coordinate_norm_pos c₀ c₁ (hc ▸ ha)
        exact_mod_cast hpos
      simp only [grossenThetaTerm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have h1 : grossenAlpha 𝔪 ψ * (t - 1 / 2) * 1 ≤
          grossenAlpha 𝔪 ψ * (t - 1 / 2) * ‖ringComplex a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm1 (by nlinarith)
      have h2 : grossenAlpha 𝔪 ψ / 2 * t ≤ grossenAlpha 𝔪 ψ * (t - 1 / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left ht hα.le]
      nlinarith
  calc ‖grossenTheta 𝔪 ψ k t‖
      ≤ ∑' a : O, ‖grossenThetaTerm 𝔪 ψ k t a‖ :=
        norm_tsum_le_tsum_norm (summable_norm_grossenThetaTerm 𝔪 ψ k ht0)
    _ ≤ ∑' a : O, ‖grossenThetaTerm 𝔪 ψ k (1 / 2) a‖ *
          Real.exp (-(grossenAlpha 𝔪 ψ / 2 * t)) :=
        Summable.tsum_le_tsum hle_term (summable_norm_grossenThetaTerm 𝔪 ψ k ht0)
          (hsum_half.mul_right _)
    _ = (∑' a : O, ‖grossenThetaTerm 𝔪 ψ k (1 / 2) a‖) *
          Real.exp (-(grossenAlpha 𝔪 ψ / 2 * t)) := tsum_mul_right

theorem continuousOn_grossenTheta (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) :
    ContinuousOn (grossenTheta 𝔪 ψ k) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀_pos : 0 < t₀ := ht₀
  have hmaj := summable_norm_grossenThetaTerm 𝔪 ψ k (half_pos ht₀_pos)
  have hcont : ContinuousOn (fun t : ℝ => ∑' a : O, grossenThetaTerm 𝔪 ψ k t a)
      (Ici (t₀ / 2)) := by
    refine continuousOn_tsum (fun a => ?_) hmaj (fun a t ht => ?_)
    · unfold grossenThetaTerm
      fun_prop
    · have ht_ge : t₀ / 2 ≤ t := ht
      have hα := grossenAlpha_pos 𝔪 ψ
      simp only [grossenThetaTerm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht_ge hα.le) (sq_nonneg ‖ringComplex a‖)]
  exact (hcont t₀ (half_le_self ht₀_pos.le)).continuousAt
    (Ici_mem_nhds (half_lt_self ht₀_pos)) |>.continuousWithinAt

theorem grossenTheta_isBigO_rpow (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) (r : ℝ) :
    (fun t => grossenTheta 𝔪 ψ k t - 0) =O[atTop] (fun t : ℝ => t ^ r) := by
  obtain ⟨C, _, hb⟩ := exists_grossenTheta_exp_decay 𝔪 ψ hk
  have hα : 0 < grossenAlpha 𝔪 ψ / 2 := half_pos (grossenAlpha_pos 𝔪 ψ)
  have hdecay : (fun t => grossenTheta 𝔪 ψ k t - 0) =O[atTop]
      (fun t : ℝ => Real.exp (-(grossenAlpha 𝔪 ψ / 2) * t)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [sub_zero, neg_mul, Real.norm_of_nonneg (Real.exp_pos _).le] using hb t ht
  exact hdecay.trans (isLittleO_exp_neg_mul_rpow_atTop hα r).isBigO

/-- Strong functional-equation pair attached to `grossenTheta 𝔪 ψ k` (`k ≥ 1`). -/
def grossenFEPair (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (hk : 1 ≤ k) :
    WeakFEPair ℂ where
  f := grossenTheta 𝔪 ψ k
  g t := conj (grossenTheta 𝔪 ψ k t)
  k := (6 * k + 1 : ℕ)
  ε := grossenRootNumber 𝔪 ψ k
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_grossenTheta 𝔪 ψ k).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_conj.comp_continuousOn
    (continuousOn_grossenTheta 𝔪 ψ k)).locallyIntegrableOn measurableSet_Ioi
  hk := by exact_mod_cast Nat.succ_pos (6 * k)
  hε := grossenRootNumber_ne_zero 𝔪 ψ k
  h_feq := by
    intro x hx
    have hx_pos : 0 < x := hx
    rw [grossenTheta_inv 𝔪 ψ k hx_pos, smul_eq_mul, Real.rpow_natCast, Complex.ofReal_pow]
  hf_top := grossenTheta_isBigO_rpow 𝔪 ψ hk
  hg_top r := by
    have h := grossenTheta_isBigO_rpow 𝔪 ψ hk r
    rw [Asymptotics.isBigO_iff] at h ⊢
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.mono fun t ht => by simpa only [sub_zero, Complex.norm_conj] using ht⟩

theorem isStrong_grossenFEPair (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (hk : 1 ≤ k) :
    IsStrongFEPair (grossenFEPair 𝔪 ψ k hk) :=
  ⟨rfl, rfl⟩

/-- **The completed Grossencharacter `L`-function** `(1 / 6) · Λ_{Θ}(w + 3k)` (`k ≥ 1`, `0` at
`k = 0`). -/
def grossenCompletedL (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ) : ℂ :=
  if hk : 1 ≤ k then (1 / 6 : ℂ) * (grossenFEPair 𝔪 ψ k hk).Λ (w + (3 * k : ℕ)) else 0

theorem grossenCompletedL_eq_mellin (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) (w : ℂ) :
    grossenCompletedL 𝔪 ψ k w =
      (1 / 6 : ℂ) * mellin (grossenTheta 𝔪 ψ k) (w + (3 * k : ℕ)) := by
  rw [grossenCompletedL, dif_pos hk, (isStrong_grossenFEPair 𝔪 ψ k hk).Λ_eq]
  rfl

/-- **`grossenCompletedL` is entire on `ℂ`.** -/
theorem differentiable_grossenCompletedL (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    Differentiable ℂ (grossenCompletedL 𝔪 ψ k) := by
  have heq : grossenCompletedL 𝔪 ψ k =
      fun w => (1 / 6 : ℂ) * (grossenFEPair 𝔪 ψ k hk).Λ (w + (3 * k : ℕ)) := by
    funext w; simp [grossenCompletedL, hk]
  rw [heq]
  exact ((isStrong_grossenFEPair 𝔪 ψ k hk).differentiable_Λ.comp
    (differentiable_id.add (differentiable_const _))).const_mul _

/-- **`grossenCompletedL` has an order-one growth envelope.** -/
theorem orderOneEnvelope_grossenCompletedL (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    OrderOneEnvelope (grossenCompletedL 𝔪 ψ k) := by
  obtain ⟨C, hC, hb⟩ := exists_grossenTheta_exp_decay 𝔪 ψ hk
  have hα : 0 < grossenAlpha 𝔪 ψ / 2 := half_pos (grossenAlpha_pos 𝔪 ψ)
  have hk_half : (1 / 2 : ℝ) ≤ (grossenFEPair 𝔪 ψ k hk).k := by
    change (1 / 2 : ℝ) ≤ ((6 * k + 1 : ℕ) : ℝ)
    have : (1 : ℝ) ≤ (6 * k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos (6 * k)
    linarith
  obtain ⟨C₀, q, hC₀, hq, hdtop, hdhead⟩ := _root_.RHTower.weakFEPair_f_decay
    (grossenFEPair 𝔪 ψ k hk) hC hα hk_half hb (fun t ht => by
      change ‖conj (grossenTheta 𝔪 ψ k t)‖ ≤ _
      rw [Complex.norm_conj]
      exact hb t ht)
  have hmellin : OrderOneEnvelope (mellin (grossenTheta 𝔪 ψ k)) :=
    _root_.RHTower.mellin_orderOneEnvelope_of_decay (grossenTheta 𝔪 ψ k) hq hC₀ hdtop hdhead
  refine ((hmellin.comp_affine 1 (3 * k : ℕ)).const_mul (1 / 6 : ℂ)).congr fun w => ?_
  rw [one_mul, ← grossenCompletedL_eq_mellin 𝔪 ψ hk w]

/-- **Functional equation of `grossenCompletedL`:**
`Λ(1 − w) = ε(ψ, k) · conj(Λ(conj w))` for all `w ∈ ℂ`. -/
theorem grossenCompletedL_one_sub (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) (w : ℂ) :
    grossenCompletedL 𝔪 ψ k (1 - w) =
      grossenRootNumber 𝔪 ψ k * conj (grossenCompletedL 𝔪 ψ k (conj w)) := by
  have harg : (1 - w) + (3 * k : ℕ) =
      ((grossenFEPair 𝔪 ψ k hk).k : ℂ) - (w + (3 * k : ℕ)) := by
    change (1 - w) + (3 * k : ℕ) = ((6 * k + 1 : ℕ) : ℂ) - (w + (3 * k : ℕ))
    push_cast
    ring
  have hfe := (grossenFEPair 𝔪 ψ k hk).functional_equation (w + (3 * k : ℕ))
  rw [← harg, smul_eq_mul, (isStrong_grossenFEPair 𝔪 ψ k hk).symm_Λ_eq] at hfe
  have hsymm : mellin (grossenFEPair 𝔪 ψ k hk).g (w + (3 * k : ℕ)) =
      conj (mellin (grossenTheta 𝔪 ψ k) (conj w + (3 * k : ℕ))) := by
    have hc := HTGeometry.mellin_conj (grossenTheta 𝔪 ψ k) (conj w + (3 * k : ℕ))
    have hcc : conj (conj w + (3 * k : ℕ)) = w + (3 * k : ℕ) := by
      rw [map_add, conj_conj, map_natCast]
    rw [hcc] at hc
    exact hc
  have h16 : conj (1 / 6 : ℂ) = (1 / 6 : ℂ) := by rw [one_div, map_inv₀, map_ofNat]
  rw [grossenCompletedL, dif_pos hk, hfe, hsymm, grossenCompletedL_eq_mellin 𝔪 ψ hk (conj w),
    map_mul, h16]
  change (1 / 6 : ℂ) * (grossenRootNumber 𝔪 ψ k *
      conj (mellin (grossenTheta 𝔪 ψ k) (conj w + (3 * k : ℕ)))) = _
  ring

/-- Archimedean Gamma-scale factor `α_𝔣^{−(w + 3k)} Γ(w + 3k)`. -/
def grossenArchimedeanFactor (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ) : ℂ :=
  ((grossenAlpha 𝔪 ψ : ℂ) ^ (-(w + (3 * k : ℕ)))) * Complex.Gamma (w + (3 * k : ℕ))

theorem grossenArchimedeanFactor_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : -(3 * (k : ℝ)) < w.re) :
    grossenArchimedeanFactor 𝔪 ψ k w ≠ 0 := by
  have hre : 0 < (w + (3 * k : ℕ)).re := by
    rw [add_re, Complex.natCast_re, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hα : (grossenAlpha 𝔪 ψ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (grossenAlpha_pos 𝔪 ψ).ne'
  refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hre)
  rw [Complex.cpow_def_of_ne_zero hα]
  exact Complex.exp_ne_zero _

theorem differentiableOn_grossenArchimedeanFactor (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (k : ℕ) :
    DifferentiableOn ℂ (grossenArchimedeanFactor 𝔪 ψ k) {w : ℂ | -(3 * (k : ℝ)) < w.re} := by
  have hα : (grossenAlpha 𝔪 ψ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (grossenAlpha_pos 𝔪 ψ).ne'
  intro w hw
  have hw' : -(3 * (k : ℝ)) < w.re := hw
  have hre : 0 < (w + (3 * k : ℕ)).re := by
    rw [add_re, Complex.natCast_re, Nat.cast_mul, Nat.cast_ofNat]; linarith
  have hcpow_eq : (fun z : ℂ => (grossenAlpha 𝔪 ψ : ℂ) ^ (-(z + (3 * k : ℕ)))) =
      fun z : ℂ => cexp (Complex.log (grossenAlpha 𝔪 ψ : ℂ) * (-(z + (3 * k : ℕ)))) := by
    funext z; exact Complex.cpow_def_of_ne_zero hα _
  have hd1 : DifferentiableAt ℂ
      (fun z : ℂ => (grossenAlpha 𝔪 ψ : ℂ) ^ (-(z + (3 * k : ℕ)))) w := by
    rw [hcpow_eq]
    exact (((differentiableAt_id.add (differentiableAt_const _)).neg).const_mul _).cexp
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + (3 * k : ℕ))) w := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp w
      (differentiableAt_id.add (differentiableAt_const _))
    have hrm := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hrm
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (hd1.mul hd2).differentiableWithinAt

/-- **The primitive Grossencharacter `L`-function** `L(w, ψ₆^k χ_𝔣)` (`k ≥ 1`). -/
def grossenLFunction (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ) : ℂ :=
  grossenCompletedL 𝔪 ψ k w / grossenArchimedeanFactor 𝔪 ψ k w

/-- **`grossenLFunction` is holomorphic on `Re w > −3k`.** -/
theorem differentiableOn_grossenLFunction (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    DifferentiableOn ℂ (grossenLFunction 𝔪 ψ k) {w : ℂ | -(3 * (k : ℝ)) < w.re} :=
  (differentiable_grossenCompletedL 𝔪 ψ hk).differentiableOn.div
    (differentiableOn_grossenArchimedeanFactor 𝔪 ψ k)
    (fun _ hw => grossenArchimedeanFactor_ne_zero 𝔪 ψ k hw)

theorem grossenCompletedL_eq_archimedean_mul (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : -(3 * (k : ℝ)) < w.re) :
    grossenCompletedL 𝔪 ψ k w =
      grossenArchimedeanFactor 𝔪 ψ k w * grossenLFunction 𝔪 ψ k w := by
  rw [grossenLFunction, mul_div_cancel₀ _ (grossenArchimedeanFactor_ne_zero 𝔪 ψ k hw)]

/-! ### Ideal-level primitive character, Mellin–Dirichlet identity, and Euler product -/

/-- The primitive finite character of `ψ` evaluated on ideals of `O`: `0` on `⊥`, and
`heckePrimitiveFiniteCharacter 𝔪 ψ (mk (generator I))` on `I ≠ ⊥` (well-defined because global
units act trivially). -/
def primitiveIdealValue (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) : Ideal O →*₀ ℂ where
  toFun I := if I = ⊥ then 0 else
    heckePrimitiveFiniteCharacter 𝔪 ψ
      (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) (Submodule.IsPrincipal.generator I))
  map_zero' := if_pos rfl
  map_one' := by
    have h1 : (1 : Ideal O) ≠ ⊥ := one_ne_zero
    rw [if_neg h1]
    have hspan : Ideal.span {Submodule.IsPrincipal.generator (1 : Ideal O)} = Ideal.span {(1 : O)} := by
      rw [Ideal.span_singleton_generator, Ideal.one_eq_top, Ideal.span_singleton_one]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have hgen : Submodule.IsPrincipal.generator (1 : Ideal O) = ((u⁻¹ : Oˣ) : O) := by
      calc Submodule.IsPrincipal.generator (1 : Ideal O)
          = (Submodule.IsPrincipal.generator (1 : Ideal O) * (u : O)) * ((u⁻¹ : Oˣ) : O) := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        _ = 1 * ((u⁻¹ : Oˣ) : O) := by rw [hu]
        _ = ((u⁻¹ : Oˣ) : O) := one_mul _
    rw [hgen]
    exact heckePrimitiveFiniteCharacter_globalUnit 𝔪 ψ u⁻¹
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst hI; simp
    by_cases hJ : J = ⊥
    · subst hJ; simp
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    rw [if_neg hI, if_neg hJ, if_neg hIJ]
    have hspan : Ideal.span {Submodule.IsPrincipal.generator (I * J)} =
        Ideal.span {Submodule.IsPrincipal.generator I * Submodule.IsPrincipal.generator J} := by
      rw [Ideal.span_singleton_generator, ← Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_generator, Ideal.span_singleton_generator]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have hgen : Submodule.IsPrincipal.generator I * Submodule.IsPrincipal.generator J =
        Submodule.IsPrincipal.generator (I * J) * (u : O) := hu.symm
    have hmk := congrArg
      (fun x : O => heckePrimitiveFiniteCharacter 𝔪 ψ
        (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) x)) hgen
    simp only [map_mul, heckePrimitiveFiniteCharacter_globalUnit, mul_one] at hmk
    exact hmk.symm

theorem primitiveIdealValue_span_singleton (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {a : O} (ha : a ≠ 0) :
    primitiveIdealValue 𝔪 ψ (Ideal.span {a}) =
      heckePrimitiveFiniteCharacter 𝔪 ψ
        (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) := by
  have hbot : Ideal.span {a} ≠ (⊥ : Ideal O) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  change (if Ideal.span {a} = ⊥ then 0 else _) = _
  rw [if_neg hbot]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp
    (Ideal.span_singleton_generator (Ideal.span {a}))
  have ha_eq : a = Submodule.IsPrincipal.generator (Ideal.span {a}) * (u : O) := hu.symm
  conv_rhs => rw [ha_eq]
  simp only [map_mul, heckePrimitiveFiniteCharacter_globalUnit, mul_one]

theorem norm_primitiveIdealValue_le_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (I : Ideal O) :
    ‖primitiveIdealValue 𝔪 ψ I‖ ≤ 1 := by
  change ‖if I = ⊥ then 0 else _‖ ≤ 1
  by_cases hI : I = ⊥
  · simp [hI]
  · rw [if_neg hI]
    exact norm_mulChar_finite_le_one (heckePrimitiveFiniteCharacter 𝔪 ψ) _

/-- At every prime `v` not dividing `𝔪.fin`, `primitiveIdealValue 𝔪 ψ v.asIdeal` equals
`heckeValue 𝔪 ψ v.asIdeal`. -/
theorem primitiveIdealValue_eq_heckeValue_of_not_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {v : HeightOneSpectrum O} (hv : ¬ (𝔪.fin ≤ v.asIdeal)) :
    primitiveIdealValue 𝔪 ψ v.asIdeal = heckeValue 𝔪 ψ v.asIdeal := by
  set g := Submodule.IsPrincipal.generator v.asIdeal
  have hspan : Ideal.span {g} = v.asIdeal := Ideal.span_singleton_generator v.asIdeal
  have hg0 : g ≠ 0 := by
    intro h0
    apply v.ne_bot
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hcop : v.asIdeal ⊔ 𝔪.fin = ⊤ := by
    by_contra hnot
    have heq := v.isMaximal.eq_of_le hnot le_sup_left
    exact hv (le_sup_right.trans heq.symm.le)
  have hmem1 : (1 : O) ∈ Ideal.span {g} ⊔ 𝔪.fin := by
    rw [hspan, hcop]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem1
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hmul1 : Ideal.Quotient.mk 𝔪.fin g * Ideal.Quotient.mk 𝔪.fin r = 1 := by
    rw [← map_mul]
    have hy0 : Ideal.Quotient.mk 𝔪.fin y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have h1 := congrArg (Ideal.Quotient.mk 𝔪.fin) hxy
    simpa [hy0] using h1
  let u_mod : (O ⧸ 𝔪.fin)ˣ :=
    ⟨Ideal.Quotient.mk 𝔪.fin g, Ideal.Quotient.mk 𝔪.fin r, hmul1, by rw [mul_comm]; exact hmul1⟩
  have hred : heckeConductorReduction 𝔪 ψ (u_mod : O ⧸ 𝔪.fin) =
      Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) g := rfl
  rw [← hspan, primitiveIdealValue_span_singleton 𝔪 ψ hg0, ← hred,
    heckePrimitiveFiniteCharacter_unit 𝔪 ψ u_mod]
  change integralHeckeWeight 𝔪 ψ g = _
  rw [integralHeckeWeight_eq_heckeValue 𝔪 ψ hg0]

/-- Multiplicative Grossencharacter summand on nonzero ideals `(Ideal O)⁰`. -/
def grossenIdealTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ) :
    (Ideal O)⁰ →* ℂ where
  toFun I := idealPsiSix (I : Ideal O) ^ k * primitiveIdealValue 𝔪 ψ (I : Ideal O) *
    (Ideal.absNorm (I : Ideal O) : ℂ) ^ (-w)
  map_one' := by
    change idealPsiSix 1 ^ k * primitiveIdealValue 𝔪 ψ 1 * (Ideal.absNorm (1 : Ideal O) : ℂ) ^ (-w) = 1
    rw [idealPsiSix_one, one_pow, map_one, map_one, Nat.cast_one, Complex.one_cpow, one_mul, mul_one]
  map_mul' I J := by
    simp only [Submonoid.coe_mul, idealPsiSix_mul, mul_pow, map_mul, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow]
    ring

/-- Prime Euler-factor ratio `ψ₆(v)^k χ_𝔣(v) N(v)^{−w}`. -/
def grossenPrimeTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ)
    (v : HeightOneSpectrum O) : ℂ :=
  idealPsiSix v.asIdeal ^ k * primitiveIdealValue 𝔪 ψ v.asIdeal *
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)

theorem norm_grossenPrimeTerm_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (w : ℂ)
    (v : HeightOneSpectrum O) :
    ‖grossenPrimeTerm 𝔪 ψ k w v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) := by
  have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hv0 : 0 < Ideal.absNorm v.asIdeal := by omega
  have hcoeff : ‖idealPsiSix v.asIdeal ^ k * primitiveIdealValue 𝔪 ψ v.asIdeal‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
      (norm_nonneg _) (norm_primitiveIdealValue_le_one 𝔪 ψ _)
  rw [grossenPrimeTerm, norm_mul, Complex.norm_natCast_cpow_of_pos hv0, neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hcoeff

theorem norm_grossenPrimeTerm_lt_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) (v : HeightOneSpectrum O) :
    ‖grossenPrimeTerm 𝔪 ψ k w v‖ < 1 := by
  have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  exact (norm_grossenPrimeTerm_le 𝔪 ψ k w v).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast lt_of_lt_of_le one_lt_two hv2)
      (by linarith))

theorem summable_norm_grossenPrimeTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) :
    Summable fun v : HeightOneSpectrum O => ‖grossenPrimeTerm 𝔪 ψ k w v‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_)
    (numberField_summable_finitePlace_norm_cpow (K := K) hw)
  have hv0 : 0 < Ideal.absNorm v.asIdeal :=
    lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  rw [Complex.norm_natCast_cpow_of_pos hv0, neg_re]
  exact norm_grossenPrimeTerm_le 𝔪 ψ k w v

theorem grossenIdealTerm_idealOfPrimeExponents (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (w : ℂ) (ν : HeightOneSpectrum O →₀ ℕ) :
    grossenIdealTerm 𝔪 ψ k w (idealOfPrimeExponents ν) =
      HTGeometry.nomeMonomial (grossenPrimeTerm 𝔪 ψ k w) ν := by
  have hprod : idealOfPrimeExponents ν =
      ∏ v ∈ ν.support, (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : (Ideal O)⁰) ^ ν v := by
    apply Subtype.ext
    simp [idealOfPrimeExponents, Finsupp.prod]
  rw [hprod, map_prod, HTGeometry.nomeMonomial, Finsupp.prod]
  exact Finset.prod_congr rfl fun v _ => by rw [map_pow]; rfl

theorem summable_norm_grossenIdealTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) :
    Summable fun I : (Ideal O)⁰ => ‖grossenIdealTerm 𝔪 ψ k w I‖ := by
  have h := (HTGeometry.summable_nomeMonomial_pow_iff 0 (grossenPrimeTerm 𝔪 ψ k w)
    (norm_grossenPrimeTerm_lt_one 𝔪 ψ k hw)).mpr
    (by simpa only [zero_add, pow_one] using summable_norm_grossenPrimeTerm 𝔪 ψ k hw)
  apply (primeExponentsIdealEquiv (K := K)).summable_iff.mp
  refine h.congr fun ν => ?_
  simp only [zero_add, pow_one]
  exact congrArg norm (grossenIdealTerm_idealOfPrimeExponents 𝔪 ψ k w ν).symm

theorem hasProd_grossenEulerProduct (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {w : ℂ} (hw : 1 < w.re) :
    HasProd (fun v : HeightOneSpectrum O => (1 - grossenPrimeTerm 𝔪 ψ k w v)⁻¹)
      (∑' I : (Ideal O)⁰, grossenIdealTerm 𝔪 ψ k w I) := by
  have h := HTGeometry.hasProd_inv_one_sub_nome (grossenPrimeTerm 𝔪 ψ k w)
    (norm_grossenPrimeTerm_lt_one 𝔪 ψ k hw) (summable_norm_grossenPrimeTerm 𝔪 ψ k hw)
  have hsum : (∑' ν, HTGeometry.nomeMonomial (grossenPrimeTerm 𝔪 ψ k w) ν) =
      ∑' I : (Ideal O)⁰, grossenIdealTerm 𝔪 ψ k w I := by
    rw [← (primeExponentsIdealEquiv (K := K)).tsum_eq (grossenIdealTerm 𝔪 ψ k w)]
    exact tsum_congr fun ν => (grossenIdealTerm_idealOfPrimeExponents 𝔪 ψ k w ν).symm
  exact hsum ▸ h

/-- Bijection between nonzero integral ideals times global units and nonzero Eisenstein integers. -/
private def idealUnitEquivNonzeroO : (Ideal O)⁰ × Oˣ ≃ {a : O // a ≠ 0} :=
  Equiv.ofBijective
    (fun p => ⟨Submodule.IsPrincipal.generator p.1.1 * (p.2 : O), by
      have hg0 : Submodule.IsPrincipal.generator p.1.1 ≠ 0 := by
        intro h0
        exact mem_nonZeroDivisors_iff_ne_zero.mp p.1.2
          (by rw [Submodule.zero_eq_bot, ← Ideal.span_singleton_generator p.1.1, h0,
            Ideal.span_singleton_eq_bot])
      exact mul_ne_zero hg0 p.2.ne_zero⟩)
    ⟨by
      rintro ⟨I, u⟩ ⟨J, v⟩ h
      have hval : Submodule.IsPrincipal.generator I.1 * (u : O) =
          Submodule.IsPrincipal.generator J.1 * (v : O) := congrArg Subtype.val h
      have hIJ : I = J := by
        apply Subtype.ext
        calc I.1 = Ideal.span {Submodule.IsPrincipal.generator I.1 * (u : O)} := by
              rw [Ideal.span_singleton_mul_right_unit u.isUnit, Ideal.span_singleton_generator]
          _ = Ideal.span {Submodule.IsPrincipal.generator J.1 * (v : O)} := by rw [hval]
          _ = J.1 := by
              rw [Ideal.span_singleton_mul_right_unit v.isUnit, Ideal.span_singleton_generator]
      subst hIJ
      have hg0 : Submodule.IsPrincipal.generator I.1 ≠ 0 := by
        intro h0
        exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
          (by rw [Submodule.zero_eq_bot, ← Ideal.span_singleton_generator I.1, h0,
            Ideal.span_singleton_eq_bot])
      exact Prod.ext rfl (Units.ext (mul_left_cancel₀ hg0 hval)),
     by
      rintro ⟨a, ha⟩
      have hI : Ideal.span {a} ∈ (Ideal O)⁰ :=
        mem_nonZeroDivisors_of_ne_zero
          (by rw [Submodule.zero_eq_bot]; simpa [Ideal.span_singleton_eq_bot] using ha)
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp
        (Ideal.span_singleton_generator (Ideal.span {a}))
      exact ⟨(⟨Ideal.span {a}, hI⟩, u), Subtype.ext hu⟩⟩

private theorem norm_ringComplex_sq_eq_absNorm_span (a : O) :
    ‖ringComplex a‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  by_cases ha : a = 0
  · subst ha; simp
  · set c₀ := (Coordinates.coords a).1
    set c₁ := (Coordinates.coords a).2
    have hc : Coordinates.eval c₀ c₁ = a := Coordinates.eval_coords a
    rw [← hc, Coordinates.complex_norm_eval_sq, Ideal.absNorm_span_singleton, Coordinates.norm_eval]
    have hpos := Coordinates.coordinate_norm_pos c₀ c₁ (hc.symm ▸ ha)
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
    push_cast
    ring

/-- **Mellin–Dirichlet identity for `grossenTheta` on `Re w > 1`.** -/
theorem mellin_grossenTheta_eq_tsum_ideals (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    mellin (grossenTheta 𝔪 ψ k) (w + (3 * k : ℕ)) =
      (6 : ℂ) * grossenArchimedeanFactor 𝔪 ψ k w *
        ∑' I : (Ideal O)⁰, grossenIdealTerm 𝔪 ψ k w I := by
  set s : ℂ := w + (3 * k : ℕ)
  have hs0 : 0 < s.re := by
    simp only [s, add_re, Complex.natCast_re]
    push_cast
    linarith
  have hα := grossenAlpha_pos 𝔪 ψ
  set coeff : O → ℂ := fun a =>
    heckePrimitiveFiniteCharacter 𝔪 ψ (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) *
      conj (ringComplex a) ^ (6 * k)
  set rate : O → ℝ := fun a => grossenAlpha 𝔪 ψ * ‖ringComplex a‖ ^ 2
  have hp : ∀ a : O, coeff a = 0 ∨ 0 < rate a := by
    intro a
    by_cases ha : a = 0
    · left
      have hk0 : 6 * k ≠ 0 := by omega
      simp [coeff, ha, zero_pow hk0]
    · right
      have hz : 0 < ‖ringComplex a‖ :=
        norm_pos_iff.mpr fun h => ha (ringComplex_injective (by simpa using h))
      exact mul_pos hα (sq_pos_of_pos hz)
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun a : O => coeff a * Real.exp (-rate a * t)) (grossenTheta 𝔪 ψ k t) := by
    intro t ht
    have hs_t := (summable_norm_grossenThetaTerm 𝔪 ψ k ht).of_norm.hasSum
    refine hs_t.congr_fun fun a => ?_
    simp only [grossenThetaTerm, coeff, rate]
    congr 1
    congr 1
    ring
  -- Summability of `‖coeff a‖ / rate a ^ s.re` by grouping over `(Ideal O)⁰ × Oˣ`
  have hdom_ideal : Summable fun I : (Ideal O)⁰ =>
      grossenAlpha 𝔪 ψ ^ (-s.re) * (Ideal.absNorm I.1 : ℝ) ^ (-w.re) := by
    have hzeta := summable_norm_heckeIdealTerm (trivialModulus K) 1 hw
    refine (hzeta.mul_left (grossenAlpha 𝔪 ψ ^ (-s.re))).congr fun I => ?_
    congr 1
    have hne : I.1 ≠ ⊥ := by
      have h0 : I.1 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      rwa [Submodule.zero_eq_bot] at h0
    have hI0 : 0 < Ideal.absNorm I.1 := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hne)
    simp [heckeIdealTerm, heckeValue_trivialModulus_one hne,
      Complex.norm_natCast_cpow_of_pos hI0]
  have hweight_sum : Summable fun a : O => ‖coeff a‖ / rate a ^ s.re := by
    have hsupp : Function.support (fun a : O => ‖coeff a‖ / rate a ^ s.re) ⊆ {a : O | a ≠ 0} := by
      intro a ha h0
      apply ha
      have hk0 : 6 * k ≠ 0 := by omega
      simp [coeff, h0, zero_pow hk0]
    have hsub : Summable fun a : {a : O // a ≠ 0} => ‖coeff a.1‖ / rate a.1 ^ s.re := by
      rw [← idealUnitEquivNonzeroO.summable_iff]
      letI : Fintype Oˣ := Fintype.ofFinite Oˣ
      refine (summable_prod_of_nonneg (fun _ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg
        (mul_nonneg hα.le (sq_nonneg _)) _))).mpr ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
      refine (hdom_ideal.mul_right (Fintype.card Oˣ : ℝ)).of_nonneg_of_le
        (fun _ => tsum_nonneg fun _ => div_nonneg (norm_nonneg _)
          (Real.rpow_nonneg (mul_nonneg hα.le (sq_nonneg _)) _)) fun I => ?_
      rw [tsum_fintype]
      calc ∑ u : Oˣ, ‖coeff (idealUnitEquivNonzeroO (I, u)).1‖ /
              rate (idealUnitEquivNonzeroO (I, u)).1 ^ s.re
          ≤ ∑ _u : Oˣ, grossenAlpha 𝔪 ψ ^ (-s.re) * (Ideal.absNorm I.1 : ℝ) ^ (-w.re) := by
            refine Finset.sum_le_sum fun u _ => ?_
            set a := (idealUnitEquivNonzeroO (I, u)).1
            have ha0 : a ≠ 0 := (idealUnitEquivNonzeroO (I, u)).2
            have hspan_a : Ideal.span {a} = I.1 := by
              change Ideal.span {Submodule.IsPrincipal.generator I.1 * (u : O)} = I.1
              rw [Ideal.span_singleton_mul_right_unit u.isUnit, Ideal.span_singleton_generator]
            have hz : 0 < ‖ringComplex a‖ :=
              norm_pos_iff.mpr fun h => ha0 (ringComplex_injective (by simpa using h))
            have hc_le : ‖coeff a‖ ≤ ‖ringComplex a‖ ^ (6 * k) := by
              simp only [coeff, norm_mul, norm_pow, Complex.norm_conj]
              exact mul_le_of_le_one_left (pow_nonneg hz.le _)
                (norm_mulChar_finite_le_one (heckePrimitiveFiniteCharacter 𝔪 ψ) _)
            have hr_eq : rate a ^ s.re =
                grossenAlpha 𝔪 ψ ^ s.re * (‖ringComplex a‖ ^ 2) ^ w.re *
                  ‖ringComplex a‖ ^ (6 * k) := by
              have hs_re : s.re = w.re + (3 * k : ℕ) := by simp [s]
              dsimp only [rate]
              rw [Real.mul_rpow hα.le (sq_nonneg _), hs_re,
                Real.rpow_add (sq_pos_of_pos hz), Real.rpow_natCast, ← pow_mul,
                show 2 * (3 * k) = 6 * k by ring, ← hs_re, mul_assoc]
            rw [hr_eq, div_le_iff₀ (by positivity)]
            calc ‖coeff a‖ ≤ ‖ringComplex a‖ ^ (6 * k) := hc_le
              _ = (grossenAlpha 𝔪 ψ ^ (-s.re) * grossenAlpha 𝔪 ψ ^ s.re) *
                    ((‖ringComplex a‖ ^ 2) ^ (-w.re) * (‖ringComplex a‖ ^ 2) ^ w.re) *
                    ‖ringComplex a‖ ^ (6 * k) := by
                  rw [← Real.rpow_add hα, ← Real.rpow_add (sq_pos_of_pos hz), neg_add_cancel,
                    neg_add_cancel, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul]
              _ = grossenAlpha 𝔪 ψ ^ (-s.re) * (Ideal.absNorm I.1 : ℝ) ^ (-w.re) *
                    (grossenAlpha 𝔪 ψ ^ s.re * (‖ringComplex a‖ ^ 2) ^ w.re *
                      ‖ringComplex a‖ ^ (6 * k)) := by
                  rw [norm_ringComplex_sq_eq_absNorm_span a, hspan_a]
                  ring
        _ = (grossenAlpha 𝔪 ψ ^ (-s.re) * (Ideal.absNorm I.1 : ℝ) ^ (-w.re)) *
              (Fintype.card Oˣ : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hsub.hasSum).summable
  -- Apply `hasSum_mellin` and group by `(Ideal O)⁰ × Oˣ`
  have hm := hasSum_mellin hp hs0 hF hweight_sum
  rw [← hm.tsum_eq]
  have hsupp_term : Function.support (fun a : O => Complex.Gamma s * coeff a / (rate a : ℂ) ^ s) ⊆
      {a : O | a ≠ 0} := by
    intro a ha h0
    apply ha
    have hk0 : 6 * k ≠ 0 := by omega
    simp [coeff, h0, zero_pow hk0]
  have hsub_eq : (∑' a : O, Complex.Gamma s * coeff a / (rate a : ℂ) ^ s) =
      ∑' a : {a : O // a ≠ 0}, Complex.Gamma s * coeff a.1 / (rate a.1 : ℂ) ^ s := by
    have hs1 := hm.summable
    exact ((hasSum_subtype_iff_of_support_subset hsupp_term).mpr hs1.hasSum).tsum_eq.symm
  rw [hsub_eq, ← idealUnitEquivNonzeroO.tsum_eq]
  have hprod_sum : Summable fun p : (Ideal O)⁰ × Oˣ =>
      Complex.Gamma s * coeff (idealUnitEquivNonzeroO p).1 /
        (rate (idealUnitEquivNonzeroO p).1 : ℂ) ^ s :=
    idealUnitEquivNonzeroO.summable_iff.mpr (hm.summable.subtype _)
  letI : Fintype Oˣ := Fintype.ofFinite Oˣ
  rw [hprod_sum.tsum_prod]
  have hterm_eq : ∀ (I : (Ideal O)⁰) (u : Oˣ),
      Complex.Gamma s * coeff (idealUnitEquivNonzeroO (I, u)).1 /
        (rate (idealUnitEquivNonzeroO (I, u)).1 : ℂ) ^ s =
        grossenArchimedeanFactor 𝔪 ψ k w * grossenIdealTerm 𝔪 ψ k w I := by
    intro I u
    set a := (idealUnitEquivNonzeroO (I, u)).1
    have ha0 : a ≠ 0 := (idealUnitEquivNonzeroO (I, u)).2
    have hspan_a : Ideal.span {a} = I.1 := by
      change Ideal.span {Submodule.IsPrincipal.generator I.1 * (u : O)} = I.1
      rw [Ideal.span_singleton_mul_right_unit u.isUnit, Ideal.span_singleton_generator]
    have hz : 0 < ‖ringComplex a‖ :=
      norm_pos_iff.mpr fun h => ha0 (ringComplex_injective (by simpa using h))
    have hrate_cpow : ((rate a : ℝ) : ℂ) ^ s =
        (grossenAlpha 𝔪 ψ : ℂ) ^ s * (Ideal.absNorm I.1 : ℂ) ^ w *
          ((‖ringComplex a‖ : ℂ) ^ (6 * k)) := by
      have hmul_cpow : ((grossenAlpha 𝔪 ψ * ‖ringComplex a‖ ^ 2 : ℝ) : ℂ) ^ s =
          (grossenAlpha 𝔪 ψ : ℂ) ^ s * ((‖ringComplex a‖ ^ 2 : ℝ) : ℂ) ^ s := by
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hα.le (sq_nonneg _)]
      have hnorm_cpow : ((‖ringComplex a‖ ^ 2 : ℝ) : ℂ) ^ s =
          (Ideal.absNorm I.1 : ℂ) ^ w * ((‖ringComplex a‖ : ℂ) ^ (6 * k)) := by
        have hpos_sq : (0 : ℝ) < ‖ringComplex a‖ ^ 2 := sq_pos_of_pos hz
        have hne_sq : ((‖ringComplex a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos_sq.ne'
        rw [show s = w + (3 * k : ℕ) from rfl, Complex.cpow_add _ _ hne_sq,
          Complex.cpow_natCast]
        congr 1
        · rw [norm_ringComplex_sq_eq_absNorm_span a, hspan_a, Complex.ofReal_natCast]
        · push_cast
          rw [← pow_mul, show 2 * (3 * k) = 6 * k by ring]
      exact hmul_cpow.trans (by rw [hnorm_cpow, mul_assoc])
    have hpsi : conj (ringComplex a) ^ (6 * k) / ((‖ringComplex a‖ : ℂ) ^ (6 * k)) =
        idealPsiSix I.1 ^ k := by
      rw [← div_pow, pow_mul, ← hspan_a, idealPsiSix_span_singleton, elemPsiSix_apply,
        complexUnitConj_apply]
    have hchi : heckePrimitiveFiniteCharacter 𝔪 ψ
        (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) =
        primitiveIdealValue 𝔪 ψ I.1 := by
      rw [← hspan_a, primitiveIdealValue_span_singleton 𝔪 ψ ha0]
    have hα_ne : (grossenAlpha 𝔪 ψ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hI_ne : I.1 ≠ ⊥ := by
      have h0 : I.1 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      rwa [Submodule.zero_eq_bot] at h0
    have hN_ne : (Ideal.absNorm I.1 : ℂ) ≠ 0 := by
      exact_mod_cast mt Ideal.absNorm_eq_zero_iff.mp hI_ne
    have hnorm_ne : ((‖ringComplex a‖ : ℂ) ^ (6 * k)) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hz.ne')
    rw [hrate_cpow]
    calc Complex.Gamma s * (heckePrimitiveFiniteCharacter 𝔪 ψ
            (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) * conj (ringComplex a) ^ (6 * k)) /
            ((grossenAlpha 𝔪 ψ : ℂ) ^ s * (Ideal.absNorm I.1 : ℂ) ^ w *
              (‖ringComplex a‖ : ℂ) ^ (6 * k))
        = ((grossenAlpha 𝔪 ψ : ℂ) ^ s)⁻¹ * Complex.Gamma s *
            ((conj (ringComplex a) ^ (6 * k) / (‖ringComplex a‖ : ℂ) ^ (6 * k)) *
              heckePrimitiveFiniteCharacter 𝔪 ψ
                (Ideal.Quotient.mk (heckeFiniteConductor 𝔪 ψ) a) *
              ((Ideal.absNorm I.1 : ℂ) ^ w)⁻¹) := by
          field_simp [hα_ne, hN_ne, hnorm_ne]
      _ = grossenArchimedeanFactor 𝔪 ψ k w * grossenIdealTerm 𝔪 ψ k w I := by
          rw [hpsi, hchi, grossenArchimedeanFactor, grossenIdealTerm, MonoidHom.coe_mk,
            OneHom.coe_mk, ← Complex.cpow_neg, ← Complex.cpow_neg]
  have hcard : (Fintype.card Oˣ : ℂ) = 6 := by
    have hc := card_units_thirdCyclotomic K
    rw [Nat.card_eq_fintype_card] at hc
    exact_mod_cast hc
  calc (∑' I : (Ideal O)⁰, ∑' u : Oˣ,
          Complex.Gamma s * coeff (idealUnitEquivNonzeroO (I, u)).1 /
            (rate (idealUnitEquivNonzeroO (I, u)).1 : ℂ) ^ s)
      = ∑' I : (Ideal O)⁰, (6 : ℂ) *
          (grossenArchimedeanFactor 𝔪 ψ k w * grossenIdealTerm 𝔪 ψ k w I) := by
        refine tsum_congr fun I => ?_
        rw [tsum_fintype]
        simp_rw [hterm_eq I, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ = _ := by rw [tsum_mul_left, tsum_mul_left, ← mul_assoc]

/-- **Dirichlet series representation of `grossenLFunction` on `Re w > 1`.** -/
theorem grossenLFunction_eq_tsum_ideals (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w = ∑' I : (Ideal O)⁰, grossenIdealTerm 𝔪 ψ k w I := by
  have hw_re : -(3 * (k : ℝ)) < w.re := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have harch := grossenArchimedeanFactor_ne_zero 𝔪 ψ k hw_re
  rw [grossenLFunction, grossenCompletedL_eq_mellin 𝔪 ψ hk w,
    mellin_grossenTheta_eq_tsum_ideals 𝔪 ψ hk hw]
  field_simp [harch]

/-- **Convergent Euler product of `grossenLFunction` on `Re w > 1`.** -/
theorem grossenLFunction_eq_eulerProduct (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w =
      ∏' v : HeightOneSpectrum O, (1 - grossenPrimeTerm 𝔪 ψ k w v)⁻¹ := by
  rw [grossenLFunction_eq_tsum_ideals 𝔪 ψ hk hw, (hasProd_grossenEulerProduct 𝔪 ψ k hw).tprod_eq]

/-! ### Finite Euler-factor bridge between `grossenEulerProductModS` and `grossenLFunction` -/

/-- The finite set of primes either in `S` or dividing `𝔪.fin`. -/
def grossenBadPrimesSet (𝔪 : Modulus K) (S : Finset (HeightOneSpectrum O)) :
    Set (HeightOneSpectrum O) :=
  {v : HeightOneSpectrum O | v ∈ S ∨ 𝔪.fin ≤ v.asIdeal}

theorem finite_grossenBadPrimesSet (𝔪 : Modulus K) (S : Finset (HeightOneSpectrum O)) :
    (grossenBadPrimesSet 𝔪 S).Finite := by
  have hmod_pos : 0 < Ideal.absNorm 𝔪.fin :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp 𝔪.fin_ne_bot)
  have hfin_ideals : {I : Ideal O | Ideal.absNorm I ≤ Ideal.absNorm 𝔪.fin}.Finite := by
    have hsub : {I : Ideal O | Ideal.absNorm I ≤ Ideal.absNorm 𝔪.fin} ⊆
        ⋃ n ∈ Finset.range (Ideal.absNorm 𝔪.fin + 1), {I : Ideal O | Ideal.absNorm I = n} := by
      intro I hI
      exact mem_iUnion₂.mpr ⟨Ideal.absNorm I, Finset.mem_range.mpr (Nat.lt_succ_of_le hI), rfl⟩
    exact (Finset.finite_toSet _).biUnion (fun n _ => Ideal.finite_setOf_absNorm_eq n) |>.subset hsub
  have hfin_div : {v : HeightOneSpectrum O | 𝔪.fin ≤ v.asIdeal}.Finite := by
    refine (hfin_ideals.preimage fun _ _ _ _ h => HeightOneSpectrum.ext h).subset fun v hv => ?_
    exact Nat.le_of_dvd hmod_pos (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr hv))
  exact S.finite_toSet.union hfin_div

/-- Subtype of primes either in `S` or dividing `𝔪.fin` (equipped with `Fintype` without
`DecidableEq (HeightOneSpectrum O)`). -/
abbrev GrossenBadPrime (𝔪 : Modulus K) (S : Finset (HeightOneSpectrum O)) : Type _ :=
  {v : HeightOneSpectrum O // v ∈ grossenBadPrimesSet 𝔪 S}

noncomputable instance fintype_grossenBadPrime (𝔪 : Modulus K)
    (S : Finset (HeightOneSpectrum O)) : Fintype (GrossenBadPrime 𝔪 S) :=
  (finite_grossenBadPrimesSet 𝔪 S).fintype

private theorem tprod_split_subtype {ι : Type*} (P : ι → Prop) [Fintype {i : ι // P i}]
    (f : ι → ℂ) (hgood : Multipliable fun i : {i : ι // ¬ P i} => f i.1) :
    (∏' i : ι, f i) =
      (∏ i : {i : ι // P i}, f i.1) * ∏' i : {i : ι // ¬ P i}, f i.1 := by
  have hbad : Multipliable fun i : {i : ι // P i} => f i.1 := (hasProd_fintype _).multipliable
  rw [← (Equiv.sumCompl P).tprod_eq]
  exact (Multipliable.tprod_sum (f := fun x => f (Equiv.sumCompl P x)) hbad hgood).trans
    (by rw [tprod_fintype]; rfl)

/-- The finite product of primitive local inverse Euler factors `1 − ψ₆(v)^k χ_𝔣(v) N(v)^{−w}` over
`v ∈ S` or `v ∣ 𝔪.fin`. -/
def grossenDeletedFactors (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (w : ℂ) : ℂ :=
  ∏ v : GrossenBadPrime 𝔪 S, (1 - grossenPrimeTerm 𝔪 ψ k w v.1)

/-- `grossenDeletedFactors` is entire on all of `ℂ`. -/
theorem differentiable_grossenDeletedFactors (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) :
    Differentiable ℂ (grossenDeletedFactors 𝔪 ψ k S) := by
  rw [← differentiableOn_univ]
  unfold grossenDeletedFactors
  refine DifferentiableOn.fun_finsetProd fun v _ w _ => ?_
  have hv0 : (Ideal.absNorm v.1.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_two
      (ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot)).ne'
  unfold grossenPrimeTerm
  exact ((differentiableAt_const (1 : ℂ)).sub
    ((differentiableAt_id.neg.const_cpow (Or.inl hv0)).const_mul _)).differentiableWithinAt

/-- `grossenDeletedFactors` is everywhere nonvanishing on `Re w > 0`. -/
theorem grossenDeletedFactors_ne_zero (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) {w : ℂ} (hw : 0 < w.re) :
    grossenDeletedFactors 𝔪 ψ k S w ≠ 0 := by
  unfold grossenDeletedFactors
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
  have hlt : ‖grossenPrimeTerm 𝔪 ψ k w v.1‖ < 1 :=
    (norm_grossenPrimeTerm_le 𝔪 ψ k w v.1).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast lt_of_lt_of_le one_lt_two hv2)
        (by linarith))
  intro h0
  have htri := norm_sub_norm_le (1 : ℂ) (grossenPrimeTerm 𝔪 ψ k w v.1)
  rw [h0, norm_zero, norm_one] at htri
  linarith

/-- Uniform boundedness of `grossenDeletedFactors` on `Re w ≥ 0`. -/
theorem norm_grossenDeletedFactors_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖grossenDeletedFactors 𝔪 ψ k S w‖ ≤ 2 ^ Fintype.card (GrossenBadPrime 𝔪 S) := by
  unfold grossenDeletedFactors
  refine (Finset.norm_prod_le _ _).trans ?_
  calc ∏ v : GrossenBadPrime 𝔪 S, ‖1 - grossenPrimeTerm 𝔪 ψ k w v.1‖
      ≤ ∏ _v : GrossenBadPrime 𝔪 S, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
        have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
        have hle1 : ‖grossenPrimeTerm 𝔪 ψ k w v.1‖ ≤ 1 :=
          (norm_grossenPrimeTerm_le 𝔪 ψ k w v.1).trans
            (Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast (lt_of_lt_of_le one_lt_two hv2).le) (by linarith))
        have h := norm_sub_le (1 : ℂ) (grossenPrimeTerm 𝔪 ψ k w v.1)
        rw [norm_one] at h
        linarith
    _ = 2 ^ Fintype.card (GrossenBadPrime 𝔪 S) := by
        rw [Finset.prod_const, Finset.card_univ]

/-- **Exact factorization of `grossenEulerProductModS` on `Re w > 1`:** for **every** finite prime
set `S`, `grossenEulerProductModS 𝔪 ψ k S w = grossenLFunction 𝔪 ψ k w · grossenDeletedFactors 𝔪 ψ k S w`. -/
theorem grossenEulerProductModS_eq_mul_deletedFactors (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O)) {w : ℂ} (hw : 1 < w.re) :
    grossenEulerProductModS 𝔪 ψ k S w =
      grossenLFunction 𝔪 ψ k w * grossenDeletedFactors 𝔪 ψ k S w := by
  -- Multipliability on good primes `v ∉ grossenBadPrimesSet 𝔪 S`
  have hmul_good : Multipliable fun v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S} =>
      (1 - grossenPrimeTerm 𝔪 ψ k w v.1)⁻¹ := by
    have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S} =>
        ‖grossenPrimeTerm 𝔪 ψ k w v.1‖ :=
      (summable_norm_grossenPrimeTerm 𝔪 ψ k hw).subtype _
    refine multipliable_one_sub_inv hmaj fun v => ?_
    have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
    calc ‖grossenPrimeTerm 𝔪 ψ k w v.1‖
        ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-w.re) := norm_grossenPrimeTerm_le 𝔪 ψ k w v.1
      _ ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (lt_of_lt_of_le one_lt_two hv2).le)
            (by linarith)
      _ = ((Ideal.absNorm v.1.asIdeal : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by
          have hv2r : (2 : ℝ) ≤ Ideal.absNorm v.1.asIdeal := by exact_mod_cast hv2
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hL_split : grossenLFunction 𝔪 ψ k w =
      (∏ v : GrossenBadPrime 𝔪 S, (1 - grossenPrimeTerm 𝔪 ψ k w v.1)⁻¹) *
        ∏' v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S},
          (1 - grossenPrimeTerm 𝔪 ψ k w v.1)⁻¹ := by
    rw [grossenLFunction_eq_eulerProduct 𝔪 ψ hk hw]
    exact tprod_split_subtype (fun v => v ∈ grossenBadPrimesSet 𝔪 S)
      (fun v => (1 - grossenPrimeTerm 𝔪 ψ k w v)⁻¹) hmul_good
  have hcancel : (∏ v : GrossenBadPrime 𝔪 S, (1 - grossenPrimeTerm 𝔪 ψ k w v.1)⁻¹) *
      grossenDeletedFactors 𝔪 ψ k S w = 1 := by
    unfold grossenDeletedFactors
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => inv_mul_cancel₀ ?_
    have hlt := norm_grossenPrimeTerm_lt_one 𝔪 ψ k hw v.1
    intro h0
    have htri := norm_sub_norm_le (1 : ℂ) (grossenPrimeTerm 𝔪 ψ k w v.1)
    rw [h0, norm_zero, norm_one] at htri
    linarith
  have hrhs : grossenLFunction 𝔪 ψ k w * grossenDeletedFactors 𝔪 ψ k S w =
      ∏' v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S},
        (1 - grossenPrimeTerm 𝔪 ψ k w v.1)⁻¹ := by
    rw [hL_split, mul_right_comm, hcancel, one_mul]
  rw [hrhs]
  have hinj : Function.Injective
      (fun v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S} =>
        (⟨v.1, fun hS => v.2 (Or.inl hS)⟩ : {v : HeightOneSpectrum O // v ∉ S})) := by
    rintro ⟨v₁, _⟩ ⟨v₂, _⟩ h
    injection h with h'
    exact Subtype.ext h'
  have hsupp : Function.mulSupport
      (fun u : {v : HeightOneSpectrum O // v ∉ S} =>
        (1 - idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
          (primeNorm u.1 : ℂ) ^ (-w))⁻¹) ⊆
      Set.range (fun v : {v : HeightOneSpectrum O // v ∉ grossenBadPrimesSet 𝔪 S} =>
        (⟨v.1, fun hS => v.2 (Or.inl hS)⟩ : {v : HeightOneSpectrum O // v ∉ S})) := by
    intro u hu
    have hnot_le : ¬ (𝔪.fin ≤ u.1.asIdeal) := by
      intro hle
      apply hu
      have hval0 : heckeValue 𝔪 ψ u.1.asIdeal = 0 := by
        apply heckeValue_of_not_mem
        rintro ⟨_, hm⟩
        have h := hm u.1 (Ideal.dvd_iff_le.mpr hle)
        rw [coe_idealUnit, FractionalIdeal.count_self] at h
        exact one_ne_zero h
      simp [hval0]
    exact ⟨⟨u.1, fun hbad => hbad.elim u.2 hnot_le⟩, rfl⟩
  unfold grossenEulerProductModS
  rw [← hinj.tprod_eq hsupp]
  refine tprod_congr fun v => ?_
  have hnot_le : ¬ (𝔪.fin ≤ v.1.asIdeal) := fun hle => v.2 (Or.inr hle)
  rw [grossenPrimeTerm, primitiveIdealValue_eq_heckeValue_of_not_le 𝔪 ψ hnot_le]
  rfl

end GaloisForLFunctions.FamilyContinuationTheory
