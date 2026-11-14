import Mathlib.Analysis.Complex.HasPrimitives
import GaloisForLFunctions.Bottcher.ModularLambda
import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive
import GaloisForLFunctions.RHTower.ThetaGroupFormCuspBounds
import GaloisForLFunctions.RHTower.HalfWeightThetaExceptionalEigenvalue
import GaloisForLFunctions.RHTower.HalfWeightConstantCoefficient
import GaloisForLFunctions.RHTower.HalfWeightCoefficientL

/-!
# The Weight-`½` Twisted Three-Term Horizon Calibration at `λ = 3/16`

This module constructs the explicit unitary-multiplier calibration on which purely geometric or
transfer-operator horizon arguments for a resonance-free strip fail in weight `½` (double cover):

1. **Unitary Vector Jacobi Theta Representation:** On `ℂ³` (`Fin 3 → ℂ`), the vector of Jacobi
   theta constants `Θ⃗(τ) = (ϑ₃(τ), ϑ₄(τ), ϑ₂(τ))` satisfies
   `Θ⃗(τ + 1) = U_T Θ⃗(τ)` and `Θ⃗(-1/τ) = (-iτ)^{1/2} P_S Θ⃗(τ)` on `{Im τ > 0}`, where `U_T`,
   `U_S = e^{-πi/4} P_S`, and `U_{T'} = P_S U_T⁻¹ P_S` are strictly unitary on `ℓ²(Fin 3)`.
2. **Mordell–Lewis–Zagier Period Vector at `w = 3/2` (`s = 3/4`, `λ = 3/16`):** The integral
   `Ψ_ϑ(z) = i ∫_0^∞ (z + iy)^{-3/2} Θ⃗(iy) dy` is holomorphic on `{Re z > 0}`, strictly
   non-vanishing on `(0, ∞)` (`Re(Ψ_ϑ(a)_0) > 0`), decays as `O(a^{-1/2} + a^{-1})` as `a → +∞`
   (excluding every coboundary `v - a^{-3/2} U_T v`), satisfies anti-unitary chiral `S`-reciprocity
   `conj(Ψ_ϑ(a)) = a^{-3/2} U_S Ψ_ϑ(1/a)`, and obeys the exact unitary-multiplier three-term
   Lewis–Zagier functional equation
   `Ψ_ϑ(a) = U_T Ψ_ϑ(a + 1) + (a + 1)^{-3/2} U_{T'} Ψ_ϑ(a / (a + 1))` for all `a > 0`.
3. **Möbius-Blindness of Weight-`½` Fourier Modes:** Alongside `y^{1/4} θ ∈ L²(Γ₀(4)\ℍ, j_ϑ)` at
   `λ = 3/16 < 1/4`, the constant-term arithmetic factor `fN 0 = phiSq` is non-negative and
   supported strictly on squares, and non-zero Eisenstein Fourier modes factor through `sqfChi`
   (`L(s, χ)/L(2s, χ²)`), carrying no odd-order Gauss-sum Möbius sign.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RingdownOfTheCubicCover

/-! ## Elementary complex-power identities on `{Re z > 0}` -/

private theorem norm_cpow_ofReal (z : ℂ) (hz : z ≠ 0) (r : ℝ) :
    ‖z ^ (r : ℂ)‖ = ‖z‖ ^ r := by
  rw [Complex.norm_cpow_of_ne_zero hz]
  simp [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm]

private theorem mul_ofReal_cpow_pos {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (z * (r : ℂ)) ^ w = z ^ w * (r : ℂ) ^ w := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have harg : z.arg + (r : ℂ).arg ∈ Ioc (-π) π := by
    rw [Complex.arg_ofReal_of_nonneg hr.le, add_zero]
    exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hz hrC), Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hrC, Complex.log_mul hz hrC harg, add_mul, Complex.exp_add]

private theorem ofReal_mul_cpow_pos {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  rw [mul_comm, mul_ofReal_cpow_pos hz hr w, mul_comm]

private theorem mul_cpow_of_arg_sum {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (harg : u.arg + v.arg ∈ Ioc (-π) π) (w : ℂ) :
    (u * v) ^ w = u ^ w * v ^ w := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hu hv), Complex.cpow_def_of_ne_zero hu,
    Complex.cpow_def_of_ne_zero hv, Complex.log_mul hu hv harg, add_mul, Complex.exp_add]

private theorem inv_cpow_of_re_pos {z : ℂ} (hz : 0 < z.re) (w : ℂ) :
    z⁻¹ ^ w = (z ^ w)⁻¹ := by
  have hne : z ≠ 0 := fun h => by simp [h] at hz
  have harg : z.arg ≠ π := by
    have hlt : z.arg < π / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    linarith [Real.pi_pos]
  rw [Complex.inv_cpow_eq_ite z w, if_neg harg]

private theorem arg_mem_Ioo_first_quad {z : ℂ} (hre : 0 < z.re) (him : 0 < z.im) :
    z.arg ∈ Ioo 0 (π / 2) := by
  refine ⟨?_, Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩
  have hne : z ≠ 0 := fun h => by simp [h] at hre
  have hnot_neg : ¬ z.arg < 0 := fun hn => (Complex.arg_neg_iff.mp hn).not_gt him
  have hne0 : z.arg ≠ 0 := by
    intro h0
    have hs := Complex.sin_arg z
    rw [h0, Real.sin_zero] at hs
    exact (div_pos him (norm_pos_iff.mpr hne)).ne hs
  exact lt_of_le_of_ne (not_lt.mp hnot_neg) hne0.symm

private theorem arg_inv_mem_Ioo_fourth_quad {z : ℂ} (hre : 0 < z.re) (him : 0 < z.im) :
    z⁻¹.arg ∈ Ioo (-(π / 2)) 0 := by
  have hnorm : 0 < Complex.normSq z := by
    rw [Complex.normSq_pos]
    intro h; simp [h] at hre
  have hre' : 0 < z⁻¹.re := by rw [Complex.inv_re]; exact div_pos hre hnorm
  have him' : z⁻¹.im < 0 := by
    rw [Complex.inv_im]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr him) hnorm
  refine ⟨?_, ?_⟩
  · exact Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre')
  · exact Complex.arg_neg_iff.mpr him'

/-! ## Unitary Vector Jacobi Theta Representation -/

/-- The eighth root of unity `e^{πi/4}` governing the `T`-transformation of `ϑ₂`. -/
def thetaEighthPhase : ℂ := Complex.exp ((Real.pi : ℂ) * I / 4)

/-- Conjugate eighth root of unity `e^{-πi/4}` governing `U_T⁻¹` and the chiral `S`-phase. -/
def thetaInvEighthPhase : ℂ := Complex.exp (-(Real.pi : ℂ) * I / 4)

theorem norm_thetaEighthPhase : ‖thetaEighthPhase‖ = 1 := by
  unfold thetaEighthPhase
  rw [Complex.norm_exp]
  have hre : ((Real.pi : ℂ) * I / 4).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem norm_thetaInvEighthPhase : ‖thetaInvEighthPhase‖ = 1 := by
  unfold thetaInvEighthPhase
  rw [Complex.norm_exp]
  have hre : (-(Real.pi : ℂ) * I / 4).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem thetaEighthPhase_mul_inv : thetaEighthPhase * thetaInvEighthPhase = 1 := by
  unfold thetaEighthPhase thetaInvEighthPhase
  rw [← Complex.exp_add]
  have h : (Real.pi : ℂ) * I / 4 + -(Real.pi : ℂ) * I / 4 = 0 := by ring
  rw [h, Complex.exp_zero]

/-- Vector of Jacobi theta constants `Θ⃗(τ) = (ϑ₃(τ), ϑ₄(τ), ϑ₂(τ))`. -/
def thetaVec (τ : ℂ) : Fin 3 → ℂ :=
  ![Bottcher.thetaThree τ, Bottcher.thetaFour τ, Bottcher.thetaTwo τ]

/-- Euclidean squared norm `∑_{j=0}^2 ‖v_j‖²` on `ℂ³`. -/
def vecNormSq (v : Fin 3 → ℂ) : ℝ := ∑ j : Fin 3, ‖v j‖ ^ 2

/-- The unitary `T`-generator `U_T(v₀, v₁, v₂) = (v₁, v₀, e^{πi/4} v₂)`. -/
def thetaUT : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 1, v 0, thetaEighthPhase * v 2]
  map_add' u v := by ext j; fin_cases j <;> simp [mul_add]
  map_smul' c v := by ext j; fin_cases j <;> simp [mul_left_comm]

/-- Inverse `U_T⁻¹(v₀, v₁, v₂) = (v₁, v₀, e^{-πi/4} v₂)`. -/
def thetaUTInv : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 1, v 0, thetaInvEighthPhase * v 2]
  map_add' u v := by ext j; fin_cases j <;> simp [mul_add]
  map_smul' c v := by ext j; fin_cases j <;> simp [mul_left_comm]

/-- Permutation `P_S(v₀, v₁, v₂) = (v₀, v₂, v₁)` induced by `S(τ) = -1/τ`. -/
def thetaPS : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0, v 2, v 1]
  map_add' u v := by ext j; fin_cases j <;> simp
  map_smul' c v := by ext j; fin_cases j <;> simp

/-- Chiral unitary `S`-generator `U_S = e^{-πi/4} P_S`. -/
def thetaUS : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  thetaInvEighthPhase • thetaPS

/-- Parabolic cusp generator `U_{T'} = P_S U_T⁻¹ P_S = U_S U_T⁻¹ U_S⁻¹` for `T'(τ) = τ/(1 + τ)`. -/
def thetaUTPrime : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  thetaPS.comp (thetaUTInv.comp thetaPS)

theorem thetaUT_comp_thetaUTInv : thetaUT.comp thetaUTInv = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun j => ?_
  fin_cases j
  · rfl
  · rfl
  · change thetaEighthPhase * (thetaInvEighthPhase * v 2) = v 2
    rw [← mul_assoc, thetaEighthPhase_mul_inv, one_mul]

theorem thetaUTInv_comp_thetaUT : thetaUTInv.comp thetaUT = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun j => ?_
  fin_cases j
  · rfl
  · rfl
  · change thetaInvEighthPhase * (thetaEighthPhase * v 2) = v 2
    rw [← mul_assoc, mul_comm thetaInvEighthPhase thetaEighthPhase, thetaEighthPhase_mul_inv,
      one_mul]

theorem thetaPS_comp_thetaPS : thetaPS.comp thetaPS = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun j => ?_
  fin_cases j <;> rfl

theorem vecNormSq_thetaUT (v : Fin 3 → ℂ) : vecNormSq (thetaUT v) = vecNormSq v := by
  have h0 : thetaUT v 0 = v 1 := rfl
  have h1 : thetaUT v 1 = v 0 := rfl
  have h2 : thetaUT v 2 = thetaEighthPhase * v 2 := rfl
  simp only [vecNormSq, Fin.sum_univ_three, h0, h1, h2, norm_mul, norm_thetaEighthPhase, one_mul]
  ring

theorem vecNormSq_thetaUTInv (v : Fin 3 → ℂ) : vecNormSq (thetaUTInv v) = vecNormSq v := by
  have h0 : thetaUTInv v 0 = v 1 := rfl
  have h1 : thetaUTInv v 1 = v 0 := rfl
  have h2 : thetaUTInv v 2 = thetaInvEighthPhase * v 2 := rfl
  simp only [vecNormSq, Fin.sum_univ_three, h0, h1, h2, norm_mul, norm_thetaInvEighthPhase, one_mul]
  ring

theorem vecNormSq_thetaPS (v : Fin 3 → ℂ) : vecNormSq (thetaPS v) = vecNormSq v := by
  have h0 : thetaPS v 0 = v 0 := rfl
  have h1 : thetaPS v 1 = v 2 := rfl
  have h2 : thetaPS v 2 = v 1 := rfl
  simp only [vecNormSq, Fin.sum_univ_three, h0, h1, h2]
  ring

theorem vecNormSq_thetaUS (v : Fin 3 → ℂ) : vecNormSq (thetaUS v) = vecNormSq v := by
  have h0 : thetaUS v 0 = thetaInvEighthPhase * v 0 := rfl
  have h1 : thetaUS v 1 = thetaInvEighthPhase * v 2 := rfl
  have h2 : thetaUS v 2 = thetaInvEighthPhase * v 1 := rfl
  simp only [vecNormSq, Fin.sum_univ_three, h0, h1, h2, norm_mul, norm_thetaInvEighthPhase, one_mul]
  ring

theorem vecNormSq_thetaUTPrime (v : Fin 3 → ℂ) : vecNormSq (thetaUTPrime v) = vecNormSq v := by
  unfold thetaUTPrime
  simp only [LinearMap.comp_apply, vecNormSq_thetaPS, vecNormSq_thetaUTInv]

/-- Modular `T`-covariance of the vector Jacobi theta function. -/
theorem thetaVec_add_one (τ : ℂ) : thetaVec (τ + 1) = thetaUT (thetaVec τ) := by
  ext j
  fin_cases j
  · simp [thetaVec, thetaUT, Bottcher.thetaThree_add_one]
  · simp [thetaVec, thetaUT, Bottcher.thetaFour_add_one]
  · simp [thetaVec, thetaUT, thetaEighthPhase, Bottcher.thetaTwo_add_one]

/-- Modular `S`-covariance of the vector Jacobi theta function on the upper half-plane. -/
theorem thetaVec_neg_inv {τ : ℂ} (hτ : 0 < τ.im) :
    thetaVec (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) • thetaPS (thetaVec τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hre : 0 < (-I * τ).re := by simp [Complex.mul_re, hτ]
  have hinv_eq : I / τ = (-I * τ)⁻¹ := by
    rw [inv_eq_one_div, div_eq_div_iff hτ0 (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0)]
    linear_combination -τ * Complex.I_sq
  have hcpow : 1 / (I / τ) ^ (1 / 2 : ℂ) = (-I * τ) ^ (1 / 2 : ℂ) := by
    rw [hinv_eq, inv_cpow_of_re_pos hre, one_div, inv_inv]
  ext j
  fin_cases j
  · change Bottcher.thetaThree (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * Bottcher.thetaThree τ
    exact Bottcher.thetaThree_S τ hτ0
  · change Bottcher.thetaFour (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * Bottcher.thetaTwo τ
    rw [Bottcher.thetaFour_S τ hτ0, hcpow]
  · change Bottcher.thetaTwo (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * Bottcher.thetaFour τ
    rw [Bottcher.thetaTwo_S τ hτ0, hcpow]

/-- Parabolic `T'`-covariance `Θ⃗(iy / (1 + iy)) = (1 + iy)^{1/2} U_{T'} Θ⃗(iy)` for `y > 0`. -/
theorem thetaVec_TPrime_axis {y : ℝ} (hy : 0 < y) :
    thetaVec ((I * (y : ℂ)) / (1 + I * (y : ℂ))) =
      (1 + I * (y : ℂ)) ^ (1 / 2 : ℂ) • thetaUTPrime (thetaVec (I * (y : ℂ))) := by
  set τ : ℂ := I * (y : ℂ)
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hτ0 : τ ≠ 0 := mul_ne_zero I_ne_zero hyC
  have hτim : 0 < τ.im := by simp [τ, hy]
  set u : ℂ := -1 / τ - 1
  have hu_eq : u = I / (y : ℂ) - 1 := by
    change -1 / (I * (y : ℂ)) - 1 = I / (y : ℂ) - 1
    have hdiv : -1 / (I * (y : ℂ)) = I / (y : ℂ) := by
      rw [div_eq_div_iff (mul_ne_zero I_ne_zero hyC) hyC]
      rw [show I * (I * (y : ℂ)) = I ^ 2 * (y : ℂ) by ring, Complex.I_sq]
    rw [hdiv]
  have huim : 0 < u.im := by
    rw [hu_eq]
    have : (I / (y : ℂ) - 1).im = 1 / y := by
      rw [show I / (y : ℂ) = ((1 / y : ℝ) : ℂ) * I by push_cast; ring]
      simp
    rw [this]; positivity
  have hu1 : u + 1 = -1 / τ := by simp [u]
  have hT : thetaVec u = thetaUTInv (thetaVec (-1 / τ)) := by
    have h1 := congrArg thetaUTInv (thetaVec_add_one u)
    rw [hu1] at h1
    have h2 : thetaUTInv (thetaUT (thetaVec u)) = thetaVec u := by
      simpa using LinearMap.congr_fun thetaUTInv_comp_thetaUT (thetaVec u)
    rw [h2] at h1
    exact h1.symm
  have hneg_u : -1 / u = τ / (1 + τ) := by
    have h1τ : 1 + τ ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [τ, hy.ne'] at him
    have hden : u ≠ 0 := fun h => by rw [h] at huim; simp at huim
    rw [div_eq_div_iff hden h1τ]
    simp only [u]
    field_simp [hτ0]
    ring
  have hSu := thetaVec_neg_inv huim
  rw [hneg_u, hT, thetaVec_neg_inv hτim, LinearMap.map_smul, LinearMap.map_smul, smul_smul] at hSu
  have hprod : (-I * u) ^ (1 / 2 : ℂ) * (-I * τ) ^ (1 / 2 : ℂ) =
      (1 + I * (y : ℂ)) ^ (1 / 2 : ℂ) := by
    have h1 : -I * τ = (y : ℂ) := by
      change -I * (I * (y : ℂ)) = (y : ℂ)
      linear_combination -(y : ℂ) * Complex.I_sq
    have h2 : -I * u = (1 + I * (y : ℂ)) * ((1 / y : ℝ) : ℂ) := by
      rw [hu_eq]; push_cast
      have hy1 : (y : ℂ) * (1 / (y : ℂ)) = 1 := mul_one_div_cancel hyC
      calc -I * (I / (y : ℂ) - 1)
          = -(I ^ 2) * (1 / (y : ℂ)) + I * ((y : ℂ) * (1 / (y : ℂ))) := by
            rw [hy1]; ring
        _ = (1 + I * (y : ℂ)) * (1 / (y : ℂ)) := by rw [Complex.I_sq]; ring
    have hne1 : 1 + I * (y : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    rw [h1, h2, mul_ofReal_cpow_pos hne1 (one_div_pos.mpr hy), mul_assoc]
    have hcancel : ((1 / y : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ) = 1 := by
      rw [← mul_ofReal_cpow_pos
        (Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hy).ne') hy]
      have : ((1 / y : ℝ) : ℂ) * (y : ℂ) = 1 := by push_cast; field_simp [hy.ne']
      rw [this, Complex.one_cpow]
    rw [hcancel, mul_one]
  rw [hprod] at hSu
  exact hSu

/-! ## Holomorphicity, Reality on the Imaginary Axis, and Cusp Bounds -/

theorem differentiableAt_thetaVec {τ : ℂ} (hτ : 0 < τ.im) (j : Fin 3) :
    DifferentiableAt ℂ (fun w => thetaVec w j) τ := by
  fin_cases j
  · exact Bottcher.differentiableAt_thetaThree hτ
  · exact Bottcher.differentiableAt_thetaFour hτ
  · exact Bottcher.differentiableAt_thetaTwo hτ

/-- Uniform cusp constant bounding `ϑ₃, ϑ₄, ϑ₂` on `{Im τ ≥ 1}`. -/
def thetaCuspBound : ℝ := max 2 RHTower.thetaTwoCuspConstant

theorem two_le_thetaCuspBound : (2 : ℝ) ≤ thetaCuspBound := le_max_left _ _

theorem thetaCuspBound_pos : 0 < thetaCuspBound := lt_of_lt_of_le two_pos two_le_thetaCuspBound

theorem norm_thetaVec_le_of_one_le_im {τ : ℂ} (hτ : 1 ≤ τ.im) (j : Fin 3) :
    ‖thetaVec τ j‖ ≤ thetaCuspBound := by
  fin_cases j
  · exact (RHTower.norm_thetaThree_le_two hτ).trans (le_max_left _ _)
  · exact (RHTower.norm_thetaFour_le_two hτ).trans (le_max_left _ _)
  · have h2 := RHTower.norm_thetaTwo_le_cusp hτ
    have hexp : Real.exp (-π * τ.im / 4) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < π * τ.im := mul_pos Real.pi_pos (by linarith)
      linarith
    have hK := RHTower.thetaTwoCuspConstant_nonneg
    calc ‖thetaVec τ 2‖ = ‖Bottcher.thetaTwo τ‖ := rfl
      _ ≤ RHTower.thetaTwoCuspConstant * Real.exp (-π * τ.im / 4) := h2
      _ ≤ RHTower.thetaTwoCuspConstant * 1 := mul_le_mul_of_nonneg_left hexp hK
      _ ≤ thetaCuspBound := by rw [mul_one]; exact le_max_right _ _

theorem norm_thetaVec_le_of_inv_im {τ : ℂ} (hτ0 : 0 < τ.im) (hinv : 1 ≤ (-1 / τ).im)
    (j : Fin 3) :
    ‖thetaVec τ j‖ ≤ thetaCuspBound * ‖τ‖ ^ (-1 / 2 : ℝ) := by
  have hτne : τ ≠ 0 := fun h => by simp [h] at hτ0
  have hS := thetaVec_neg_inv hτ0
  have hPS : thetaPS (thetaVec (-1 / τ)) = (-I * τ) ^ (1 / 2 : ℂ) • thetaVec τ := by
    rw [hS, LinearMap.map_smul]
    have := LinearMap.congr_fun thetaPS_comp_thetaPS (thetaVec τ)
    simpa using congrArg ((fun v => (-I * τ) ^ (1 / 2 : ℂ) • v)) this
  have hnorm_eq := congrArg (fun v => ‖v j‖) hPS
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul] at hnorm_eq
  have hne_mul : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτne
  have hcp : ‖(-I * τ) ^ (1 / 2 : ℂ)‖ = ‖τ‖ ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_ofReal _ hne_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [hcp] at hnorm_eq
  have hb : ‖(thetaPS (thetaVec (-1 / τ))) j‖ ≤ thetaCuspBound := by
    fin_cases j <;> simp [thetaPS] <;> exact norm_thetaVec_le_of_one_le_im hinv _
  have hpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτne
  have hrpos : 0 < ‖τ‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  rw [hnorm_eq] at hb
  calc ‖thetaVec τ j‖ = ‖thetaVec τ j‖ * ‖τ‖ ^ (1 / 2 : ℝ) * ‖τ‖ ^ (-1 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; norm_num
    _ ≤ thetaCuspBound * ‖τ‖ ^ (-1 / 2 : ℝ) := by
        rw [mul_comm (‖thetaVec τ j‖)]
        exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hpos.le _)

/-- Pointwise bound for `Θ⃗(iy)` along the entire positive imaginary ray `y > 0`. -/
theorem norm_thetaVec_axis_le {y : ℝ} (hy : 0 < y) (j : Fin 3) :
    ‖thetaVec (I * (y : ℂ)) j‖ ≤ thetaCuspBound * (1 + y ^ (-1 / 2 : ℝ)) := by
  have hB : 0 ≤ thetaCuspBound := thetaCuspBound_pos.le
  by_cases hy1 : 1 ≤ y
  · have him : 1 ≤ (I * (y : ℂ)).im := by simp [hy1]
    calc ‖thetaVec (I * (y : ℂ)) j‖ ≤ thetaCuspBound := norm_thetaVec_le_of_one_le_im him j
      _ ≤ thetaCuspBound * (1 + y ^ (-1 / 2 : ℝ)) := by
        nlinarith [Real.rpow_nonneg hy.le (-1 / 2 : ℝ)]
  · have hy1' : y < 1 := lt_of_not_ge hy1
    have him0 : 0 < (I * (y : ℂ)).im := by simp [hy]
    have hinv : 1 ≤ (-1 / (I * (y : ℂ))).im := by
      have heq : -1 / (I * (y : ℂ)) = I * ((1 / y : ℝ) : ℂ) := by
        have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
        push_cast
        rw [div_eq_iff (mul_ne_zero I_ne_zero hyC)]
        rw [show I * (1 / (y : ℂ)) * (I * (y : ℂ)) = I ^ 2 * ((1 / (y : ℂ)) * (y : ℂ)) by ring]
        rw [one_div_mul_cancel hyC, Complex.I_sq, mul_one]
      rw [heq]; simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, one_mul, zero_add]
      exact one_le_one_div hy hy1'.le
    have hb := norm_thetaVec_le_of_inv_im him0 hinv j
    have hnorm : ‖I * (y : ℂ)‖ = y := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    rw [hnorm] at hb
    nlinarith [thetaCuspBound_pos]

/-- All three Jacobi theta constants are real-valued on the positive imaginary axis `τ = iy`. -/
theorem conj_thetaVec_axis {y : ℝ} (_hy : 0 < y) (j : Fin 3) :
    starRingEnd ℂ (thetaVec (I * (y : ℂ)) j) = thetaVec (I * (y : ℂ)) j := by
  fin_cases j
  · change starRingEnd ℂ (Bottcher.thetaThree (I * (y : ℂ))) = Bottcher.thetaThree (I * (y : ℂ))
    rw [RHTower.thetaThree_eq_jacobiTheta, jacobiTheta, Complex.conj_tsum]
    refine tsum_congr fun n => ?_
    rw [← Complex.exp_conj]
    congr 1
    simp
  · change starRingEnd ℂ (Bottcher.thetaFour (I * (y : ℂ))) = Bottcher.thetaFour (I * (y : ℂ))
    unfold Bottcher.thetaFour jacobiTheta₂
    rw [Complex.conj_tsum, ← Equiv.tsum_eq (Equiv.neg ℤ)]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, jacobiTheta₂_term, ← Complex.exp_conj]
    congr 1
    simp only [map_add, map_mul, map_pow, map_div₀, map_ofNat, map_one, map_neg, map_intCast,
      Complex.conj_ofReal, Complex.conj_I, Int.cast_neg]
    ring
  · change starRingEnd ℂ (Bottcher.thetaTwo (I * (y : ℂ))) = Bottcher.thetaTwo (I * (y : ℂ))
    rw [Bottcher.thetaTwo_eq_tsum, Complex.conj_tsum]
    refine tsum_congr fun n => ?_
    have hexp : (Real.pi : ℂ) * I * ((n : ℂ) + 1 / 2) ^ (2 : ℕ) * (I * (y : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1 / 2) ^ (2 : ℕ) * y : ℝ) : ℂ) := by
      rw [show (Real.pi : ℂ) * I * ((n : ℂ) + 1 / 2) ^ (2 : ℕ) * (I * (y : ℂ)) =
        (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ (2 : ℕ) * (y : ℂ) * I ^ 2 by ring, Complex.I_sq]
      push_cast; ring
    rw [hexp, ← Complex.ofReal_exp, Complex.conj_ofReal]

/-- On the positive imaginary axis, `ϑ₃(iy) ≥ 1`. -/
theorem one_le_thetaThree_axis_re {y : ℝ} (hy : 0 < y) :
    1 ≤ (thetaVec (I * (y : ℂ)) 0).re := by
  change 1 ≤ (Bottcher.thetaThree (I * (y : ℂ))).re
  rw [RHTower.thetaThree_eq_jacobiTheta, jacobiTheta]
  have hterm : ∀ n : ℤ,
      cexp (↑π * I * (n : ℂ) ^ 2 * (I * (y : ℂ))) =
        (Real.exp (-π * (n : ℝ) ^ 2 * y) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    rw [show (Real.pi : ℂ) * I * (n : ℂ) ^ 2 * (I * (y : ℂ)) =
      (Real.pi : ℂ) * (n : ℂ) ^ 2 * (y : ℂ) * I ^ 2 by ring, Complex.I_sq]
    push_cast; ring
  simp_rw [hterm]
  have hsum : Summable (fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * y)) := by
    have hs0 := (hasSum_jacobiTheta₂_term 0 (τ := I * (y : ℂ)) (by simp [hy])).summable
    have hs : Summable (fun n : ℤ => cexp (↑π * I * (n : ℂ) ^ 2 * (I * (y : ℂ)))) := by
      refine hs0.congr fun n => ?_
      simp [jacobiTheta₂_term]
    have heq : (fun n : ℤ => ‖cexp (↑π * I * (n : ℂ) ^ 2 * (I * (y : ℂ)))‖) =
        fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * y) := by
      ext n
      rw [hterm n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rwa [← heq, summable_norm_iff]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have h0 : Real.exp (-π * ((0 : ℤ) : ℝ) ^ 2 * y) ≤
      ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * y) :=
    Summable.le_tsum hsum 0 (fun n _ => (Real.exp_pos _).le)
  simpa using h0

/-! ## Integrability and Holomorphicity of the Mordell–Lewis–Zagier Period Vector -/

/-- Integrand `(z + iy)^{-3/2} Θ⃗_j(iy)` of the weight-`½` Lewis–Zagier period vector at `w = 3/2`. -/
def thetaLewisIntegrand (z : ℂ) (j : Fin 3) (y : ℝ) : ℂ :=
  (z + I * (y : ℂ)) ^ (-3 / 2 : ℂ) * thetaVec (I * (y : ℂ)) j

/-- Mordell–Lewis–Zagier period vector `Ψ_ϑ(z) = i ∫_0^∞ (z + iy)^{-3/2} Θ⃗(iy) dy` (`w = 3/2`). -/
def thetaLewisPeriod (z : ℂ) : Fin 3 → ℂ :=
  fun j => I * ∫ y in Ioi (0 : ℝ), thetaLewisIntegrand z j y

private theorem integrableOn_rpow_neg_half_Ioc {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ (-1 / 2 : ℝ)) (Ioc 0 a) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

private theorem integrableOn_rpow_neg_three_halves_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ (-3 / 2 : ℝ)) (Ioi a) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) ha

private def periodDomBound (c B : ℝ) (y : ℝ) : ℝ :=
  if y ≤ 2 * B + 1 then
    thetaCuspBound * c ^ (-3 / 2 : ℝ) * (1 + y ^ (-1 / 2 : ℝ))
  else
    2 * thetaCuspBound * (y / 2) ^ (-3 / 2 : ℝ)

private theorem integrableOn_periodDomBound {c B : ℝ} (_hc : 0 < c) (hB : 0 ≤ B) :
    IntegrableOn (periodDomBound c B) (Ioi 0) := by
  have hR : 0 < 2 * B + 1 := by linarith
  have hunion : Ioi (0 : ℝ) = Ioc 0 (2 * B + 1) ∪ Ioi (2 * B + 1) :=
    (Ioc_union_Ioi_eq_Ioi hR.le).symm
  rw [hunion]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ =>
        thetaCuspBound * c ^ (-3 / 2 : ℝ) * (1 + y ^ (-1 / 2 : ℝ))) (Ioc 0 (2 * B + 1)) := by
      have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 (2 * B + 1)) := by simp
      exact (hconst.add (integrableOn_rpow_neg_half_Ioc hR)).const_mul _
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
    dsimp only [periodDomBound]
    rw [if_pos hy.2]
  · have h2 : IntegrableOn (fun y : ℝ => 2 * thetaCuspBound * (2 : ℝ) ^ (3 / 2 : ℝ) *
        y ^ (-3 / 2 : ℝ)) (Ioi (2 * B + 1)) :=
      (integrableOn_rpow_neg_three_halves_Ioi hR).const_mul _
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hyR : ¬ y ≤ 2 * B + 1 := not_le.mpr hy
    have hy0 : 0 < y := hR.trans hy
    have h2pow : ((2 : ℝ) ^ (-3 / 2 : ℝ))⁻¹ = (2 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
    have hrdiv : (y / 2) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * y ^ (-3 / 2 : ℝ) := by
      rw [Real.div_rpow hy0.le (by norm_num), div_eq_mul_inv, h2pow, mul_comm]
    dsimp only [periodDomBound]
    rw [if_neg hyR, hrdiv]
    ring

private theorem norm_thetaLewisIntegrand_le_dom {c B : ℝ} (hc : 0 < c)
    {z : ℂ} (hzre : c ≤ z.re) (hzim : |z.im| ≤ B) (j : Fin 3) {y : ℝ} (hy : 0 < y) :
    ‖thetaLewisIntegrand z j y‖ ≤ periodDomBound c B y := by
  have hzpos : 0 < (z + I * (y : ℂ)).re := by simp; linarith
  have hzne : z + I * (y : ℂ) ≠ 0 := fun h => by simp [h] at hzpos
  have hcpow : ‖(z + I * (y : ℂ)) ^ (-3 / 2 : ℂ)‖ = ‖z + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact norm_cpow_ofReal _ hzne _
  unfold thetaLewisIntegrand periodDomBound
  rw [norm_mul, hcpow]
  have hθ := norm_thetaVec_axis_le hy j
  split_ifs with hyR
  · have hnorm_ge : c ≤ ‖z + I * (y : ℂ)‖ := by
      have hre_le := Complex.re_le_norm (z + I * (y : ℂ))
      simp at hre_le; linarith
    have hrpow : ‖z + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) ≤ c ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hc hnorm_ge (by norm_num)
    calc ‖z + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) * ‖thetaVec (I * (y : ℂ)) j‖
        ≤ c ^ (-3 / 2 : ℝ) * (thetaCuspBound * (1 + y ^ (-1 / 2 : ℝ))) :=
          mul_le_mul hrpow hθ (norm_nonneg _) (Real.rpow_nonneg hc.le _)
      _ = thetaCuspBound * c ^ (-3 / 2 : ℝ) * (1 + y ^ (-1 / 2 : ℝ)) := by ring
  · have hyR' : 2 * B + 1 < y := lt_of_not_ge hyR
    have hy1 : 1 ≤ y := by
      have hB0 : 0 ≤ |z.im| := abs_nonneg _
      linarith
    have him_ge : y / 2 ≤ ‖z + I * (y : ℂ)‖ := by
      have him_le := Complex.abs_im_le_norm (z + I * (y : ℂ))
      have him_eq : (z + I * (y : ℂ)).im = z.im + y := by simp
      rw [him_eq] at him_le
      have hneg := neg_le_abs z.im
      have hpos_im : y / 2 ≤ z.im + y := by linarith
      exact hpos_im.trans ((le_abs_self _).trans him_le)
    have hrpow : ‖z + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) ≤ (y / 2) ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) him_ge (by norm_num)
    have hy_inv : y ^ (-1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
    have hθ2 : ‖thetaVec (I * (y : ℂ)) j‖ ≤ thetaCuspBound * 2 :=
      hθ.trans (by nlinarith [thetaCuspBound_pos, hy_inv])
    calc ‖z + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) * ‖thetaVec (I * (y : ℂ)) j‖
        ≤ (y / 2) ^ (-3 / 2 : ℝ) * (thetaCuspBound * 2) :=
          mul_le_mul hrpow hθ2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = 2 * thetaCuspBound * (y / 2) ^ (-3 / 2 : ℝ) := by ring

private theorem continuousOn_thetaLewisIntegrand {z : ℂ} (hz : 0 < z.re) (j : Fin 3) :
    ContinuousOn (thetaLewisIntegrand z j) (Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  have h1 : ContinuousAt (fun t : ℝ => z + I * (t : ℂ)) y := by fun_prop
  have hslit : z + I * (y : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hz]))
  have hcpow : ContinuousAt (fun t : ℝ => (z + I * (t : ℂ)) ^ (-3 / 2 : ℂ)) y :=
    ContinuousAt.comp (f := fun t : ℝ => z + I * (t : ℂ))
      (differentiableAt_id.cpow_const hslit).continuousAt h1
  have hθ : ContinuousAt (fun t : ℝ => thetaVec (I * (t : ℂ)) j) y := by
    have hd := differentiableAt_thetaVec (τ := I * (y : ℂ)) (by simp [hy0]) j
    exact ContinuousAt.comp (f := fun t : ℝ => I * (t : ℂ)) hd.continuousAt (by fun_prop)
  exact (hcpow.mul hθ).continuousWithinAt

theorem integrableOn_thetaLewisIntegrand {z : ℂ} (hz : 0 < z.re) (j : Fin 3) :
    IntegrableOn (thetaLewisIntegrand z j) (Ioi 0) := by
  refine (integrableOn_periodDomBound (hz.trans_le (le_refl _)) (abs_nonneg z.im)).mono' ?_ ?_
  · exact (continuousOn_thetaLewisIntegrand hz j).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact norm_thetaLewisIntegrand_le_dom hz (le_refl _) (le_refl _) j hy

/-- `Ψ_ϑ` is holomorphic on the entire open right half-plane `{z : ℂ | 0 < z.re}`. -/
theorem differentiableOn_thetaLewisPeriod (j : Fin 3) :
    DifferentiableOn ℂ (fun z => thetaLewisPeriod z j) {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  have hz₀_pos : 0 < z₀.re := hz₀
  set δ := z₀.re / 2
  have hδ : 0 < δ := half_pos hz₀_pos
  set B := |z₀.im| + δ
  have hB : 0 ≤ B := by positivity
  let F' : ℂ → ℝ → ℂ := fun z y =>
    (-3 / 2 : ℂ) * (z + I * (y : ℂ)) ^ (-5 / 2 : ℂ) * thetaVec (I * (y : ℂ)) j
  let dBound : ℝ → ℝ := fun y => (3 / 2 / δ) * periodDomBound δ B y
  have hdBoundInt : IntegrableOn dBound (Ioi 0) :=
    (integrableOn_periodDomBound hδ hB).const_mul _
  have hball_re : ∀ z ∈ Metric.ball z₀ δ, δ ≤ z.re ∧ |z.im| ≤ B := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - z₀)
    have him := Complex.abs_im_le_norm (z - z₀)
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    have h1 := neg_abs_le (z.re - z₀.re)
    have h2 : |z.im| ≤ |z₀.im| + |z.im - z₀.im| := by
      calc |z.im| = |z₀.im + (z.im - z₀.im)| := by ring_nf
        _ ≤ |z₀.im| + |z.im - z₀.im| := abs_add_le _ _
    have hδ_def : δ = z₀.re / 2 := rfl
    have hB_def : B = |z₀.im| + δ := rfl
    exact ⟨by linarith, by linarith⟩
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (thetaLewisIntegrand z j) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hδ] with z hz
    exact (continuousOn_thetaLewisIntegrand (hδ.trans_le (hball_re z hz).1) j).aestronglyMeasurable
      measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    have hslit : z₀ + I * (y : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hz₀_pos]))
    have h1 : ContinuousAt (fun t : ℝ => z₀ + I * (t : ℂ)) y := by fun_prop
    have hcpow : ContinuousAt (fun t : ℝ => (z₀ + I * (t : ℂ)) ^ (-5 / 2 : ℂ)) y :=
      ContinuousAt.comp (f := fun t : ℝ => z₀ + I * (t : ℂ))
        (differentiableAt_id.cpow_const hslit).continuousAt h1
    have hθ : ContinuousAt (fun t : ℝ => thetaVec (I * (t : ℂ)) j) y := by
      have hd := differentiableAt_thetaVec (τ := I * (y : ℂ)) (by simp [hy0]) j
      exact ContinuousAt.comp (f := fun t : ℝ => I * (t : ℂ)) hd.continuousAt (by fun_prop)
    exact ((continuousAt_const.mul hcpow).mul hθ).continuousWithinAt
  have h_bound : ∀ᵐ y ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ δ, ‖F' z y‖ ≤ dBound y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    obtain ⟨hzre, hzim⟩ := hball_re z hz
    have hy0 : 0 < y := hy
    have hre_pos : 0 < (z + I * (y : ℂ)).re := by simp; linarith
    have hne : z + I * (y : ℂ) ≠ 0 := fun h => by simp [h] at hre_pos
    have hsplit : (z + I * (y : ℂ)) ^ (-5 / 2 : ℂ) =
        (z + I * (y : ℂ))⁻¹ * (z + I * (y : ℂ)) ^ (-3 / 2 : ℂ) := by
      have hexp : (-5 / 2 : ℂ) = (-1 : ℂ) + (-3 / 2 : ℂ) := by norm_num
      rw [hexp, Complex.cpow_add _ _ hne, Complex.cpow_neg_one]
    have hnorm_ge : δ ≤ ‖z + I * (y : ℂ)‖ := by
      have := Complex.re_le_norm (z + I * (y : ℂ)); simp at this; linarith
    have hinv_le : ‖(z + I * (y : ℂ))⁻¹‖ ≤ 1 / δ := by
      rw [norm_inv, one_div]
      exact inv_anti₀ hδ hnorm_ge
    have h32 : ‖(-3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    calc ‖F' z y‖
        = (3 / 2) * ‖(z + I * (y : ℂ))⁻¹‖ * ‖thetaLewisIntegrand z j y‖ := by
          simp only [F', thetaLewisIntegrand, hsplit, norm_mul, h32]; ring
      _ ≤ (3 / 2) * (1 / δ) * periodDomBound δ B y := by
          have hb := norm_thetaLewisIntegrand_le_dom hδ hzre hzim j hy0
          have hb0 : 0 ≤ ‖thetaLewisIntegrand z j y‖ := norm_nonneg _
          nlinarith [mul_le_mul hinv_le hb hb0 (by positivity)]
      _ = dBound y := by simp only [dBound]; ring
  have h_diff : ∀ᵐ y ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball z₀ δ,
      HasDerivAt (fun w => thetaLewisIntegrand w j y) (F' z y) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _ z hz
    obtain ⟨hzre, _⟩ := hball_re z hz
    have hslit : z + I * (y : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    have h1 : HasDerivAt (fun w : ℂ => w + I * (y : ℂ)) 1 z :=
      (hasDerivAt_id z).add_const _
    have h2 := h1.cpow_const hslit (c := (-3 / 2 : ℂ))
    have h3 := h2.mul_const (thetaVec (I * (y : ℂ)) j)
    refine h3.congr_deriv ?_
    simp only [F']
    have hexp : (-3 / 2 : ℂ) - 1 = -5 / 2 := by norm_num
    rw [hexp]; ring
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ hδ) hF_meas (integrableOn_thetaLewisIntegrand hz₀_pos j)
    hF'_meas h_bound hdBoundInt h_diff).2
  exact (hderiv.const_mul I).differentiableAt.differentiableWithinAt

/-! ## Strict Non-Vanishing, Cusp Decay, and Exclusion of Coboundaries -/

/-- For every `a > 0`, `Re(Ψ_ϑ(a)_0) > 0`; in particular `Ψ_ϑ(a) ≠ 0`. -/
theorem thetaLewisPeriod_zero_re_pos {a : ℝ} (ha : 0 < a) :
    0 < (thetaLewisPeriod (a : ℂ) 0).re := by
  have hre_eq : (thetaLewisPeriod (a : ℂ) 0).re =
      ∫ y in Ioi (0 : ℝ), (I * thetaLewisIntegrand (a : ℂ) 0 y).re := by
    unfold thetaLewisPeriod
    rw [← integral_const_mul]
    have hint := (integrableOn_thetaLewisIntegrand (z := (a : ℂ)) (by simp [ha]) 0).const_mul I
    exact (Complex.reCLM.integral_comp_comm hint).symm
  rw [hre_eq]
  set f : ℝ → ℝ := fun y => (I * thetaLewisIntegrand (a : ℂ) 0 y).re
  have hf_int : IntegrableOn f (Ioi 0) := by
    have hint := (integrableOn_thetaLewisIntegrand (z := (a : ℂ)) (by simp [ha]) 0).const_mul I
    exact Complex.reCLM.integrable_comp hint
  have hf_pos : ∀ y : ℝ, 0 < y → 0 < f y := by
    intro y hy
    have hθ_real : (thetaVec (I * (y : ℂ)) 0).im = 0 :=
      Complex.conj_eq_iff_im.mp (conj_thetaVec_axis hy 0)
    have hθ_ge := one_le_thetaThree_axis_re hy
    set w : ℂ := (a : ℂ) + I * (y : ℂ)
    have hw_re : 0 < w.re := by simp [w, ha]
    have hw_im : 0 < w.im := by simp [w, hy]
    have hw_ne : w ≠ 0 := fun h => by simp [h] at hw_re
    have harg := arg_mem_Ioo_first_quad hw_re hw_im
    have hsin_neg : Real.sin ((-3 / 2 : ℝ) * w.arg) < 0 := by
      refine Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [harg.1]) ?_
      linarith [harg.2, Real.pi_pos]
    have hcpow_im : (w ^ (-3 / 2 : ℂ)).im =
        ‖w‖ ^ (-3 / 2 : ℝ) * Real.sin ((-3 / 2 : ℝ) * w.arg) := by
      set r1 : ℝ := (-3 / 2 : ℝ) * Real.log ‖w‖
      set r2 : ℝ := (-3 / 2 : ℝ) * w.arg
      have hlog : Complex.log w * (-3 / 2 : ℂ) = (r1 : ℂ) + (r2 : ℂ) * I := by
        simp only [r1, r2, Complex.log]; push_cast; ring
      rw [Complex.cpow_def_of_ne_zero hw_ne, hlog, Complex.exp_add_mul_I,
        ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have him_calc : ((Real.exp r1 : ℂ) * ((Real.cos r2 : ℂ) + (Real.sin r2 : ℂ) * I)).im =
          Real.exp r1 * Real.sin r2 := by
        simp [Complex.exp_ofReal_re, Complex.sin_ofReal_re]
      rw [him_calc, Real.rpow_def_of_pos (norm_pos_iff.mpr hw_ne)]
      simp only [r1, r2]
      congr 2
      ring
    have hval : f y = (-(w ^ (-3 / 2 : ℂ)).im) * (thetaVec (I * (y : ℂ)) 0).re := by
      simp only [f, thetaLewisIntegrand, w]
      simp [Complex.mul_re, Complex.mul_im, hθ_real]
    rw [hval, hcpow_im]
    have hrpos : 0 < ‖w‖ ^ (-3 / 2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw_ne) _
    have him_neg : 0 < -(‖w‖ ^ (-3 / 2 : ℝ) * Real.sin ((-3 / 2 : ℝ) * w.arg)) := by
      nlinarith [mul_neg_of_pos_of_neg hrpos hsin_neg]
    exact mul_pos him_neg (by linarith)
  have hsub : Icc (a / 2) a ⊆ Ioi 0 := fun y hy => by dsimp [Ioi]; linarith [hy.1, ha]
  have hf_cont : ContinuousOn f (Icc (a / 2) a) := by
    have hc := continuousOn_thetaLewisIntegrand (z := (a : ℂ)) (by simp [ha]) 0
    exact Complex.continuous_re.comp_continuousOn ((continuousOn_const.mul hc).mono hsub)
  have hne : (Icc (a / 2) a).Nonempty := ⟨a, by linarith, le_refl a⟩
  obtain ⟨y₀, hy₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf_cont
  have hfy₀ : 0 < f y₀ := hf_pos y₀ (hsub hy₀)
  have hmono_set : ∫ y in Icc (a / 2) a, f y ≤ ∫ y in Ioi (0 : ℝ), f y :=
    setIntegral_mono_set hf_int
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => (hf_pos y hy).le)
      (Eventually.of_forall hsub)
  have hconst_le : ∫ _ in Icc (a / 2) a, f y₀ ≤ ∫ y in Icc (a / 2) a, f y :=
    setIntegral_mono_on (integrableOn_const (by simp)) (hf_int.mono_set hsub) measurableSet_Icc
      fun y hy => hmin hy
  have hval_const : ∫ _ in Icc (a / 2) a, f y₀ = (a - a / 2) * f y₀ := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  linarith [mul_pos (by linarith : 0 < a - a / 2) hfy₀]

theorem thetaLewisPeriod_ne_zero {a : ℝ} (ha : 0 < a) :
    thetaLewisPeriod (a : ℂ) ≠ 0 := by
  intro h
  have h0 := congrArg (fun v => (v 0).re) h
  simp at h0
  linarith [thetaLewisPeriod_zero_re_pos ha]

/-- Quantitative cusp decay `‖Ψ_ϑ(a)_j‖ ≤ 4 C_ϑ (a^{-1/2} + a^{-1})` for all `a > 0`. -/
theorem norm_thetaLewisPeriod_le {a : ℝ} (ha : 0 < a) (j : Fin 3) :
    ‖thetaLewisPeriod (a : ℂ) j‖ ≤
      4 * thetaCuspBound * (a ^ (-1 / 2 : ℝ) + a ^ (-1 : ℝ)) := by
  unfold thetaLewisPeriod
  rw [norm_mul, Complex.norm_I, one_mul]
  have hint : IntegrableOn (fun y => ‖thetaLewisIntegrand (a : ℂ) j y‖) (Ioi 0) :=
    (integrableOn_thetaLewisIntegrand (z := (a : ℂ)) (by simp [ha]) j).norm
  have hnorm_int : ‖∫ y in Ioi (0 : ℝ), thetaLewisIntegrand (a : ℂ) j y‖ ≤
      ∫ y in Ioi (0 : ℝ), ‖thetaLewisIntegrand (a : ℂ) j y‖ := norm_integral_le_integral_norm _
  have hunion : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hdisj : Disjoint (Ioc 0 a) (Ioi a) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => hx1.2.not_gt hx2
  have hsplit : ∫ y in Ioi (0 : ℝ), ‖thetaLewisIntegrand (a : ℂ) j y‖ =
      (∫ y in Ioc 0 a, ‖thetaLewisIntegrand (a : ℂ) j y‖) +
      (∫ y in Ioi a, ‖thetaLewisIntegrand (a : ℂ) j y‖) := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (fun _ hy => hy.1)) (hint.mono_set (fun _ hy => ha.trans hy))]
  -- Piece 1: `(0, a]`
  have hIoc_le : ∫ y in Ioc 0 a, ‖thetaLewisIntegrand (a : ℂ) j y‖ ≤
      thetaCuspBound * (a ^ (-1 / 2 : ℝ) + 2 * a ^ (-1 : ℝ)) := by
    let g1 : ℝ → ℝ := fun y => thetaCuspBound * a ^ (-3 / 2 : ℝ) * (1 + y ^ (-1 / 2 : ℝ))
    have hg1_int : IntegrableOn g1 (Ioc 0 a) :=
      ((integrableOn_const (by simp)).add (integrableOn_rpow_neg_half_Ioc ha)).const_mul _
    have hle1 : ∫ y in Ioc 0 a, ‖thetaLewisIntegrand (a : ℂ) j y‖ ≤ ∫ y in Ioc 0 a, g1 y := by
      refine setIntegral_mono_on (hint.mono_set (fun _ hy => hy.1)) hg1_int measurableSet_Ioc ?_
      intro y hy
      have hne : (a : ℂ) + I * (y : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp [ha.ne'] at this
      have hcpow : ‖((a : ℂ) + I * (y : ℂ)) ^ (-3 / 2 : ℂ)‖ =
          ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact norm_cpow_ofReal _ hne _
      have hge : a ≤ ‖(a : ℂ) + I * (y : ℂ)‖ := by
        have := Complex.re_le_norm ((a : ℂ) + I * (y : ℂ)); simpa using this
      have hr : ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) ≤ a ^ (-3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha hge (by norm_num)
      calc ‖thetaLewisIntegrand (a : ℂ) j y‖
          = ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) * ‖thetaVec (I * (y : ℂ)) j‖ := by
            rw [thetaLewisIntegrand, norm_mul, hcpow]
        _ ≤ a ^ (-3 / 2 : ℝ) * (thetaCuspBound * (1 + y ^ (-1 / 2 : ℝ))) :=
            mul_le_mul hr (norm_thetaVec_axis_le hy.1 j) (norm_nonneg _) (Real.rpow_nonneg ha.le _)
        _ = g1 y := by simp only [g1]; ring
    have hg1_eval : ∫ y in Ioc 0 a, g1 y =
        thetaCuspBound * (a ^ (-1 / 2 : ℝ) + 2 * a ^ (-1 : ℝ)) := by
      have hconst_int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 a) :=
        integrableOn_const (by simp)
      simp only [g1]
      rw [integral_const_mul, MeasureTheory.integral_add hconst_int
        (integrableOn_rpow_neg_half_Ioc ha)]
      have h1 : ∫ _ in Ioc 0 a, (1 : ℝ) = a := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le ha.le, sub_zero, smul_eq_mul,
          mul_one]
      have h2 : ∫ y in Ioc 0 a, y ^ (-1 / 2 : ℝ) = 2 * a ^ (1 / 2 : ℝ) := by
        rw [← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl (by norm_num))]
        rw [Real.zero_rpow (by norm_num)]
        ring_nf
      rw [h1, h2]
      have hp1 : a ^ (-3 / 2 : ℝ) * a = a ^ (-1 / 2 : ℝ) := by
        calc a ^ (-3 / 2 : ℝ) * a = a ^ (-3 / 2 : ℝ) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = a ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add ha]; norm_num
      have hp2 : a ^ (-3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a ^ (-1 : ℝ) := by
        rw [← Real.rpow_add ha]; norm_num
      linear_combination thetaCuspBound * hp1 + 2 * thetaCuspBound * hp2
    linarith
  -- Piece 2: `(a, ∞)`
  have hIoi_le : ∫ y in Ioi a, ‖thetaLewisIntegrand (a : ℂ) j y‖ ≤
      thetaCuspBound * (2 * a ^ (-1 / 2 : ℝ) + 2 * a ^ (-1 : ℝ)) := by
    let g2 : ℝ → ℝ := fun y => thetaCuspBound * (1 + a ^ (-1 / 2 : ℝ)) * y ^ (-3 / 2 : ℝ)
    have hg2_int : IntegrableOn g2 (Ioi a) :=
      (integrableOn_rpow_neg_three_halves_Ioi ha).const_mul _
    have hle2 : ∫ y in Ioi a, ‖thetaLewisIntegrand (a : ℂ) j y‖ ≤ ∫ y in Ioi a, g2 y := by
      refine setIntegral_mono_on (hint.mono_set (fun _ hy => ha.trans hy)) hg2_int
        measurableSet_Ioi ?_
      intro y hy
      have hy0 : 0 < y := ha.trans hy
      have hne : (a : ℂ) + I * (y : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp [ha.ne'] at this
      have hcpow : ‖((a : ℂ) + I * (y : ℂ)) ^ (-3 / 2 : ℂ)‖ =
          ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact norm_cpow_ofReal _ hne _
      have hge : y ≤ ‖(a : ℂ) + I * (y : ℂ)‖ := by
        have := Complex.im_le_norm ((a : ℂ) + I * (y : ℂ)); simpa using this
      have hr : ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) ≤ y ^ (-3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hy0 hge (by norm_num)
      have hy_le_a : y ^ (-1 / 2 : ℝ) ≤ a ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha hy.le (by norm_num)
      have hθ_le : ‖thetaVec (I * (y : ℂ)) j‖ ≤ thetaCuspBound * (1 + a ^ (-1 / 2 : ℝ)) :=
        (norm_thetaVec_axis_le hy0 j).trans (by nlinarith [thetaCuspBound_pos])
      calc ‖thetaLewisIntegrand (a : ℂ) j y‖
          = ‖(a : ℂ) + I * (y : ℂ)‖ ^ (-3 / 2 : ℝ) * ‖thetaVec (I * (y : ℂ)) j‖ := by
            rw [thetaLewisIntegrand, norm_mul, hcpow]
        _ ≤ y ^ (-3 / 2 : ℝ) * (thetaCuspBound * (1 + a ^ (-1 / 2 : ℝ))) :=
            mul_le_mul hr hθ_le (norm_nonneg _) (Real.rpow_nonneg hy0.le _)
        _ = g2 y := by simp only [g2]; ring
    have hg2_eval : ∫ y in Ioi a, g2 y =
        thetaCuspBound * (2 * a ^ (-1 / 2 : ℝ) + 2 * a ^ (-1 : ℝ)) := by
      simp only [g2]
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
      have hexp : (-3 / 2 : ℝ) + 1 = -1 / 2 := by norm_num
      rw [hexp]
      have hp : a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = a ^ (-1 : ℝ) := by
        rw [← Real.rpow_add ha]; norm_num
      linear_combination 2 * thetaCuspBound * hp
    linarith
  have ha12 : 0 ≤ a ^ (-1 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  nlinarith [thetaCuspBound_pos]

/-- `Ψ_ϑ(a) → 0` at the cusp `a → +∞`. -/
theorem tendsto_thetaLewisPeriod_atTop (j : Fin 3) :
    Tendsto (fun a : ℝ => thetaLewisPeriod (a : ℂ) j) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun a : ℝ =>
      4 * thetaCuspBound * (a ^ (-1 / 2 : ℝ) + a ^ (-1 : ℝ))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, show (-1 : ℝ) = -(1 : ℝ) by ring]
    simpa using (h1.add h2).const_mul (4 * thetaCuspBound)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact norm_thetaLewisPeriod_le ha j

/-- `Ψ_ϑ` is not a coboundary `v - a^{-3/2} U_T v` for any `v ∈ ℂ³`. -/
theorem not_exists_coboundary_eq_thetaLewisPeriod :
    ¬ ∃ v : Fin 3 → ℂ, ∀ a : ℝ, 0 < a →
      thetaLewisPeriod (a : ℂ) = v - ((a : ℂ) ^ (-3 / 2 : ℂ)) • thetaUT v := by
  rintro ⟨v, hv⟩
  have hv_zero : v = 0 := by
    ext j
    have hlimL := tendsto_thetaLewisPeriod_atTop j
    have hlimR : Tendsto (fun a : ℝ => v j - ((a : ℂ) ^ (-3 / 2 : ℂ) * (thetaUT v j)))
        atTop (𝓝 (v j)) := by
      have hc : Tendsto (fun a : ℝ => (a : ℂ) ^ (-3 / 2 : ℂ)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
          norm_cpow_ofReal _ (Complex.ofReal_ne_zero.mpr ha.ne'),
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
          show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num]
      simpa using tendsto_const_nhds.sub (hc.mul_const (thetaUT v j))
    have heq : (fun a : ℝ => thetaLewisPeriod (a : ℂ) j) =ᶠ[atTop]
        fun a : ℝ => v j - ((a : ℂ) ^ (-3 / 2 : ℂ) * (thetaUT v j)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      exact congrArg (fun w => w j) (hv a ha)
    exact (tendsto_nhds_unique (hlimL.congr' heq) hlimR).symm
  have h1 := hv 1 one_pos
  rw [hv_zero] at h1
  simp at h1
  exact thetaLewisPeriod_ne_zero one_pos h1

/-! ## Anti-Unitary Chiral `S`-Reciprocity on `(0, ∞)` -/

private theorem integral_Ioi_inv_change (g : ℝ → ℂ) :
    (∫ y in Ioi (0 : ℝ), g y) = ∫ u in Ioi (0 : ℝ), ((u ^ (-2 : ℝ) : ℝ) : ℂ) * g u⁻¹ := by
  have himg : (fun u : ℝ => u⁻¹) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨u, hu, huy⟩ => huy ▸ inv_pos.mpr hu,
      fun hy => ⟨y⁻¹, inv_pos.mpr hy, inv_inv y⟩⟩
  have hinj : InjOn (fun u : ℝ => u⁻¹) (Ioi 0) := fun _ _ _ _ h => inv_injective h
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi (fun u (hu : 0 < u) => (hasDerivAt_inv hu.ne').hasDerivWithinAt) hinj g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  have habs : |-(u ^ 2)⁻¹| = u ^ (-2 : ℝ) := by
    rw [abs_neg, abs_of_pos (by positivity), Real.rpow_neg hu0.le, Real.rpow_two]
  change |-(u ^ 2)⁻¹| • g u⁻¹ = ((u ^ (-2 : ℝ) : ℝ) : ℂ) * g u⁻¹
  rw [habs, Complex.real_smul]

/-- Anti-unitary chiral `S`-reciprocity `conj(Ψ_ϑ(a)) = a^{-3/2} U_S Ψ_ϑ(1/a)` for `a > 0`. -/
theorem thetaLewisPeriod_S_reciprocity {a : ℝ} (ha : 0 < a) :
    (fun j => starRingEnd ℂ (thetaLewisPeriod (a : ℂ) j)) =
      ((a : ℂ) ^ (-3 / 2 : ℂ)) • thetaUS (thetaLewisPeriod ((1 / a : ℝ) : ℂ)) := by
  ext j
  have hconj_int : starRingEnd ℂ (thetaLewisPeriod (a : ℂ) j) =
      -I * ∫ y in Ioi (0 : ℝ), starRingEnd ℂ (thetaLewisIntegrand (a : ℂ) j y) := by
    unfold thetaLewisPeriod
    rw [map_mul, Complex.conj_I, ← integral_conj]
  rw [hconj_int, integral_Ioi_inv_change]
  have hcongr : ∫ u in Ioi (0 : ℝ),
      ((u ^ (-2 : ℝ) : ℝ) : ℂ) * starRingEnd ℂ (thetaLewisIntegrand (a : ℂ) j u⁻¹) =
      (a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
        ∫ u in Ioi (0 : ℝ), thetaLewisIntegrand ((1 / a : ℝ) : ℂ) (Fin.cases 0 ![2, 1] j) u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    -- Theta inversion at `y = u⁻¹`
    have hθ_inv : thetaVec (I * (u⁻¹ : ℂ)) j =
        (u : ℂ) ^ (1 / 2 : ℂ) * thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j) := by
      have heq : I * (u⁻¹ : ℂ) = -1 / (I * (u : ℂ)) := by
        rw [inv_eq_one_div, mul_one_div, div_eq_div_iff huC (mul_ne_zero I_ne_zero huC)]
        rw [show I * (I * (u : ℂ)) = I ^ 2 * (u : ℂ) by ring, Complex.I_sq]
      rw [heq]
      have hS := congrArg (fun v => v j) (thetaVec_neg_inv (τ := I * (u : ℂ)) (by simp [hu0]))
      have hIu : -I * (I * (u : ℂ)) = (u : ℂ) := by
        linear_combination -(u : ℂ) * Complex.I_sq
      rw [hIu] at hS
      fin_cases j <;> simp [thetaPS] at hS ⊢ <;> exact hS
    -- Conjugate of `thetaLewisIntegrand`
    have hconj_θ := conj_thetaVec_axis (inv_pos.mpr hu0) j
    set w0 : ℂ := (a : ℂ) + I * ((u⁻¹ : ℝ) : ℂ)
    have hw_re : 0 < w0.re := by simp [w0, ha]
    have hw_ne : w0 ≠ 0 := fun h => by simp [h] at hw_re
    have hw_arg_ne : w0.arg ≠ π := by
      have := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hw_re)
      linarith [Real.pi_pos]
    have hconj_w0 : starRingEnd ℂ w0 = (a : ℂ) - I * (u : ℂ)⁻¹ := by
      simp [w0, sub_eq_add_neg]
    have hw_conj_ne : (a : ℂ) - I * (u : ℂ)⁻¹ ≠ 0 := by
      intro h
      apply hw_ne
      apply (starRingEnd ℂ).injective
      rw [hconj_w0, h, map_zero]
    have hconj_cpow :
        starRingEnd ℂ (w0 ^ (-3 / 2 : ℂ)) =
          ((a : ℂ) - I * (u : ℂ)⁻¹) ^ (-3 / 2 : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero hw_ne, Complex.cpow_def_of_ne_zero hw_conj_ne,
        ← Complex.exp_conj, map_mul, ← Complex.log_conj _ hw_arg_ne, hconj_w0]
      have hre_exp : starRingEnd ℂ (-3 / 2 : ℂ) = (-3 / 2 : ℂ) := by simp [map_ofNat]
      rw [hre_exp]
    -- Factor `a - I * u⁻¹ = (a * u - I) * u⁻¹` and `a * u - I = a * (-I) * (1/a + I * u)`
    have hau_re : 0 < ((a : ℂ) * (u : ℂ) - I).re := by simp [mul_pos ha hu0]
    have hau_ne : (a : ℂ) * (u : ℂ) - I ≠ 0 := fun h => by simp [h] at hau_re
    have hstep1 : ((a : ℂ) - I * (u : ℂ)⁻¹) ^ (-3 / 2 : ℂ) =
        ((a : ℂ) * (u : ℂ) - I) ^ (-3 / 2 : ℂ) * (u : ℂ) ^ (3 / 2 : ℂ) := by
      have hfac : (a : ℂ) - I * (u : ℂ)⁻¹ = ((a : ℂ) * (u : ℂ) - I) * ((u⁻¹ : ℝ) : ℂ) := by
        push_cast; field_simp [huC]
      rw [hfac, mul_ofReal_cpow_pos hau_ne (inv_pos.mpr hu0)]
      have hupow : ((u⁻¹ : ℝ) : ℂ) ^ (-3 / 2 : ℂ) = (u : ℂ) ^ (3 / 2 : ℂ) := by
        rw [Complex.ofReal_inv, inv_cpow_of_re_pos (by simp [hu0]),
          ← Complex.cpow_neg]
        norm_num
      rw [hupow]
    have hstep2 : ((a : ℂ) * (u : ℂ) - I) ^ (-3 / 2 : ℂ) =
        (a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
          (((1 / a : ℝ) : ℂ) + I * (u : ℂ)) ^ (-3 / 2 : ℂ) := by
      set q : ℂ := ((1 / a : ℝ) : ℂ) + I * (u : ℂ)
      have hq_re : 0 < q.re := by simp [q, ha]
      have hq_im : 0 < q.im := by simp [q, hu0]
      have hq_ne : q ≠ 0 := fun h => by simp [h] at hq_re
      have hfac : (a : ℂ) * (u : ℂ) - I = (a : ℂ) * ((-I) * q) := by
        simp only [q]; push_cast
        have hmul_a : (a : ℂ) * (1 / (a : ℂ)) = 1 := mul_one_div_cancel haC
        calc (a : ℂ) * (u : ℂ) - I
            = -(a : ℂ) * (u : ℂ) * I ^ 2 - I * ((a : ℂ) * (1 / (a : ℂ))) := by
              rw [Complex.I_sq, hmul_a]; ring
          _ = (a : ℂ) * ((-I) * (1 / (a : ℂ) + I * (u : ℂ))) := by ring
      have harg_sum : (-I).arg + q.arg ∈ Ioc (-π) π := by
        have hq_arg := arg_mem_Ioo_first_quad hq_re hq_im
        rw [Complex.arg_neg_I]
        exact ⟨by linarith [hq_arg.1, Real.pi_pos], by linarith [hq_arg.2, Real.pi_pos]⟩
      have hnegI : (-I) ^ (-3 / 2 : ℂ) = Complex.exp ((3 * Real.pi / 4 : ℝ) * I) := by
        rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), Complex.log,
          norm_neg, Complex.norm_I, Real.log_one, Complex.ofReal_zero, zero_add,
          Complex.arg_neg_I]
        congr 1; push_cast; ring
      rw [hfac, ofReal_mul_cpow_pos ha (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hq_ne),
        mul_cpow_of_arg_sum (neg_ne_zero.mpr I_ne_zero) hq_ne harg_sum, hnegI, mul_assoc]
    -- Combine `u^{-2} * u^{3/2} * u^{1/2} = 1`
    have hu_cancel : ((u ^ (-2 : ℝ) : ℝ) : ℂ) * (u : ℂ) ^ (3 / 2 : ℂ) * (u : ℂ) ^ (1 / 2 : ℂ) = 1 := by
      have h1 : ((u ^ (-2 : ℝ) : ℝ) : ℂ) = (u : ℂ) ^ (-2 : ℂ) := by
        rw [Complex.ofReal_cpow hu0.le]; push_cast; rfl
      rw [h1, mul_assoc, ← Complex.cpow_add _ _ huC, ← Complex.cpow_add _ _ huC]
      norm_num
    change ((u ^ (-2 : ℝ) : ℝ) : ℂ) *
        starRingEnd ℂ (w0 ^ (-3 / 2 : ℂ) * thetaVec (I * ((u⁻¹ : ℝ) : ℂ)) j) =
      (a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
        ((((1 / a : ℝ) : ℂ) + I * (u : ℂ)) ^ (-3 / 2 : ℂ) *
          thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j))
    rw [map_mul, hconj_θ, hconj_cpow, Complex.ofReal_inv]
    have hθ_inv' : thetaVec (I * (u : ℂ)⁻¹) j =
        (u : ℂ) ^ (1 / 2 : ℂ) * thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j) := by
      simpa [Complex.ofReal_inv] using hθ_inv
    rw [hstep1, hstep2, hθ_inv']
    calc ((u ^ (-2 : ℝ) : ℝ) : ℂ) *
          (((a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
            (((1 / a : ℝ) : ℂ) + I * (u : ℂ)) ^ (-3 / 2 : ℂ) * (u : ℂ) ^ (3 / 2 : ℂ)) *
            ((u : ℂ) ^ (1 / 2 : ℂ) * thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j)))
        = (((u ^ (-2 : ℝ) : ℝ) : ℂ) * (u : ℂ) ^ (3 / 2 : ℂ) * (u : ℂ) ^ (1 / 2 : ℂ)) *
          ((a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
            ((((1 / a : ℝ) : ℂ) + I * (u : ℂ)) ^ (-3 / 2 : ℂ) *
              thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j))) := by ring
      _ = (a : ℂ) ^ (-3 / 2 : ℂ) * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) *
          ((((1 / a : ℝ) : ℂ) + I * (u : ℂ)) ^ (-3 / 2 : ℂ) *
            thetaVec (I * (u : ℂ)) (Fin.cases 0 ![2, 1] j)) := by rw [hu_cancel, one_mul]
  rw [hcongr]
  have hphase : -I * Complex.exp ((3 * Real.pi / 4 : ℝ) * I) =
      thetaInvEighthPhase * I := by
    unfold thetaInvEighthPhase
    have h1 : Complex.exp ((3 * Real.pi / 4 : ℝ) * I) =
        Complex.exp ((Real.pi : ℂ) * I) * Complex.exp (-(Real.pi : ℂ) * I / 4) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, Complex.exp_pi_mul_I]
    ring
  have hUS_idx : (thetaUS (thetaLewisPeriod ((1 / a : ℝ) : ℂ))) j =
      thetaInvEighthPhase *
        (I * ∫ u in Ioi (0 : ℝ), thetaLewisIntegrand ((1 / a : ℝ) : ℂ) (Fin.cases 0 ![2, 1] j) u) := by
    fin_cases j <;> rfl
  simp only [Pi.smul_apply, smul_eq_mul, hUS_idx]
  linear_combination (a : ℂ) ^ (-3 / 2 : ℂ) *
    (∫ u in Ioi (0 : ℝ), thetaLewisIntegrand ((1 / a : ℝ) : ℂ) (Fin.cases 0 ![2, 1] j) u) *
    hphase

/-! ## Exact Twisted Three-Term Lewis–Zagier Functional Equation at `w = 3/2` -/

/-- Global holomorphic primitives exist on the open upper half-plane `{τ : ℂ | 0 < τ.im}`. -/
private theorem isExactOn_upperHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im}) :
    IsExactOn f {τ : ℂ | 0 < τ.im} := by
  have hf_rot : DifferentiableOn ℂ (fun s : ℂ => I * f (I * s)) {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs_pos : 0 < s.re := hs
    have him : 0 < (I * s).im := by simp [hs_pos]
    have hd := (hf (I * s) him).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds him)
    exact ((hd.comp s (differentiableAt_id.const_mul I)).const_mul I).differentiableWithinAt
  obtain ⟨G, hG⟩ := HTGeometry.isExactOn_rightHalfPlane hf_rot
  refine ⟨fun τ => G (-I * τ), fun τ hτ => ?_⟩
  have hτ_pos : 0 < τ.im := hτ
  have hre : 0 < (-I * τ).re := by simp [hτ_pos]
  have h1 := (hG (-I * τ) hre).comp τ ((hasDerivAt_id τ).const_mul (-I))
  refine h1.congr_deriv ?_
  dsimp only
  have hI : I * (-I * τ) = τ := by linear_combination -τ * Complex.I_sq
  rw [hI, show I * f τ * (-I * 1) = -(I ^ 2) * f τ by ring, Complex.I_sq]
  ring

/-- Pointwise pullback identity along the parabolic arc `γ₂(y) = iy / (1 + iy)` (`y > 0`). -/
private theorem gammaTwo_pullback {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) (j : Fin 3) :
    (I / (1 + I * (y : ℂ)) ^ 2) *
      (((a : ℂ) + (I * (y : ℂ)) / (1 + I * (y : ℂ))) ^ (-3 / 2 : ℂ) *
        thetaVec ((I * (y : ℂ)) / (1 + I * (y : ℂ))) j) =
      (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
        thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j) := by
  have ha1 : 0 < a + 1 := by linarith
  have ha1C : ((a + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha1.ne'
  set D : ℂ := 1 + I * (y : ℂ)
  have hD_re : 0 < D.re := by simp [D]
  have hD_im : 0 < D.im := by simp [D, hy]
  have hD_ne : D ≠ 0 := fun h => by simp [h] at hD_re
  set Q : ℂ := ((a / (a + 1) : ℝ) : ℂ) + I * (y : ℂ)
  have ha_div : 0 < a / (a + 1) := div_pos ha ha1
  have hQ_re : 0 < Q.re := by
    dsimp only [Q]; rw [Complex.add_re, Complex.ofReal_re]; simp [ha_div]
  have hQ_im : 0 < Q.im := by
    dsimp only [Q]; rw [Complex.add_im, Complex.ofReal_im]; simp [hy]
  have hQ_ne : Q ≠ 0 := fun h => by simp [h] at hQ_re
  have hfac : (a : ℂ) + (I * (y : ℂ)) / D = ((a + 1 : ℝ) : ℂ) * (Q * D⁻¹) := by
    have hnum : ((a + 1 : ℝ) : ℂ) * Q = (a : ℂ) * D + I * (y : ℂ) := by
      simp only [D, Q]; push_cast
      have hmul : ((a : ℂ) + 1) * ((a : ℂ) / ((a : ℂ) + 1)) = (a : ℂ) :=
        mul_div_cancel₀ _ (by simpa using ha1C)
      linear_combination hmul
    rw [← mul_assoc, hnum, ← div_eq_mul_inv, add_div, mul_div_cancel_right₀ _ hD_ne]
  have harg_QD : Q.arg + D⁻¹.arg ∈ Ioc (-π) π := by
    have h1 := arg_mem_Ioo_first_quad hQ_re hQ_im
    have h2 := arg_inv_mem_Ioo_fourth_quad hD_re hD_im
    exact ⟨by linarith [h1.1, h2.1, Real.pi_pos], by linarith [h1.2, h2.2, Real.pi_pos]⟩
  have hcpow : ((a : ℂ) + (I * (y : ℂ)) / D) ^ (-3 / 2 : ℂ) =
      ((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) * Q ^ (-3 / 2 : ℂ) * D ^ (3 / 2 : ℂ) := by
    rw [hfac, ofReal_mul_cpow_pos ha1 (mul_ne_zero hQ_ne (inv_ne_zero hD_ne)),
      mul_cpow_of_arg_sum hQ_ne (inv_ne_zero hD_ne) harg_QD,
      inv_cpow_of_re_pos hD_re, ← Complex.cpow_neg, mul_assoc]
    congr 2
    norm_num
  have hθ := congrArg (fun v => v j) (thetaVec_TPrime_axis hy)
  simp only [Pi.smul_apply, smul_eq_mul] at hθ
  have hθD : thetaVec ((I * (y : ℂ)) / D) j =
      D ^ (1 / 2 : ℂ) * (thetaUTPrime (thetaVec (I * (y : ℂ))) j) := hθ
  have hD_cancel : D ^ (3 / 2 : ℂ) * D ^ (1 / 2 : ℂ) / D ^ 2 = 1 := by
    rw [← Complex.cpow_add _ _ hD_ne]
    have h2 : (3 / 2 : ℂ) + 1 / 2 = (2 : ℕ) := by norm_num
    rw [h2, Complex.cpow_natCast]
    exact div_self (pow_ne_zero 2 hD_ne)
  change (I / D ^ 2) * (((a : ℂ) + (I * (y : ℂ)) / D) ^ (-3 / 2 : ℂ) *
      thetaVec ((I * (y : ℂ)) / D) j) =
    (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
      thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j)
  rw [hcpow, hθD]
  have hlin : thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j =
      I * Q ^ (-3 / 2 : ℂ) * (thetaUTPrime (thetaVec (I * (y : ℂ))) j) := by
    have heq : (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) =
        (I * Q ^ (-3 / 2 : ℂ)) • thetaVec (I * (y : ℂ)) := by
      ext k; simp [thetaLewisIntegrand, Q, mul_assoc]
    rw [heq, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hlin]
  calc I / D ^ 2 * (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) * Q ^ (-3 / 2 : ℂ) * D ^ (3 / 2 : ℂ) *
        (D ^ (1 / 2 : ℂ) * (thetaUTPrime (thetaVec (I * (y : ℂ))) j)))
      = (D ^ (3 / 2 : ℂ) * D ^ (1 / 2 : ℂ) / D ^ 2) *
        (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
          (I * Q ^ (-3 / 2 : ℂ) * (thetaUTPrime (thetaVec (I * (y : ℂ))) j))) := by ring
    _ = ((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
        (I * Q ^ (-3 / 2 : ℂ) * (thetaUTPrime (thetaVec (I * (y : ℂ))) j)) := by
        rw [hD_cancel, one_mul]

private theorem gammaTwo_eq_re_im (y : ℝ) :
    (I * (y : ℂ)) / (1 + I * (y : ℂ)) =
      ((y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) + I * ((y / (1 + y ^ 2) : ℝ) : ℂ) := by
  have hden : 1 + I * (y : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have h1y : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hden]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
    field_simp [h1y]; ring
  · simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
    field_simp [h1y]; ring

/-- Mean-value bound on a short chord near `0`: for `R ≥ 4` and any `w ∈ segment ℝ (I/R) ((I/R)/(1 + I/R))`,
`(-1/w).im ≥ 1`, `w.re ≥ 0`, and `‖w‖ ≥ 1 / (2R)`. -/
private theorem chord_zero_estimates {R : ℝ} (hR : 4 ≤ R) {w : ℂ}
    (hw : w ∈ segment ℝ (I * ((1 / R : ℝ) : ℂ))
      ((I * ((1 / R : ℝ) : ℂ)) / (1 + I * ((1 / R : ℝ) : ℂ)))) :
    0 ≤ w.re ∧ 1 / (2 * R) ≤ w.im ∧ 1 ≤ (-1 / w).im := by
  set t : ℝ := 1 / R
  have ht0 : 0 < t := one_div_pos.mpr (by linarith)
  have ht4 : t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hR
  set z1 : ℂ := I * (t : ℂ)
  set z2 : ℂ := (I * (t : ℂ)) / (1 + I * (t : ℂ))
  have hz2_re_im : z2.re = t ^ 2 / (1 + t ^ 2) ∧ z2.im = t / (1 + t ^ 2) := by
    dsimp only [z2]
    rw [gammaTwo_eq_re_im t]
    exact ⟨by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero],
      by simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, one_mul, mul_zero, zero_add]⟩
  rw [segment_eq_image] at hw
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw
  dsimp only
  have hw_re : ((1 - θ) • z1 + θ • z2).re = θ * (t ^ 2 / (1 + t ^ 2)) := by
    simp [z1, hz2_re_im.1]
  have hw_im : ((1 - θ) • z1 + θ • z2).im = (1 - θ) * t + θ * (t / (1 + t ^ 2)) := by
    simp [z1, hz2_re_im.2]
  have ht_sq_le : 1 + t ^ 2 ≤ 2 := by nlinarith
  have hz2_im_ge : t / 2 ≤ t / (1 + t ^ 2) :=
    div_le_div_of_nonneg_left ht0.le (by positivity) ht_sq_le
  have him_ge : t / 2 ≤ ((1 - θ) • z1 + θ • z2).im := by
    rw [hw_im]
    have h1 : (1 - θ) * (t / 2) ≤ (1 - θ) * t :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : θ * (t / 2) ≤ θ * (t / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hz2_im_ge hθ0
    linarith
  have him_le : ((1 - θ) • z1 + θ • z2).im ≤ t := by
    rw [hw_im]
    have hle : t / (1 + t ^ 2) ≤ t := div_le_self ht0.le (by nlinarith)
    have h2 : θ * (t / (1 + t ^ 2)) ≤ θ * t := mul_le_mul_of_nonneg_left hle hθ0
    linarith
  have hre_nonneg : 0 ≤ ((1 - θ) • z1 + θ • z2).re := by
    rw [hw_re]; exact mul_nonneg hθ0 (by positivity)
  have hre_le : ((1 - θ) • z1 + θ • z2).re ≤ t ^ 2 := by
    rw [hw_re]
    have h1 : t ^ 2 / (1 + t ^ 2) ≤ t ^ 2 := div_le_self (sq_nonneg t) (by nlinarith)
    nlinarith [sq_nonneg t]
  refine ⟨hre_nonneg, ?_, ?_⟩
  · have : 1 / (2 * R) = t / 2 := by simp [t]; ring
    linarith
  · set u := (1 - θ) • z1 + θ • z2
    have hunorm : Complex.normSq u ≤ 2 * t ^ 2 := by
      rw [Complex.normSq_apply]
      have ht4_sq : t ^ 4 ≤ t ^ 2 := by nlinarith
      nlinarith [hre_nonneg, hre_le, him_ge, him_le]
    have hupos : 0 < Complex.normSq u := by
      rw [Complex.normSq_apply]; nlinarith [him_ge, ht0]
    have hu_inv_im : (-1 / u).im = u.im / Complex.normSq u := by
      rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]; ring
    rw [hu_inv_im, le_div_iff₀ hupos]
    nlinarith

/-- Mean-value bound on a short chord near `1`: for `R ≥ 4` and `w ∈ segment ℝ (1 + I/R) ((I*R)/(1 + I*R))`,
`0 ≤ w.re`, `1 / (2 * R) ≤ w.im`, and `1 ≤ (-1 / (w - 1)).im`. -/
private theorem chord_one_estimates {R : ℝ} (hR : 4 ≤ R) {w : ℂ}
    (hw : w ∈ segment ℝ (1 + I * ((1 / R : ℝ) : ℂ))
      ((I * (R : ℂ)) / (1 + I * (R : ℂ)))) :
    0 ≤ w.re ∧ 1 / (2 * R) ≤ w.im ∧ 1 ≤ (-1 / (w - 1)).im := by
  set t : ℝ := 1 / R
  have ht0 : 0 < t := one_div_pos.mpr (by linarith)
  have ht4 : t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hR
  set u1 : ℂ := I * (t : ℂ)
  set u2 : ℂ := -1 / (1 + I * (R : ℂ))
  have hw2_eq : (I * (R : ℂ)) / (1 + I * (R : ℂ)) = 1 + u2 := by
    have hden : 1 + I * (R : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    change (I * (R : ℂ)) / (1 + I * (R : ℂ)) = 1 + (-1 / (1 + I * (R : ℂ)))
    field_simp [hden]; ring
  rw [hw2_eq, segment_eq_image] at hw
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw
  dsimp only
  set v : ℂ := (1 - θ) • u1 + θ • u2
  have hv_shift : ((1 - θ) • (1 + u1) + θ • (1 + u2)) - 1 = v := by
    simp only [v, Complex.real_smul]; push_cast; ring
  have hu2_re_im : u2.re = -(t ^ 2 / (1 + t ^ 2)) ∧ u2.im = t / (1 + t ^ 2) := by
    have hdenR : 1 + I * (R : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have hR0 : R ≠ 0 := by linarith
    have h1t : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
    have heq : u2 = ((-(t ^ 2 / (1 + t ^ 2)) : ℝ) : ℂ) + I * ((t / (1 + t ^ 2) : ℝ) : ℂ) := by
      change -1 / (1 + I * (R : ℂ)) = _
      rw [div_eq_iff hdenR]
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.one_im, Complex.neg_re]
        simp only [t]; field_simp [hR0]; ring
      · simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.one_im, Complex.neg_im]
        simp only [t]; field_simp [hR0]; ring
    rw [heq]
    exact ⟨by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero],
      by simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, one_mul, mul_zero, zero_add]⟩
  have hv_re : v.re = -(θ * (t ^ 2 / (1 + t ^ 2))) := by simp [v, u1, hu2_re_im.1]
  have hv_im : v.im = (1 - θ) * t + θ * (t / (1 + t ^ 2)) := by simp [v, u1, hu2_re_im.2]
  have ht_sq_le : 1 + t ^ 2 ≤ 2 := by nlinarith
  have hu2_im_ge : t / 2 ≤ t / (1 + t ^ 2) :=
    div_le_div_of_nonneg_left ht0.le (by positivity) ht_sq_le
  have him_ge : t / 2 ≤ v.im := by
    rw [hv_im]
    linarith [mul_le_mul_of_nonneg_left (by linarith : t / 2 ≤ t) (by linarith : 0 ≤ 1 - θ),
      mul_le_mul_of_nonneg_left hu2_im_ge hθ0]
  have him_le : v.im ≤ t := by
    rw [hv_im]
    have hle : t / (1 + t ^ 2) ≤ t := div_le_self ht0.le (by nlinarith)
    linarith [mul_le_mul_of_nonneg_left hle hθ0]
  have hvre_abs : |v.re| ≤ t ^ 2 := by
    rw [hv_re, abs_neg, abs_of_nonneg (mul_nonneg hθ0 (by positivity))]
    have h1 : t ^ 2 / (1 + t ^ 2) ≤ t ^ 2 := div_le_self (sq_nonneg t) (by nlinarith)
    nlinarith [sq_nonneg t]
  have hw_eq : (1 - θ) • (1 + u1) + θ • (1 + u2) = 1 + v := by
    rw [← hv_shift]; ring
  rw [hv_shift, hw_eq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.one_re]
    have := neg_abs_le v.re
    linarith
  · simp only [Complex.add_im, Complex.one_im, zero_add]
    have : 1 / (2 * R) = t / 2 := by simp [t]; ring
    linarith
  · have hvnorm : Complex.normSq v ≤ 2 * t ^ 2 := by
      rw [Complex.normSq_apply]
      have hsq : v.re ^ 2 ≤ (t ^ 2) ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg (sq_nonneg t)])
      nlinarith [him_ge, him_le]
    have hvpos : 0 < Complex.normSq v := by
      rw [Complex.normSq_apply]; nlinarith [him_ge, ht0]
    have hv_inv_im : (-1 / v).im = v.im / Complex.normSq v := by
      rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]; ring
    rw [hv_inv_im, le_div_iff₀ hvpos]
    nlinarith

private theorem tendsto_intervalIntegral_inv_to_Ioi {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun R : ℝ => ∫ y in (1 / R)..R, f y) atTop (𝓝 (∫ y in Ioi (0 : ℝ), f y)) := by
  let F : ℝ → ℝ → ℂ := fun R y => (Ioc (1 / R) R).indicator f y
  have h_eq : (fun R : ℝ => ∫ y in (1 / R)..R, f y) =ᶠ[atTop]
      fun R : ℝ => ∫ y in Ioi (0 : ℝ), F R y := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := by linarith
    have hle : 1 / R ≤ R := (div_le_one_of_le₀ hR hR0.le).trans hR
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    have hinter : Ioi (0 : ℝ) ∩ Ioc (1 / R) R = Ioc (1 / R) R := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      exact ⟨fun h => h.2, fun h => ⟨(one_div_pos.mpr hR0).trans h.1, h⟩⟩
    rw [hinter]
  refine Tendsto.congr' h_eq.symm ?_
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun _ =>
      hf.aestronglyMeasurable.indicator measurableSet_Ioc
  · exact Eventually.of_forall fun R =>
      Eventually.of_forall fun y => by
        dsimp only [F]
        rw [Set.indicator_apply]
        split_ifs <;> simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max (1 / y) y)] with R hR
    have h1 : 1 / y < R := (le_max_left _ _).trans_lt hR
    have h2 : y ≤ R := ((le_max_right _ _).trans_lt hR).le
    have hR0 : 0 < R := hy0.trans_le h2
    have hinv : 1 / R < y := by
      rw [div_lt_iff₀ hR0]
      have hyR : 1 < R * y := (div_lt_iff₀ hy0).mp h1
      linarith
    dsimp only [F]
    exact (Set.indicator_of_mem (mem_Ioc.mpr ⟨hinv, h2⟩) f).symm

/-- **Twisted Three-Term Lewis–Zagier Functional Equation in Weight `½` (`w = 3/2`, `λ = 3/16`).**
For every `a > 0`,
`Ψ_ϑ(a) = U_T Ψ_ϑ(a + 1) + (a + 1)^{-3/2} U_{T'} Ψ_ϑ(a / (a + 1))`. -/
theorem thetaLewisPeriod_three_term {a : ℝ} (ha : 0 < a) :
    thetaLewisPeriod (a : ℂ) =
      thetaUT (thetaLewisPeriod ((a + 1 : ℝ) : ℂ)) +
        (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ)) •
          thetaUTPrime (thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ)) := by
  ext j
  set g : ℂ → ℂ := fun τ => ((a : ℂ) + τ) ^ (-3 / 2 : ℂ) * thetaVec τ j
  have hg_diff : DifferentiableOn ℂ g {τ : ℂ | 0 < τ.im} := by
    intro τ hτ
    have hτ_im : 0 < τ.im := hτ
    have hslit : (a : ℂ) + τ ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (by simp; exact hτ_im.ne'))
    have hcp : DifferentiableAt ℂ (fun w : ℂ => ((a : ℂ) + w) ^ (-3 / 2 : ℂ)) τ :=
      (differentiableAt_id.const_add (a : ℂ)).cpow_const hslit
    exact (hcp.mul (differentiableAt_thetaVec hτ_im j)).differentiableWithinAt
  obtain ⟨P, hP⟩ := isExactOn_upperHalfPlane hg_diff
  -- Truncated integrals on `[1/R, R]` expressed via the global primitive `P`
  let γ0 : ℝ → ℂ := fun y => I * (y : ℂ)
  let γ1 : ℝ → ℂ := fun y => 1 + I * (y : ℂ)
  let γ2 : ℝ → ℂ := fun y => (I * (y : ℂ)) / (1 + I * (y : ℂ))
  have hFTC0 : ∀ R : ℝ, 4 ≤ R →
      (∫ y in (1 / R)..R, I * thetaLewisIntegrand (a : ℂ) j y) = P (γ0 R) - P (γ0 (1 / R)) := by
    intro R hR
    have hle : 1 / R ≤ R := by
      have : 1 / R ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      linarith
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => P (γ0 y))
      (fun y hy => ?_) ?_
    · rw [uIcc_of_le hle] at hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      have hd := (hP (γ0 y) (by simp [γ0, hy0])).comp y
        (((hasDerivAt_id y).ofReal_comp).const_mul I)
      refine hd.congr_deriv ?_
      simp [g, γ0, thetaLewisIntegrand]; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      exact (continuousOn_const.mul
        (continuousOn_thetaLewisIntegrand (by simp [ha]) j)).mono
        (fun y hy => lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1)
  have hFTC1 : ∀ R : ℝ, 4 ≤ R →
      (∫ y in (1 / R)..R, thetaUT (fun k => I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) k y) j) =
        P (γ1 R) - P (γ1 (1 / R)) := by
    intro R hR
    have hle : 1 / R ≤ R := by
      have : 1 / R ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      linarith
    have hpull : ∀ y : ℝ,
        thetaUT (fun k => I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) k y) j = I * g (γ1 y) := by
      intro y
      have heq_vec : (fun k => I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) k y) =
          (I * (((a + 1 : ℝ) : ℂ) + I * (y : ℂ)) ^ (-3 / 2 : ℂ)) • thetaVec (I * (y : ℂ)) := by
        ext k; simp [thetaLewisIntegrand, mul_assoc]
      rw [heq_vec, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, ← thetaVec_add_one]
      simp only [g, γ1]; push_cast
      have h1 : (a : ℂ) + 1 + I * (y : ℂ) = (a : ℂ) + (1 + I * (y : ℂ)) := by ring
      have h2 : I * (y : ℂ) + 1 = 1 + I * (y : ℂ) := by ring
      rw [h1, h2]; ring
    simp_rw [hpull]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => P (γ1 y))
      (fun y hy => ?_) ?_
    · rw [uIcc_of_le hle] at hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      have hd := (hP (γ1 y) (by simp [γ1, hy0])).comp y
        ((((hasDerivAt_id y).ofReal_comp).const_mul I).const_add 1)
      refine hd.congr_deriv ?_; push_cast; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      have hc_γ1 : ContinuousAt γ1 y :=
        ((((hasDerivAt_id y).ofReal_comp).const_mul I).const_add 1).continuousAt
      exact (continuousAt_const.mul (ContinuousAt.comp (f := γ1)
        (((hg_diff (γ1 y) (by simp [γ1, hy0])).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
            (by simp [γ1, hy0]))).continuousAt)
        hc_γ1)).continuousWithinAt
  have hFTC2 : ∀ R : ℝ, 4 ≤ R →
      (∫ y in (1 / R)..R, (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
        thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j)) =
        P (γ2 R) - P (γ2 (1 / R)) := by
    intro R hR
    have hle : 1 / R ≤ R := by
      have : 1 / R ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      linarith
    have hγ2_im : ∀ y : ℝ, 0 < y → 0 < (γ2 y).im := by
      intro y hy
      dsimp only [γ2]
      rw [gammaTwo_eq_re_im y]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, one_mul, mul_zero, zero_add]
      positivity
    have hγ2_deriv : ∀ y : ℝ, HasDerivAt γ2 (I / (1 + I * (y : ℂ)) ^ 2) y := by
      intro y
      have hden : 1 + I * (y : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hd1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) (I * 1) y :=
        ((hasDerivAt_id y).ofReal_comp).const_mul I
      have hd2 : HasDerivAt (fun t : ℝ => 1 + I * (t : ℂ)) (I * 1) y := hd1.const_add 1
      refine (hd1.div hd2 hden).congr_deriv ?_
      ring
    refine (intervalIntegral.integral_congr fun y hy => ?_).trans
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y => P (γ2 y))
        (f' := fun y => (I / (1 + I * (y : ℂ)) ^ 2) * g (γ2 y))
        (fun y hy => ?_) ?_)
    · rw [uIcc_of_le hle] at hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      exact (gammaTwo_pullback ha hy0 j).symm
    · rw [uIcc_of_le hle] at hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      have hd := (hP (γ2 y) (hγ2_im y hy0)).comp y (hγ2_deriv y)
      refine hd.congr_deriv ?_; simp [g, γ2]; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr (by linarith)) hy.1
      have hc1 : ContinuousAt (fun t : ℝ => I / (1 + I * (t : ℂ)) ^ 2) y := by
        have hden : (1 + I * (y : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 fun h => by
          have := congrArg Complex.re h; simp at this
        fun_prop (disch := exact hden)
      have hc2 : ContinuousAt (fun t : ℝ => g (γ2 t)) y :=
        ContinuousAt.comp (f := γ2)
          (((hg_diff (γ2 y) (hγ2_im y hy0)).differentiableAt
            ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
              (hγ2_im y hy0))).continuousAt)
          (hγ2_deriv y).continuousAt
      exact (hc1.mul hc2).continuousWithinAt
  -- Defect 1: `P(γ0 R) - P(γ1 R) → 0`
  have hdef_top : Tendsto (fun R : ℝ => P (γ0 R) - P (γ1 R)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun R : ℝ => thetaCuspBound * R ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num]
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul thetaCuspBound
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
    have hseg_sub : ∀ w ∈ segment ℝ (γ1 R) (γ0 R), 1 ≤ w.im := by
      intro w hw
      rw [segment_eq_image] at hw
      obtain ⟨θ, _, rfl⟩ := hw
      dsimp only
      have him : ((1 - θ) • γ1 R + θ • γ0 R).im = R := by simp [γ0, γ1]; ring
      rw [him]; linarith
    have hbound_seg : ∀ w ∈ segment ℝ (γ1 R) (γ0 R),
        ‖g w‖ ≤ thetaCuspBound * R ^ (-3 / 2 : ℝ) := by
      intro w hw
      have him1 : 1 ≤ w.im := hseg_sub w hw
      have himR : w.im = R := by
        rw [segment_eq_image] at hw
        obtain ⟨θ, _, rfl⟩ := hw
        simp [γ0, γ1]; ring
      have hgeR : R ≤ ‖(a : ℂ) + w‖ := by
        have := Complex.im_le_norm ((a : ℂ) + w); simpa [himR] using this
      have hne : (a : ℂ) + w ≠ 0 := fun h => by
        have := congrArg Complex.im h; simp [himR] at this; linarith
      have hcp : ‖((a : ℂ) + w) ^ (-3 / 2 : ℂ)‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact norm_cpow_ofReal _ hne _
      calc ‖g w‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) * ‖thetaVec w j‖ := by
            simp [g, hcp]
        _ ≤ R ^ (-3 / 2 : ℝ) * thetaCuspBound :=
            mul_le_mul (Real.rpow_le_rpow_of_nonpos (by linarith) hgeR (by norm_num))
              (norm_thetaVec_le_of_one_le_im him1 j) (norm_nonneg _)
              (Real.rpow_nonneg (by linarith) _)
        _ = thetaCuspBound * R ^ (-3 / 2 : ℝ) := mul_comm _ _
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := P) (f' := g) (s := segment ℝ (γ1 R) (γ0 R))
      (fun w hw => (hP w (show 0 < w.im from lt_of_lt_of_le one_pos (hseg_sub w hw))).hasDerivWithinAt)
      hbound_seg (convex_segment _ _) (right_mem_segment _ _ _) (left_mem_segment _ _ _)
    have hlen : ‖γ0 R - γ1 R‖ = 1 := by simp [γ0, γ1]
    rw [norm_sub_rev (P (γ1 R)), norm_sub_rev (γ1 R), hlen, mul_one] at hmvt
    exact hmvt
  -- Defect 2: `P(γ2 (1/R)) - P(γ0 (1/R)) → 0`
  have hdef_zero : Tendsto (fun R : ℝ => P (γ2 (1 / R)) - P (γ0 (1 / R))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    set C0 := a ^ (-3 / 2 : ℝ) * thetaCuspBound * (2 : ℝ) ^ (1 / 2 : ℝ)
    have h0 : Tendsto (fun R : ℝ => C0 * R ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num]
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul C0
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
    have hbound_seg : ∀ w ∈ segment ℝ (γ0 (1 / R)) (γ2 (1 / R)),
        ‖g w‖ ≤ C0 * R ^ (1 / 2 : ℝ) := by
      intro w hw
      obtain ⟨hw_re, hw_im, hinv⟩ := chord_zero_estimates hR hw
      have hw_im_pos : 0 < w.im := lt_of_lt_of_le (by positivity) hw_im
      have hge_a : a ≤ ‖(a : ℂ) + w‖ := by
        have := Complex.re_le_norm ((a : ℂ) + w); simp at this; linarith
      have hne : (a : ℂ) + w ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hcp : ‖((a : ℂ) + w) ^ (-3 / 2 : ℂ)‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact norm_cpow_ofReal _ hne _
      have hw_norm_ge : 1 / (2 * R) ≤ ‖w‖ := hw_im.trans (Complex.im_le_norm w)
      have hw_rpow : ‖w‖ ^ (-1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) := by
        calc ‖w‖ ^ (-1 / 2 : ℝ) ≤ (1 / (2 * R)) ^ (-1 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hw_norm_ge (by norm_num)
          _ = (2 * R) ^ (1 / 2 : ℝ) := by
              rw [one_div, Real.inv_rpow (by positivity),
                show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
                Real.rpow_neg (by positivity), inv_inv]
          _ = (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) :=
              Real.mul_rpow (by norm_num) (by linarith)
      calc ‖g w‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) * ‖thetaVec w j‖ := by
            simp [g, hcp]
        _ ≤ a ^ (-3 / 2 : ℝ) * (thetaCuspBound * ‖w‖ ^ (-1 / 2 : ℝ)) :=
            mul_le_mul (Real.rpow_le_rpow_of_nonpos ha hge_a (by norm_num))
              (norm_thetaVec_le_of_inv_im hw_im_pos hinv j) (norm_nonneg _)
              (Real.rpow_nonneg ha.le _)
        _ ≤ a ^ (-3 / 2 : ℝ) * (thetaCuspBound * ((2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hw_rpow thetaCuspBound_pos.le)
              (Real.rpow_nonneg ha.le _)
        _ = C0 * R ^ (1 / 2 : ℝ) := by simp only [C0]; ring
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := P) (f' := g) (s := segment ℝ (γ0 (1 / R)) (γ2 (1 / R)))
      (fun w hw => (hP w (show 0 < w.im from lt_of_lt_of_le (by positivity) (chord_zero_estimates hR hw).2.1)).hasDerivWithinAt)
      hbound_seg (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    have hlen : ‖γ2 (1 / R) - γ0 (1 / R)‖ ≤ R ^ (-2 : ℝ) := by
      have hden : 1 + I * ((1 / R : ℝ) : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hdiff : γ2 (1 / R) - γ0 (1 / R) =
          -((I * ((1 / R : ℝ) : ℂ)) ^ 2) / (1 + I * ((1 / R : ℝ) : ℂ)) := by
        change (I * ((1 / R : ℝ) : ℂ)) / (1 + I * ((1 / R : ℝ) : ℂ)) - I * ((1 / R : ℝ) : ℂ) = _
        field_simp [hden]; ring
      have hden_ge : 1 ≤ ‖1 + I * ((1 / R : ℝ) : ℂ)‖ := by
        have := Complex.re_le_norm (1 + I * ((1 / R : ℝ) : ℂ)); simpa using this
      rw [hdiff, norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith))]
      calc (1 / R) ^ 2 / ‖1 + I * ((1 / R : ℝ) : ℂ)‖ ≤ (1 / R) ^ 2 / 1 :=
            div_le_div_of_nonneg_left (sq_nonneg _) one_pos hden_ge
        _ = R ^ (-2 : ℝ) := by
            rw [div_one, one_div, inv_pow, Real.rpow_neg (by linarith), Real.rpow_two]
    have hC0_nonneg : 0 ≤ C0 := mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ha.le _) thetaCuspBound_pos.le)
      (Real.rpow_nonneg (by norm_num) _)
    have hCR0 : 0 ≤ C0 * R ^ (1 / 2 : ℝ) :=
      mul_nonneg hC0_nonneg (Real.rpow_nonneg (by linarith) _)
    calc ‖P (γ2 (1 / R)) - P (γ0 (1 / R))‖
        ≤ (C0 * R ^ (1 / 2 : ℝ)) * R ^ (-2 : ℝ) :=
          hmvt.trans (mul_le_mul_of_nonneg_left hlen hCR0)
      _ = C0 * R ^ (-3 / 2 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < R)]; norm_num
  -- Defect 3: `P(γ1 (1/R)) - P(γ2 R) → 0`
  have hdef_one : Tendsto (fun R : ℝ => P (γ1 (1 / R)) - P (γ2 R)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    set C1 := a ^ (-3 / 2 : ℝ) * thetaCuspBound * (2 : ℝ) ^ (1 / 2 : ℝ)
    have h0 : Tendsto (fun R : ℝ => C1 * R ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num]
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul C1
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
    have hbound_seg : ∀ w ∈ segment ℝ (γ1 (1 / R)) (γ2 R),
        ‖g w‖ ≤ C1 * R ^ (1 / 2 : ℝ) := by
      intro w hw
      obtain ⟨hw_re, hw_im, hinv⟩ := chord_one_estimates hR hw
      have hw1_im_pos : 0 < (w - 1).im := by
        simp; linarith [hw_im, one_div_pos.mpr (by linarith : 0 < 2 * R)]
      have hge_a : a ≤ ‖(a : ℂ) + w‖ := by
        have := Complex.re_le_norm ((a : ℂ) + w); simp at this; linarith
      have hne : (a : ℂ) + w ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hcp : ‖((a : ℂ) + w) ^ (-3 / 2 : ℂ)‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact norm_cpow_ofReal _ hne _
      have hθ_shift : ‖thetaVec w j‖ ≤ thetaCuspBound * ‖w - 1‖ ^ (-1 / 2 : ℝ) := by
        have hw_eq : w = (w - 1) + 1 := by ring
        have hT := congrArg (fun v => ‖v j‖) (thetaVec_add_one (w - 1))
        rw [← hw_eq] at hT
        rw [hT]
        fin_cases j
        · simpa [thetaUT] using norm_thetaVec_le_of_inv_im hw1_im_pos hinv 1
        · simpa [thetaUT] using norm_thetaVec_le_of_inv_im hw1_im_pos hinv 0
        · change ‖thetaEighthPhase * thetaVec (w - 1) 2‖ ≤ _
          rw [norm_mul, norm_thetaEighthPhase, one_mul]
          exact norm_thetaVec_le_of_inv_im hw1_im_pos hinv 2
      have hw1_norm_ge : 1 / (2 * R) ≤ ‖w - 1‖ := by
        have him : (w - 1).im = w.im := by simp
        exact hw_im.trans (him ▸ Complex.im_le_norm (w - 1))
      have hw1_rpow : ‖w - 1‖ ^ (-1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) := by
        calc ‖w - 1‖ ^ (-1 / 2 : ℝ) ≤ (1 / (2 * R)) ^ (-1 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hw1_norm_ge (by norm_num)
          _ = (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) := by
              rw [one_div, Real.inv_rpow (by positivity),
                show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
                Real.rpow_neg (by positivity), inv_inv,
                Real.mul_rpow (by norm_num) (by linarith)]
      calc ‖g w‖ = ‖(a : ℂ) + w‖ ^ (-3 / 2 : ℝ) * ‖thetaVec w j‖ := by
            simp [g, hcp]
        _ ≤ a ^ (-3 / 2 : ℝ) * (thetaCuspBound * ((2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ))) :=
            mul_le_mul (Real.rpow_le_rpow_of_nonpos ha hge_a (by norm_num))
              (hθ_shift.trans (mul_le_mul_of_nonneg_left hw1_rpow thetaCuspBound_pos.le))
              (norm_nonneg _) (Real.rpow_nonneg ha.le _)
        _ = C1 * R ^ (1 / 2 : ℝ) := by simp only [C1]; ring
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := P) (f' := g) (s := segment ℝ (γ2 R) (γ1 (1 / R)))
      (fun w hw => by
        rw [segment_symm] at hw
        exact (hP w (show 0 < w.im from lt_of_lt_of_le (by positivity) (chord_one_estimates hR hw).2.1)).hasDerivWithinAt)
      (fun w hw => by rw [segment_symm] at hw; exact hbound_seg w hw)
      (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    have hlen : ‖γ1 (1 / R) - γ2 R‖ ≤ R ^ (-2 : ℝ) := by
      have hden : 1 + I * (R : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      have hdiff : γ1 (1 / R) - γ2 R = (I * ((1 / R : ℝ) : ℂ)) / (1 + I * (R : ℂ)) := by
        change 1 + I * ((1 / R : ℝ) : ℂ) - (I * (R : ℂ)) / (1 + I * (R : ℂ)) = _
        have hmulR : ((1 / R : ℝ) : ℂ) * (R : ℂ) = 1 := by push_cast; exact one_div_mul_cancel hR0
        field_simp [hden]
        calc (1 + I * ((1 / R : ℝ) : ℂ)) * (1 + I * (R : ℂ)) - I * (R : ℂ)
            = 1 + I ^ 2 * (((1 / R : ℝ) : ℂ) * (R : ℂ)) + I * ((1 / R : ℝ) : ℂ) := by ring
          _ = I * ((1 / R : ℝ) : ℂ) := by rw [hmulR, Complex.I_sq]; ring
      have hden_ge : R ≤ ‖1 + I * (R : ℂ)‖ := by
        have := Complex.im_le_norm (1 + I * (R : ℂ)); simpa using this
      rw [hdiff, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith : 0 < R))]
      calc (1 / R) / ‖1 + I * (R : ℂ)‖ ≤ (1 / R) / R :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hden_ge
        _ = R ^ (-2 : ℝ) := by
            rw [div_div, ← sq, one_div, Real.rpow_neg (by linarith), Real.rpow_two]
    have hC1_nonneg : 0 ≤ C1 := mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ha.le _) thetaCuspBound_pos.le)
      (Real.rpow_nonneg (by norm_num) _)
    have hCR1 : 0 ≤ C1 * R ^ (1 / 2 : ℝ) :=
      mul_nonneg hC1_nonneg (Real.rpow_nonneg (by linarith) _)
    calc ‖P (γ1 (1 / R)) - P (γ2 R)‖
        ≤ (C1 * R ^ (1 / 2 : ℝ)) * R ^ (-2 : ℝ) :=
          hmvt.trans (mul_le_mul_of_nonneg_left hlen hCR1)
      _ = C1 * R ^ (-3 / 2 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < R)]; norm_num
  -- Pass `R → +∞` on all three truncated improper integrals
  have hlim_base : ∀ (z : ℂ), 0 < z.re → ∀ (k : Fin 3),
      Tendsto (fun R : ℝ => ∫ y in (1 / R)..R, I * thetaLewisIntegrand z k y)
        atTop (𝓝 (thetaLewisPeriod z k)) := by
    intro z hz k
    have hint := (integrableOn_thetaLewisIntegrand hz k).const_mul I
    simpa only [thetaLewisPeriod, integral_const_mul] using
      tendsto_intervalIntegral_inv_to_Ioi hint
  have hlim0 : Tendsto (fun R : ℝ => ∫ y in (1 / R)..R, I * thetaLewisIntegrand (a : ℂ) j y)
      atTop (𝓝 (thetaLewisPeriod (a : ℂ) j)) :=
    hlim_base (a : ℂ) (by simp [ha]) j
  have hlim1 : Tendsto (fun R : ℝ =>
      ∫ y in (1 / R)..R, thetaUT (fun k => I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) k y) j)
      atTop (𝓝 ((thetaUT (thetaLewisPeriod ((a + 1 : ℝ) : ℂ))) j)) := by
    have ha1 : 0 < ((a + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
    fin_cases j
    · exact hlim_base _ ha1 1
    · exact hlim_base _ ha1 0
    · change Tendsto (fun R : ℝ => ∫ y in (1 / R)..R,
          thetaEighthPhase * (I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) 2 y))
        atTop (𝓝 (thetaEighthPhase * thetaLewisPeriod ((a + 1 : ℝ) : ℂ) 2))
      have hp : (fun R : ℝ => ∫ y in (1 / R)..R,
          thetaEighthPhase * (I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) 2 y)) =
        fun R : ℝ => thetaEighthPhase *
          ∫ y in (1 / R)..R, I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) 2 y := by
        ext R; exact intervalIntegral.integral_const_mul _ _
      rw [hp]
      exact (hlim_base _ ha1 2).const_mul thetaEighthPhase
  have hlim2 : Tendsto (fun R : ℝ =>
      ∫ y in (1 / R)..R, (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
        thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j))
      atTop (𝓝 ((((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ)) *
        (thetaUTPrime (thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ))) j)) := by
    have hqa : 0 < ((a / (a + 1) : ℝ) : ℂ).re := by
      rw [Complex.ofReal_re]; exact div_pos ha (by linarith)
    set c := ((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ)
    fin_cases j
    · change Tendsto (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 2 y))
        atTop (𝓝 (c * thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ) 2))
      have hp : (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 2 y)) =
        fun R : ℝ => c *
          ∫ y in (1 / R)..R, I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 2 y := by
        ext R; exact intervalIntegral.integral_const_mul _ _
      rw [hp]
      exact (hlim_base _ hqa 2).const_mul c
    · change Tendsto (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (thetaInvEighthPhase * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 1 y)))
        atTop (𝓝 (c * (thetaInvEighthPhase * thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ) 1)))
      have hp : (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (thetaInvEighthPhase * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 1 y))) =
        fun R : ℝ => c * (thetaInvEighthPhase *
          ∫ y in (1 / R)..R, I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 1 y) := by
        ext R
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [hp]
      exact ((hlim_base _ hqa 1).const_mul thetaInvEighthPhase).const_mul c
    · change Tendsto (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 0 y))
        atTop (𝓝 (c * thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ) 0))
      have hp : (fun R : ℝ => ∫ y in (1 / R)..R,
          c * (I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 0 y)) =
        fun R : ℝ => c *
          ∫ y in (1 / R)..R, I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) 0 y := by
        ext R; exact intervalIntegral.integral_const_mul _ _
      rw [hp]
      exact (hlim_base _ hqa 0).const_mul c
  have hdiff_tendsto : Tendsto (fun R : ℝ =>
      (∫ y in (1 / R)..R, I * thetaLewisIntegrand (a : ℂ) j y) -
      (∫ y in (1 / R)..R, thetaUT (fun k => I * thetaLewisIntegrand ((a + 1 : ℝ) : ℂ) k y) j) -
      (∫ y in (1 / R)..R, (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ) *
        thetaUTPrime (fun k => I * thetaLewisIntegrand ((a / (a + 1) : ℝ) : ℂ) k y) j)))
      atTop (𝓝 0) := by
    have hsum := (hdef_top.add hdef_one).add hdef_zero
    simp only [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
    rw [hFTC0 R hR, hFTC1 R hR, hFTC2 R hR]
    ring
  have hlim_diff := (hlim0.sub hlim1).sub hlim2
  have heq0 := tendsto_nhds_unique hlim_diff hdiff_tendsto
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination heq0

/-! ## Complete Weight-`½` Horizon Calibration Package -/

/-- Complete calibration theorem for weight `½` (`λ = 3/16`, spectral parameter `w = 2s = 3/2`):
1. `y^{1/4} θ` is a non-zero `L²` residual eigenfunction of `Δ_{1/2}` on `Γ₀(4)` with unitary
   theta multiplier `j_ϑ` at exceptional eigenvalue `λ = (3/4)(1 - 3/4) = 3/16 < 1/4`.
2. `Ψ_ϑ` is holomorphic on `{Re z > 0}`, strictly non-zero on `(0, ∞)`, vanishes at `+∞`
   (not a coboundary), obeys anti-unitary `S`-reciprocity, and satisfies the unitary-multiplier
   three-term Lewis–Zagier equation at `w = 3/2`.
3. Weight-`½` Eisenstein constant-term arithmetic `(μ * N(0)) = phiSq` is non-negative and
   supported strictly on squares (`phiSq c = 0` off squares), with no odd-order Möbius sign. -/
theorem weight_half_horizon_calibration :
    ((3 / 4 : ℝ) * (1 - 3 / 4) = 3 / 16 ∧ (3 / 16 : ℝ) < 1 / 4) ∧
    (∀ v : Fin 3 → ℂ,
      vecNormSq (thetaUT v) = vecNormSq v ∧
      vecNormSq (thetaUS v) = vecNormSq v ∧
      vecNormSq (thetaUTPrime v) = vecNormSq v) ∧
    (∀ j : Fin 3, DifferentiableOn ℂ (fun z => thetaLewisPeriod z j) {z : ℂ | 0 < z.re}) ∧
    (∀ a : ℝ, 0 < a → 0 < (thetaLewisPeriod (a : ℂ) 0).re) ∧
    (¬ ∃ v : Fin 3 → ℂ, ∀ a : ℝ, 0 < a →
      thetaLewisPeriod (a : ℂ) = v - ((a : ℂ) ^ (-3 / 2 : ℂ)) • thetaUT v) ∧
    (∀ a : ℝ, 0 < a →
      (fun j => starRingEnd ℂ (thetaLewisPeriod (a : ℂ) j)) =
        ((a : ℂ) ^ (-3 / 2 : ℂ)) • thetaUS (thetaLewisPeriod ((1 / a : ℝ) : ℂ))) ∧
    (∀ a : ℝ, 0 < a →
      thetaLewisPeriod (a : ℂ) =
        thetaUT (thetaLewisPeriod ((a + 1 : ℝ) : ℂ)) +
          (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ)) •
            thetaUTPrime (thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ))) ∧
    (RHTower.HalfWeight.fN 0 = RHTower.HalfWeight.phiSq ∧
      ∀ c : ℕ, ¬ IsSquare c → RHTower.HalfWeight.phiSq c = 0) := by
  refine ⟨⟨by norm_num, by norm_num⟩,
    fun v => ⟨vecNormSq_thetaUT v, vecNormSq_thetaUS v, vecNormSq_thetaUTPrime v⟩,
    differentiableOn_thetaLewisPeriod,
    fun _ ha => thetaLewisPeriod_zero_re_pos ha,
    not_exists_coboundary_eq_thetaLewisPeriod,
    fun _ ha => thetaLewisPeriod_S_reciprocity ha,
    fun _ ha => thetaLewisPeriod_three_term ha,
    ⟨RHTower.HalfWeight.fN_zero_eq, fun c hc => ?_⟩⟩
  rw [RHTower.HalfWeight.phiSq_apply, if_neg hc]

end GaloisForLFunctions.RingdownOfTheCubicCover

end
