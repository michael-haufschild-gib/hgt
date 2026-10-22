import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalShiftedXi
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Suzuki's canonical shifted-Xi ratio

This module introduces the literal functions `E^omega` and `Theta_omega` from Suzuki (2012),
equations (105_1)--(108).  Lean functions use total division, so the printed meromorphic identity
`Theta_omega(z) Theta_omega(-z) = 1` cannot honestly be stated pointwise at a pole: `0 / 0` is
defined as zero in the ambient field.  We therefore prove both the unconditional numerator/
denominator reflection identities and the exact quotient identity on its regular locus.  This is
the pointwise representative of the paper's meromorphic identity, without silently filling poles.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- Suzuki's literal `E^omega(z) = xi(1/2 + omega - iz)`. -/
def suzukiCanonicalE (omega : ℝ) (z : ℂ) : ℂ :=
  xi (1 / 2 + (omega : ℂ) - z * I)

/-- Schwarz reflection of Suzuki's `E^omega`. -/
def suzukiCanonicalESharp (omega : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (suzukiCanonicalE omega ((starRingEnd ℂ) z))

/-- Suzuki's literal meromorphic ratio, equation (105_1). -/
def suzukiCanonicalTheta (omega : ℝ) (z : ℂ) : ℂ :=
  xi (1 / 2 - (omega : ℂ) - z * I) /
    xi (1 / 2 + (omega : ℂ) - z * I)

/-- Centered-Xi coordinate for `E^omega`. -/
theorem suzukiCanonicalE_eq_XiC_shift (omega : ℝ) (z : ℂ) :
    suzukiCanonicalE omega z = XiC (-z - (omega : ℂ) * I) := by
  rw [suzukiCanonicalE, XiC]
  congr 1
  rw [sub_mul, mul_assoc, Complex.I_mul_I]
  ring

/-- The Schwarz reflection is the opposite spectral argument. -/
theorem suzukiCanonicalESharp_eq_E_neg (omega : ℝ) (z : ℂ) :
    suzukiCanonicalESharp omega z = suzukiCanonicalE omega (-z) := by
  rw [suzukiCanonicalESharp, suzukiCanonicalE, suzukiCanonicalE, ← xi_conj]
  congr 1
  apply Complex.ext
  · simp
  · simp

/-- Functional equation form of the numerator in equation (105_1). -/
theorem suzukiCanonicalE_neg_eq_thetaNumerator (omega : ℝ) (z : ℂ) :
    suzukiCanonicalE omega (-z) =
      xi (1 / 2 - (omega : ℂ) - z * I) := by
  have h := xi_one_sub (1 / 2 - (omega : ℂ) - z * I)
  rw [suzukiCanonicalE]
  rw [← h]
  congr 1
  ring

/-- The source ratio is exactly `E sharp / E`. -/
theorem suzukiCanonicalTheta_eq_ESharp_div_E (omega : ℝ) (z : ℂ) :
    suzukiCanonicalTheta omega z =
      suzukiCanonicalESharp omega z / suzukiCanonicalE omega z := by
  rw [suzukiCanonicalTheta, suzukiCanonicalESharp_eq_E_neg,
    suzukiCanonicalE_neg_eq_thetaNumerator, suzukiCanonicalE]

/-- Equivalent opposite-argument quotient form. -/
theorem suzukiCanonicalTheta_eq_E_neg_div_E (omega : ℝ) (z : ℂ) :
    suzukiCanonicalTheta omega z =
      suzukiCanonicalE omega (-z) / suzukiCanonicalE omega z := by
  rw [suzukiCanonicalTheta_eq_ESharp_div_E,
    suzukiCanonicalESharp_eq_E_neg]

theorem differentiable_suzukiCanonicalE (omega : ℝ) :
    Differentiable ℂ (suzukiCanonicalE omega) := by
  change Differentiable ℂ
    (fun z : ℂ => xi (1 / 2 + (omega : ℂ) - z * I))
  exact xi_differentiable.comp (by fun_prop)

theorem differentiable_suzukiCanonicalESharp (omega : ℝ) :
    Differentiable ℂ (suzukiCanonicalESharp omega) := by
  rw [show suzukiCanonicalESharp omega =
      fun z => suzukiCanonicalE omega (-z) by
    funext z
    exact suzukiCanonicalESharp_eq_E_neg omega z]
  exact (differentiable_suzukiCanonicalE omega).comp (by fun_prop)

/-- The literal ratio is meromorphic on the whole plane. -/
theorem meromorphicOn_suzukiCanonicalTheta (omega : ℝ) :
    MeromorphicOn (suzukiCanonicalTheta omega) Set.univ := by
  rw [show suzukiCanonicalTheta omega = fun z =>
      suzukiCanonicalESharp omega z / suzukiCanonicalE omega z by
    funext z
    exact suzukiCanonicalTheta_eq_ESharp_div_E omega z]
  have hsharp : AnalyticOnNhd ℂ (suzukiCanonicalESharp omega) Set.univ :=
    fun z _ => (differentiable_suzukiCanonicalESharp omega).analyticAt z
  have hE : AnalyticOnNhd ℂ (suzukiCanonicalE omega) Set.univ :=
    fun z _ => (differentiable_suzukiCanonicalE omega).analyticAt z
  exact hsharp.meromorphicOn.div hE.meromorphicOn

/-- Equation (105) on the regular locus of its meromorphic pointwise representative. -/
theorem suzukiCanonicalTheta_mul_neg_eq_one
    (omega : ℝ) (z : ℂ)
    (hz : suzukiCanonicalE omega z ≠ 0)
    (hneg : suzukiCanonicalE omega (-z) ≠ 0) :
    suzukiCanonicalTheta omega z * suzukiCanonicalTheta omega (-z) = 1 := by
  rw [suzukiCanonicalTheta_eq_E_neg_div_E,
    suzukiCanonicalTheta_eq_E_neg_div_E]
  simp only [neg_neg]
  field_simp

/-- Set-theoretic form of the regular-locus meromorphic functional equation. -/
theorem suzukiCanonicalTheta_mul_neg_eqOn (omega : ℝ) :
    Set.EqOn
      (fun z => suzukiCanonicalTheta omega z * suzukiCanonicalTheta omega (-z))
      (fun _ => 1)
      {z | suzukiCanonicalE omega z ≠ 0 ∧
        suzukiCanonicalE omega (-z) ≠ 0} := by
  intro z hz
  exact suzukiCanonicalTheta_mul_neg_eq_one omega z hz.1 hz.2

/-- `E^omega(0)` lies on the zero-free real Xi axis. -/
theorem suzukiCanonicalE_zero_ne_zero (omega : ℝ) :
    suzukiCanonicalE omega 0 ≠ 0 := by
  rw [suzukiCanonicalE]
  convert xi_ne_zero_of_real (1 / 2 + omega) using 1
  push_cast
  ring

/-- Suzuki (2012), equation (107): `Theta_omega(0)=1`. -/
theorem suzukiCanonicalTheta_zero (omega : ℝ) :
    suzukiCanonicalTheta omega 0 = 1 := by
  rw [suzukiCanonicalTheta_eq_E_neg_div_E]
  simp only [neg_zero]
  exact div_self (suzukiCanonicalE_zero_ne_zero omega)

/-- On the real boundary the numerator is the conjugate denominator. -/
theorem suzukiCanonicalTheta_ofReal_eq_conj_E_div_E (omega u : ℝ) :
    suzukiCanonicalTheta omega (u : ℂ) =
      (starRingEnd ℂ) (suzukiCanonicalE omega (u : ℂ)) /
        suzukiCanonicalE omega (u : ℂ) := by
  rw [suzukiCanonicalTheta_eq_ESharp_div_E, suzukiCanonicalESharp]
  simp

/-- Suzuki (2012), equation (106), at every regular real boundary point. -/
theorem norm_suzukiCanonicalTheta_ofReal_eq_one
    (omega u : ℝ) (hE : suzukiCanonicalE omega (u : ℂ) ≠ 0) :
    ‖suzukiCanonicalTheta omega (u : ℂ)‖ = 1 := by
  rw [suzukiCanonicalTheta_ofReal_eq_conj_E_div_E, norm_div, norm_conj,
    div_self (norm_ne_zero_iff.mpr hE)]

/-- The literal Hermite--Biehler condition (102) for Suzuki's source. -/
def SuzukiCanonicalHermiteBiehler (omega : ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    ‖suzukiCanonicalESharp omega z‖ < ‖suzukiCanonicalE omega z‖

/-- Exact regularity-and-disk reformulation of equations (102) and (108). -/
theorem suzukiCanonicalHermiteBiehler_iff_theta_disk (omega : ℝ) :
    SuzukiCanonicalHermiteBiehler omega ↔
      ∀ z : ℂ, 0 < z.im →
        suzukiCanonicalE omega z ≠ 0 ∧
          ‖suzukiCanonicalTheta omega z‖ < 1 := by
  constructor
  · intro hHB z hz
    have hlt := hHB z hz
    have hE : suzukiCanonicalE omega z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hlt
      exact (not_lt_of_ge (norm_nonneg _)) hlt
    refine ⟨hE, ?_⟩
    rw [suzukiCanonicalTheta_eq_ESharp_div_E, norm_div,
      div_lt_one (norm_pos_iff.mpr hE)]
    exact hlt
  · intro h z hz
    obtain ⟨hE, htheta⟩ := h z hz
    rw [suzukiCanonicalTheta_eq_ESharp_div_E, norm_div,
      div_lt_one (norm_pos_iff.mpr hE)] at htheta
    exact htheta

/-- The paper's `A^omega` is the real part of the `E^omega,E^omega sharp` pair. -/
theorem suzukiCanonicalA_eq_E_ESharp_average (omega : ℝ) (z : ℂ) :
    suzukiCanonicalA omega z =
      (suzukiCanonicalE omega z + suzukiCanonicalESharp omega z) / 2 := by
  rw [suzukiCanonicalA, suzukiCanonicalE,
    suzukiCanonicalESharp_eq_E_neg,
    suzukiCanonicalE_neg_eq_thetaNumerator]

/-- The paper's `B^omega` is the skew part of the same source pair. -/
theorem suzukiCanonicalB_eq_E_ESharp_difference (omega : ℝ) (z : ℂ) :
    suzukiCanonicalB omega z =
      I / 2 * (suzukiCanonicalE omega z - suzukiCanonicalESharp omega z) := by
  rw [suzukiCanonicalB, suzukiCanonicalE,
    suzukiCanonicalESharp_eq_E_neg,
    suzukiCanonicalE_neg_eq_thetaNumerator]

end RHTower
