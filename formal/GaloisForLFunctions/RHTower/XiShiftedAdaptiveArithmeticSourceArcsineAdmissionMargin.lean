import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveArithmeticSourceFarRightPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Exact arcsine margin of canonical adaptive source admission

The far-right shifted-Xi moment face is the normalized arcsine moment functional.  Its monic
fixed-degree null admission is the shifted Chebyshev polynomial
`2^(1-2n) T_n(2X-1)`.  This module evaluates the actual adaptive shear on that admission.

The result is sharply two-sided.  Every nonconstant admitted degree has strictly positive source
margin: `11/64` in degree one and `2^(2-4n) (8n+3)/16` from degree two onward.  Yet these margins
tend to zero.  Canonical coefficient conditioning therefore preserves source sign, while degree
escape destroys every uniform coercive bound.  No reporter, orientation map, reflection aggregate,
or RH hypothesis occurs.
-/

open Filter MeasureTheory Polynomial Topology
open scoped Real Interval

namespace RHTower

namespace XiShiftedArcsineAdmission

noncomputable section

def affine : Polynomial ℝ := 2 * X - 1

theorem affine_eval_cos_sq (x : ℝ) :
    affine.eval (Real.cos x ^ 2) = Real.cos (2 * x) := by
  simp [affine, Real.cos_two_mul]

theorem bridge (P : Polynomial ℝ) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom (P.comp affine) =
      (∫ x, P.eval x ∂Polynomial.Chebyshev.measureT) / Real.pi := by
  rw [GaloisForLFunctions.HTGeometry.momentFunctional_normalizedCentralBinom_eq_quarterIntegral]
  rw [Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  have hi :
      (∫ x in (0 : ℝ)..Real.pi / 2, (P.comp affine).eval (Real.cos x ^ 2)) =
        (2 : ℝ)⁻¹ * ∫ x in (0 : ℝ)..Real.pi, P.eval (Real.cos x) := by
    rw [intervalIntegral.integral_congr (fun x _ => by
      rw [Polynomial.eval_comp, affine_eval_cos_sq])]
    have hs := intervalIntegral.integral_comp_mul_left
        (f := fun x : ℝ => P.eval (Real.cos x))
        (a := (0 : ℝ)) (b := Real.pi / 2) (by norm_num : (2 : ℝ) ≠ 0)
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at hs
    norm_num only [mul_zero] at hs
    simpa only [smul_eq_mul, inv_eq_one_div] using hs
  rw [hi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

def L (P : Polynomial ℝ) : ℝ :=
  HTGeometry.momentFunctional
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom (P.comp affine)

theorem L_eq (P : Polynomial ℝ) :
    L P = (∫ x, P.eval x ∂Polynomial.Chebyshev.measureT) / Real.pi := bridge P

theorem L_add (P Q : Polynomial ℝ) : L (P + Q) = L P + L Q := by
  simp [L, Polynomial.add_comp, HTGeometry.momentFunctional_add]

theorem L_smul (a : ℝ) (P : Polynomial ℝ) : L (a • P) = a * L P := by
  simp [L, Polynomial.smul_comp, HTGeometry.momentFunctional_smul]

theorem L_C_mul (a : ℝ) (P : Polynomial ℝ) : L (Polynomial.C a * P) = a * L P := by
  simpa [Polynomial.smul_eq_C_mul] using L_smul a P

@[simp] theorem L_natCast_mul (a : ℕ) (P : Polynomial ℝ) :
    L ((a : Polynomial ℝ) * P) = (a : ℝ) * L P := by
  change L (Polynomial.C (a : ℝ) * P) = (a : ℝ) * L P
  exact L_C_mul (a : ℝ) P

theorem L_two_mul (P : Polynomial ℝ) : L (2 * P) = 2 * L P := by
  change L (Polynomial.C (2 : ℝ) * P) = 2 * L P
  exact L_C_mul 2 P

theorem L_three_mul (P : Polynomial ℝ) : L (3 * P) = 3 * L P := by
  change L (Polynomial.C (3 : ℝ) * P) = 3 * L P
  exact L_C_mul 3 P

theorem L_four_mul (P : Polynomial ℝ) : L (4 * P) = 4 * L P := by
  change L (Polynomial.C (4 : ℝ) * P) = 4 * L P
  exact L_C_mul 4 P

theorem L_T_mul_T_of_ne {n m : ℕ} (h : n ≠ m) :
    L (Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ m) = 0 := by
  rw [L_eq]
  simp only [Polynomial.eval_mul]
  rw [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h]
  simp

theorem L_T_mul_self_zero :
    L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ 0) = 1 := by
  rw [L_eq]
  simp only [Polynomial.eval_mul]
  rw [Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
  field_simp [ne_of_gt Real.pi_pos]

theorem L_T_mul_self_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    L (Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ n) = 1 / 2 := by
  rw [L_eq]
  simp only [Polynomial.eval_mul]
  rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn]
  field_simp [ne_of_gt Real.pi_pos]

theorem one_add_X_sq_cheb :
    2 * (1 + X : Polynomial ℝ) ^ 2 =
      3 * Polynomial.Chebyshev.T ℝ 0 +
      4 * Polynomial.Chebyshev.T ℝ 1 +
      Polynomial.Chebyshev.T ℝ 2 := by
  simp [Polynomial.Chebyshev.T_two]
  ring

theorem one_add_X_cube_cheb :
    4 * (1 + X : Polynomial ℝ) ^ 3 =
      10 * Polynomial.Chebyshev.T ℝ 0 +
      15 * Polynomial.Chebyshev.T ℝ 1 +
      6 * Polynomial.Chebyshev.T ℝ 2 +
      Polynomial.Chebyshev.T ℝ 3 := by
  have hT3 : Polynomial.Chebyshev.T ℝ 3 = 4 * X ^ 3 - 3 * X := by
    rw [show (3 : ℤ) = 1 + 2 by norm_num,
      Polynomial.Chebyshev.T_add_two]
    norm_num [Polynomial.Chebyshev.T_two]
    ring
  simp [hT3, Polynomial.Chebyshev.T_two]
  ring

theorem two_mul_L_T_mul_T_sq (k n : ℕ) :
    2 * L (Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ n ^ 2) =
      L (Polynomial.Chebyshev.T ℝ k *
          Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ)) +
        L (Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ 0) := by
  have hprod := Polynomial.Chebyshev.T_mul_T ℝ (n : ℤ) (n : ℤ)
  have hpoly :
      (2 : Polynomial ℝ) *
          (Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ n ^ 2) =
        Polynomial.Chebyshev.T ℝ k *
            Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ) +
          Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ 0 := by
    rw [show (n : ℤ) + n = (2 * n : ℕ) by omega,
      show (n : ℤ) - n = 0 by omega] at hprod
    linear_combination Polynomial.Chebyshev.T ℝ k * hprod
  calc
    _ = L ((2 : Polynomial ℝ) *
        (Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ n ^ 2)) := by
          exact (L_natCast_mul 2 _).symm
    _ = L (Polynomial.Chebyshev.T ℝ k *
          Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ) +
        Polynomial.Chebyshev.T ℝ k * Polynomial.Chebyshev.T ℝ 0) := congrArg L hpoly
    _ = _ := L_add _ _

theorem L_one_add_X_sq_mul_T_sq_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    L ((1 + X : Polynomial ℝ) ^ 2 * Polynomial.Chebyshev.T ℝ n ^ 2) = 3 / 4 := by
  have h0 : L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ n ^ 2) = 1 / 2 := by
    simpa [pow_two] using L_T_mul_self_of_ne_zero (show n ≠ 0 by omega)
  have h1 : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ n ^ 2) = 0 := by
    have h := two_mul_L_T_mul_T_sq 1 n
    have ha : L (Polynomial.Chebyshev.T ℝ 1 *
        Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ)) = 0 := by
      exact L_T_mul_T_of_ne (show 1 ≠ 2 * n by omega)
    have hb : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 0) = 0 := by
      exact L_T_mul_T_of_ne (show (1 : ℕ) ≠ 0 by omega)
    change 2 * L (Polynomial.Chebyshev.T ℝ (1 : ℤ) *
        Polynomial.Chebyshev.T ℝ n ^ 2) =
      L (Polynomial.Chebyshev.T ℝ (1 : ℤ) *
        Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ)) +
      L (Polynomial.Chebyshev.T ℝ (1 : ℤ) * Polynomial.Chebyshev.T ℝ (0 : ℤ)) at h
    rw [ha, hb] at h
    linarith
  have h2 : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ n ^ 2) = 0 := by
    have h := two_mul_L_T_mul_T_sq 2 n
    have ha : L (Polynomial.Chebyshev.T ℝ 2 *
        Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ)) = 0 := by
      exact L_T_mul_T_of_ne (show 2 ≠ 2 * n by omega)
    have hb : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 0) = 0 := by
      exact L_T_mul_T_of_ne (show (2 : ℕ) ≠ 0 by omega)
    change 2 * L (Polynomial.Chebyshev.T ℝ (2 : ℤ) *
        Polynomial.Chebyshev.T ℝ n ^ 2) =
      L (Polynomial.Chebyshev.T ℝ (2 : ℤ) *
        Polynomial.Chebyshev.T ℝ ((2 * n : ℕ) : ℤ)) +
      L (Polynomial.Chebyshev.T ℝ (2 : ℤ) * Polynomial.Chebyshev.T ℝ (0 : ℤ)) at h
    rw [ha, hb] at h
    linarith
  have hpoly := congrArg
    (fun P : Polynomial ℝ => P * Polynomial.Chebyshev.T ℝ n ^ 2)
    one_add_X_sq_cheb
  have hfun := congrArg L hpoly
  have hleft : L (2 * (1 + X : Polynomial ℝ) ^ 2 *
      Polynomial.Chebyshev.T ℝ n ^ 2) =
      2 * L ((1 + X : Polynomial ℝ) ^ 2 * Polynomial.Chebyshev.T ℝ n ^ 2) := by
    rw [show 2 * (1 + X : Polynomial ℝ) ^ 2 * Polynomial.Chebyshev.T ℝ n ^ 2 =
      (2 : Polynomial ℝ) * ((1 + X : Polynomial ℝ) ^ 2 *
        Polynomial.Chebyshev.T ℝ n ^ 2) by ring, L_two_mul]
  have hright : L ((3 * Polynomial.Chebyshev.T ℝ 0 +
      4 * Polynomial.Chebyshev.T ℝ 1 + Polynomial.Chebyshev.T ℝ 2) *
        Polynomial.Chebyshev.T ℝ n ^ 2) = 3 / 2 := by
    rw [show (3 * Polynomial.Chebyshev.T ℝ 0 +
        4 * Polynomial.Chebyshev.T ℝ 1 + Polynomial.Chebyshev.T ℝ 2) *
          Polynomial.Chebyshev.T ℝ n ^ 2 =
      (3 : Polynomial ℝ) * (Polynomial.Chebyshev.T ℝ 0 *
        Polynomial.Chebyshev.T ℝ n ^ 2) +
      (4 : Polynomial ℝ) * (Polynomial.Chebyshev.T ℝ 1 *
        Polynomial.Chebyshev.T ℝ n ^ 2) +
      Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ n ^ 2 by ring,
      L_add, L_add, L_three_mul, L_four_mul, h0, h1, h2]
    norm_num
  rw [hleft, hright] at hfun
  norm_num at hfun ⊢
  linarith

theorem L_one_add_X_sq_mul_T_one_sq :
    L ((1 + X : Polynomial ℝ) ^ 2 *
      Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ) ^ 2) = 7 / 8 := by
  have h0 : L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ 1 ^ 2) = 1 / 2 := by
    simpa [pow_two] using L_T_mul_self_of_ne_zero (show (1 : ℕ) ≠ 0 by omega)
  have h1 : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 1 ^ 2) = 0 := by
    have h := two_mul_L_T_mul_T_sq 1 1
    have ha : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 2) = 0 := by
      exact L_T_mul_T_of_ne (show (1 : ℕ) ≠ 2 by omega)
    have hb : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 0) = 0 := by
      exact L_T_mul_T_of_ne (show (1 : ℕ) ≠ 0 by omega)
    change 2 * L (Polynomial.Chebyshev.T ℝ (1 : ℤ) *
        Polynomial.Chebyshev.T ℝ (1 : ℤ) ^ 2) =
      L (Polynomial.Chebyshev.T ℝ (1 : ℤ) * Polynomial.Chebyshev.T ℝ (2 : ℤ)) +
      L (Polynomial.Chebyshev.T ℝ (1 : ℤ) * Polynomial.Chebyshev.T ℝ (0 : ℤ)) at h
    rw [ha, hb] at h
    linarith
  have h2 : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 1 ^ 2) = 1 / 4 := by
    have h := two_mul_L_T_mul_T_sq 2 1
    have ha : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 2) = 1 / 2 := by
      exact L_T_mul_self_of_ne_zero (show (2 : ℕ) ≠ 0 by omega)
    have hb : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 0) = 0 := by
      exact L_T_mul_T_of_ne (show (2 : ℕ) ≠ 0 by omega)
    change 2 * L (Polynomial.Chebyshev.T ℝ (2 : ℤ) *
        Polynomial.Chebyshev.T ℝ (1 : ℤ) ^ 2) =
      L (Polynomial.Chebyshev.T ℝ (2 : ℤ) * Polynomial.Chebyshev.T ℝ (2 : ℤ)) +
      L (Polynomial.Chebyshev.T ℝ (2 : ℤ) * Polynomial.Chebyshev.T ℝ (0 : ℤ)) at h
    rw [ha, hb] at h
    linarith
  have hpoly := congrArg
    (fun P : Polynomial ℝ => P * Polynomial.Chebyshev.T ℝ 1 ^ 2)
    one_add_X_sq_cheb
  have hfun := congrArg L hpoly
  have hleft : L (2 * (1 + X : Polynomial ℝ) ^ 2 *
      Polynomial.Chebyshev.T ℝ 1 ^ 2) =
      2 * L ((1 + X : Polynomial ℝ) ^ 2 * Polynomial.Chebyshev.T ℝ 1 ^ 2) := by
    rw [show 2 * (1 + X : Polynomial ℝ) ^ 2 * Polynomial.Chebyshev.T ℝ 1 ^ 2 =
      (2 : Polynomial ℝ) * ((1 + X : Polynomial ℝ) ^ 2 *
        Polynomial.Chebyshev.T ℝ 1 ^ 2) by ring, L_two_mul]
  have hright : L ((3 * Polynomial.Chebyshev.T ℝ 0 +
      4 * Polynomial.Chebyshev.T ℝ 1 + Polynomial.Chebyshev.T ℝ 2) *
        Polynomial.Chebyshev.T ℝ 1 ^ 2) = 7 / 4 := by
    rw [show (3 * Polynomial.Chebyshev.T ℝ 0 +
        4 * Polynomial.Chebyshev.T ℝ 1 + Polynomial.Chebyshev.T ℝ 2) *
          Polynomial.Chebyshev.T ℝ 1 ^ 2 =
      (3 : Polynomial ℝ) * (Polynomial.Chebyshev.T ℝ 0 *
        Polynomial.Chebyshev.T ℝ 1 ^ 2) +
      (4 : Polynomial ℝ) * (Polynomial.Chebyshev.T ℝ 1 *
        Polynomial.Chebyshev.T ℝ 1 ^ 2) +
      Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 1 ^ 2 by ring,
      L_add, L_add, L_three_mul, L_four_mul, h0, h1, h2]
    norm_num
  rw [hleft, hright] at hfun
  norm_num at hfun ⊢
  linarith

theorem two_mul_T_mul_U_pred {n : ℕ} (hn : n ≠ 0) :
    2 * Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.U ℝ (n - 1) =
      Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ) := by
  have hprod := Polynomial.Chebyshev.T_mul_T ℝ (n : ℤ) (n : ℤ)
  rw [show (n : ℤ) + n = (2 * n : ℕ) by omega,
    show (n : ℤ) - n = 0 by omega] at hprod
  have hderiv := congrArg Polynomial.derivative hprod
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_ofNat, zero_mul, zero_add,
    Polynomial.Chebyshev.T_derivative_eq_U] at hderiv
  have hcast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hindex : ((2 * n : ℕ) : ℤ) - 1 = ((2 * n - 1 : ℕ) : ℤ) := by omega
  rw [hindex] at hderiv
  simp only [← Polynomial.C_eq_intCast] at hderiv
  push_cast at hderiv
  have hC : Polynomial.C (2 * (n : ℝ)) =
      (2 : Polynomial ℝ) * Polynomial.C (n : ℝ) := by
    change Polynomial.C (2 * (n : ℝ)) =
      Polynomial.C (2 : ℝ) * Polynomial.C (n : ℝ)
    rw [Polynomial.C_mul]
  have hc : Polynomial.C (2 * (n : ℝ)) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (mul_ne_zero (by norm_num) hcast)
  apply mul_left_cancel₀ hc
  rw [hC]
  rw [hC] at hderiv
  simp only [Polynomial.C_0, zero_mul, add_zero] at hderiv
  linear_combination hderiv

theorem four_mul_L_one_add_X_cube_mul_T (k : ℕ) :
    4 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ k) =
      10 * L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ k) +
      15 * L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ k) +
      6 * L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ k) +
      L (Polynomial.Chebyshev.T ℝ 3 * Polynomial.Chebyshev.T ℝ k) := by
  have hpoly := congrArg
    (fun P : Polynomial ℝ => P * Polynomial.Chebyshev.T ℝ k)
    one_add_X_cube_cheb
  have hfun := congrArg L hpoly
  have hleft : L (4 * (1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.T ℝ k) =
      4 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ k) := by
    rw [show 4 * (1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ k =
      4 * ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ k) by ring,
      L_four_mul]
  have hright :
      L ((10 * Polynomial.Chebyshev.T ℝ 0 +
          15 * Polynomial.Chebyshev.T ℝ 1 +
          6 * Polynomial.Chebyshev.T ℝ 2 +
          Polynomial.Chebyshev.T ℝ 3) * Polynomial.Chebyshev.T ℝ k) =
        10 * L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ k) +
        15 * L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ k) +
        6 * L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ k) +
        L (Polynomial.Chebyshev.T ℝ 3 * Polynomial.Chebyshev.T ℝ k) := by
    rw [show (10 * Polynomial.Chebyshev.T ℝ 0 +
          15 * Polynomial.Chebyshev.T ℝ 1 +
          6 * Polynomial.Chebyshev.T ℝ 2 +
          Polynomial.Chebyshev.T ℝ 3) * Polynomial.Chebyshev.T ℝ k =
      10 * (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ k) +
      15 * (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ k) +
      6 * (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ k) +
      Polynomial.Chebyshev.T ℝ 3 * Polynomial.Chebyshev.T ℝ k by ring,
      L_add, L_add, L_add]
    change
      L (Polynomial.C (10 : ℝ) * _) + L (Polynomial.C (15 : ℝ) * _) +
          L (Polynomial.C (6 : ℝ) * _) + _ = _
    rw [L_C_mul, L_C_mul, L_C_mul]
  rw [hleft, hright] at hfun
  exact hfun

theorem L_one_add_X_cube_mul_T_one :
    L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ 1) = 15 / 8 := by
  have h := four_mul_L_one_add_X_cube_mul_T 1
  have h01 : L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ 1) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 0) (m := 1) (by omega))
  have h11 : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 1) = 1 / 2 :=
    by simpa using (L_T_mul_self_of_ne_zero (n := 1) (by omega))
  have h21 : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 1) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 2) (m := 1) (by omega))
  have h31 : L (Polynomial.Chebyshev.T ℝ 3 * Polynomial.Chebyshev.T ℝ 1) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 3) (m := 1) (by omega))
  change 4 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ (1 : ℤ)) =
    10 * L (Polynomial.Chebyshev.T ℝ (0 : ℤ) * Polynomial.Chebyshev.T ℝ (1 : ℤ)) +
    15 * L (Polynomial.Chebyshev.T ℝ (1 : ℤ) * Polynomial.Chebyshev.T ℝ (1 : ℤ)) +
    6 * L (Polynomial.Chebyshev.T ℝ (2 : ℤ) * Polynomial.Chebyshev.T ℝ (1 : ℤ)) +
    L (Polynomial.Chebyshev.T ℝ (3 : ℤ) * Polynomial.Chebyshev.T ℝ (1 : ℤ)) at h
  rw [h01, h11, h21, h31] at h
  norm_num at h ⊢
  linarith

theorem L_one_add_X_cube_mul_T_three :
    L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ 3) = 1 / 8 := by
  have h := four_mul_L_one_add_X_cube_mul_T 3
  have h03 : L (Polynomial.Chebyshev.T ℝ 0 * Polynomial.Chebyshev.T ℝ 3) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 0) (m := 3) (by omega))
  have h13 : L (Polynomial.Chebyshev.T ℝ 1 * Polynomial.Chebyshev.T ℝ 3) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 1) (m := 3) (by omega))
  have h23 : L (Polynomial.Chebyshev.T ℝ 2 * Polynomial.Chebyshev.T ℝ 3) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 2) (m := 3) (by omega))
  have h33 : L (Polynomial.Chebyshev.T ℝ 3 * Polynomial.Chebyshev.T ℝ 3) = 1 / 2 :=
    by simpa using (L_T_mul_self_of_ne_zero (n := 3) (by omega))
  change 4 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ (3 : ℤ)) =
    10 * L (Polynomial.Chebyshev.T ℝ (0 : ℤ) * Polynomial.Chebyshev.T ℝ (3 : ℤ)) +
    15 * L (Polynomial.Chebyshev.T ℝ (1 : ℤ) * Polynomial.Chebyshev.T ℝ (3 : ℤ)) +
    6 * L (Polynomial.Chebyshev.T ℝ (2 : ℤ) * Polynomial.Chebyshev.T ℝ (3 : ℤ)) +
    L (Polynomial.Chebyshev.T ℝ (3 : ℤ) * Polynomial.Chebyshev.T ℝ (3 : ℤ)) at h
  rw [h03, h13, h23, h33] at h
  norm_num at h ⊢
  linarith

theorem L_one_add_X_cube_mul_T_odd_of_two_le {j : ℕ} (hj : 2 ≤ j) :
    L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) = 0 := by
  have h := four_mul_L_one_add_X_cube_mul_T (2 * j + 1)
  have h0 : L (Polynomial.Chebyshev.T ℝ 0 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 0) (m := 2 * j + 1) (by omega))
  have h1 : L (Polynomial.Chebyshev.T ℝ 1 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 1) (m := 2 * j + 1) (by omega))
  have h2 : L (Polynomial.Chebyshev.T ℝ 2 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 2) (m := 2 * j + 1) (by omega))
  have h3 : L (Polynomial.Chebyshev.T ℝ 3 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) = 0 :=
    by simpa using (L_T_mul_T_of_ne (n := 3) (m := 2 * j + 1) (by omega))
  change 4 * L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) =
    10 * L (Polynomial.Chebyshev.T ℝ (0 : ℤ) *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) +
    15 * L (Polynomial.Chebyshev.T ℝ (1 : ℤ) *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) +
    6 * L (Polynomial.Chebyshev.T ℝ (2 : ℤ) *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) +
    L (Polynomial.Chebyshev.T ℝ (3 : ℤ) *
      Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) at h
  rw [h0, h1, h2, h3] at h
  norm_num at h
  exact h

theorem L_one_add_X_cube_mul_U_one :
    L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.U ℝ 1) = 15 / 4 := by
  have hU : Polynomial.Chebyshev.U ℝ 1 =
      2 * Polynomial.Chebyshev.T ℝ 1 := by simp
  rw [hU, show (1 + X : Polynomial ℝ) ^ 3 *
      (2 * Polynomial.Chebyshev.T ℝ 1) =
    2 * ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ 1) by ring,
    L_two_mul, L_one_add_X_cube_mul_T_one]
  norm_num

theorem L_one_add_X_cube_mul_U_three :
    L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.U ℝ 3) = 4 := by
  have hrec := Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (1 : ℤ)
  have hU1 : Polynomial.Chebyshev.U ℝ 1 =
      2 * Polynomial.Chebyshev.T ℝ 1 := by simp
  rw [show (1 : ℤ) + 2 = 3 by norm_num, hU1] at hrec
  rw [hrec, mul_add, L_add]
  rw [show (1 + X : Polynomial ℝ) ^ 3 *
      (2 * Polynomial.Chebyshev.T ℝ 3) =
    2 * ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ 3) by ring,
    show (1 + X : Polynomial ℝ) ^ 3 *
      (2 * Polynomial.Chebyshev.T ℝ 1) =
    2 * ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ 1) by ring,
    L_two_mul, L_two_mul, L_one_add_X_cube_mul_T_three,
    L_one_add_X_cube_mul_T_one]
  norm_num

theorem L_one_add_X_cube_mul_U_odd_of_one_le {j : ℕ} (hj : 1 ≤ j) :
    L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.U ℝ ((2 * j + 1 : ℕ) : ℤ)) = 4 := by
  induction j, hj using Nat.le_induction with
  | base => simpa using L_one_add_X_cube_mul_U_three
  | succ j hj ih =>
      have hrec := Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ
        ((2 * j + 1 : ℕ) : ℤ)
      have hleft : ((2 * j + 1 : ℕ) : ℤ) + 2 =
          ((2 * (j + 1) + 1 : ℕ) : ℤ) := by omega
      rw [hleft] at hrec
      rw [hrec, mul_add, L_add]
      rw [show (1 + X : Polynomial ℝ) ^ 3 *
          (2 * Polynomial.Chebyshev.T ℝ ((2 * (j + 1) + 1 : ℕ) : ℤ)) =
        2 * ((1 + X : Polynomial ℝ) ^ 3 *
          Polynomial.Chebyshev.T ℝ ((2 * (j + 1) + 1 : ℕ) : ℤ)) by ring,
        L_two_mul]
      have hzero := L_one_add_X_cube_mul_T_odd_of_two_le
        (j := j + 1) (by omega)
      rw [hzero, ih]
      norm_num

theorem L_one_add_X_cube_mul_U_two_mul_sub_one_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)) = 4 := by
  have h := L_one_add_X_cube_mul_U_odd_of_one_le (j := n - 1) (by omega)
  convert h using 1
  congr 3
  omega

theorem two_mul_T_mul_derivative_T {n : ℕ} (hn : n ≠ 0) :
    2 * Polynomial.Chebyshev.T ℝ n *
        Polynomial.derivative (Polynomial.Chebyshev.T ℝ n) =
      (n : Polynomial ℝ) *
        Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ) := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  have hindex : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  rw [hindex]
  have hTU := two_mul_T_mul_U_pred hn
  rw [hindex] at hTU
  rw [← Polynomial.C_eq_intCast (n : ℤ), ← Polynomial.C_eq_natCast n]
  push_cast
  change 2 * Polynomial.Chebyshev.T ℝ n *
      (Polynomial.C (n : ℝ) *
        Polynomial.Chebyshev.U ℝ ((n - 1 : ℕ) : ℤ)) =
    Polynomial.C (n : ℝ) *
      Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)
  linear_combination Polynomial.C (n : ℝ) * hTU

theorem two_mul_L_one_add_X_cube_mul_T_derivative_T
    {n : ℕ} (hn : n ≠ 0) :
    2 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ n *
        Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)) =
      (n : ℝ) * L ((1 + X : Polynomial ℝ) ^ 3 *
        Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)) := by
  have hpoly := congrArg
    (fun P : Polynomial ℝ => (1 + X : Polynomial ℝ) ^ 3 * P)
    (two_mul_T_mul_derivative_T hn)
  have hfun := congrArg L hpoly
  have hleft :
      L ((1 + X : Polynomial ℝ) ^ 3 *
        (2 * Polynomial.Chebyshev.T ℝ n *
          Polynomial.derivative (Polynomial.Chebyshev.T ℝ n))) =
      2 * L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ n *
        Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)) := by
    rw [show (1 + X : Polynomial ℝ) ^ 3 *
          (2 * Polynomial.Chebyshev.T ℝ n *
            Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)) =
        2 * ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ n *
          Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)) by ring,
      L_two_mul]
  have hright :
      L ((1 + X : Polynomial ℝ) ^ 3 *
        ((n : Polynomial ℝ) *
          Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ))) =
      (n : ℝ) * L ((1 + X : Polynomial ℝ) ^ 3 *
        Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)) := by
    rw [show (1 + X : Polynomial ℝ) ^ 3 *
          ((n : Polynomial ℝ) *
            Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)) =
        (n : Polynomial ℝ) * ((1 + X : Polynomial ℝ) ^ 3 *
          Polynomial.Chebyshev.U ℝ ((2 * n - 1 : ℕ) : ℤ)) by ring,
      L_natCast_mul]
  rw [hleft, hright] at hfun
  exact hfun

theorem L_one_add_X_cube_mul_T_derivative_T_one :
    L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ) *
      Polynomial.derivative (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ))) = 15 / 8 := by
  have h := two_mul_L_one_add_X_cube_mul_T_derivative_T
    (n := 1) (by omega)
  have hU : L ((1 + X : Polynomial ℝ) ^ 3 *
      Polynomial.Chebyshev.U ℝ ((2 * 1 - 1 : ℕ) : ℤ)) = 15 / 4 := by
    convert L_one_add_X_cube_mul_U_one using 1
    norm_num
  rw [hU] at h
  norm_num at h ⊢
  linarith

theorem L_one_add_X_cube_mul_T_derivative_T_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    L ((1 + X : Polynomial ℝ) ^ 3 * Polynomial.Chebyshev.T ℝ n *
      Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)) = 2 * n := by
  have h := two_mul_L_one_add_X_cube_mul_T_derivative_T
    (n := n) (by omega)
  rw [L_one_add_X_cube_mul_U_two_mul_sub_one_of_two_le hn] at h
  linarith

def core (n : ℕ) : Polynomial ℝ :=
  (1 + X) ^ 2 * Polynomial.Chebyshev.T ℝ n ^ 2 +
    (1 + X) ^ 3 * Polynomial.Chebyshev.T ℝ n *
      Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)

theorem adaptiveShear_smul_chebyshev_comp_affine (a : ℝ) (n : ℕ) :
    RHTower.xiShiftedBoundaryAdaptiveShearPolynomial
        (a • (Polynomial.Chebyshev.T ℝ n).comp affine) =
      (a ^ 2 / 4) • (core n).comp affine := by
  simp only [RHTower.xiShiftedBoundaryAdaptiveShearPolynomial,
    RHTower.xiShiftedBoundaryShiftedEuler, Polynomial.derivative_comp,
    Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_ofNat,
    Polynomial.derivative_X, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.smul_eq_C_mul, affine, core]
  norm_num
  have h4 : Polynomial.C (a ^ 2 * (1 / 4 : ℝ)) * 4 =
      Polynomial.C (a ^ 2) := by
    change Polynomial.C (a ^ 2 * (1 / 4 : ℝ)) * Polynomial.C (4 : ℝ) =
      Polynomial.C (a ^ 2)
    rw [← Polynomial.C_mul]
    congr 1
    ring
  have h8 : Polynomial.C (a ^ 2 * (1 / 4 : ℝ)) * 8 =
      Polynomial.C (a ^ 2) * 2 := by
    change Polynomial.C (a ^ 2 * (1 / 4 : ℝ)) * Polynomial.C (8 : ℝ) =
      Polynomial.C (a ^ 2) * Polynomial.C (2 : ℝ)
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 1
    ring
  ring_nf
  rw [← Polynomial.C_pow]
  linear_combination
    -(X ^ 2 * (Polynomial.Chebyshev.T ℝ n).comp (-1 + X * 2) ^ 2) * h4 -
    (X ^ 3 * (Polynomial.Chebyshev.T ℝ n).comp (-1 + X * 2) *
      (Polynomial.derivative (Polynomial.Chebyshev.T ℝ n)).comp (-1 + X * 2)) * h8

theorem momentFunctional_adaptiveShear_smul_chebyshev_comp_affine_one (a : ℝ) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (RHTower.xiShiftedBoundaryAdaptiveShearPolynomial
          (a • (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).comp affine)) =
      a ^ 2 * 11 / 16 := by
  rw [adaptiveShear_smul_chebyshev_comp_affine]
  rw [HTGeometry.momentFunctional_smul]
  change a ^ 2 / 4 * L (core 1) = _
  have hcore : L (core 1) = 11 / 4 := by
    rw [core, L_add, L_one_add_X_sq_mul_T_one_sq,
      L_one_add_X_cube_mul_T_derivative_T_one]
    norm_num
  rw [hcore]
  ring

theorem momentFunctional_adaptiveShear_smul_chebyshev_comp_affine_of_two_le
    (a : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (RHTower.xiShiftedBoundaryAdaptiveShearPolynomial
          (a • (Polynomial.Chebyshev.T ℝ n).comp affine)) =
      a ^ 2 * (8 * n + 3) / 16 := by
  rw [adaptiveShear_smul_chebyshev_comp_affine]
  rw [HTGeometry.momentFunctional_smul]
  change a ^ 2 / 4 * L (core n) = _
  have hcore : L (core n) = (8 * n + 3) / 4 := by
    rw [core, L_add, L_one_add_X_sq_mul_T_sq_of_two_le hn,
      L_one_add_X_cube_mul_T_derivative_T_of_two_le hn]
    ring
  rw [hcore]
  ring

def monicScale (n : ℕ) : ℝ := ((2 : ℝ) ^ (2 * n - 1))⁻¹

def amplitude (n : ℕ) : Polynomial ℝ :=
  monicScale n • (Polynomial.Chebyshev.T ℝ n).comp affine

theorem leadingCoeff_chebyshev_comp_affine {n : ℕ} (_hn : n ≠ 0) :
    ((Polynomial.Chebyshev.T ℝ n).comp affine).leadingCoeff =
      (2 : ℝ) ^ (2 * n - 1) := by
  have haff : affine = Polynomial.C (2 : ℝ) * X + Polynomial.C (-1 : ℝ) := by
    rw [affine]
    change Polynomial.C (2 : ℝ) * X - Polynomial.C (1 : ℝ) =
      Polynomial.C (2 : ℝ) * X + Polynomial.C (-1 : ℝ)
    rw [Polynomial.C_neg]
    ring
  have hdeg : affine.natDegree = 1 := by
    rw [haff, Polynomial.natDegree_linear (by norm_num : (2 : ℝ) ≠ 0)]
  have hlc : affine.leadingCoeff = 2 := by
    rw [haff, Polynomial.leadingCoeff_linear (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Polynomial.leadingCoeff_comp (by omega : affine.natDegree ≠ 0)]
  simp only [Polynomial.Chebyshev.leadingCoeff_T,
    Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  have htrail : n - 1 + n = 2 * n - 1 := by omega
  rw [hlc, ← pow_add, htrail]

theorem amplitude_monic {n : ℕ} (hn : n ≠ 0) : (amplitude n).Monic := by
  have hs : monicScale n ≠ 0 := by
    unfold monicScale
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  rw [Polynomial.Monic.def, amplitude, Polynomial.smul_eq_C_mul,
    Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hs),
    leadingCoeff_chebyshev_comp_affine hn]
  unfold monicScale
  rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]

theorem momentFunctional_adaptiveShear_amplitude_one :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (RHTower.xiShiftedBoundaryAdaptiveShearPolynomial (amplitude 1)) = 11 / 64 := by
  rw [amplitude, momentFunctional_adaptiveShear_smul_chebyshev_comp_affine_one]
  norm_num [monicScale]

theorem momentFunctional_adaptiveShear_amplitude_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (RHTower.xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) =
      monicScale n ^ 2 * (8 * n + 3) / 16 := by
  exact momentFunctional_adaptiveShear_smul_chebyshev_comp_affine_of_two_le
    (monicScale n) hn

theorem momentFunctional_adaptiveShear_amplitude_pos {n : ℕ} (hn : n ≠ 0) :
    0 < HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (RHTower.xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      cases n with
      | zero =>
          rw [momentFunctional_adaptiveShear_amplitude_one]
          norm_num
      | succ n =>
          rw [momentFunctional_adaptiveShear_amplitude_of_two_le (by omega)]
          have hs : 0 < monicScale (Nat.succ (Nat.succ n)) := by
            unfold monicScale
            exact inv_pos.mpr (pow_pos (by norm_num) _)
          positivity

def margin (n : ℕ) : ℝ := monicScale n ^ 2 * (8 * n + 3) / 16

theorem monicScale_sq {n : ℕ} (hn : n ≠ 0) :
    monicScale n ^ 2 = 4 * (1 / 16 : ℝ) ^ n := by
  have hden : (2 : ℝ) ^ (2 * n - 1) * 2 = 4 ^ n := by
    calc
      _ = (2 : ℝ) ^ (2 * n - 1) * 2 ^ 1 := by ring
      _ = (2 : ℝ) ^ (2 * n - 1 + 1) := (pow_add _ _ _).symm
      _ = (2 : ℝ) ^ (2 * n) := by congr 1; omega
      _ = ((2 : ℝ) ^ 2) ^ n := by rw [← pow_mul]
      _ = 4 ^ n := by norm_num
  have h16 : (16 : ℝ) ^ n = (4 ^ n) ^ 2 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    simp only [← pow_mul]
    congr 1
    omega
  unfold monicScale
  rw [inv_pow]
  have hinv : (1 / 16 : ℝ) ^ n = ((16 : ℝ) ^ n)⁻¹ := by
    rw [one_div, inv_pow]
  rw [hinv]
  field_simp [pow_ne_zero]
  rw [h16, ← hden]
  ring

theorem margin_eq_geometric {n : ℕ} (hn : n ≠ 0) :
    margin n = (2 * n + 3 / 4) * (1 / 16 : ℝ) ^ n := by
  rw [margin, monicScale_sq hn]
  ring

theorem tendsto_margin_zero : Tendsto margin atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (1 / 16 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnp : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 16 : ℝ) ^ n)
      atTop (nhds 0) := tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have h := (hnp.const_mul 2).add (hp.const_mul (3 / 4))
  have hg : Tendsto
      (fun n : ℕ => (2 * n + 3 / 4) * (1 / 16 : ℝ) ^ n)
      atTop (nhds 0) := by
    convert h using 1
    · funext n
      ring_nf
    · ring_nf
  apply hg.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
  rw [margin_eq_geometric (by omega)]

theorem no_uniform_positive_margin (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, n ≠ 0 ∧ 0 < margin n ∧ margin n < ε := by
  have hevent := tendsto_margin_zero.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let n := max N 1
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn1 : 1 ≤ n := Nat.le_max_right _ _
  refine ⟨n, by omega, ?_, hN n hnN⟩
  rw [margin]
  have hs : 0 < monicScale n := by
    unfold monicScale
    exact inv_pos.mpr (pow_pos (by norm_num) _)
  positivity

end

end XiShiftedArcsineAdmission

end RHTower
