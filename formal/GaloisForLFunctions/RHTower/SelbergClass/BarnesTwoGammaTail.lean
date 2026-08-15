import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Vertical-tail bound for the scalar Barnes two-Gamma integrand

This file proves only a pointwise bound on the vertical tails.  It deliberately
contains neither a contour identity nor a continuation interface.
-/

open Complex Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The scalar integrand in the Barnes representation on `w = c + t I`. -/
def barnesTwoGammaIntegrand (ξ η : ℂ) (c t : ℝ) : ℂ :=
  Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I)) *
    Complex.Gamma ((c : ℂ) + (t : ℂ) * I) *
      η ^ (-((c : ℂ) + (t : ℂ) * I))

/--
For the actual scalar Barnes integrand, the two Gamma factors and the complex
power give a strict exponential vertical-tail rate
`π - |arg η|`.  The height condition is the true height of the shifted Gamma
factor, namely `|ξ.im| + 1 ≤ |t|`.
-/
theorem exists_bound_norm_barnesTwoGammaIntegrand_tail
    (ξ η : ℂ) (c : ℝ) (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    0 < Real.pi - |Complex.arg η| ∧
      ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ, |ξ.im| + 1 ≤ |t| →
        ‖barnesTwoGammaIntegrand ξ η c t‖
          ≤ C * |t| ^ N * Real.exp (-((Real.pi - |Complex.arg η|) * |t|)) := by
  refine ⟨sub_pos.mpr harg, ?_⟩
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip hc c
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (by linarith : 0 < ξ.re - c) (ξ.re - c)
  let B : ℝ := |ξ.im|
  let R : ℝ := ‖η‖ ^ (-c)
  let C : ℝ := C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R
  refine ⟨C, N₁ + N₂, ?_, ?_⟩
  · dsimp [C, R]
    positivity
  intro t ht
  have hB : 0 ≤ B := by dsimp [B]; exact abs_nonneg _
  have htone : 1 ≤ |t| := by linarith
  have hlower : |t| - B ≤ |ξ.im - t| := by
    have h := abs_sub_le t ξ.im 0
    simpa [B, abs_sub_comm] using h
  have htGamma : 1 ≤ |ξ.im - t| := by linarith
  have hupper0 : |ξ.im - t| ≤ B + |t| := by
    have h := abs_sub_le ξ.im 0 t
    simpa [B] using h
  have hupper : |ξ.im - t| ≤ (B + 1) * |t| := by
    have haux : 0 ≤ B * (|t| - 1) := mul_nonneg hB (sub_nonneg.mpr htone)
    linarith
  have hshape : ξ - ((c : ℂ) + (t : ℂ) * I) =
      ((ξ.re - c : ℝ) : ℂ) + ((ξ.im - t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
  have hG₁ : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖
      ≤ C₁ * |t| ^ N₁ * Real.exp (-(Real.pi * |t| / 2)) :=
    hΓ₁ c t le_rfl le_rfl htone
  have hpow₂ : |ξ.im - t| ^ N₂ ≤ ((B + 1) * |t|) ^ N₂ :=
    pow_le_pow_left₀ (abs_nonneg _) hupper N₂
  have hG₂ : ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I))‖
      ≤ C₂ * ((B + 1) * |t|) ^ N₂ * Real.exp (-(Real.pi * |ξ.im - t| / 2)) := by
    rw [hshape]
    calc
      ‖Complex.Gamma (((ξ.re - c : ℝ) : ℂ) + ((ξ.im - t : ℝ) : ℂ) * I)‖
          ≤ C₂ * |ξ.im - t| ^ N₂ * Real.exp (-(Real.pi * |ξ.im - t| / 2)) :=
            hΓ₂ (ξ.re - c) (ξ.im - t) le_rfl le_rfl htGamma
      _ ≤ C₂ * ((B + 1) * |t|) ^ N₂ * Real.exp (-(Real.pi * |ξ.im - t| / 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow₂ hC₂) (Real.exp_pos _).le
  have hE₂ : Real.exp (-(Real.pi * |ξ.im - t| / 2))
      ≤ Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * |t| / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hG₂' : ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I))‖
      ≤ C₂ * ((B + 1) * |t|) ^ N₂ *
        (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * |t| / 2))) := by
    have hbase : 0 ≤ (B + 1) * |t| :=
      mul_nonneg (by linarith) (abs_nonneg _)
    have hcoeff : 0 ≤ C₂ * ((B + 1) * |t|) ^ N₂ :=
      mul_nonneg hC₂ (pow_nonneg hbase _)
    exact hG₂.trans (mul_le_mul_of_nonneg_left hE₂ hcoeff)
  have hΓprod :
      ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I)) *
        Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖
      ≤ C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * |t| ^ (N₁ + N₂) *
        Real.exp (-(Real.pi * |t|)) := by
    calc
      ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I)) *
          Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖
        = ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I))‖ *
          ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := norm_mul _ _
      _ ≤ (C₂ * ((B + 1) * |t|) ^ N₂ *
            (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * |t| / 2)))) *
          (C₁ * |t| ^ N₁ * Real.exp (-(Real.pi * |t| / 2))) :=
            mul_le_mul hG₂' hG₁ (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * |t| ^ (N₁ + N₂) *
          Real.exp (-(Real.pi * |t|)) := by
            have hpow : |t| ^ N₂ * |t| ^ N₁ = |t| ^ (N₁ + N₂) := by
              rw [← pow_add, Nat.add_comm]
            have hExp : Real.exp (-(Real.pi * |t| / 2)) *
                Real.exp (-(Real.pi * |t| / 2)) = Real.exp (-(Real.pi * |t|)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [mul_pow]
            calc
              C₂ * ((B + 1) ^ N₂ * |t| ^ N₂) *
                    (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * |t| / 2))) *
                  (C₁ * |t| ^ N₁ * Real.exp (-(Real.pi * |t| / 2)))
                  = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) *
                      (|t| ^ N₂ * |t| ^ N₁) *
                        (Real.exp (-(Real.pi * |t| / 2)) *
                          Real.exp (-(Real.pi * |t| / 2))) := by ring
              _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * |t| ^ (N₁ + N₂) *
                    Real.exp (-(Real.pi * |t|)) := by rw [hpow, hExp]
  have hηbound : ‖η ^ (-((c : ℂ) + (t : ℂ) * I))‖
      ≤ R * Real.exp (|Complex.arg η| * |t|) := by
    rw [Complex.norm_cpow_of_ne_zero hη]
    have hre : (-((c : ℂ) + (t : ℂ) * I)).re = -c := by simp
    have him : (-((c : ℂ) + (t : ℂ) * I)).im = -t := by simp
    rw [hre, him]
    calc
      ‖η‖ ^ (-c) / Real.exp (Complex.arg η * -t)
          = R * Real.exp (Complex.arg η * t) := by
            dsimp [R]
            rw [show Complex.arg η * -t = -(Complex.arg η * t) by ring, Real.exp_neg,
              div_inv_eq_mul]
      _ ≤ R * Real.exp (|Complex.arg η| * |t|) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (Real.rpow_nonneg (norm_nonneg _) _)
        calc Complex.arg η * t ≤ |Complex.arg η * t| := le_abs_self _
          _ = |Complex.arg η| * |t| := abs_mul _ _
  unfold barnesTwoGammaIntegrand
  calc
    ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I)) *
        Complex.Gamma ((c : ℂ) + (t : ℂ) * I) * η ^ (-((c : ℂ) + (t : ℂ) * I))‖
      = ‖Complex.Gamma (ξ - ((c : ℂ) + (t : ℂ) * I)) *
          Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ * ‖η ^ (-((c : ℂ) + (t : ℂ) * I))‖ := norm_mul _ _
    _ ≤ (C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * |t| ^ (N₁ + N₂) *
          Real.exp (-(Real.pi * |t|))) * (R * Real.exp (|Complex.arg η| * |t|)) :=
        mul_le_mul hΓprod hηbound (norm_nonneg _) (by positivity)
    _ = C * |t| ^ (N₁ + N₂) *
        Real.exp (-((Real.pi - |Complex.arg η|) * |t|)) := by
          have hExp : Real.exp (-(Real.pi * |t|)) * Real.exp (|Complex.arg η| * |t|) =
              Real.exp (-((Real.pi - |Complex.arg η|) * |t|)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          dsimp [C]
          calc
            C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * |t| ^ (N₁ + N₂) *
                Real.exp (-(Real.pi * |t|)) * (R * Real.exp (|Complex.arg η| * |t|))
                = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R * |t| ^ (N₁ + N₂) *
                    (Real.exp (-(Real.pi * |t|)) * Real.exp (|Complex.arg η| * |t|)) := by ring
            _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R * |t| ^ (N₁ + N₂) *
                Real.exp (-((Real.pi - |Complex.arg η|) * |t|)) := by rw [hExp]

end

end RHTower
