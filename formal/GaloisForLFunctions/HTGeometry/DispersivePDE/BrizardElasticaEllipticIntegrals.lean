import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Complete elliptic integrals for Brizard's extended modulus

Appendix A of arXiv:2607.21750 uses complete elliptic integrals of first and second kind, including
negative real parameters.  Mathlib currently has no corresponding named real functions.  We define
the paper's parameter convention directly by interval integrals and prove the reflection and
negative-to-classical integrand transformations needed for the knot-closure function `Q`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open scoped Interval

/-- Paper equation (A1), with parameter (not modulus) convention. -/
noncomputable def completeEllipticK (m : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹

/-- Paper equation (A5), with parameter (not modulus) convention. -/
noncomputable def completeEllipticE (m : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sqrt (1 - m * Real.sin θ ^ 2)

theorem completeEllipticK_zero : completeEllipticK 0 = Real.pi / 2 := by
  simp [completeEllipticK]

theorem completeEllipticE_zero : completeEllipticE 0 = Real.pi / 2 := by
  simp [completeEllipticE]

/-- Reflection `φ=π/2-θ` changes the sine-square integrand to cosine-square. -/
theorem completeEllipticK_reflection (m : ℝ) :
    completeEllipticK m =
      ∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.sqrt (1 - m * Real.cos θ ^ 2))⁻¹ := by
  rw [completeEllipticK]
  simpa only [sub_self, sub_zero, Real.sin_pi_div_two_sub] using
    (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (fun θ : ℝ => (Real.sqrt (1 - m * Real.sin θ ^ 2))⁻¹)
      (Real.pi / 2)).symm

/-- Reflection `φ=π/2-θ` for the second-kind integral. -/
theorem completeEllipticE_reflection (m : ℝ) :
    completeEllipticE m =
      ∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.sqrt (1 - m * Real.cos θ ^ 2) := by
  rw [completeEllipticE]
  simpa only [sub_self, sub_zero, Real.sin_pi_div_two_sub] using
    (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (fun θ : ℝ => Real.sqrt (1 - m * Real.sin θ ^ 2))
      (Real.pi / 2)).symm

theorem negativeModulus_factorization (m : NegativeModulus) (θ : ℝ) :
    1 - (m : ℝ) * Real.cos θ ^ 2 =
      (1 - (m : ℝ)) *
        (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2) := by
  have hm0 : (m : ℝ) < 0 := m.property
  have hcos : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hcos]
  rw [extendedToClassical]
  have hm : 1 - (m : ℝ) ≠ 0 := by linarith [hm0]
  field_simp [hm]
  ring

theorem transformedKRadicand_pos (m : NegativeModulus) (θ : ℝ) :
    0 < 1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2 := by
  have hn0 := (extendedToClassical m).property.1
  have hn1 := (extendedToClassical m).property.2
  have hs : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  nlinarith

/-- Pointwise first-kind transformation behind paper equation (A2). -/
theorem negativeKIntegrand_transform (m : NegativeModulus) (θ : ℝ) :
    (Real.sqrt (1 - (m : ℝ) * Real.cos θ ^ 2))⁻¹ =
      (Real.sqrt (1 - (m : ℝ)))⁻¹ *
        (Real.sqrt
          (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2))⁻¹ := by
  have hm0 : (m : ℝ) < 0 := m.property
  rw [negativeModulus_factorization]
  rw [Real.sqrt_mul (by linarith [hm0])]
  exact mul_inv _ _

/-- Pointwise second-kind transformation behind paper equation (A6). -/
theorem negativeEIntegrand_transform (m : NegativeModulus) (θ : ℝ) :
    Real.sqrt (1 - (m : ℝ) * Real.cos θ ^ 2) =
      Real.sqrt (1 - (m : ℝ)) *
        Real.sqrt (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2) := by
  have hm0 : (m : ℝ) < 0 := m.property
  rw [negativeModulus_factorization]
  exact Real.sqrt_mul (by linarith [hm0]) _

/-- Integrated first-kind transformation in raw scale form. -/
theorem completeEllipticK_negative_transform_raw (m : NegativeModulus) :
    completeEllipticK m =
      (Real.sqrt (1 - (m : ℝ)))⁻¹ * completeEllipticK (extendedToClassical m) := by
  rw [completeEllipticK_reflection]
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        (Real.sqrt (1 - (m : ℝ) * Real.cos θ ^ 2))⁻¹) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          (Real.sqrt (1 - (m : ℝ)))⁻¹ *
            (Real.sqrt
              (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2))⁻¹ := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact negativeKIntegrand_transform m θ
    _ = (Real.sqrt (1 - (m : ℝ)))⁻¹ *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          (Real.sqrt
            (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2))⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := rfl

/-- Paper equation (A2): negative `K` transported to a classical parameter. -/
theorem completeEllipticK_negative_transform (m : NegativeModulus) :
    completeEllipticK m =
      Real.sqrt (1 - (extendedToClassical m : ℝ)) *
        completeEllipticK (extendedToClassical m) := by
  rw [completeEllipticK_negative_transform_raw, transformedComplement, one_div,
    Real.sqrt_inv]

/-- Integrated second-kind transformation in raw scale form. -/
theorem completeEllipticE_negative_transform_raw (m : NegativeModulus) :
    completeEllipticE m =
      Real.sqrt (1 - (m : ℝ)) * completeEllipticE (extendedToClassical m) := by
  rw [completeEllipticE_reflection]
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.sqrt (1 - (m : ℝ) * Real.cos θ ^ 2)) =
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (1 - (m : ℝ)) *
            Real.sqrt
              (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact negativeEIntegrand_transform m θ
    _ = Real.sqrt (1 - (m : ℝ)) *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sqrt
            (1 - (extendedToClassical m : ℝ) * Real.sin θ ^ 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := rfl

/-- Paper equation (A6): negative `E` transported to a classical parameter. -/
theorem completeEllipticE_negative_transform (m : NegativeModulus) :
    completeEllipticE m =
      completeEllipticE (extendedToClassical m) /
        Real.sqrt (1 - (extendedToClassical m : ℝ)) := by
  rw [completeEllipticE_negative_transform_raw, transformedComplement, one_div,
    Real.sqrt_inv]
  have hm0 : (m : ℝ) < 0 := m.property
  have hs : Real.sqrt (1 - (m : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by linarith [hm0])
  field_simp [hs]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
