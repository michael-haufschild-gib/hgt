/-
# Physical-box form of Bourgain's `A₆` moment

Bourgain applies curve decoupling on the physical box with side scales
`H,H²,H²,H`.  This module identifies its twelfth moment exactly with
`H⁶` times the literal normalized `A₆` moment.
-/
import GaloisForLFunctions.RHTower.BourgainA6TorusBaseline

namespace RHTower

noncomputable section

/-- Bourgain's `A₆` sum in physical coordinates. -/
def bourgainA6PhysicalExponentialSum
    (H : ℕ) (y₁ y₂ y₃ y₄ : ℝ) : ℂ :=
  bourgainA6ExponentialSum H
    (y₁ / (H : ℝ))
    (y₂ / (H : ℝ) ^ (2 : ℕ))
    (y₃ / (H : ℝ) ^ (2 : ℕ))
    (y₄ / (H : ℝ))

/-- Twelfth moment on the physical box
`[0,H]×[0,H²]×[-H²,H²]×[-H,H]`. -/
def bourgainA6PhysicalMoment (H : ℕ) : ℝ :=
  ∫ y₃ in (-((H : ℝ) ^ (2 : ℕ)))..((H : ℝ) ^ (2 : ℕ)),
    ∫ y₄ in (-(H : ℝ))..(H : ℝ),
      ∫ y₂ in (0 : ℝ)..((H : ℝ) ^ (2 : ℕ)),
        ∫ y₁ in (0 : ℝ)..(H : ℝ),
          ‖bourgainA6PhysicalExponentialSum H y₁ y₂ y₃ y₄‖ ^
            (12 : ℕ)

/-- Exact physical-to-normalized change of variables. -/
theorem bourgainA6PhysicalMoment_eq
    (H : ℕ) (hH : 0 < H) :
    bourgainA6PhysicalMoment H =
      (H : ℝ) ^ (6 : ℕ) * bourgainA6LiteralMoment H := by
  have hHr : (0 : ℝ) < H := by
    exact_mod_cast hH
  have hH0 : (H : ℝ) ≠ 0 := hHr.ne'
  have hH20 : (H : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hH0
  let F : ℝ → ℝ → ℝ → ℝ → ℝ :=
    fun x₁ x₂ x₃ x₄ =>
      ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)
  have hy₁ (y₂ y₃ y₄ : ℝ) :
      (∫ y₁ in (0 : ℝ)..(H : ℝ),
          F (y₁ / (H : ℝ))
            (y₂ / (H : ℝ) ^ (2 : ℕ))
            (y₃ / (H : ℝ) ^ (2 : ℕ))
            (y₄ / (H : ℝ))) =
        (H : ℝ) *
          ∫ x₁ in (0 : ℝ)..1,
            F x₁
              (y₂ / (H : ℝ) ^ (2 : ℕ))
              (y₃ / (H : ℝ) ^ (2 : ℕ))
              (y₄ / (H : ℝ)) := by
    simpa only [zero_div, div_self hH0] using
      (intervalIntegral.integral_comp_div
        (fun x₁ : ℝ =>
          F x₁
            (y₂ / (H : ℝ) ^ (2 : ℕ))
            (y₃ / (H : ℝ) ^ (2 : ℕ))
            (y₄ / (H : ℝ)))
        hH0 (a := (0 : ℝ)) (b := (H : ℝ)))
  have hy₂ (y₃ y₄ : ℝ) :
      (∫ y₂ in (0 : ℝ)..((H : ℝ) ^ (2 : ℕ)),
          ∫ y₁ in (0 : ℝ)..(H : ℝ),
            F (y₁ / (H : ℝ))
              (y₂ / (H : ℝ) ^ (2 : ℕ))
              (y₃ / (H : ℝ) ^ (2 : ℕ))
              (y₄ / (H : ℝ))) =
        (H : ℝ) ^ (3 : ℕ) *
          ∫ x₂ in (0 : ℝ)..1,
            ∫ x₁ in (0 : ℝ)..1,
              F x₁ x₂
                (y₃ / (H : ℝ) ^ (2 : ℕ))
                (y₄ / (H : ℝ)) := by
    simp_rw [hy₁]
    rw [intervalIntegral.integral_const_mul]
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun x₂ : ℝ =>
          ∫ x₁ in (0 : ℝ)..1,
            F x₁ x₂
              (y₃ / (H : ℝ) ^ (2 : ℕ))
              (y₄ / (H : ℝ)))
        hH20 (a := (0 : ℝ)) (b := ((H : ℝ) ^ (2 : ℕ)))
    rw [hchange]
    simp only [zero_div, div_self hH20]
    ring
  have hy₄ (y₃ : ℝ) :
      (∫ y₄ in (-(H : ℝ))..(H : ℝ),
          ∫ y₂ in (0 : ℝ)..((H : ℝ) ^ (2 : ℕ)),
            ∫ y₁ in (0 : ℝ)..(H : ℝ),
              F (y₁ / (H : ℝ))
                (y₂ / (H : ℝ) ^ (2 : ℕ))
                (y₃ / (H : ℝ) ^ (2 : ℕ))
                (y₄ / (H : ℝ))) =
        (H : ℝ) ^ (4 : ℕ) *
          ∫ x₄ in (-1 : ℝ)..1,
            ∫ x₂ in (0 : ℝ)..1,
              ∫ x₁ in (0 : ℝ)..1,
                F x₁ x₂ (y₃ / (H : ℝ) ^ (2 : ℕ)) x₄ := by
    simp_rw [hy₂]
    rw [intervalIntegral.integral_const_mul]
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun x₄ : ℝ =>
          ∫ x₂ in (0 : ℝ)..1,
            ∫ x₁ in (0 : ℝ)..1,
              F x₁ x₂ (y₃ / (H : ℝ) ^ (2 : ℕ)) x₄)
        hH0
        (a := (-(H : ℝ)))
        (b := (H : ℝ))
    rw [hchange]
    simp only [neg_div, div_self hH0]
    ring
  unfold bourgainA6PhysicalMoment bourgainA6PhysicalExponentialSum
  change
    (∫ y₃ in (-((H : ℝ) ^ (2 : ℕ)))..((H : ℝ) ^ (2 : ℕ)),
      ∫ y₄ in (-(H : ℝ))..(H : ℝ),
        ∫ y₂ in (0 : ℝ)..((H : ℝ) ^ (2 : ℕ)),
          ∫ y₁ in (0 : ℝ)..(H : ℝ),
            F (y₁ / (H : ℝ))
              (y₂ / (H : ℝ) ^ (2 : ℕ))
              (y₃ / (H : ℝ) ^ (2 : ℕ))
              (y₄ / (H : ℝ))) = _
  simp_rw [hy₄]
  rw [intervalIntegral.integral_const_mul]
  have hchange :=
    intervalIntegral.integral_comp_div
      (fun x₃ : ℝ =>
        ∫ x₄ in (-1 : ℝ)..1,
          ∫ x₂ in (0 : ℝ)..1,
            ∫ x₁ in (0 : ℝ)..1,
              F x₁ x₂ x₃ x₄)
      hH20
      (a := (-((H : ℝ) ^ (2 : ℕ))))
      (b := ((H : ℝ) ^ (2 : ℕ)))
  rw [hchange]
  simp only [neg_div, div_self hH20]
  change
    (H : ℝ) ^ (4 : ℕ) *
        ((H : ℝ) ^ (2 : ℕ) *
          ∫ x₃ in (-1 : ℝ)..1,
            ∫ x₄ in (-1 : ℝ)..1,
              ∫ x₂ in (0 : ℝ)..1,
                ∫ x₁ in (0 : ℝ)..1,
                  F x₁ x₂ x₃ x₄) =
      (H : ℝ) ^ (6 : ℕ) * bourgainA6LiteralMoment H
  change
    (H : ℝ) ^ (4 : ℕ) *
        ((H : ℝ) ^ (2 : ℕ) * bourgainA6LiteralMoment H) =
      (H : ℝ) ^ (6 : ℕ) * bourgainA6LiteralMoment H
  ring

/-- The sharp physical-box estimate and sharp literal `A₆` estimate are
equivalent up to the exact Jacobian factor. -/
theorem bourgainA6PhysicalMoment_le_iff
    (H : ℕ) (hH : 0 < H) (B : ℝ) :
    bourgainA6PhysicalMoment H ≤ (H : ℝ) ^ (6 : ℕ) * B ↔
      bourgainA6LiteralMoment H ≤ B := by
  rw [bourgainA6PhysicalMoment_eq H hH]
  have hscale : (0 : ℝ) < (H : ℝ) ^ (6 : ℕ) := by
    positivity
  constructor <;> intro h <;> nlinarith

end

end RHTower
