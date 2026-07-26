/-
# Physical-box form of Bourgain's `A₆` moment

Bourgain applies curve decoupling on the physical box with side scales
`H,H²,H²,H`.  This module identifies its twelfth moment exactly with
`H⁶` times the literal normalized `A₆` moment.
-/
import GaloisForLFunctions.RHTower.BourgainA6TorusBaseline
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticModel

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

/-- Same physical sum written directly as normalized square-root-curve
samples. -/
def bourgainA6NormalizedCurveSum
    (H : ℕ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ n : Fin H,
    bourgainUnitCharacter
      (bourgainSquareRootCurvePhase x
        ((bourgainIndex n : ℝ) / (H : ℝ)))

/-- Exact equality between physical `A₆` coordinates and normalized curve
coordinates. -/
theorem bourgainA6NormalizedCurveSum_eq_physical
    (H : ℕ) (hH : 0 < H) (x : BourgainPhaseSpace) :
    bourgainA6NormalizedCurveSum H x =
      bourgainA6PhysicalExponentialSum H (x 0) (x 1) (x 2) (x 3) := by
  have hHr : (0 : ℝ) < H := by
    exact_mod_cast hH
  have hH0 : (H : ℝ) ≠ 0 := hHr.ne'
  have hH20 : (H : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hH0
  have hHhalf : (0 : ℝ) < (H : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hHr _
  have hHthreeHalf : (0 : ℝ) < (H : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hHr _
  have hmulHalf :
      (H : ℝ) ^ (1 / 2 : ℝ) *
          (H : ℝ) ^ (1 / 2 : ℝ) =
        (H : ℝ) := by
    calc
      (H : ℝ) ^ (1 / 2 : ℝ) *
          (H : ℝ) ^ (1 / 2 : ℝ) =
          (H : ℝ) ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
            rw [Real.rpow_add hHr]
      _ = (H : ℝ) := by norm_num
  have hmulThreeHalf :
      (H : ℝ) ^ (1 / 2 : ℝ) *
          (H : ℝ) ^ (3 / 2 : ℝ) =
        (H : ℝ) ^ (2 : ℕ) := by
    calc
      (H : ℝ) ^ (1 / 2 : ℝ) *
          (H : ℝ) ^ (3 / 2 : ℝ) =
          (H : ℝ) ^ ((1 / 2 : ℝ) + (3 / 2 : ℝ)) := by
            rw [Real.rpow_add hHr]
      _ = (H : ℝ) ^ (2 : ℕ) := by
        norm_num [Real.rpow_two]
  have hscaleHalf :
      (H : ℝ) ^ (1 / 2 : ℝ) / (H : ℝ) =
        1 / (H : ℝ) ^ (1 / 2 : ℝ) := by
    field_simp
    simpa [pow_two] using hmulHalf
  have hscaleThreeHalf :
      (H : ℝ) ^ (1 / 2 : ℝ) / (H : ℝ) ^ (2 : ℕ) =
        1 / (H : ℝ) ^ (3 / 2 : ℝ) := by
    field_simp
    exact hmulThreeHalf
  have hphase (n : Fin H) :
      bourgainSquareRootCurvePhase x
          ((bourgainIndex n : ℝ) / (H : ℝ)) =
        (bourgainIndex n : ℝ) * (x 0 / (H : ℝ)) +
          (bourgainIndex n : ℝ) ^ (2 : ℕ) *
            (x 1 / (H : ℝ) ^ (2 : ℕ)) +
          bourgainA6HigherPhase H
            (x 2 / (H : ℝ) ^ (2 : ℕ))
            (x 3 / (H : ℝ)) n := by
    have hn : (0 : ℝ) ≤ bourgainIndex n := by positivity
    have hcoefHalf :
        (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) /
            (H : ℝ) ^ (1 / 2 : ℝ) =
          (H : ℝ) ^ (1 / 2 : ℝ) *
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) / (H : ℝ) := by
      calc
        (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) /
              (H : ℝ) ^ (1 / 2 : ℝ) =
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) *
              (1 / (H : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) *
              ((H : ℝ) ^ (1 / 2 : ℝ) / (H : ℝ)) := by
            rw [hscaleHalf]
        _ = (H : ℝ) ^ (1 / 2 : ℝ) *
              (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) / (H : ℝ) := by
            ring
    have hcoefThreeHalf :
        (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) /
            (H : ℝ) ^ (3 / 2 : ℝ) =
          (H : ℝ) ^ (1 / 2 : ℝ) *
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) /
              (H : ℝ) ^ (2 : ℕ) := by
      calc
        (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) /
              (H : ℝ) ^ (3 / 2 : ℝ) =
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) *
              (1 / (H : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) *
              ((H : ℝ) ^ (1 / 2 : ℝ) /
                (H : ℝ) ^ (2 : ℕ)) := by
            rw [hscaleThreeHalf]
        _ = (H : ℝ) ^ (1 / 2 : ℝ) *
              (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) /
                (H : ℝ) ^ (2 : ℕ) := by
            ring
    have hcoefHalf' :
        (bourgainIndex n : ℝ) ^ (2 : ℝ)⁻¹ /
            (H : ℝ) ^ (2 : ℝ)⁻¹ =
          (H : ℝ) ^ (2 : ℝ)⁻¹ *
            (bourgainIndex n : ℝ) ^ (2 : ℝ)⁻¹ / (H : ℝ) := by
      simpa [one_div] using hcoefHalf
    simp [bourgainSquareRootCurvePhase, bourgainSquareRootCurve,
      bourgainDot, Fin.sum_univ_four, Matrix.cons_val,
      bourgainA6HigherPhase]
    rw [Real.div_rpow hn hHr.le, Real.div_rpow hn hHr.le,
      hcoefHalf', hcoefThreeHalf]
    field_simp
    ring
  unfold bourgainA6NormalizedCurveSum
    bourgainA6PhysicalExponentialSum bourgainA6ExponentialSum
  apply Fintype.sum_congr
  intro n
  rw [hphase]
  rfl

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
