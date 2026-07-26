/-
# Fundamental physical cell for the discrete parabola

The physical parabola extension has periods `H` and `H²` in its linear and
quadratic phase coordinates.  Its natural fundamental cell therefore has
volume `H³`, not the isotropic `H⁴` square used by a coarse cube estimate.
This exact volume saving is the elementary periodicity input behind
Bourgain's anisotropic argument in Section 2.
-/
import GaloisForLFunctions.RHTower.BourgainScaledParabolaDecoupling

namespace RHTower

noncomputable section

/-- Exact transport of one physical period rectangle
`[0,H] × [0,H²]` to the unit two-torus. -/
theorem integral_scaledParabola_fundamentalCell_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) :
    (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x in (0 : ℝ)..(H : ℝ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      (H : ℝ) ^ (3 : ℕ) *
        ∫ v in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..1,
            ‖bourgainDiscreteParabolaExtension H a u v‖ ^
              (6 : ℕ) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hH20 : (H : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hH0
  unfold bourgainScaledParabolaExtension
  have hx (y : ℝ) :
      (∫ x in (0 : ℝ)..(H : ℝ),
        ‖bourgainDiscreteParabolaExtension H a
          (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ)) =
        (H : ℝ) *
          ∫ u in (0 : ℝ)..1,
            ‖bourgainDiscreteParabolaExtension H a u
              (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ) := by
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun u : ℝ =>
          ‖bourgainDiscreteParabolaExtension H a u
            (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ))
        hH0
        (a := (0 : ℝ)) (b := (H : ℝ))
    have hquot : (H : ℝ) / (H : ℝ) = 1 := div_self hH0
    rw [hquot] at hchange
    simpa using hchange
  simp_rw [hx]
  rw [intervalIntegral.integral_const_mul]
  have hychange :=
    intervalIntegral.integral_comp_div
      (fun v : ℝ =>
        ∫ u in (0 : ℝ)..1,
          ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ))
      hH20
      (a := (0 : ℝ)) (b := (H : ℝ) ^ (2 : ℕ))
  rw [hychange]
  simp only [zero_div, div_self hH20]
  ring

/-- Translation of a fundamental physical period cell leaves its sixth
moment unchanged. -/
theorem integral_scaledParabola_translatedFundamentalCell_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ)
    (x₀ y₀ : ℝ) :
    (∫ y in y₀..y₀ + (H : ℝ) ^ (2 : ℕ),
      ∫ x in x₀..x₀ + (H : ℝ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ) := by
  have hx (y : ℝ) :
      (∫ x in x₀..x₀ + (H : ℝ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
        ∫ x in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ) := by
    have hperiod :
        Function.Periodic
          (fun x =>
            ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ))
          (H : ℝ) := by
      intro x
      have hphase :=
        periodic_bourgainScaledParabolaExtension_first H hH a y x
      change
        bourgainScaledParabolaExtension H a (x + (H : ℝ)) y =
          bourgainScaledParabolaExtension H a x y at hphase
      exact congrArg (fun z : ℂ => ‖z‖ ^ (6 : ℕ)) hphase
    simpa using hperiod.intervalIntegral_add_eq x₀ 0
  rw [show
    (fun y : ℝ =>
      ∫ x in x₀..x₀ + (H : ℝ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      (fun y : ℝ =>
        ∫ x in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) by
      funext y
      exact hx y]
  have hyperiod :
      Function.Periodic
        (fun y =>
          ∫ x in (0 : ℝ)..(H : ℝ),
            ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ))
        ((H : ℝ) ^ (2 : ℕ)) := by
    intro y
    apply intervalIntegral.integral_congr
    intro x _
    have hphase :=
      periodic_bourgainScaledParabolaExtension_second H hH a x y
    change
      bourgainScaledParabolaExtension H a x
          (y + (H : ℝ) ^ (2 : ℕ)) =
        bourgainScaledParabolaExtension H a x y at hphase
    exact congrArg (fun z : ℂ => ‖z‖ ^ (6 : ℕ)) hphase
  simpa using hyperiod.intervalIntegral_add_eq y₀ 0

/-- Centered form of the fundamental-cell identity. -/
theorem integral_scaledParabola_centeredFundamentalCell_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) :
    (∫ y in (-(H : ℝ) ^ (2 : ℕ) / 2)..
          ((H : ℝ) ^ (2 : ℕ) / 2),
      ∫ x in (-(H : ℝ) / 2)..((H : ℝ) / 2),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ) := by
  have htranslate :=
    integral_scaledParabola_translatedFundamentalCell_eq
      H hH a (-(H : ℝ) / 2) (-((H : ℝ) ^ (2 : ℕ)) / 2)
  convert htranslate using 1 <;> ring

/-- Unconditional discrete planar `L⁶` estimate on the sharp physical
fundamental cell of volume `H³`. -/
theorem integral_scaledParabola_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ a : Fin H → ℂ,
        (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ),
            ‖bourgainScaledParabolaExtension H a x y‖ ^
              (6 : ℕ)) ≤
          (H : ℝ) ^ (3 : ℕ) *
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hunit⟩ :=
    integral_unitSquare_discreteParabola_norm_pow_six_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH a
  rw [integral_scaledParabola_fundamentalCell_eq H hH a]
  exact mul_le_mul_of_nonneg_left (hunit H a) (by positivity)

/-- Product of the two physical fundamental-cell moments.  This is the
factored target obtained after Bourgain's two pairs of periodic phase
coordinates have been separated. -/
def bourgainScaledParabolaBilinearFundamentalMoment
    (H : ℕ) (a₁ a₂ : Fin H → ℂ) : ℝ :=
  ∫ v₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
    ∫ u₂ in (0 : ℝ)..(H : ℝ),
      ∫ v₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ u₁ in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a₁ u₁ v₁‖ ^
              (6 : ℕ) *
            ‖bourgainScaledParabolaExtension H a₂ u₂ v₂‖ ^
              (6 : ℕ)

/-- Fubini factorization of the physical four-coordinate bilinear cell. -/
theorem bourgainScaledParabolaBilinearFundamentalMoment_eq_mul
    (H : ℕ) (a₁ a₂ : Fin H → ℂ) :
    bourgainScaledParabolaBilinearFundamentalMoment H a₁ a₂ =
      (∫ v₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ u₁ in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a₁ u₁ v₁‖ ^
            (6 : ℕ)) *
      (∫ v₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ u₂ in (0 : ℝ)..(H : ℝ),
          ‖bourgainScaledParabolaExtension H a₂ u₂ v₂‖ ^
            (6 : ℕ)) := by
  unfold bourgainScaledParabolaBilinearFundamentalMoment
  simp only [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]

/-- Unconditional product estimate on the sharp four-coordinate physical
cell.  The exponent is left in factored form so no asymptotic algebra is
hidden. -/
theorem bourgainScaledParabolaBilinearFundamentalMoment_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ (a₁ a₂ : Fin H → ℂ),
        bourgainScaledParabolaBilinearFundamentalMoment H a₁ a₂ ≤
          ((H : ℝ) ^ (3 : ℕ) *
            (C * (H : ℝ) ^ (ε / 2) *
              (∑ n : Fin H, ‖a₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) *
          ((H : ℝ) ^ (3 : ℕ) *
            (C * (H : ℝ) ^ (ε / 2) *
              (∑ n : Fin H, ‖a₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨C, hC, hcell⟩ :=
    integral_scaledParabola_fundamentalCell_subpower hhalf
  refine ⟨C, hC, ?_⟩
  intro H hH a₁ a₂
  rw [bourgainScaledParabolaBilinearFundamentalMoment_eq_mul]
  exact mul_le_mul
    (hcell H hH a₁) (hcell H hH a₂)
    (by
      apply intervalIntegral.integral_nonneg (by positivity)
      intro v _
      apply intervalIntegral.integral_nonneg (by positivity)
      intro u _
      positivity)
    (by positivity)

end

end RHTower
