/-
# Uniform two-torus baseline for Bourgain's `A₆` phase

The first two coordinates in Bourgain's mean value theorem are the periodic
frequencies `n` and `n²`.  After fixing the remaining coordinates, their
contribution is the discrete-parabola two-torus sum with unimodular
coefficients

`e(H^(1/2) n^(3/2) x₃ + H^(1/2) n^(1/2) x₄)`.

This file instantiates the unconditional parabola estimate uniformly in
`x₃,x₄`.  It gives the exact `H^(9+ε)` baseline.  Bourgain's four-dimensional
decoupling and bilinear induction are precisely what improve this to the
`H^(6+ε)` target of Theorem 2.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaTwoTorusL12
import GaloisForLFunctions.RHTower.BourgainUnitIntervalTorus

namespace RHTower

noncomputable section

/-- Higher-order part of Bourgain's `A₆` phase after fixing `x₃,x₄`. -/
def bourgainA6HigherPhase
    (H : ℕ) (x₃ x₄ : ℝ) (n : Fin H) : ℝ :=
  (H : ℝ) ^ (1 / 2 : ℝ) *
      (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) * x₃ +
    (H : ℝ) ^ (1 / 2 : ℝ) *
      (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) * x₄

/-- Unimodular coefficient supplied by the two non-periodic coordinates. -/
def bourgainA6HigherPhaseTwist
    (H : ℕ) (x₃ x₄ : ℝ) (n : Fin H) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      (bourgainA6HigherPhase H x₃ x₄ n : ℂ))

/-- Literal four-variable exponential sum in Bourgain's Theorem 2. -/
def bourgainA6ExponentialSum
    (H : ℕ) (x₁ x₂ x₃ x₄ : ℝ) : ℂ :=
  ∑ n : Fin H,
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        (((bourgainIndex n : ℝ) * x₁ +
          (bourgainIndex n : ℝ) ^ (2 : ℕ) * x₂ +
          bourgainA6HigherPhase H x₃ x₄ n : ℝ) : ℂ))

@[simp] theorem norm_bourgainA6HigherPhaseTwist
    (H : ℕ) (x₃ x₄ : ℝ) (n : Fin H) :
    ‖bourgainA6HigherPhaseTwist H x₃ x₄ n‖ = 1 := by
  rw [bourgainA6HigherPhaseTwist, Complex.norm_exp]
  have hre :
      (2 * (Real.pi : ℂ) * Complex.I *
        (bourgainA6HigherPhase H x₃ x₄ n : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- Bourgain's four-coordinate sum with its first two variables represented
by the two unit-circle parameters. -/
def bourgainA6TwoTorusSum
    (H : ℕ) (x₃ x₄ : ℝ) (u v : ℂ) : ℂ :=
  bourgainParabolaTwoTorusSum H
    (bourgainA6HigherPhaseTwist H x₃ x₄) u v

/-- Twelfth moment in the first two, periodic, coordinates. -/
def bourgainA6TwoTorusMoment
    (H : ℕ) (x₃ x₄ : ℝ) : ℝ :=
  Real.circleAverage
    (fun v =>
      Real.circleAverage
        (fun u => ‖bourgainA6TwoTorusSum H x₃ x₄ u v‖ ^ (12 : ℕ))
        0 1)
    0 1

/-- Four-variable `A₆` moment, with the periodic coordinates represented by
unit-circle averages and the remaining coordinates integrated over
`[-1,1]²`. -/
def bourgainA6RectangleMoment (H : ℕ) : ℝ :=
  ∫ x₃ in (-1 : ℝ)..1,
    ∫ x₄ in (-1 : ℝ)..1,
      bourgainA6TwoTorusMoment H x₃ x₄

/-- Literal nested-interval version of the four-variable `A₆` moment. -/
def bourgainA6LiteralMoment (H : ℕ) : ℝ :=
  ∫ x₃ in (-1 : ℝ)..1,
    ∫ x₄ in (-1 : ℝ)..1,
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)

/-- Exact expansion of the two-torus `A₆` sum. -/
theorem bourgainA6TwoTorusSum_eq
    (H : ℕ) (x₃ x₄ : ℝ) (u v : ℂ) :
    bourgainA6TwoTorusSum H x₃ x₄ u v =
      ∑ n : Fin H,
        bourgainA6HigherPhaseTwist H x₃ x₄ n *
          u ^ bourgainIndex n *
          v ^ (bourgainIndex n ^ (2 : ℕ)) := by
  rfl

/-- Substituting `u=e(x₁)` and `v=e(x₂)` gives the literal phase in
Bourgain's equation (2.12). -/
theorem bourgainA6TwoTorusSum_unitCharacter_eq
    (H : ℕ) (x₁ x₂ x₃ x₄ : ℝ) :
    bourgainA6TwoTorusSum H x₃ x₄
        (bourgainUnitCharacter x₁) (bourgainUnitCharacter x₂) =
      bourgainA6ExponentialSum H x₁ x₂ x₃ x₄ := by
  unfold bourgainA6TwoTorusSum bourgainParabolaTwoTorusSum
    bourgainA6HigherPhaseTwist bourgainUnitCharacter
    bourgainA6ExponentialSum
  apply Fintype.sum_congr
  intro n
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact identification of the circle-average and literal `[0,1]²`
versions of the periodic coordinates. -/
theorem bourgainA6TwoTorusMoment_eq_unitSquare
    (H : ℕ) (x₃ x₄ : ℝ) :
    bourgainA6TwoTorusMoment H x₃ x₄ =
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ) := by
  unfold bourgainA6TwoTorusMoment
  rw [circleAverage_circleAverage_zero_one_eq_unitSquare]
  apply intervalIntegral.integral_congr
  intro x₂ _
  apply intervalIntegral.integral_congr
  intro x₁ _
  dsimp
  rw [bourgainA6TwoTorusSum_unitCharacter_eq]

/-- The internal circle-average object is exactly Bourgain's literal
four-variable moment. -/
theorem bourgainA6RectangleMoment_eq_literal (H : ℕ) :
    bourgainA6RectangleMoment H = bourgainA6LiteralMoment H := by
  unfold bourgainA6RectangleMoment bourgainA6LiteralMoment
  apply intervalIntegral.integral_congr
  intro x₃ _
  apply intervalIntegral.integral_congr
  intro x₄ _
  exact bourgainA6TwoTorusMoment_eq_unitSquare H x₃ x₄

/-- Uniform unconditional `H^(9+ε)` baseline for the first two torus
coordinates of Bourgain's `A₆` mean value. -/
theorem circleAverage_circleAverage_bourgainA6_pow_twelve_baseline
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (x₃ x₄ : ℝ),
        Real.circleAverage
            (fun v =>
              Real.circleAverage
                (fun u =>
                  ‖bourgainA6TwoTorusSum H x₃ x₄ u v‖ ^ (12 : ℕ))
                0 1)
            0 1 ≤
          C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    circleAverage_circleAverage_parabola_norm_one_coeff_pow_twelve_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H x₃ x₄
  simpa [bourgainA6TwoTorusSum] using
    hbound H (bourgainA6HigherPhaseTwist H x₃ x₄)
      (norm_bourgainA6HigherPhaseTwist H x₃ x₄)

/-- Continuity needed to integrate the uniform torus estimate in `x₄`. -/
theorem continuous_bourgainA6TwoTorusMoment_right
    (H : ℕ) (x₃ : ℝ) :
    Continuous fun x₄ : ℝ =>
      bourgainA6TwoTorusMoment H x₃ x₄ := by
  unfold bourgainA6TwoTorusMoment bourgainA6TwoTorusSum
    bourgainParabolaTwoTorusSum bourgainA6HigherPhaseTwist
    bourgainA6HigherPhase
  fun_prop [Real.circleAverage]

/-- The `x₄`-integrated torus moment varies continuously in `x₃`. -/
theorem continuous_intervalIntegral_bourgainA6TwoTorusMoment
    (H : ℕ) :
    Continuous fun x₃ : ℝ =>
      ∫ x₄ in (-1 : ℝ)..1,
        bourgainA6TwoTorusMoment H x₃ x₄ := by
  unfold bourgainA6TwoTorusMoment bourgainA6TwoTorusSum
    bourgainParabolaTwoTorusSum bourgainA6HigherPhaseTwist
    bourgainA6HigherPhase
  fun_prop [Real.circleAverage]

/-- Integrating the uniform baseline over the two remaining coordinates gives
the unconditional full `A₆` estimate `H^(9+ε)`. -/
theorem bourgainA6RectangleMoment_baseline
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℕ,
        bourgainA6RectangleMoment H ≤
          C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    circleAverage_circleAverage_bourgainA6_pow_twelve_baseline hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro H
  let B : ℝ := C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ)
  have hinner (x₃ : ℝ) :
      (∫ x₄ in (-1 : ℝ)..1,
        bourgainA6TwoTorusMoment H x₃ x₄) ≤ 2 * B := by
    calc
      (∫ x₄ in (-1 : ℝ)..1,
          bourgainA6TwoTorusMoment H x₃ x₄) ≤
          ∫ _x₄ in (-1 : ℝ)..1, B := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact
            (continuous_bourgainA6TwoTorusMoment_right H x₃).intervalIntegrable
              (-1) 1
        · exact intervalIntegrable_const
        · intro x₄ _
          simpa [bourgainA6TwoTorusMoment, B] using hpoint H x₃ x₄
      _ = 2 * B := by
        rw [intervalIntegral.integral_const]
        norm_num
  calc
    bourgainA6RectangleMoment H =
        ∫ x₃ in (-1 : ℝ)..1,
          ∫ x₄ in (-1 : ℝ)..1,
            bourgainA6TwoTorusMoment H x₃ x₄ := rfl
    _ ≤ ∫ _x₃ in (-1 : ℝ)..1, 2 * B := by
      apply intervalIntegral.integral_mono_on
      · norm_num
      · exact
          (continuous_intervalIntegral_bourgainA6TwoTorusMoment H).intervalIntegrable
            (-1) 1
      · exact intervalIntegrable_const
      · intro x₃ _
        exact hinner x₃
    _ = 4 * C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
      rw [intervalIntegral.integral_const]
      norm_num
      dsimp [B]
      ring

/-- Literal four-variable form of the unconditional `H^(9+ε)` baseline. -/
theorem bourgainA6LiteralMoment_baseline
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℕ,
        bourgainA6LiteralMoment H ≤
          C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ := bourgainA6RectangleMoment_baseline hε
  refine ⟨C, hC, ?_⟩
  intro H
  rw [← bourgainA6RectangleMoment_eq_literal]
  exact hbound H

end

end RHTower
