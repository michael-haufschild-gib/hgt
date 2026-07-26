/-
# Physical periodicity of normalized `A₆` blocks

Normalized curve samples `(q+m)/N` have exact physical periods `N` in the
linear coordinate and `N²` in the quadratic coordinate.  These are the two
periodic averages used in Bourgain's physical localization argument.
-/
import GaloisForLFunctions.RHTower.BourgainA6PointwiseBilinear

namespace RHTower

noncomputable section

theorem bourgainUnitCharacter_natCast (k : ℕ) :
    bourgainUnitCharacter (k : ℝ) = 1 := by
  unfold bourgainUnitCharacter
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) =
        (k : ℕ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring,
    Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

theorem bourgainUnitCharacter_add_natCast (u : ℝ) (k : ℕ) :
    bourgainUnitCharacter (u + k) = bourgainUnitCharacter u := by
  rw [bourgainUnitCharacter_add, bourgainUnitCharacter_natCast, mul_one]

/-- Coordinate form of one normalized physical block. -/
def bourgainA6PhysicalBlockCoordinateSum
    (N M q : ℕ) (c : Fin M → ℂ)
    (x₁ x₂ x₃ x₄ : ℝ) : ℂ :=
  bourgainA6PhysicalBlockSum N M q c ![x₁, x₂, x₃, x₄]

/-- Exact period `N` in the physical linear coordinate. -/
theorem periodic_bourgainA6PhysicalBlockCoordinateSum_first
    (N M q : ℕ) (hN : 0 < N) (c : Fin M → ℂ)
    (x₂ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₁ =>
        bourgainA6PhysicalBlockCoordinateSum
          N M q c x₁ x₂ x₃ x₄)
      (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  intro x₁
  unfold bourgainA6PhysicalBlockCoordinateSum
    bourgainA6PhysicalBlockSum
  apply Fintype.sum_congr
  intro m
  congr 1
  have hphase :
      bourgainSquareRootCurvePhase
          ![x₁ + (N : ℝ), x₂, x₃, x₄]
          (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)) =
        bourgainSquareRootCurvePhase
            ![x₁, x₂, x₃, x₄]
            (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)) +
          ((q + bourgainIndex m : ℕ) : ℝ) := by
    simp [bourgainSquareRootCurvePhase, bourgainSquareRootCurve,
      bourgainDot, Fin.sum_univ_four, Matrix.cons_val]
    field_simp
    ring
  rw [hphase]
  exact bourgainUnitCharacter_add_natCast _ _

/-- Exact period `N²` in the physical quadratic coordinate. -/
theorem periodic_bourgainA6PhysicalBlockCoordinateSum_second
    (N M q : ℕ) (hN : 0 < N) (c : Fin M → ℂ)
    (x₁ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₂ =>
        bourgainA6PhysicalBlockCoordinateSum
          N M q c x₁ x₂ x₃ x₄)
      ((N : ℝ) ^ (2 : ℕ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN20 : (N : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hN0
  intro x₂
  unfold bourgainA6PhysicalBlockCoordinateSum
    bourgainA6PhysicalBlockSum
  apply Fintype.sum_congr
  intro m
  congr 1
  have hphase :
      bourgainSquareRootCurvePhase
          ![x₁, x₂ + (N : ℝ) ^ (2 : ℕ), x₃, x₄]
          (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)) =
        bourgainSquareRootCurvePhase
            ![x₁, x₂, x₃, x₄]
            (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)) +
          (((q + bourgainIndex m : ℕ) ^ (2 : ℕ) : ℕ) : ℝ) := by
    simp [bourgainSquareRootCurvePhase, bourgainSquareRootCurve,
      bourgainDot, Fin.sum_univ_four, Matrix.cons_val]
    field_simp
    ring
  rw [hphase]
  exact bourgainUnitCharacter_add_natCast _ _

/-- The bilinear sixth-power product of two blocks inherits both physical
periods. -/
theorem periodic_bourgainA6PhysicalBlockProduct_first
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₂ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₁ =>
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ))
      (N : ℝ) := by
  intro x₁
  change
    ‖bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ (x₁ + (N : ℝ)) x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ (x₁ + (N : ℝ)) x₂ x₃ x₄‖ ^ (6 : ℕ) =
      ‖bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)
  have h₁ :=
    periodic_bourgainA6PhysicalBlockCoordinateSum_first
      N M q₁ hN c₁ x₂ x₃ x₄ x₁
  have h₂ :=
    periodic_bourgainA6PhysicalBlockCoordinateSum_first
      N M q₂ hN c₂ x₂ x₃ x₄ x₁
  change
    bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ (x₁ + (N : ℝ)) x₂ x₃ x₄ =
      bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ x₂ x₃ x₄ at h₁
  change
    bourgainA6PhysicalBlockCoordinateSum
        N M q₂ c₂ (x₁ + (N : ℝ)) x₂ x₃ x₄ =
      bourgainA6PhysicalBlockCoordinateSum
        N M q₂ c₂ x₁ x₂ x₃ x₄ at h₂
  rw [h₁, h₂]

theorem periodic_bourgainA6PhysicalBlockProduct_second
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₁ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₂ =>
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ))
      ((N : ℝ) ^ (2 : ℕ)) := by
  intro x₂
  change
    ‖bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ (x₂ + (N : ℝ) ^ (2 : ℕ)) x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ (x₂ + (N : ℝ) ^ (2 : ℕ)) x₃ x₄‖ ^
            (6 : ℕ) =
      ‖bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)
  have h₁ :=
    periodic_bourgainA6PhysicalBlockCoordinateSum_second
      N M q₁ hN c₁ x₁ x₃ x₄ x₂
  have h₂ :=
    periodic_bourgainA6PhysicalBlockCoordinateSum_second
      N M q₂ hN c₂ x₁ x₃ x₄ x₂
  change
    bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ (x₂ + (N : ℝ) ^ (2 : ℕ)) x₃ x₄ =
      bourgainA6PhysicalBlockCoordinateSum
        N M q₁ c₁ x₁ x₂ x₃ x₄ at h₁
  change
    bourgainA6PhysicalBlockCoordinateSum
        N M q₂ c₂ x₁ (x₂ + (N : ℝ) ^ (2 : ℕ)) x₃ x₄ =
      bourgainA6PhysicalBlockCoordinateSum
        N M q₂ c₂ x₁ x₂ x₃ x₄ at h₂
  rw [h₁, h₂]

/-- A full physical linear period may be centered without changing the
bilinear moment. -/
theorem integral_bourgainA6PhysicalBlockProduct_first_centered
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₂ x₃ x₄ : ℝ) :
    (∫ x₁ in (-(N : ℝ) / 2)..((N : ℝ) / 2),
      ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)) =
      ∫ x₁ in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) := by
  have hp :=
    (periodic_bourgainA6PhysicalBlockProduct_first
      N M q₁ q₂ hN c₁ c₂ x₂ x₃ x₄).intervalIntegral_add_eq
        (-(N : ℝ) / 2) 0
  convert hp using 1 <;> ring_nf

/-- A full physical quadratic period may be centered without changing the
bilinear moment. -/
theorem integral_bourgainA6PhysicalBlockProduct_second_centered
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₁ x₃ x₄ : ℝ) :
    (∫ x₂ in (-((N : ℝ) ^ (2 : ℕ)) / 2)..
        (((N : ℝ) ^ (2 : ℕ)) / 2),
      ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)) =
      ∫ x₂ in (0 : ℝ)..((N : ℝ) ^ (2 : ℕ)),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) := by
  have hp :=
    (periodic_bourgainA6PhysicalBlockProduct_second
      N M q₁ q₂ hN c₁ c₂ x₁ x₃ x₄).intervalIntegral_add_eq
        (-((N : ℝ) ^ (2 : ℕ)) / 2) 0
  convert hp using 1 <;> ring_nf

/-- Exact simultaneous centering of the two periodic physical coordinates. -/
theorem integral_bourgainA6PhysicalBlockProduct_two_periods_centered
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₃ x₄ : ℝ) :
    (∫ x₂ in (-((N : ℝ) ^ (2 : ℕ)) / 2)..
        (((N : ℝ) ^ (2 : ℕ)) / 2),
      ∫ x₁ in (-(N : ℝ) / 2)..((N : ℝ) / 2),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)) =
      ∫ x₂ in (0 : ℝ)..((N : ℝ) ^ (2 : ℕ)),
        ∫ x₁ in (0 : ℝ)..(N : ℝ),
          ‖bourgainA6PhysicalBlockCoordinateSum
              N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
            ‖bourgainA6PhysicalBlockCoordinateSum
              N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) := by
  simp_rw [integral_bourgainA6PhysicalBlockProduct_first_centered
    N M q₁ q₂ hN c₁ c₂]
  let F : ℝ → ℝ := fun x₂ =>
    ∫ x₁ in (0 : ℝ)..(N : ℝ),
      ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₁ c₁ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₂ c₂ x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)
  have hperiod : Function.Periodic F ((N : ℝ) ^ (2 : ℕ)) := by
    intro x₂
    apply intervalIntegral.integral_congr
    intro x₁ hx₁
    exact periodic_bourgainA6PhysicalBlockProduct_second
      N M q₁ q₂ hN c₁ c₂ x₁ x₃ x₄ x₂
  have hp := hperiod.intervalIntegral_add_eq
    (-((N : ℝ) ^ (2 : ℕ)) / 2) 0
  change
    (∫ x₂ in (-((N : ℝ) ^ (2 : ℕ)) / 2)..
        (((N : ℝ) ^ (2 : ℕ)) / 2), F x₂) =
      ∫ x₂ in (0 : ℝ)..((N : ℝ) ^ (2 : ℕ)), F x₂
  convert hp using 1 <;> ring_nf

end

end RHTower
