/-
# Exact periodic averaging for normalized `A₆` blocks

The linear physical coordinate has period `N`.  Averaging two independently
translated blocks over one full period therefore separates their sixth
moments exactly.  This is the finite-sum periodicity step used between
Bourgain's (2.4) and (2.7).
-/
import GaloisForLFunctions.RHTower.BourgainA6BlockPeriodicity

namespace RHTower

noncomputable section

/-- The sixth power of one block norm inherits physical period `N` in the
linear coordinate. -/
theorem periodic_norm_bourgainA6PhysicalBlockCoordinateSum_pow_six_first
    (N M q : ℕ) (hN : 0 < N) (c : Fin M → ℂ)
    (x₂ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₁ =>
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q c x₁ x₂ x₃ x₄‖ ^ (6 : ℕ))
      (N : ℝ) := by
  intro x₁
  change
    ‖bourgainA6PhysicalBlockCoordinateSum
        N M q c (x₁ + (N : ℝ)) x₂ x₃ x₄‖ ^ (6 : ℕ) =
      ‖bourgainA6PhysicalBlockCoordinateSum
        N M q c x₁ x₂ x₃ x₄‖ ^ (6 : ℕ)
  have hphase :=
    periodic_bourgainA6PhysicalBlockCoordinateSum_first
      N M q hN c x₂ x₃ x₄ x₁
  change
    bourgainA6PhysicalBlockCoordinateSum
        N M q c (x₁ + (N : ℝ)) x₂ x₃ x₄ =
      bourgainA6PhysicalBlockCoordinateSum
        N M q c x₁ x₂ x₃ x₄ at hphase
  rw [hphase]

/-- Translating a block before averaging over a full physical linear period
does not change its sixth moment. -/
theorem integral_norm_bourgainA6PhysicalBlockCoordinateSum_pow_six_first_translate
    (N M q : ℕ) (hN : 0 < N) (c : Fin M → ℂ)
    (x₁ x₂ x₃ x₄ : ℝ) :
    (∫ z in (0 : ℝ)..(N : ℝ),
      ‖bourgainA6PhysicalBlockCoordinateSum
          N M q c (x₁ + z) x₂ x₃ x₄‖ ^ (6 : ℕ)) =
      ∫ z in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q c z x₂ x₃ x₄‖ ^ (6 : ℕ) := by
  let F : ℝ → ℝ := fun z =>
    ‖bourgainA6PhysicalBlockCoordinateSum
        N M q c z x₂ x₃ x₄‖ ^ (6 : ℕ)
  have hp : Function.Periodic F (N : ℝ) :=
    periodic_norm_bourgainA6PhysicalBlockCoordinateSum_pow_six_first
      N M q hN c x₂ x₃ x₄
  rw [show
      (∫ z in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q c (x₁ + z) x₂ x₃ x₄‖ ^ (6 : ℕ)) =
        ∫ z in (0 : ℝ)..(N : ℝ), F (z + x₁) by
      apply intervalIntegral.integral_congr
      intro z hz
      simp only [F, add_comm]]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [F, zero_add, add_zero, add_comm x₁ (N : ℝ)] using
    hp.intervalIntegral_add_eq x₁ 0

/-- Two independent full-period translations separate the two block
sixth moments exactly. -/
theorem integral_two_linear_translates_bourgainA6PhysicalBlockProduct_eq
    (N M q₁ q₂ : ℕ) (hN : 0 < N)
    (c₁ c₂ : Fin M → ℂ) (x₁ x₂ x₃ x₄ : ℝ) :
    (∫ z₂ in (0 : ℝ)..(N : ℝ),
      ∫ z₁ in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ (x₁ + z₁) x₂ x₃ x₄‖ ^ (6 : ℕ) *
          ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ (x₁ + z₂) x₂ x₃ x₄‖ ^ (6 : ℕ)) =
      (∫ z₁ in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ z₁ x₂ x₃ x₄‖ ^ (6 : ℕ)) *
      (∫ z₂ in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₂ c₂ z₂ x₂ x₃ x₄‖ ^ (6 : ℕ)) := by
  let A : ℝ :=
    ∫ z₁ in (0 : ℝ)..(N : ℝ),
      ‖bourgainA6PhysicalBlockCoordinateSum
          N M q₁ c₁ z₁ x₂ x₃ x₄‖ ^ (6 : ℕ)
  have h₁ :
      (∫ z₁ in (0 : ℝ)..(N : ℝ),
        ‖bourgainA6PhysicalBlockCoordinateSum
            N M q₁ c₁ (x₁ + z₁) x₂ x₃ x₄‖ ^ (6 : ℕ)) = A := by
    exact
      integral_norm_bourgainA6PhysicalBlockCoordinateSum_pow_six_first_translate
        N M q₁ hN c₁ x₁ x₂ x₃ x₄
  simp_rw [intervalIntegral.integral_mul_const, h₁]
  rw [intervalIntegral.integral_const_mul]
  rw [
    integral_norm_bourgainA6PhysicalBlockCoordinateSum_pow_six_first_translate
      N M q₂ hN c₂ x₁ x₂ x₃ x₄]

end

end RHTower
