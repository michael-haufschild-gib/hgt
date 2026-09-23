import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Regular negative-GUP Friedmann law

Equations (17)--(18) of arXiv:2609.02912 have removable quotients at
zero coupling. On the negative branch `beta * PlanckLength² = -b²`,
rationalization defines a smooth friction factor and Friedmann density
for all real `b,H`. Their derivative relation is exact, not a perturbative
expansion. The classical limit is included as an actual parameter value.
-/
noncomputable section
namespace HTGeometry

/-- Square-root deformation on the entire negative-coupling branch. -/
def gupRoot (b H : ℝ) : ℝ := Real.sqrt (1 + b ^ (2 : ℕ) * H ^ (2 : ℕ))

/-- Rationalized coefficient of `Hdot` in the second Friedmann equation. -/
def gupFriction (b H : ℝ) : ℝ := (1 + gupRoot b H) / 2

/-- Continuous extension of the first Friedmann left side at zero coupling. -/
def gupDensity (b H : ℝ) : ℝ :=
  H ^ (2 : ℕ) / 2 + H ^ (2 : ℕ) * (1 + gupRoot b H + gupRoot b H ^ (2 : ℕ)) /
    (3 * (1 + gupRoot b H))

theorem gupRoot_positive (b H : ℝ) : 0 < gupRoot b H := by
  unfold gupRoot
  positivity

theorem gupRoot_sq (b H : ℝ) : gupRoot b H ^ (2 : ℕ) = 1 + b ^ (2 : ℕ) * H ^ (2 : ℕ) := by
  unfold gupRoot
  exact Real.sq_sqrt (by positivity)

/-- Negative coupling increases, rather than decreases, the friction coefficient. -/
theorem one_le_gupFriction (b H : ℝ) : 1 ≤ gupFriction b H := by
  have hs := gupRoot_sq b H
  have hp := gupRoot_positive b H
  have hh : 1 ≤ gupRoot b H := by nlinarith [sq_nonneg (b * H)]
  unfold gupFriction
  linarith

/-- Polynomial identity replacing the singular native quotient in equation (17). -/
theorem gupFriction_rationalization (b H : ℝ) :
    (2 - 2 * gupRoot b H) * gupFriction b H = -(b ^ (2 : ℕ) * H ^ (2 : ℕ)) := by
  unfold gupFriction
  nlinarith [gupRoot_sq b H]

/-- The regularized coefficient satisfies a quadratic algebraic equation. -/
theorem gupFriction_quadratic (b H : ℝ) :
    gupFriction b H ^ (2 : ℕ) - gupFriction b H = b ^ (2 : ℕ) * H ^ (2 : ℕ) / 4 := by
  unfold gupFriction
  nlinarith [gupRoot_sq b H]

/-- Polynomial identity replacing the singular native quotient in equation (18). -/
theorem gupDensity_rationalization (b H : ℝ) :
    3 * b ^ (2 : ℕ) * (gupDensity b H - H ^ (2 : ℕ) / 2) = gupRoot b H ^ (3 : ℕ) - 1 := by
  have hp : 1 + gupRoot b H ≠ 0 := by linarith [gupRoot_positive b H]
  have hs := gupRoot_sq b H
  unfold gupDensity
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * (1 + gupRoot b H + gupRoot b H ^ (2 : ℕ))) hs]

/-- Classical Friedmann friction at zero deformation. -/
theorem gupFriction_zero (H : ℝ) : gupFriction 0 H = 1 := by
  norm_num [gupFriction, gupRoot]

/-- Classical Friedmann density at zero deformation. -/
theorem gupDensity_zero (H : ℝ) : gupDensity 0 H = H ^ (2 : ℕ) := by
  norm_num [gupDensity, gupRoot]
  ring

/-- Nonnegative excess over classical Friedmann density. -/
theorem gupDensity_excess (b H : ℝ) :
    gupDensity b H - H ^ (2 : ℕ) =
      H ^ (2 : ℕ) * (gupRoot b H - 1) * (2 * gupRoot b H + 1) /
        (6 * (1 + gupRoot b H)) := by
  have hp : 1 + gupRoot b H ≠ 0 := by linarith [gupRoot_positive b H]
  unfold gupDensity
  field_simp [hp]
  ring

/-- The corrected density dominates `H²` on the negative branch. -/
theorem sq_le_gupDensity (b H : ℝ) : H ^ (2 : ℕ) ≤ gupDensity b H := by
  have hs : 0 ≤ gupRoot b H - 1 := by
    have h := one_le_gupFriction b H
    unfold gupFriction at h
    linarith
  have hn : 0 ≤ gupDensity b H - H ^ (2 : ℕ) := by
    rw [gupDensity_excess]
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg H) hs)
      (by linarith [gupRoot_positive b H])) (by linarith [gupRoot_positive b H])
  linarith

/-- Derivative of the square-root branch, including `b = 0` and `H = 0`. -/
theorem hasDerivAt_gupRoot (b H : ℝ) :
    HasDerivAt (gupRoot b) (b ^ (2 : ℕ) * H / gupRoot b H) H := by
  have h := (((hasDerivAt_const H 1).add
    (((hasDerivAt_id H).pow 2).const_mul (b ^ (2 : ℕ)))).sqrt
      (by positivity : 1 + b ^ (2 : ℕ) * H ^ (2 : ℕ) ≠ 0))
  exact h.congr_deriv (by dsimp [gupRoot]; ring)


/-- Exact differential consistency of the two regularized Friedmann equations. -/
theorem hasDerivAt_gupDensity (b H : ℝ) :
    HasDerivAt (gupDensity b) (2 * H * gupFriction b H) H := by
  have hr := hasDerivAt_gupRoot b H
  have hp : 3 * (1 + gupRoot b H) ≠ 0 := by linarith [gupRoot_positive b H]
  have h := (((hasDerivAt_id H).pow 2).div_const 2).add
    ((((hasDerivAt_id H).pow 2).mul
      (((hasDerivAt_const H 1).add hr).add (hr.pow 2))).div
        (((hasDerivAt_const H 1).add hr).const_mul 3) hp)
  apply h.congr_deriv
  dsimp [gupFriction]
  have hs := gupRoot_sq b H
  have hn := (gupRoot_positive b H).ne'
  have hden : 1 + gupRoot b H ≠ 0 := by linarith [gupRoot_positive b H]
  field_simp [hn, hden]
  nlinarith [congrArg (fun z : ℝ => z * H) hs,
    congrArg (fun z : ℝ => z * (H * gupRoot b H)) hs,
    congrArg (fun z : ℝ => z * (H * gupRoot b H ^ (2 : ℕ))) hs]

end HTGeometry
