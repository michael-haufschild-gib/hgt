import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Exact calculus of the GUP momentum deformation

arXiv:2609.02912, equations (29)--(35), uses `K = k (1 + b k²)`.
Its exact logarithmic derivative is `(1 + 3 b k²)/(1 + b k²)`.
The positive deformation below takes `b = a²` and `k = exp t`, so all
logarithms and denominators are valid for every real parameter, including zero
coupling. The negative branch has an explicit nonzero-momentum turning point.
-/

noncomputable section
namespace HTGeometry

/-- Cubic momentum deformation, with `b = beta * PlanckLength²`. -/
def gupMomentum (b k : ℝ) : ℝ := k * (1 + b * k ^ (2 : ℕ))

/-- Exact symbolic derivative of the momentum deformation. -/
theorem hasDerivAt_gupMomentum (b k : ℝ) :
    HasDerivAt (gupMomentum b) (1 + 3 * b * k ^ (2 : ℕ)) k := by
  have h := (hasDerivAt_id k).mul
    ((hasDerivAt_const k 1).add ((hasDerivAt_id k).pow 2 |>.const_mul b))
  exact h.congr_deriv (by dsimp; ring)


/-- Logarithm of positive deformed momentum, in logarithmic input coordinates. -/
def gupLogMomentum (a t : ℝ) : ℝ :=
  Real.log (gupMomentum (a ^ (2 : ℕ)) (Real.exp t))

/-- The chain-rule conversion from logarithmic deformed momentum to logarithmic momentum. -/
def gupLogSlopeCorrection (a t : ℝ) : ℝ :=
  (1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) / (1 + 3 * a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ))

theorem gupMomentum_positive (a t : ℝ) :
    0 < gupMomentum (a ^ (2 : ℕ)) (Real.exp t) := by
  unfold gupMomentum
  positivity

/-- The exact Jacobian has a cubic coefficient in its numerator. -/
theorem hasDerivAt_gupLogMomentum (a t : ℝ) :
    HasDerivAt (gupLogMomentum a)
      ((1 + 3 * a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) / (1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ))) t := by
  have h := ((hasDerivAt_gupMomentum (a ^ (2 : ℕ)) (Real.exp t)).comp t
    (Real.hasDerivAt_exp t)).log (gupMomentum_positive a t).ne'
  convert h using 1
  · rfl
  · dsimp [gupMomentum, Function.comp_def]
    field_simp

/-- Reciprocal Jacobians cancel with no exceptional positive-branch parameters. -/
theorem gupLogSlopeCorrection_inverse (a t : ℝ) :
    gupLogSlopeCorrection a t * deriv (gupLogMomentum a) t = 1 := by
  rw [(hasDerivAt_gupLogMomentum a t).deriv]
  unfold gupLogSlopeCorrection
  have h1 : 1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ) ≠ 0 := by positivity
  have h3 : 1 + 3 * a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp

/-- Positive deformation can only reduce the exact logarithmic slope. -/
theorem gupLogSlopeCorrection_le_one (a t : ℝ) :
    gupLogSlopeCorrection a t ≤ 1 := by
  unfold gupLogSlopeCorrection
  apply (div_le_one (by positivity)).2
  nlinarith [sq_nonneg (a * Real.exp t)]

/-- The reduction is always strictly less than a factor of three. -/
theorem one_third_lt_gupLogSlopeCorrection (a t : ℝ) :
    1 / 3 < gupLogSlopeCorrection a t := by
  unfold gupLogSlopeCorrection
  apply (lt_div_iff₀ (by positivity)).2
  ring_nf
  linarith

/-- Exact residual of the paper's multiplier against the logarithmic chain rule. -/
theorem gup_paper_multiplier_residual (a t : ℝ) :
    (1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) - gupLogSlopeCorrection a t =
      3 * (a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) * (1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) /
        (1 + 3 * a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) := by
  unfold gupLogSlopeCorrection
  field_simp
  ring

/-- The paper multiplier equals the exact chain-rule factor only at zero deformation. -/
theorem gup_paper_multiplier_eq_iff (a t : ℝ) :
    (1 + a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ)) = gupLogSlopeCorrection a t ↔ a = 0 := by
  constructor
  · intro h
    have hm := gupLogSlopeCorrection_le_one a t
    rw [← h] at hm
    have hz : a ^ (2 : ℕ) * Real.exp t ^ (2 : ℕ) = 0 := by
      nlinarith [sq_nonneg (a * Real.exp t)]
    simpa [mul_eq_zero, Real.exp_ne_zero] using hz
  · rintro rfl
    simp [gupLogSlopeCorrection]

/-- A negative deformation can erase the Jacobian while momentum stays nonzero. -/
theorem gup_negative_turning_point :
    gupMomentum (-(1 / 3)) 1 = 2 / 3 ∧
      deriv (gupMomentum (-(1 / 3))) 1 = 0 := by
  rw [(hasDerivAt_gupMomentum _ _).deriv]
  norm_num [gupMomentum]

/-- A quotient-free consistency law remains meaningful at every deformation value. -/
theorem gup_consistency_polynomial (b k epsilon : ℝ) :
    (1 + b * k ^ (2 : ℕ)) * (16 * epsilon) +
      8 * (-(1 + b * k ^ (2 : ℕ)) * (2 * epsilon)) = 0 := by
  ring

/-- Exact difference factorization classifies collisions of the deformed momentum map. -/
theorem gupMomentum_difference (b k l : ℝ) :
    gupMomentum b k - gupMomentum b l =
      (k - l) * (1 + b * (k ^ (2 : ℕ) + k * l + l ^ (2 : ℕ))) := by
  unfold gupMomentum
  ring

/-- Positive deformation never identifies distinct input momenta. -/
theorem gupMomentum_sq_injective (a : ℝ) : Function.Injective (gupMomentum (a ^ (2 : ℕ))) := by
  intro k l h
  have hr := gupMomentum_difference (a ^ (2 : ℕ)) k l
  rw [h, sub_self] at hr
  have hs : 0 ≤ k ^ (2 : ℕ) + k * l + l ^ (2 : ℕ) := by nlinarith [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hp : 1 + a ^ (2 : ℕ) * (k ^ (2 : ℕ) + k * l + l ^ (2 : ℕ)) ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hr.symm).resolve_right hp)

/-- Negative deformation has an exact three-point collision. -/
theorem gupMomentum_negative_three_point_collision :
    gupMomentum (-1) (-1) = gupMomentum (-1) 0 ∧
      gupMomentum (-1) 0 = gupMomentum (-1) 1 := by
  norm_num [gupMomentum]

end HTGeometry
