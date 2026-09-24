import GaloisForLFunctions.RHTower.ThetaGibbsMomentLogConvexity
import GaloisForLFunctions.RHTower.ThetaGibbsSteinSourceMinor

/-!
# Separating the Ward combinations into per-index Gibbs bounds

The Stein certificates bound only the Ward combinations `W (j+1) = 4 (j+1) G (2j+1) - G (2j+2)`,
never a single Gibbs moment.  The absolute factorial ceiling bounds the subtracted term, so the
combinations separate.  Here that is carried out at the first place where it is needed: an
individual upper bound for `G 3`, from the Stein upper bound on `W 2` and the ceiling at index `4`.
-/

namespace RHTower

noncomputable section

/-- Explicit ceiling at index four. -/
theorem thetaCuspLiouvilleGibbsMoment_four_le :
    thetaCuspLiouvilleGibbsMoment 4 1 ≤ (7 / 100 : ℝ) * Real.exp (-Real.pi) := by
  have hceil := twelve_pow_mul_thetaCuspFirstAtomGibbsMoment_sq_le 4
  have hnn := thetaCuspLiouvilleGibbsMoment_nonneg 4 1
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  norm_num [Nat.factorial] at hceil
  nlinarith [hceil, hnn, hexp, sq_nonneg (thetaCuspLiouvilleGibbsMoment 4 1 - (7/100) * Real.exp (-Real.pi))]

/-- **Per-index separation.**  The Stein bound on the second Ward moment together with the ceiling
at index four gives an individual upper bound on the third Gibbs moment. -/
theorem thetaCuspLiouvilleGibbsMoment_three_le :
    thetaCuspLiouvilleGibbsMoment 3 1 ≤ (11 / 1000 : ℝ) * Real.exp (-Real.pi) := by
  obtain ⟨-, -, hW2, -⟩ := thetaCuspFirstAtomWardMoment_stein_bounds
  have hfour := thetaCuspLiouvilleGibbsMoment_four_le
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  simp only [thetaCuspFirstAtomWardMoment] at hW2
  norm_num at hW2
  linarith [hW2, hfour, hexp]

/-- Explicit ceiling at index six. -/
theorem thetaCuspLiouvilleGibbsMoment_six_le :
    thetaCuspLiouvilleGibbsMoment 6 1 ≤ (32 / 1000 : ℝ) * Real.exp (-Real.pi) := by
  have hceil := twelve_pow_mul_thetaCuspFirstAtomGibbsMoment_sq_le 6
  have hnn := thetaCuspLiouvilleGibbsMoment_nonneg 6 1
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  norm_num [Nat.factorial] at hceil
  nlinarith [hceil, hnn, hexp,
    sq_nonneg (thetaCuspLiouvilleGibbsMoment 6 1 - (32/1000) * Real.exp (-Real.pi))]

/-- Explicit ceiling at index five. -/
theorem thetaCuspLiouvilleGibbsMoment_five_le :
    thetaCuspLiouvilleGibbsMoment 5 1 ≤ (44 / 1000 : ℝ) * Real.exp (-Real.pi) := by
  have hceil := twelve_pow_mul_thetaCuspFirstAtomGibbsMoment_sq_le 5
  have hnn := thetaCuspLiouvilleGibbsMoment_nonneg 5 1
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  norm_num [Nat.factorial] at hceil
  nlinarith [hceil, hnn, hexp,
    sq_nonneg (thetaCuspLiouvilleGibbsMoment 5 1 - (44/1000) * Real.exp (-Real.pi))]

/-- **Per-index separation at the next rung.**  The Stein lower bound on the third Ward moment
gives an individual strictly positive lower bound for the fifth Gibbs moment. -/
theorem thetaCuspLiouvilleGibbsMoment_five_ge :
    (441 / 2400000 : ℝ) * Real.exp (-Real.pi) ≤ thetaCuspLiouvilleGibbsMoment 5 1 := by
  obtain ⟨-, -, -, hW3⟩ := thetaCuspFirstAtomWardMoment_stein_bounds
  have hsix := thetaCuspLiouvilleGibbsMoment_nonneg 6 1
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  simp only [thetaCuspFirstAtomWardMoment] at hW3
  norm_num at hW3
  linarith [hW3, hsix, hexp]

end

end RHTower
