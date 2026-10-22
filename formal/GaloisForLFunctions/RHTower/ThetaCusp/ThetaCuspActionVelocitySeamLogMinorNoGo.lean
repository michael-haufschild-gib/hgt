import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthBellTransfer
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedActionVelocityBalance

namespace RHTower

noncomputable section

/-!
# Exact wrong-way seam curvature of fixed-action velocity transport

The fixed-action centre-transport route to the completed-theta C5 gate would require the first
nonzero transverse seam coefficient to have forward orientation.  Exact self-dual modular-ODE
elimination proves the opposite sign.  The sharp survivor is the strict logarithmic seam law
`A C < 2 B²`, where `A = -L₂(0)`, `B = -L₄(0)`, and `C = -L₆(0)`.
-/

/-- Logarithmic seam minor controlling first nonzero transverse action-velocity transport. -/
def thetaCuspActionVelocitySeamLogMinor : ℝ :=
  iteratedDeriv 2 thetaCuspLogSource 0 *
      iteratedDeriv 6 thetaCuspLogSource 0 -
    2 * iteratedDeriv 4 thetaCuspLogSource 0 ^ (2 : ℕ)

/-- Above the exact theta threshold, every coefficient of the shifted modular polynomial has
the wrong sign for forward fixed-action transport. -/
theorem thetaCuspActionVelocitySeamMinorModularPolynomial_neg_of_threshold
    {X : ℝ} (hX : (191 / 10 : ℝ) ≤ X) :
    thetaCuspActionVelocitySeamMinorModularPolynomial X < 0 := by
  let y := X - (191 / 10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hXeq : X = (191 / 10 : ℝ) + y := by dsimp [y]; ring
  rw [hXeq]
  rw [show thetaCuspActionVelocitySeamMinorModularPolynomial
        ((191 / 10 : ℝ) + y) =
      -45563383733709932767 / 1677721600000000 +
        y * (-3476245474042946289 / 41943040000000) +
        y ^ (2 : ℕ) * (-12538280743912413 / 524288000000) +
        y ^ (3 : ℕ) * (-1288757011003993 / 419430400000) +
        y ^ (4 : ℕ) * (-3723531634839 / 16777216000) +
        y ^ (5 : ℕ) * (-40635683163 / 4194304000) +
        y ^ (6 : ℕ) * (-53459987 / 209715200) +
        y ^ (7 : ℕ) * (-156219 / 41943040) +
        y ^ (8 : ℕ) * (-387 / 16777216) by
      unfold thetaCuspActionVelocitySeamMinorModularPolynomial
      ring]
  have hy2 : 0 ≤ y ^ (2 : ℕ) := sq_nonneg y
  have hy3 : 0 ≤ y ^ (3 : ℕ) := pow_nonneg hy 3
  have hy4 : 0 ≤ y ^ (4 : ℕ) := pow_nonneg hy 4
  have hy5 : 0 ≤ y ^ (5 : ℕ) := pow_nonneg hy 5
  have hy6 : 0 ≤ y ^ (6 : ℕ) := pow_nonneg hy 6
  have hy7 : 0 ≤ y ^ (7 : ℕ) := pow_nonneg hy 7
  have hy8 : 0 ≤ y ^ (8 : ℕ) := pow_nonneg hy 8
  nlinarith

/-- The literal self-dual theta scale lies in the strict negative chamber. -/
theorem thetaCuspActionVelocitySeamMinorModularPolynomial_source_neg :
    thetaCuspActionVelocitySeamMinorModularPolynomial
      (thetaCuspSelfDualModularScale ^ (2 : ℕ)) < 0 :=
  thetaCuspActionVelocitySeamMinorModularPolynomial_neg_of_threshold
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le

/-- The source-specialized modular closure value is strictly negative. -/
theorem thetaCuspActionVelocitySeamMinorModularClosureValue_neg :
    thetaCuspActionVelocitySeamMinorModularClosureValue < 0 := by
  rw [thetaCuspActionVelocitySeamMinorModularClosureValue]
  have hm : 0 < thetaCuspSelfDualThetaMass := by
    linarith [
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand]
  exact mul_neg_of_pos_of_neg (pow_pos hm 4)
    thetaCuspActionVelocitySeamMinorModularPolynomial_source_neg

/-- The raw even-source seam polynomial selected by the transport minor is strictly negative. -/
theorem thetaCuspFullSource_actionVelocitySeamMinor_neg :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
    f 0 ^ (2 : ℕ) * f 2 * f 6 - 3 * f 0 * f 2 ^ (2 : ℕ) * f 4 +
        12 * f 2 ^ (4 : ℕ) - 2 * f 0 ^ (2 : ℕ) * f 4 ^ (2 : ℕ) < 0 := by
  dsimp only
  rw [thetaCuspFullSource_actionVelocitySeamMinor_eq_modularClosure]
  exact thetaCuspActionVelocitySeamMinorModularClosureValue_neg

/-- Exact Bell transfer from the raw source polynomial to the logarithmic transport minor. -/
theorem thetaCuspFullSource_actionVelocitySeamMinor_eq_logMinor :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
    f 0 ^ (2 : ℕ) * f 2 * f 6 - 3 * f 0 * f 2 ^ (2 : ℕ) * f 4 +
        12 * f 2 ^ (4 : ℕ) - 2 * f 0 ^ (2 : ℕ) * f 4 ^ (2 : ℕ) =
      thetaCuspFullSource 0 ^ (4 : ℕ) * thetaCuspActionVelocitySeamLogMinor := by
  dsimp only
  have hsource := congrFun thetaCuspFullSource_eq_logExponentialJetZero 0
  have h1 : iteratedDeriv 1 thetaCuspLogSource 0 = 0 :=
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (by norm_num)
  have h3 : iteratedDeriv 3 thetaCuspLogSource 0 = 0 :=
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (by norm_num)
  have h5 : iteratedDeriv 5 thetaCuspLogSource 0 = 0 :=
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (by norm_num)
  rw [iteratedDeriv_zero,
    iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet,
    hsource]
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetSix thetaCuspActionVelocitySeamLogMinor
  rw [h1, h3, h5]
  ring

/-- Exact theta-source obstruction: the first transverse fixed-action velocity seam minor has
strict reverse orientation. -/
theorem thetaCuspActionVelocitySeamLogMinor_neg :
    thetaCuspActionVelocitySeamLogMinor < 0 := by
  have hraw := thetaCuspFullSource_actionVelocitySeamMinor_neg
  dsimp only at hraw
  rw [thetaCuspFullSource_actionVelocitySeamMinor_eq_logMinor] at hraw
  have hmass : 0 < thetaCuspFullSource 0 ^ (4 : ℕ) :=
    pow_pos (thetaCuspFullSource_pos_all 0) 4
  rcases (mul_neg_iff.mp hraw) with h | h
  · exact h.2
  · exact False.elim (not_lt_of_ge hmass.le h.1)

/-- In curvature notation, the source satisfies the strict reverse of the proposed transverse
velocity orientation: `A C < 2 B²`. -/
theorem thetaCuspActionVelocitySeam_curvature_sixth_lt_two_fourth_sq :
    thetaCuspLogCurvature 0 *
        (-iteratedDeriv 6 thetaCuspLogSource 0) <
      2 * (-iteratedDeriv 4 thetaCuspLogSource 0) ^ (2 : ℕ) := by
  have h := thetaCuspActionVelocitySeamLogMinor_neg
  unfold thetaCuspActionVelocitySeamLogMinor at h
  unfold thetaCuspLogCurvature
  nlinarith

/-- The forward seam orientation required by monotone fixed-action transport is false for the
literal completed theta source. -/
theorem not_thetaCuspActionVelocitySeamLogMinor_nonneg :
    ¬ 0 ≤ thetaCuspActionVelocitySeamLogMinor :=
  not_le.mpr thetaCuspActionVelocitySeamLogMinor_neg

end

end RHTower
