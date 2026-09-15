import GaloisForLFunctions.RHTower.XiMassRapidityPhaseGeometry
import GaloisForLFunctions.RHTower.NearDiagonalPhaseCurvature

/-!
# Direct Vaughan phase transport is incompatible with the timelike mass action

The reduced timelike mass action `sqrt (u² - h²)` is even in the frequency
coordinate.  The positive near-diagonal Vaughan phase, pulled back through the
natural logarithmic coordinate `n = exp h`, is strictly asymmetric.  Hence the
two kernels cannot be identified directly.  This excludes only unchanged phase
transport; it leaves open a genuinely new mass-phase bilinear estimate or a
nontrivial transport identity.
-/

namespace RHTower

noncomputable section

/-- Timelike mass action after rapidity reduction. -/
def xiMassTimelikeAction (u h : ℝ) : ℝ := Real.sqrt (u ^ 2 - h ^ 2)

/-- The Vaughan near-diagonal phase in the natural logarithmic coordinate. -/
def nearDiagonalLogPhase (T r h : ℝ) : ℝ := nearDiagonalPhase T r (Real.exp h)

theorem xiMassTimelikeAction_one_eq_neg_one (u : ℝ) :
    xiMassTimelikeAction u 1 = xiMassTimelikeAction u (-1) := by
  simp [xiMassTimelikeAction]

theorem nearDiagonalLogPhase_one_lt_neg_one {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    nearDiagonalLogPhase T r 1 < nearDiagonalLogPhase T r (-1) := by
  have hexp : Real.exp (-1 : ℝ) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hratio : r / Real.exp 1 < r / Real.exp (-1 : ℝ) := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
    exact mul_lt_mul_of_pos_left hexp hr
  have hlog : Real.log (1 + r / Real.exp 1) < Real.log (1 + r / Real.exp (-1 : ℝ)) :=
    Real.strictMonoOn_log (show 0 < 1 + r / Real.exp 1 by positivity)
      (show 0 < 1 + r / Real.exp (-1 : ℝ) by positivity) (by linarith)
  rw [nearDiagonalLogPhase, nearDiagonalLogPhase, nearDiagonalPhase, nearDiagonalPhase]
  exact mul_lt_mul_of_pos_left hlog (by positivity)

/-- Positive Vaughan log-phases are strictly antitone in their natural log coordinate. -/
theorem nearDiagonalLogPhase_strictAnti {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    StrictAnti (nearDiagonalLogPhase T r) := by
  intro x y hxy
  have hexp : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  have hratio : r / Real.exp y < r / Real.exp x := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
    exact mul_lt_mul_of_pos_left hexp hr
  have hlog : Real.log (1 + r / Real.exp y) < Real.log (1 + r / Real.exp x) :=
    Real.strictMonoOn_log (show 0 < 1 + r / Real.exp y by positivity)
      (show 0 < 1 + r / Real.exp x by positivity) (by linarith)
  rw [nearDiagonalLogPhase, nearDiagonalLogPhase, nearDiagonalPhase, nearDiagonalPhase]
  exact mul_lt_mul_of_pos_left hlog (by positivity)

/-- No affine-coordinate and affine-amplitude normalization of the reduced timelike mass action
can directly equal the positive Vaughan phase in the natural log coordinate. -/
theorem affine_xiMassTimelikeAction_ne_nearDiagonalLogPhase
    {u T r A B lambda b : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (fun h => A * xiMassTimelikeAction u (lambda * (h - b)) + B) ≠
      nearDiagonalLogPhase T r := by
  intro hEq
  have haction : xiMassTimelikeAction u (lambda * ((b + 1) - b)) =
      xiMassTimelikeAction u (lambda * ((b - 1) - b)) := by
    rw [xiMassTimelikeAction, xiMassTimelikeAction]
    congr 1
    ring
  have hsym :
      A * xiMassTimelikeAction u (lambda * ((b + 1) - b)) + B =
        A * xiMassTimelikeAction u (lambda * ((b - 1) - b)) + B := by
    rw [haction]
  have hnear : nearDiagonalLogPhase T r (b + 1) = nearDiagonalLogPhase T r (b - 1) := by
    calc
      nearDiagonalLogPhase T r (b + 1) =
          A * xiMassTimelikeAction u (lambda * ((b + 1) - b)) + B :=
        (congrFun hEq (b + 1)).symm
      _ = A * xiMassTimelikeAction u (lambda * ((b - 1) - b)) + B := hsym
      _ = nearDiagonalLogPhase T r (b - 1) := congrFun hEq (b - 1)
  exact (ne_of_lt (nearDiagonalLogPhase_strictAnti hT hr (by linarith))) hnear

/-- No direct equality can transport the positive Vaughan phase to the reduced
timelike mass action in their natural frequency coordinates. -/
theorem xiMassTimelikeAction_ne_nearDiagonalLogPhase {u T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    xiMassTimelikeAction u ≠ nearDiagonalLogPhase T r := by
  intro hEq
  have hmass : xiMassTimelikeAction u 1 = xiMassTimelikeAction u (-1) :=
    xiMassTimelikeAction_one_eq_neg_one u
  have hnear : nearDiagonalLogPhase T r 1 = nearDiagonalLogPhase T r (-1) := by
    calc
      nearDiagonalLogPhase T r 1 = xiMassTimelikeAction u 1 := (congrFun hEq 1).symm
      _ = xiMassTimelikeAction u (-1) := hmass
      _ = nearDiagonalLogPhase T r (-1) := congrFun hEq (-1)
  exact (ne_of_lt (nearDiagonalLogPhase_one_lt_neg_one hT hr)) hnear

end

end RHTower
