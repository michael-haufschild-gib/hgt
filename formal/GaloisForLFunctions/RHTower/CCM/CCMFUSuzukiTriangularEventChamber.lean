import GaloisForLFunctions.RHTower.Suzuki.SuzukiAffineMixtureTriangularCurvatureReduction

/-!
# Logarithmic event chambers of the CCM--FU curvature transform

Between consecutive arithmetic event walls the literal signed transform has a
fixed finite source.  Its only moving coordinate is the reciprocal upper
wall.  This keeps the prime--polar cancellation inside each curvature cell
and turns the continuous cofinal problem into a discrete endpoint problem.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- On the open logarithmic chamber before the next integer event, the
floor-selected Suzuki event index is literally constant. -/
theorem suzukiCheckpointEventIndex_eq_of_log_chamber
    {n : ℕ} (hn : 1 ≤ n) {H : ℝ}
    (hleft : Real.log (n : ℝ) ≤ H)
    (hright : H < Real.log ((n + 1 : ℕ) : ℝ)) :
    suzukiCheckpointEventIndex H = n := by
  unfold suzukiCheckpointEventIndex
  apply (Nat.floor_eq_iff (Real.exp_pos H).le).mpr
  constructor
  · calc
      (n : ℝ) = Real.exp (Real.log (n : ℝ)) := by
        rw [Real.exp_log]
        exact_mod_cast (show 0 < n by omega)
      _ ≤ Real.exp H := Real.exp_le_exp.mpr hleft
  · calc
      Real.exp H < Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) :=
        Real.exp_lt_exp.mpr hright
      _ = ((n + 1 : ℕ) : ℝ) := by
        rw [Real.exp_log]
        positivity
      _ = (n : ℝ) + 1 := by
        push_cast
        ring

/-- Fixed finite source coefficient of the third-grade triangular curvature
transform in event chamber `n`. -/
def suzukiCheckpointTriangularChamberConstant (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 n,
    suzukiCheckpointSignedCurvatureCell j *
      (32 / Real.log ((j + 1 : ℕ) : ℝ) ^ (3 : ℕ))

/-- Reciprocal-upper-wall coefficient of the same fixed signed source. -/
def suzukiCheckpointTriangularChamberInverseMoment (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 n,
    suzukiCheckpointSignedCurvatureCell j *
      (32 / Real.log ((j + 1 : ℕ) : ℝ) ^ (2 : ℕ))

/-- The source algebra inside a fixed event chamber.  This lemma has no
arithmetic hypothesis: all cancellation remains in its literal finite sum. -/
private theorem suzukiCheckpointTriangularFixedSource_eq_chamber_affine
    (n : ℕ) {H : ℝ} (hH : H ≠ 0) :
    (∑ j ∈ Finset.Ico 2 n,
      suzukiCheckpointSignedCurvatureCell j *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H
          (Real.log ((j + 1 : ℕ) : ℝ)) ) =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n / H := by
  unfold suzukiCheckpointTriangularChamberConstant
    suzukiCheckpointTriangularChamberInverseMoment
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
  have hjlog : 0 < Real.log ((j + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < j + 1 by omega)
  unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  field_simp [hH, hjlog.ne']

/-- **Exact event-chamber law.**  Before the next arithmetic event, the
literal CCM--FU signed triangular curvature transform is affine in `1 / H`.
No cell is estimated or sign-split. -/
theorem suzukiCheckpointTriangularCurvatureTransform_eq_chamber_affine
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ}
    (hleft : Real.log (n : ℝ) ≤ H)
    (hright : H < Real.log ((n + 1 : ℕ) : ℝ)) :
    suzukiCheckpointTriangularCurvatureTransform H =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n / H := by
  have hindex := suzukiCheckpointEventIndex_eq_of_log_chamber
    (by omega : 1 ≤ n) hleft hright
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hH : 0 < H := hlogn.trans_le hleft
  rw [suzukiCheckpointTriangularCurvatureTransform, hindex]
  exact suzukiCheckpointTriangularFixedSource_eq_chamber_affine n hH.ne'

/-- At the next event wall the newly admitted curvature cell has zero
triangular coefficient.  Thus the left chamber's reciprocal-affine law
extends to its closed right endpoint without a jump. -/
theorem suzukiCheckpointTriangularCurvatureTransform_log_succ_eq_chamber_affine
    {n : ℕ} (hn : 2 ≤ n) :
    suzukiCheckpointTriangularCurvatureTransform
        (Real.log ((n + 1 : ℕ) : ℝ)) =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n /
          Real.log ((n + 1 : ℕ) : ℝ) := by
  have hlog : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hnext : Real.log ((n + 1 : ℕ) : ℝ) <
      Real.log ((n + 2 : ℕ) : ℝ) := by
    exact (Real.strictMonoOn_log.lt_iff_lt hn1pos hn2pos).mpr
      (by exact_mod_cast (show n + 1 < n + 2 by omega))
  have hindex := suzukiCheckpointEventIndex_eq_of_log_chamber
    (n := n + 1) (by omega : 1 ≤ n + 1) le_rfl hnext
  rw [suzukiCheckpointTriangularCurvatureTransform, hindex,
    Finset.sum_Ico_succ_top hn]
  have hzero : suzukiCheckpointSignedCurvatureCell n *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight
        (Real.log ((n + 1 : ℕ) : ℝ))
        (Real.log ((n + 1 : ℕ) : ℝ)) = 0 := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    rw [div_self hlog.ne', sub_self]
    simp
  rw [hzero, add_zero]
  exact suzukiCheckpointTriangularFixedSource_eq_chamber_affine n hlog.ne'

/-- **Exact endpoint velocity.**  Consecutive natural-log readings of the literal
signed transform differ by one signed inverse-moment history times the reciprocal-log
mesh gap.  Thus the remaining cofinal problem is a single telescoping signed action;
no curvature cell has been replaced by its absolute value. -/
theorem suzukiCheckpointTriangularCurvatureTransform_log_succ_sub_log_eq_inverseMoment
    {n : ℕ} (hn : 2 ≤ n) :
    suzukiCheckpointTriangularCurvatureTransform
        (Real.log ((n + 1 : ℕ) : ℝ)) -
      suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ)) =
        suzukiCheckpointTriangularChamberInverseMoment n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnext : Real.log (n : ℝ) < Real.log ((n + 1 : ℕ) : ℝ) := by
    exact (Real.strictMonoOn_log.lt_iff_lt hnpos hn1pos).mpr
      (by exact_mod_cast (show n < n + 1 by omega))
  rw [suzukiCheckpointTriangularCurvatureTransform_log_succ_eq_chamber_affine hn,
    suzukiCheckpointTriangularCurvatureTransform_eq_chamber_affine hn le_rfl hnext]
  ring

/-- **Exact endpoint Volterra law.**  Every finite displacement of natural-log
endpoint readings is the telescoping reciprocal-log action of the literal signed
inverse-moment history.  This retains the entire prime--polar cancellation and is
the discrete cofinal object a source-faithful producer must bound. -/
theorem suzukiCheckpointTriangularCurvatureTransform_log_add_eq_inverseMomentAction
    (n r : ℕ) (hn : 2 ≤ n) :
    suzukiCheckpointTriangularCurvatureTransform
        (Real.log ((n + r + 1 : ℕ) : ℝ)) -
      suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ)) =
        ∑ k ∈ Finset.Ico n (n + r + 1),
          suzukiCheckpointTriangularChamberInverseMoment k *
            (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
  induction r with
  | zero =>
      rw [Finset.sum_Ico_succ_top (le_refl n)]
      simpa using
        suzukiCheckpointTriangularCurvatureTransform_log_succ_sub_log_eq_inverseMoment hn
  | succ r ih =>
      have hnr : 2 ≤ n + r + 1 := by omega
      have hstep :=
        suzukiCheckpointTriangularCurvatureTransform_log_succ_sub_log_eq_inverseMoment hnr
      rw [show n + (r + 1) + 1 = n + r + 2 by omega]
      calc
        suzukiCheckpointTriangularCurvatureTransform
            (Real.log ((n + r + 2 : ℕ) : ℝ)) -
          suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ)) =
            (suzukiCheckpointTriangularCurvatureTransform
              (Real.log ((n + r + 2 : ℕ) : ℝ)) -
                suzukiCheckpointTriangularCurvatureTransform
                  (Real.log ((n + r + 1 : ℕ) : ℝ))) +
              (suzukiCheckpointTriangularCurvatureTransform
                (Real.log ((n + r + 1 : ℕ) : ℝ)) -
                  suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ))) := by ring
        _ = suzukiCheckpointTriangularChamberInverseMoment (n + r + 1) *
              (1 / Real.log ((n + r + 1 : ℕ) : ℝ) -
                1 / Real.log ((n + r + 2 : ℕ) : ℝ)) +
            ∑ k ∈ Finset.Ico n (n + r + 1),
              suzukiCheckpointTriangularChamberInverseMoment k *
                (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
              rw [hstep, ih]
        _ = ∑ k ∈ Finset.Ico n (n + r + 2),
              suzukiCheckpointTriangularChamberInverseMoment k *
                (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
              rw [Finset.sum_Ico_succ_top (by omega : n ≤ n + r + 1)]
              ring

/-- Absolute values of reciprocal-affine functions have no interior excess on
a positive interval.  This is the analytic mechanism that turns a continuous
event chamber into two discrete endpoint tests. -/
private theorem abs_sub_div_le_max_endpoint
    {A B L H U : ℝ} (hL : 0 < L) (hLU : L < U)
    (hLH : L ≤ H) (hHU : H ≤ U) :
    |A - B / H| ≤ max |A - B / L| |A - B / U| := by
  let alpha : ℝ := L * (U - H) / (H * (U - L))
  have hH : 0 < H := hL.trans_le hLH
  have hU : 0 < U := hH.trans_le hHU
  have hUL : 0 < U - L := sub_pos.mpr hLU
  have hden : 0 < H * (U - L) := mul_pos hH hUL
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg (mul_nonneg hL.le (sub_nonneg.mpr hHU)) hden.le
  have halpha1 : alpha ≤ 1 := by
    dsimp only [alpha]
    rw [div_le_one hden]
    nlinarith
  have hreciprocal : 1 / H = alpha / L + (1 - alpha) / U := by
    dsimp only [alpha]
    field_simp [hL.ne', hH.ne', hU.ne', hUL.ne']
    ring
  have hrepr : A - B / H =
      alpha * (A - B / L) + (1 - alpha) * (A - B / U) := by
    simp only [div_eq_mul_inv]
    have hreciprocal' : H⁻¹ = alpha * L⁻¹ + (1 - alpha) * U⁻¹ := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using hreciprocal
    rw [hreciprocal']
    ring
  rw [hrepr]
  calc
    |alpha * (A - B / L) + (1 - alpha) * (A - B / U)| ≤
        |alpha * (A - B / L)| + |(1 - alpha) * (A - B / U)| := abs_add_le _ _
    _ = alpha * |A - B / L| + (1 - alpha) * |A - B / U| := by
      rw [abs_mul, abs_of_nonneg halpha0, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr halpha1)]
    _ ≤ alpha * max |A - B / L| |A - B / U| +
          (1 - alpha) * max |A - B / L| |A - B / U| := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max |A - B / L| |A - B / U| := by ring

/-- **Discrete endpoint reduction.**  Every value of the literal signed
CCM--FU curvature transform in a closed logarithmic event chamber is bounded
by its two neighboring natural endpoint values.  It preserves all signed
prime--polar cancellation and introduces no absolute source estimate. -/
theorem abs_suzukiCheckpointTriangularCurvatureTransform_le_log_endpoints
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ}
    (hleft : Real.log (n : ℝ) ≤ H)
    (hright : H ≤ Real.log ((n + 1 : ℕ) : ℝ)) :
    |suzukiCheckpointTriangularCurvatureTransform H| ≤
      max |suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ))|
        |suzukiCheckpointTriangularCurvatureTransform
          (Real.log ((n + 1 : ℕ) : ℝ))| := by
  have hL : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hU : Real.log (n : ℝ) < Real.log ((n + 1 : ℕ) : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact (Real.strictMonoOn_log.lt_iff_lt
      hnpos hn1pos).mpr
        (by exact_mod_cast (show n < n + 1 by omega))
  have hcurrent : suzukiCheckpointTriangularCurvatureTransform H =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n / H := by
    rcases hright.lt_or_eq with hlt | heq
    · exact suzukiCheckpointTriangularCurvatureTransform_eq_chamber_affine
        hn hleft hlt
    · subst H
      exact suzukiCheckpointTriangularCurvatureTransform_log_succ_eq_chamber_affine hn
  have hleftValue : suzukiCheckpointTriangularCurvatureTransform (Real.log (n : ℝ)) =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n / Real.log (n : ℝ) :=
    suzukiCheckpointTriangularCurvatureTransform_eq_chamber_affine
      hn le_rfl hU
  have hrightValue : suzukiCheckpointTriangularCurvatureTransform
      (Real.log ((n + 1 : ℕ) : ℝ)) =
      suzukiCheckpointTriangularChamberConstant n -
        suzukiCheckpointTriangularChamberInverseMoment n /
          Real.log ((n + 1 : ℕ) : ℝ) :=
    suzukiCheckpointTriangularCurvatureTransform_log_succ_eq_chamber_affine hn
  rw [hcurrent, hleftValue, hrightValue]
  exact abs_sub_div_le_max_endpoint hL hU hleft hright

end

end RHTower
