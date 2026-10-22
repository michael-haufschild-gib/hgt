import GaloisForLFunctions.RHTower.Suzuki.SuzukiAffineMixtureTriangularCurvatureReduction
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedCurvatureArchRenormalization
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# First-moment Abel transfer to the CCM--FU triangular transform

Linear growth of the exact event-label-weighted Suzuki curvature prefixes controls both
reciprocal-log transforms occurring in the third-grade triangular reporter.  This is a signed
Abel argument: no Jordan decomposition or absolute cell majorant is used.  Consequently a single
first-moment bound, and in particular a bound on the central incoming unit-Riesz barycenter,
implies the canonical CCM--FU affine-tail premise and hence RH.
-/

open Set
open scoped BigOperators

namespace HTGeometry

/-- Reciprocal-log Abel weight on the physical checkpoint range `k = i + 3`. -/
noncomputable def shiftedReciprocalLogWeight (p i : ℕ) : ℝ :=
  1 / (((i : ℝ) + 3) * Real.log ((i : ℝ) + 3) ^ p)

/-- Potential whose discrete decrement is the non-harmonic part of the Abel variation. -/
noncomputable def shiftedReciprocalLogPotential (p i : ℕ) : ℝ :=
  1 / Real.log ((i : ℝ) + 3) ^ p

theorem one_le_log_natCast_add_three (i : ℕ) :
    1 ≤ Real.log ((i : ℝ) + 3) := by
  have hx : Real.exp 1 ≤ (i : ℝ) + 3 := by
    exact Real.exp_one_lt_three.le.trans (by
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith)
  have hlog := Real.log_le_log (Real.exp_pos 1) hx
  simpa using hlog

theorem shiftedReciprocalLogWeight_nonneg (p i : ℕ) :
    0 ≤ shiftedReciprocalLogWeight p i := by
  unfold shiftedReciprocalLogWeight
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hlog : 0 < Real.log ((i : ℝ) + 3) := Real.log_pos (by linarith)
  exact one_div_nonneg.mpr (mul_nonneg (by linarith) (pow_nonneg hlog.le p))

theorem shiftedReciprocalLogPotential_nonneg (p i : ℕ) :
    0 ≤ shiftedReciprocalLogPotential p i := by
  unfold shiftedReciprocalLogPotential
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hlog : 0 < Real.log ((i : ℝ) + 3) := Real.log_pos (by linarith)
  exact one_div_nonneg.mpr (pow_nonneg hlog.le p)

theorem shiftedReciprocalLogWeight_antitone (p : ℕ) :
    Antitone (shiftedReciprocalLogWeight p) := by
  intro i j hij
  have hxi : (0 : ℝ) < (i : ℝ) + 3 := by positivity
  have hxj : (0 : ℝ) < (j : ℝ) + 3 := by positivity
  have hxij : (i : ℝ) + 3 ≤ (j : ℝ) + 3 := by
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hii : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hjj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hli : 0 < Real.log ((i : ℝ) + 3) := Real.log_pos (by linarith)
  have hlj : 0 < Real.log ((j : ℝ) + 3) := Real.log_pos (by linarith)
  have hlog := Real.log_le_log hxi hxij
  have hpow := pow_le_pow_left₀ hli.le hlog p
  unfold shiftedReciprocalLogWeight
  apply one_div_le_one_div_of_le (mul_pos hxi (pow_pos hli p))
  exact mul_le_mul hxij hpow (pow_nonneg hli.le p) hxj.le

theorem shiftedReciprocalLogPotential_antitone (p : ℕ) :
    Antitone (shiftedReciprocalLogPotential p) := by
  intro i j hij
  have hxi : (0 : ℝ) < (i : ℝ) + 3 := by positivity
  have hxij : (i : ℝ) + 3 ≤ (j : ℝ) + 3 := by
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hii : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hli : 0 < Real.log ((i : ℝ) + 3) := Real.log_pos (by linarith)
  have hlog := Real.log_le_log hxi hxij
  have hpow := pow_le_pow_left₀ hli.le hlog p
  unfold shiftedReciprocalLogPotential
  exact one_div_le_one_div_of_le (pow_pos hli p) hpow

theorem shiftedReciprocalLog_scale (p i : ℕ) :
    ((i : ℝ) + 3) * shiftedReciprocalLogWeight p i =
      shiftedReciprocalLogPotential p i := by
  unfold shiftedReciprocalLogWeight shiftedReciprocalLogPotential
  have hxi : (i : ℝ) + 3 ≠ 0 := by positivity
  field_simp

theorem shiftedReciprocalLog_step (p i : ℕ) :
    ((i : ℝ) + 4) *
        (shiftedReciprocalLogWeight p i - shiftedReciprocalLogWeight p (i + 1)) =
      shiftedReciprocalLogWeight p i + shiftedReciprocalLogPotential p i -
        shiftedReciprocalLogPotential p (i + 1) := by
  unfold shiftedReciprocalLogWeight shiftedReciprocalLogPotential
  have hxi : (i : ℝ) + 3 ≠ 0 := by positivity
  have hxj : (i : ℝ) + 4 ≠ 0 := by positivity
  have hli : Real.log ((i : ℝ) + 3) ≠ 0 :=
    ne_of_gt (Real.log_pos (by
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith))
  have hlj : Real.log ((i : ℝ) + 4) ≠ 0 :=
    ne_of_gt (Real.log_pos (by
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith))
  push_cast
  field_simp
  ring

theorem summable_shiftedReciprocalLogWeight_two :
    Summable (shiftedReciprocalLogWeight 2) := by
  change Summable (fun i : ℕ =>
    1 / (((i : ℝ) + 3) * Real.log ((i : ℝ) + 3) ^ (2 : ℕ)))
  exact RHTower.burnolSummable_shifted_one_div_mul_log_sq

theorem summable_shiftedReciprocalLogWeight_three :
    Summable (shiftedReciprocalLogWeight 3) := by
  refine Summable.of_nonneg_of_le
    (shiftedReciprocalLogWeight_nonneg 3) ?_
    summable_shiftedReciprocalLogWeight_two
  intro i
  have hx : (0 : ℝ) < (i : ℝ) + 3 := by positivity
  have hl : 1 ≤ Real.log ((i : ℝ) + 3) := one_le_log_natCast_add_three i
  have hlpos : 0 < Real.log ((i : ℝ) + 3) := zero_lt_one.trans_le hl
  have hpows : Real.log ((i : ℝ) + 3) ^ (2 : ℕ) ≤
      Real.log ((i : ℝ) + 3) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg (Real.log ((i : ℝ) + 3)),
      mul_nonneg (sq_nonneg (Real.log ((i : ℝ) + 3))) (sub_nonneg.mpr hl)]
  unfold shiftedReciprocalLogWeight
  apply one_div_le_one_div_of_le (mul_pos hx (pow_pos hlpos 2))
  exact mul_le_mul_of_nonneg_left hpows hx.le

/-- Linear growth of signed partial sums controls every summable reciprocal-scale reporter whose
variation splits into its weight plus a telescoping nonnegative potential. -/
theorem abs_sum_mul_weight_le_of_linear_partialSum
    {f w u : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hS : ∀ n : ℕ, |partialSum f n| ≤ C * ((n : ℝ) + 3))
    (hw0 : ∀ i : ℕ, 0 ≤ w i)
    (hwanti : Antitone w)
    (hu0 : ∀ i : ℕ, 0 ≤ u i)
    (huanti : Antitone u)
    (hscale : ∀ i : ℕ, ((i : ℝ) + 3) * w i = u i)
    (hstep : ∀ i : ℕ,
      ((i : ℝ) + 4) * (w i - w (i + 1)) = w i + u i - u (i + 1))
    (hsum : Summable w)
    (n : ℕ) :
    |∑ i ∈ Finset.range n, f i * w i| ≤
      C * ((∑' i : ℕ, w i) + 2 * u 0) := by
  have hidentity := sum_mul_weight_eq f w n
  have hboundary : |partialSum f n * w n| ≤ C * u 0 := by
    rw [abs_mul, abs_of_nonneg (hw0 n)]
    calc
      |partialSum f n| * w n ≤ (C * ((n : ℝ) + 3)) * w n :=
        mul_le_mul_of_nonneg_right (hS n) (hw0 n)
      _ = C * u n := by rw [mul_assoc, hscale]
      _ ≤ C * u 0 := mul_le_mul_of_nonneg_left (huanti (Nat.zero_le n)) hC
  have hbulk :
      |∑ j ∈ Finset.range n,
          partialSum f (j + 1) * (w (j + 1) - w j)| ≤
        C * ((∑' i : ℕ, w i) + u 0) := by
    calc
      |∑ j ∈ Finset.range n,
          partialSum f (j + 1) * (w (j + 1) - w j)| ≤
          ∑ j ∈ Finset.range n,
            |partialSum f (j + 1) * (w (j + 1) - w j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.range n,
            |partialSum f (j + 1)| * (w j - w (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hwanti (Nat.le_succ j)))]
        ring
      _ ≤ ∑ j ∈ Finset.range n,
            C * ((j : ℝ) + 4) * (w j - w (j + 1)) := by
        apply Finset.sum_le_sum
        intro j _hj
        have hdiff : 0 ≤ w j - w (j + 1) := sub_nonneg.mpr (hwanti (Nat.le_succ j))
        have hsj := hS (j + 1)
        have hsj' : |partialSum f (j + 1)| ≤ C * ((j : ℝ) + 4) := by
          convert hsj using 1 <;> push_cast <;> ring
        exact mul_le_mul_of_nonneg_right hsj' hdiff
      _ = C * ((∑ j ∈ Finset.range n, w j) + (u 0 - u n)) := by
        calc
          ∑ j ∈ Finset.range n,
              C * ((j : ℝ) + 4) * (w j - w (j + 1)) =
              C * ∑ j ∈ Finset.range n,
                ((j : ℝ) + 4) * (w j - w (j + 1)) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _hj
                  ring
          _ = C * ∑ j ∈ Finset.range n, (w j + u j - u (j + 1)) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j _hj
                rw [hstep]
          _ = C * ((∑ j ∈ Finset.range n, w j) + (u 0 - u n)) := by
                congr 1
                calc
                  ∑ j ∈ Finset.range n, (w j + u j - u (j + 1)) =
                      ∑ j ∈ Finset.range n, (w j + (u j - u (j + 1))) := by
                        apply Finset.sum_congr rfl
                        intro j _hj
                        ring
                  _ = (∑ j ∈ Finset.range n, w j) +
                      ∑ j ∈ Finset.range n, (u j - u (j + 1)) :=
                        Finset.sum_add_distrib
                  _ = (∑ j ∈ Finset.range n, w j) + (u 0 - u n) := by
                        rw [Finset.sum_range_sub']
      _ ≤ C * ((∑' i : ℕ, w i) + u 0) := by
        have hfinite : (∑ j ∈ Finset.range n, w j) ≤ ∑' i : ℕ, w i :=
          hsum.sum_le_tsum (Finset.range n) (fun i _hi => hw0 i)
        have hun : 0 ≤ u n := hu0 n
        exact mul_le_mul_of_nonneg_left (by linarith) hC
  rw [hidentity]
  calc
    |partialSum f n * w n -
        ∑ j ∈ Finset.range n,
          partialSum f (j + 1) * (w (j + 1) - w j)| ≤
        |partialSum f n * w n| +
          |∑ j ∈ Finset.range n,
            partialSum f (j + 1) * (w (j + 1) - w j)| := abs_sub _ _
    _ ≤ C * u 0 + C * ((∑' i : ℕ, w i) + u 0) :=
      add_le_add hboundary hbulk
    _ = C * ((∑' i : ℕ, w i) + 2 * u 0) := by ring

end HTGeometry

namespace RHTower

open HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

/-- Linear growth of the literal event-label-weighted Suzuki curvature prefixes. -/
def CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |suzukiCheckpointWeightedSignedCurvaturePrefix N| ≤ C * (N + 2 : ℕ)

/-- Uniform control of the central incoming unit-Riesz source on natural apertures. -/
def CCMUnitRieszCentralBarycenterNaturalBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |unitRieszCompletedCoherentBarycenter (N + 2) 0| ≤ C

private noncomputable def suzukiCheckpointWeightedCurvatureCell (i : ℕ) : ℝ :=
  ((i + 3 : ℕ) : ℝ) * suzukiCheckpointSignedCurvatureCell (i + 2)

theorem partialSum_suzukiCheckpointWeightedCurvatureCell (n : ℕ) :
    HTGeometry.partialSum suzukiCheckpointWeightedCurvatureCell n =
      suzukiCheckpointWeightedSignedCurvaturePrefix (n + 1) := by
  unfold HTGeometry.partialSum suzukiCheckpointWeightedCurvatureCell
    suzukiCheckpointWeightedSignedCurvaturePrefix
  have hshift := Finset.sum_Ico_add
    (fun k : ℕ => (k : ℝ) * suzukiCheckpointSignedCurvatureCell (k - 1)) 0 n 3
  have hzero : Finset.Ico 0 n = Finset.range n := by
    ext i
    simp
  rw [hzero] at hshift
  calc
    (∑ i ∈ Finset.range n,
        ((i + 3 : ℕ) : ℝ) * suzukiCheckpointSignedCurvatureCell (i + 2)) =
      ∑ i ∈ Finset.range n,
        ((3 + i : ℕ) : ℝ) * suzukiCheckpointSignedCurvatureCell (3 + i - 1) := by
          apply Finset.sum_congr rfl
          intro i _hi
          congr 2 <;> omega
    _ = ∑ k ∈ Finset.Ico 3 (n + 3),
        (k : ℝ) * suzukiCheckpointSignedCurvatureCell (k - 1) := hshift
    _ = ∑ k ∈ Finset.Ico 3 (n + 1 + 2),
        (k : ℝ) * suzukiCheckpointSignedCurvatureCell (k - 1) := by
          congr 2

/-- Source specialization of the linear-prefix Abel theorem at any summable reciprocal-log
grade. -/
theorem abs_suzukiCheckpointWeightedCurvature_reciprocalLogSum_le
    {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ N : ℕ, 1 ≤ N →
      |suzukiCheckpointWeightedSignedCurvaturePrefix N| ≤ C * (N + 2 : ℕ))
    (p n : ℕ) (hsum : Summable (HTGeometry.shiftedReciprocalLogWeight p)) :
    |∑ i ∈ Finset.range n,
        suzukiCheckpointWeightedCurvatureCell i *
          HTGeometry.shiftedReciprocalLogWeight p i| ≤
      C * ((∑' i : ℕ, HTGeometry.shiftedReciprocalLogWeight p i) +
        2 * HTGeometry.shiftedReciprocalLogPotential p 0) := by
  apply HTGeometry.abs_sum_mul_weight_le_of_linear_partialSum hC
  · intro m
    rw [partialSum_suzukiCheckpointWeightedCurvatureCell]
    have hm := hprefix (m + 1) (by omega)
    convert hm using 1 <;> push_cast <;> ring
  · exact HTGeometry.shiftedReciprocalLogWeight_nonneg p
  · exact HTGeometry.shiftedReciprocalLogWeight_antitone p
  · exact HTGeometry.shiftedReciprocalLogPotential_nonneg p
  · exact HTGeometry.shiftedReciprocalLogPotential_antitone p
  · exact HTGeometry.shiftedReciprocalLog_scale p
  · exact HTGeometry.shiftedReciprocalLog_step p
  · exact hsum

/-- The exact third-grade triangular reporter is the difference of its cubic and quadratic
reciprocal-log Abel channels. -/
theorem suzukiCheckpointTriangularCurvatureTransform_eq_reciprocalLogSums
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointTriangularCurvatureTransform H =
      32 * ∑ i ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        suzukiCheckpointWeightedCurvatureCell i *
          HTGeometry.shiftedReciprocalLogWeight 3 i -
      (32 / H) * ∑ i ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        suzukiCheckpointWeightedCurvatureCell i *
          HTGeometry.shiftedReciprocalLogWeight 2 i := by
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hM2, _hcell⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell
    (hlog2one.trans (one_le_two.trans hH))
  let M := suzukiCheckpointEventIndex H
  let n := M - 2
  have hnM : n + 2 = M := Nat.sub_add_cancel hM2
  let term : ℕ → ℝ := fun j =>
    suzukiCheckpointSignedCurvatureCell j *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (Real.log ((j + 1 : ℕ) : ℝ))
  have hzero : Finset.Ico 0 n = Finset.range n := by
    ext i
    simp
  have hshift := Finset.sum_Ico_add term 0 n 2
  rw [hzero, hnM] at hshift
  unfold suzukiCheckpointTriangularCurvatureTransform
  change (∑ j ∈ Finset.Ico 2 M, term j) = _
  rw [← hshift]
  change (∑ i ∈ Finset.range n, term (2 + i)) = _
  calc
    (∑ i ∈ Finset.range n, term (2 + i)) =
        ∑ i ∈ Finset.range n,
          (32 * (suzukiCheckpointWeightedCurvatureCell i *
            HTGeometry.shiftedReciprocalLogWeight 3 i) -
          (32 / H) * (suzukiCheckpointWeightedCurvatureCell i *
            HTGeometry.shiftedReciprocalLogWeight 2 i)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              have hH0 : H ≠ 0 := ne_of_gt (by linarith)
              have hi0 : ((i : ℝ) + 3) ≠ 0 := by positivity
              have hlog0 : Real.log ((i : ℝ) + 3) ≠ 0 :=
                ne_of_gt (Real.log_pos (by
                  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
                  linarith))
              have hlog0' : Real.log (3 + (i : ℝ)) ≠ 0 := by
                convert hlog0 using 1 <;> ring
              unfold term suzukiCheckpointWeightedCurvatureCell
                HTGeometry.shiftedReciprocalLogWeight
                ccmGuinandWeilThirdGradeCesaroTriangularWeight
                ccmGuinandWeilThirdGradeWeight
              push_cast
              field_simp [hlog0']
              ring_nf
              field_simp [hlog0]
    _ = 32 * ∑ i ∈ Finset.range n,
          suzukiCheckpointWeightedCurvatureCell i *
            HTGeometry.shiftedReciprocalLogWeight 3 i -
        (32 / H) * ∑ i ∈ Finset.range n,
          suzukiCheckpointWeightedCurvatureCell i *
            HTGeometry.shiftedReciprocalLogWeight 2 i := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Main signed Abel transfer. Linear growth of the exact event-label first moment uniformly
controls the CCM--FU triangular curvature transform. -/
theorem ccmFUSuzukiTriangularCurvatureTransformBound_of_weightedFirstMomentLinearBound
    (hfirst : CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound) :
    CCMFUSuzukiTriangularCurvatureTransformBound := by
  obtain ⟨C, hC0, hprefix⟩ := hfirst
  let K₂ : ℝ := C *
    ((∑' i : ℕ, HTGeometry.shiftedReciprocalLogWeight 2 i) +
      2 * HTGeometry.shiftedReciprocalLogPotential 2 0)
  let K₃ : ℝ := C *
    ((∑' i : ℕ, HTGeometry.shiftedReciprocalLogWeight 3 i) +
      2 * HTGeometry.shiftedReciprocalLogPotential 3 0)
  have hK₂0 : 0 ≤ K₂ := by
    dsimp only [K₂]
    apply mul_nonneg hC0
    exact add_nonneg
      (tsum_nonneg (HTGeometry.shiftedReciprocalLogWeight_nonneg 2))
      (mul_nonneg (by norm_num) (HTGeometry.shiftedReciprocalLogPotential_nonneg 2 0))
  have hK₃0 : 0 ≤ K₃ := by
    dsimp only [K₃]
    apply mul_nonneg hC0
    exact add_nonneg
      (tsum_nonneg (HTGeometry.shiftedReciprocalLogWeight_nonneg 3))
      (mul_nonneg (by norm_num) (HTGeometry.shiftedReciprocalLogPotential_nonneg 3 0))
  refine ⟨32 * (K₂ + K₃), mul_nonneg (by norm_num) (add_nonneg hK₂0 hK₃0), ?_⟩
  intro H hH
  let n := suzukiCheckpointEventIndex H - 2
  let S₂ : ℝ := ∑ i ∈ Finset.range n,
    suzukiCheckpointWeightedCurvatureCell i *
      HTGeometry.shiftedReciprocalLogWeight 2 i
  let S₃ : ℝ := ∑ i ∈ Finset.range n,
    suzukiCheckpointWeightedCurvatureCell i *
      HTGeometry.shiftedReciprocalLogWeight 3 i
  have hS₂ : |S₂| ≤ K₂ := by
    dsimp only [S₂, K₂, n]
    exact abs_suzukiCheckpointWeightedCurvature_reciprocalLogSum_le
      hC0 hprefix 2 _ HTGeometry.summable_shiftedReciprocalLogWeight_two
  have hS₃ : |S₃| ≤ K₃ := by
    dsimp only [S₃, K₃, n]
    exact abs_suzukiCheckpointWeightedCurvature_reciprocalLogSum_le
      hC0 hprefix 3 _ HTGeometry.summable_shiftedReciprocalLogWeight_three
  have hH0 : 0 < H := by linarith
  have hcoeff0 : 0 ≤ 32 / H := by positivity
  have hcoeffLe : 32 / H ≤ (32 : ℝ) := by
    apply (div_le_iff₀ hH0).2
    nlinarith
  rw [suzukiCheckpointTriangularCurvatureTransform_eq_reciprocalLogSums hH]
  change |32 * S₃ - (32 / H) * S₂| ≤ 32 * (K₂ + K₃)
  calc
    |32 * S₃ - (32 / H) * S₂| ≤ |32 * S₃| + |(32 / H) * S₂| := abs_sub _ _
    _ = 32 * |S₃| + (32 / H) * |S₂| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32),
        abs_of_nonneg hcoeff0]
    _ ≤ 32 * K₃ + 32 * K₂ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hS₃ (by norm_num))
        ((mul_le_mul hcoeffLe hS₂ (abs_nonneg _) (by norm_num)).trans_eq (by ring))
    _ = 32 * (K₂ + K₃) := by ring

/-- Central unit-Riesz source control supplies the exact first-moment linear bound. The only
discarded term is the already-proved sublinear archimedean renormalization. -/
theorem weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound
    (hcenterBound : CCMUnitRieszCentralBarycenterNaturalBound) :
    CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound := by
  obtain ⟨D, hD0, hcenter⟩ := hcenterBound
  refine ⟨D + 13, add_nonneg hD0 (by norm_num), ?_⟩
  intro N hN
  let X : ℝ := (N + 2 : ℕ)
  have hX1 : 1 ≤ X := by
    dsimp only [X]
    exact_mod_cast (by omega : 1 ≤ N + 2)
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hsqrt : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_iff]
    exact ⟨hX0, by nlinarith⟩
  have hlanding := unitRiesz_center_eq_weightedSignedCurvature_add_arch hN
  have hrearrange : suzukiCheckpointWeightedSignedCurvaturePrefix N =
      X * unitRieszCompletedCoherentBarycenter (N + 2) 0 -
        suzukiCheckpointWeightedArchRenormalization N := by
    dsimp only [X]
    linarith
  rw [hrearrange]
  calc
    |X * unitRieszCompletedCoherentBarycenter (N + 2) 0 -
        suzukiCheckpointWeightedArchRenormalization N| ≤
      |X * unitRieszCompletedCoherentBarycenter (N + 2) 0| +
        |suzukiCheckpointWeightedArchRenormalization N| := abs_sub _ _
    _ = X * |unitRieszCompletedCoherentBarycenter (N + 2) 0| +
        |suzukiCheckpointWeightedArchRenormalization N| := by
          rw [abs_mul, abs_of_nonneg hX0]
    _ ≤ X * D + (8 * Real.sqrt X + 5) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hcenter N hN) hX0)
        (by simpa only [X] using abs_suzukiCheckpointWeightedArchRenormalization_le hN)
    _ ≤ (D + 13) * X := by
      nlinarith

/-- Source-side first-moment criterion for RH. -/
theorem riemannHypothesis_of_suzukiWeightedCurvatureFirstMomentLinearBound
    (hfirst : CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiCheckpointTriangularCurvatureTransformBound
  exact ccmFUSuzukiTriangularCurvatureTransformBound_of_weightedFirstMomentLinearBound hfirst

/-- Cross-route CCM-FU / unit-Riesz endpoint: uniform natural-aperture control of the literal
central incoming barycenter is sufficient for RH. -/
theorem riemannHypothesis_of_unitRieszCentralBarycenterNaturalBound
    (hcenter : CCMUnitRieszCentralBarycenterNaturalBound) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiWeightedCurvatureFirstMomentLinearBound
  exact weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound hcenter

end

end RHTower
