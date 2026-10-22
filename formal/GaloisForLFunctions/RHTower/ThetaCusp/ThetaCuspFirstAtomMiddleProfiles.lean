import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.HTGeometry.TwoAtomMiddleEntryBounds

/-! # First-atom normalized bounds over the whole middle interval -/
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

/-- The first-atom entry 1 is the exact zero-second-atom specialization. -/
theorem thetaCuspFirstAtomScaledEvenJet_1_eq_middleProfile {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 1 x =
      HTGeometry.twoAtomOddProfile1 (thetaCuspSingleAtomReflectionScale 1 x) 0 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by dsimp [q] at *; nlinarith
  have hd : 0 < 2*q-3 := by dsimp [q]; linarith
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hp2 : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hp2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_2, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.twoAtomOddProfile1, HTGeometry.twoAtomOddNumerator1]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', hden.ne', q]
  <;> ring_nf
  <;> field_simp [hden.ne', q]
  <;> ring

/-- The first-atom entry 2 is the exact zero-second-atom specialization. -/
theorem thetaCuspFirstAtomScaledEvenJet_2_eq_middleProfile {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 2 x =
      HTGeometry.twoAtomOddProfile2 (thetaCuspSingleAtomReflectionScale 1 x) 0 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by dsimp [q] at *; nlinarith
  have hd : 0 < 2*q-3 := by dsimp [q]; linarith
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hp2 : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hp2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_4, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.twoAtomOddProfile2, HTGeometry.twoAtomOddNumerator2]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', hden.ne', q]
  <;> ring_nf
  <;> field_simp [hden.ne', q]
  <;> ring

/-- The first-atom entry 3 is the exact zero-second-atom specialization. -/
theorem thetaCuspFirstAtomScaledEvenJet_3_eq_middleProfile {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 3 x =
      HTGeometry.twoAtomOddProfile3 (thetaCuspSingleAtomReflectionScale 1 x) 0 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by dsimp [q] at *; nlinarith
  have hd : 0 < 2*q-3 := by dsimp [q]; linarith
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hp2 : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hp2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_6, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.twoAtomOddProfile3, HTGeometry.twoAtomOddNumerator3]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', hden.ne', q]
  <;> ring_nf
  <;> field_simp [hden.ne', q]
  <;> ring

/-- The first-atom entry 4 is the exact zero-second-atom specialization. -/
theorem thetaCuspFirstAtomScaledEvenJet_4_eq_middleProfile {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 4 x =
      HTGeometry.twoAtomOddProfile4 (thetaCuspSingleAtomReflectionScale 1 x) 0 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by dsimp [q] at *; nlinarith
  have hd : 0 < 2*q-3 := by dsimp [q]; linarith
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hp2 : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hp2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_8, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.twoAtomOddProfile4, HTGeometry.twoAtomOddNumerator4]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', hden.ne', q]
  <;> ring_nf
  <;> field_simp [hden.ne', q]
  <;> ring

/-- The first-atom entry 5 is the exact zero-second-atom specialization. -/
theorem thetaCuspFirstAtomScaledEvenJet_5_eq_middleProfile {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 5 x =
      HTGeometry.twoAtomOddProfile5 (thetaCuspSingleAtomReflectionScale 1 x) 0 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by dsimp [q] at *; nlinarith
  have hd : 0 < 2*q-3 := by dsimp [q]; linarith
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hp2 : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hp2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_10, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.twoAtomOddProfile5, HTGeometry.twoAtomOddNumerator5]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', hden.ne', q]
  <;> ring_nf
  <;> field_simp [hden.ne', q]
  <;> ring

/-- All five first-atom entries have uniform absolute bounds on the middle interval. -/
theorem thetaCuspFirstAtomScaledEvenJet_bounds_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspFirstAtomScaledEvenJet 1 x| ≤ 11 ∧
    |thetaCuspFirstAtomScaledEvenJet 2 x| ≤ 310 ∧
    |thetaCuspFirstAtomScaledEvenJet 3 x| ≤ 14000 ∧
    |thetaCuspFirstAtomScaledEvenJet 4 x| ≤ 800000 ∧
    |thetaCuspFirstAtomScaledEvenJet 5 x| ≤ 55000000 := by
  have h1 := HTGeometry.twoAtomOddProfile1_middle_bounds (z := (0 : ℝ)) hq0 hq1 (by norm_num) (by norm_num)
  rw [thetaCuspFirstAtomScaledEvenJet_1_eq_middleProfile hq0]
  have h2 := HTGeometry.twoAtomOddProfile2_middle_bounds (z := (0 : ℝ)) hq0 hq1 (by norm_num) (by norm_num)
  rw [thetaCuspFirstAtomScaledEvenJet_2_eq_middleProfile hq0]
  have h3 := HTGeometry.twoAtomOddProfile3_middle_bounds (z := (0 : ℝ)) hq0 hq1 (by norm_num) (by norm_num)
  rw [thetaCuspFirstAtomScaledEvenJet_3_eq_middleProfile hq0]
  have h4 := HTGeometry.twoAtomOddProfile4_middle_bounds (z := (0 : ℝ)) hq0 hq1 (by norm_num) (by norm_num)
  rw [thetaCuspFirstAtomScaledEvenJet_4_eq_middleProfile hq0]
  have h5 := HTGeometry.twoAtomOddProfile5_middle_bounds (z := (0 : ℝ)) hq0 hq1 (by norm_num) (by norm_num)
  rw [thetaCuspFirstAtomScaledEvenJet_5_eq_middleProfile hq0]
  exact ⟨by rw [abs_of_nonneg (by linarith [h1.1])]; exact h1.2, by rw [abs_of_nonneg (by linarith [h2.1])]; exact h2.2, by rw [abs_of_nonneg (by linarith [h3.1])]; exact h3.2, by rw [abs_of_nonneg (by linarith [h4.1])]; exact h4.2, by rw [abs_of_nonneg (by linarith [h5.1])]; exact h5.2⟩

end
end RHTower
