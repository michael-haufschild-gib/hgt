import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreTwelve
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Compact-scale exponential transport retaining the complete cooling score -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
private def hA (u t : ℝ) := 37*u+50*t
private def hB (u t : ℝ) := 10*u+10*t
private def hTaylor (n : ℕ) (A B v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (20*A-49*B)^j*v^j*(20*B)^(n-j)/(j.factorial : ℝ)
private def hScore6 (A B r : ℝ) := (-64 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(6-1) + (1984 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(6-2) + (-5760 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(6-3) + (4160 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(6-4) + (-960 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(6-5) + (64 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(6-6)

private theorem weighted_score_poly6 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(6 : ℕ)*hTaylor 6 (hA u t) (hB u t) v-
      20^(6 : ℕ)*(hB u t)^(6 : ℕ)*((-1 : ℝ)^(6 : ℕ)*hScore6 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore6 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore7 (A B r : ℝ) := (-128 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(7-1) + (8064 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(7-2) + (-38528 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(7-3) + (44800 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(7-4) + (-17920 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(7-5) + (2688 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(7-6) + (-128 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(7-7)

private theorem weighted_score_poly7 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(7 : ℕ)*hTaylor 7 (hA u t) (hB u t) v-
      20^(7 : ℕ)*(hB u t)^(7 : ℕ)*((-1 : ℝ)^(7 : ℕ)*hScore7 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore7 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore8 (A B r : ℝ) := (-256 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(8-1) + (32512 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(8-2) + (-247296 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(8-3) + (435456 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(8-4) + (-268800 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(8-5) + (68096 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(8-6) + (-7168 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(8-7) + (256 : ℝ)*A^(8 : ℕ)*r^(8 : ℕ)*B^(8-8)

private theorem weighted_score_poly8 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(8 : ℕ)*hTaylor 8 (hA u t) (hB u t) v-
      20^(8 : ℕ)*(hB u t)^(8 : ℕ)*((-1 : ℝ)^(8 : ℕ)*hScore8 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore8 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore9 (A B r : ℝ) := (-512 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(9-1) + (130560 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(9-2) + (-1548800 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(9-3) + (3978240 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(9-4) + (-3558912 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(9-5) + (1354752 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(9-6) + (-236544 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(9-7) + (18432 : ℝ)*A^(8 : ℕ)*r^(8 : ℕ)*B^(9-8) + (-512 : ℝ)*A^(9 : ℕ)*r^(9 : ℕ)*B^(9-9)

private theorem weighted_score_poly9 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(9 : ℕ)*hTaylor 9 (hA u t) (hB u t) v-
      20^(9 : ℕ)*(hB u t)^(9 : ℕ)*((-1 : ℝ)^(9 : ℕ)*hScore9 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore9 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore10 (A B r : ℝ) := (-1024 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(10-1) + (523264 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(10-2) + (-9553920 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(10-3) + (34923520 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(10-4) + (-43545600 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(10-5) + (23374848 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(10-6) + (-6021120 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(10-7) + (768000 : ℝ)*A^(8 : ℕ)*r^(8 : ℕ)*B^(10-8) + (-46080 : ℝ)*A^(9 : ℕ)*r^(9 : ℕ)*B^(10-9) + (1024 : ℝ)*A^(10 : ℕ)*r^(10 : ℕ)*B^(10-10)

private theorem weighted_score_poly10 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(10 : ℕ)*hTaylor 10 (hA u t) (hB u t) v-
      20^(10 : ℕ)*(hB u t)^(10 : ℕ)*((-1 : ℝ)^(10 : ℕ)*hScore10 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore10 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore11 (A B r : ℝ) := (-2048 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(11-1) + (2095104 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(11-2) + (-58370048 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(11-3) + (298496000 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(11-4) + (-505303040 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(11-5) + (367589376 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(11-6) + (-131045376 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(11-7) + (24330240 : ℝ)*A^(8 : ℕ)*r^(8 : ℕ)*B^(11-8) + (-2365440 : ℝ)*A^(9 : ℕ)*r^(9 : ℕ)*B^(11-9) + (112640 : ℝ)*A^(10 : ℕ)*r^(10 : ℕ)*B^(11-10) + (-2048 : ℝ)*A^(11 : ℕ)*r^(11 : ℕ)*B^(11-11)

private theorem weighted_score_poly11 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(11 : ℕ)*hTaylor 11 (hA u t) (hB u t) v-
      20^(11 : ℕ)*(hB u t)^(11 : ℕ)*((-1 : ℝ)^(11 : ℕ)*hScore11 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore11 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity
private def hScore12 (A B r : ℝ) := (-4096 : ℝ)*A^(1 : ℕ)*r^(1 : ℕ)*B^(12-1) + (8384512 : ℝ)*A^(2 : ℕ)*r^(2 : ℕ)*B^(12-2) + (-354410496 : ℝ)*A^(3 : ℕ)*r^(3 : ℕ)*B^(12-3) + (2504708096 : ℝ)*A^(4 : ℕ)*r^(4 : ℕ)*B^(12-4) + (-5650022400 : ℝ)*A^(5 : ℕ)*r^(5 : ℕ)*B^(12-5) + (5421678592 : ℝ)*A^(6 : ℕ)*r^(6 : ℕ)*B^(12-6) + (-2569814016 : ℝ)*A^(7 : ℕ)*r^(7 : ℕ)*B^(12-7) + (651374592 : ℝ)*A^(8 : ℕ)*r^(8 : ℕ)*B^(12-8) + (-91238400 : ℝ)*A^(9 : ℕ)*r^(9 : ℕ)*B^(12-9) + (6983680 : ℝ)*A^(10 : ℕ)*r^(10 : ℕ)*B^(12-10) + (-270336 : ℝ)*A^(11 : ℕ)*r^(11 : ℕ)*B^(12-11) + (4096 : ℝ)*A^(12 : ℕ)*r^(12 : ℕ)*B^(12-12)

private theorem weighted_score_poly12 {u t v : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 ≤ (3/4)*(16*hA u t)^(12 : ℕ)*hTaylor 12 (hA u t) (hB u t) v-
      20^(12 : ℕ)*(hB u t)^(12 : ℕ)*((-1 : ℝ)^(12 : ℕ)*hScore12 (hA u t) (hB u t) (8+v)) := by
  unfold hTaylor hScore12 hA hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add]
  ring_nf
  positivity

private def truncatedExp (n : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), r^j/(j.factorial : ℝ)

private theorem hTaylor_scale (n : ℕ) (q v : ℝ) :
    hTaylor n (130*q) 130 v = (2600 : ℝ)^n*truncatedExp n ((q-49/20)*v) := by
  unfold hTaylor truncatedExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hp : (2600 : ℝ)^j*2600^(n-j) = 2600^n := by
    rw [← pow_add,Nat.add_sub_of_le hle]
  rw [show (20*(130*q)-49*130 : ℝ) = 2600*(q-49/20) by ring,mul_pow]
  norm_num only [show (20*130 : ℝ) = 2600 by norm_num]
  rw [mul_pow]
  calc
    _ = ((2600 : ℝ)^j*2600^(n-j))*((q-49/20)^j*v^j)/(j.factorial : ℝ) := by ring
    _ = _ := by rw [hp]; ring

private theorem weighted_score_taylor6 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(6 : ℕ)*laplaceCoolingJet 6 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(6 : ℕ)*truncatedExp 6 ((q-49/20)*v) := by
  have h := weighted_score_poly6 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore6 (130*q) 130 (8+v) =
      (130 : ℝ)^(6 : ℕ)*laplaceCoolingJet 6 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_6]
    unfold hScore6
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(6 : ℕ)*130^(6 : ℕ)*
      ((3/4)*(16*q)^(6 : ℕ)*truncatedExp 6 ((q-49/20)*v)-
        (-1 : ℝ)^(6 : ℕ)*laplaceCoolingJet 6 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor7 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(7 : ℕ)*laplaceCoolingJet 7 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(7 : ℕ)*truncatedExp 7 ((q-49/20)*v) := by
  have h := weighted_score_poly7 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore7 (130*q) 130 (8+v) =
      (130 : ℝ)^(7 : ℕ)*laplaceCoolingJet 7 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_7]
    unfold hScore7
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(7 : ℕ)*130^(7 : ℕ)*
      ((3/4)*(16*q)^(7 : ℕ)*truncatedExp 7 ((q-49/20)*v)-
        (-1 : ℝ)^(7 : ℕ)*laplaceCoolingJet 7 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor8 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(8 : ℕ)*laplaceCoolingJet 8 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(8 : ℕ)*truncatedExp 8 ((q-49/20)*v) := by
  have h := weighted_score_poly8 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore8 (130*q) 130 (8+v) =
      (130 : ℝ)^(8 : ℕ)*laplaceCoolingJet 8 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_8]
    unfold hScore8
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(8 : ℕ)*130^(8 : ℕ)*
      ((3/4)*(16*q)^(8 : ℕ)*truncatedExp 8 ((q-49/20)*v)-
        (-1 : ℝ)^(8 : ℕ)*laplaceCoolingJet 8 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor9 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(9 : ℕ)*laplaceCoolingJet 9 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(9 : ℕ)*truncatedExp 9 ((q-49/20)*v) := by
  have h := weighted_score_poly9 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore9 (130*q) 130 (8+v) =
      (130 : ℝ)^(9 : ℕ)*laplaceCoolingJet 9 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_9]
    unfold hScore9
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(9 : ℕ)*130^(9 : ℕ)*
      ((3/4)*(16*q)^(9 : ℕ)*truncatedExp 9 ((q-49/20)*v)-
        (-1 : ℝ)^(9 : ℕ)*laplaceCoolingJet 9 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor10 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(10 : ℕ)*laplaceCoolingJet 10 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(10 : ℕ)*truncatedExp 10 ((q-49/20)*v) := by
  have h := weighted_score_poly10 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore10 (130*q) 130 (8+v) =
      (130 : ℝ)^(10 : ℕ)*laplaceCoolingJet 10 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_10]
    unfold hScore10
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(10 : ℕ)*130^(10 : ℕ)*
      ((3/4)*(16*q)^(10 : ℕ)*truncatedExp 10 ((q-49/20)*v)-
        (-1 : ℝ)^(10 : ℕ)*laplaceCoolingJet 10 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor11 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(11 : ℕ)*laplaceCoolingJet 11 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(11 : ℕ)*truncatedExp 11 ((q-49/20)*v) := by
  have h := weighted_score_poly11 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore11 (130*q) 130 (8+v) =
      (130 : ℝ)^(11 : ℕ)*laplaceCoolingJet 11 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_11]
    unfold hScore11
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(11 : ℕ)*130^(11 : ℕ)*
      ((3/4)*(16*q)^(11 : ℕ)*truncatedExp 11 ((q-49/20)*v)-
        (-1 : ℝ)^(11 : ℕ)*laplaceCoolingJet 11 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

private theorem weighted_score_taylor12 {q v : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hv : 0 ≤ v) :
    (-1 : ℝ)^(12 : ℕ)*laplaceCoolingJet 12 0 (q*(8+v)) ≤
      (3/4)*(16*q)^(12 : ℕ)*truncatedExp 12 ((q-49/20)*v) := by
  have h := weighted_score_poly12 (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) hv
  have hAq : hA (50-10*q) (10*q-37) = 130*q := by unfold hA; ring
  have hBq : hB (50-10*q) (10*q-37) = 130 := by unfold hB; ring
  rw [hAq,hBq] at h
  have hs : hScore12 (130*q) 130 (8+v) =
      (130 : ℝ)^(12 : ℕ)*laplaceCoolingJet 12 0 (q*(8+v)) := by
    rw [laplaceCoolingJet_12]
    unfold hScore12
    norm_num
    ring
  rw [hs,hTaylor_scale] at h
  have he : 0 ≤ (2600 : ℝ)^(12 : ℕ)*130^(12 : ℕ)*
      ((3/4)*(16*q)^(12 : ℕ)*truncatedExp 12 ((q-49/20)*v)-
        (-1 : ℝ)^(12 : ℕ)*laplaceCoolingJet 12 0 (q*(8+v))) := by
    convert h using 1
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

/-- Exponential transport with coefficient three quarters at every high derivative needed by rank four. -/
theorem laplaceCoolingJet_inner_transport {n : ℕ} (hn : 6 ≤ n) (hnu : n ≤ 12)
    {q t : ℝ} (hq : 37/10 ≤ q) (hqu : q ≤ 5) (ht : 8 ≤ t) :
    (-1 : ℝ)^n*laplaceCoolingJet n 0 (q*t) ≤
      (3/4)*(16*q)^n*Real.exp ((q-49/20)*(t-8)) := by
  have hv : 0 ≤ t-8 := by linarith
  have hpoly : (-1 : ℝ)^n*laplaceCoolingJet n 0 (q*t) ≤
      (3/4)*(16*q)^n*truncatedExp n ((q-49/20)*(t-8)) := by
    interval_cases n
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor6 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor7 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor8 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor9 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor10 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor11 hq hqu hv
    · simpa only [show (8+(t-8) : ℝ) = t by ring] using weighted_score_taylor12 hq hqu hv
  have he := Real.sum_le_exp_of_nonneg
    (mul_nonneg (show 0 ≤ q-49/20 by linarith) hv) (n+1)
  exact hpoly.trans (mul_le_mul_of_nonneg_left he (by positivity))

end
end HTGeometry
