import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreBounds

/-!
# Absolute logarithmic Laplace-score bounds at the middle scale

The leading monomial bounds the absolute score through order ten from z=111/10.
No sign is imposed on the higher scores in this smaller regime.
-/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 1500000

private theorem absolute_score_0 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 0 0 z| ≤ (2*z)^(0 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(0 : ℕ)+laplaceCoolingJet 0 0 z =
        (2 : ℝ) := by
      rw [laplaceCoolingJet_0]
      ring
    have hp : 0 ≤ (2*z)^(0 : ℕ)+laplaceCoolingJet 0 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(0 : ℕ)-laplaceCoolingJet 0 0 z =
        (0 : ℝ) := by
      rw [laplaceCoolingJet_0]
      ring
    have hp : 0 ≤ (2*z)^(0 : ℕ)-laplaceCoolingJet 0 0 z := le_of_eq heq.symm
    linarith only [hp]

private theorem absolute_score_1 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 1 0 z| ≤ (2*z)^(1 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(1 : ℕ)+laplaceCoolingJet 1 0 z =
        (0 : ℝ) := by
      rw [laplaceCoolingJet_1]
      ring
    have hp : 0 ≤ (2*z)^(1 : ℕ)+laplaceCoolingJet 1 0 z := le_of_eq heq.symm
    linarith only [hp]
  · have heq : (2*z)^(1 : ℕ)-laplaceCoolingJet 1 0 z =
        (222/5 : ℝ) +
    (4 : ℝ)*(z-111/10)^(1 : ℕ) := by
      rw [laplaceCoolingJet_1]
      ring
    have hp : 0 ≤ (2*z)^(1 : ℕ)-laplaceCoolingJet 1 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_2 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 2 0 z| ≤ (2*z)^(2 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(2 : ℕ)+laplaceCoolingJet 2 0 z =
        (23532/25 : ℝ) +
    (868/5 : ℝ)*(z-111/10)^(1 : ℕ) +
    (8 : ℝ)*(z-111/10)^(2 : ℕ) := by
      rw [laplaceCoolingJet_2]
      ring
    have hp : 0 ≤ (2*z)^(2 : ℕ)+laplaceCoolingJet 2 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(2 : ℕ)-laplaceCoolingJet 2 0 z =
        (222/5 : ℝ) +
    (4 : ℝ)*(z-111/10)^(1 : ℕ) := by
      rw [laplaceCoolingJet_2]
      ring
    have hp : 0 ≤ (2*z)^(2 : ℕ)-laplaceCoolingJet 2 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_3 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 3 0 z| ≤ (2*z)^(3 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(3 : ℕ)+laplaceCoolingJet 3 0 z =
        (71706/25 : ℝ) +
    (2624/5 : ℝ)*(z-111/10)^(1 : ℕ) +
    (24 : ℝ)*(z-111/10)^(2 : ℕ) := by
      rw [laplaceCoolingJet_3]
      ring
    have hp : 0 ≤ (2*z)^(3 : ℕ)+laplaceCoolingJet 3 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(3 : ℕ)-laplaceCoolingJet 3 0 z =
        (2376732/125 : ℝ) +
    (134732/25 : ℝ)*(z-111/10)^(1 : ℕ) +
    (2544/5 : ℝ)*(z-111/10)^(2 : ℕ) +
    (16 : ℝ)*(z-111/10)^(3 : ℕ) := by
      rw [laplaceCoolingJet_3]
      ring
    have hp : 0 ≤ (2*z)^(3 : ℕ)-laplaceCoolingJet 3 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_4 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 4 0 z| ≤ (2*z)^(4 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(4 : ℕ)+laplaceCoolingJet 4 0 z =
        (230069922/625 : ℝ) +
    (17755336/125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (514288/25 : ℝ)*(z-111/10)^(2 : ℕ) +
    (6624/5 : ℝ)*(z-111/10)^(3 : ℕ) +
    (32 : ℝ)*(z-111/10)^(4 : ℕ) := by
      rw [laplaceCoolingJet_4]
      ring
    have hp : 0 ≤ (2*z)^(4 : ℕ)+laplaceCoolingJet 4 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(4 : ℕ)-laplaceCoolingJet 4 0 z =
        (14708832/125 : ℝ) +
    (825352/25 : ℝ)*(z-111/10)^(1 : ℕ) +
    (15424/5 : ℝ)*(z-111/10)^(2 : ℕ) +
    (96 : ℝ)*(z-111/10)^(3 : ℕ) := by
      rw [laplaceCoolingJet_4]
      ring
    have hp : 0 ≤ (2*z)^(4 : ℕ)-laplaceCoolingJet 4 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_5 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 5 0 z| ≤ (2*z)^(5 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(5 : ℕ)+laplaceCoolingJet 5 0 z =
        (477813264/125 : ℝ) +
    (36637192/25 : ℝ)*(z-111/10)^(1 : ℕ) +
    (1052016/5 : ℝ)*(z-111/10)^(2 : ℕ) +
    (13408 : ℝ)*(z-111/10)^(3 : ℕ) +
    (320 : ℝ)*(z-111/10)^(4 : ℕ) := by
      rw [laplaceCoolingJet_5]
      ring
    have hp : 0 ≤ (2*z)^(5 : ℕ)+laplaceCoolingJet 5 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(5 : ℕ)-laplaceCoolingJet 5 0 z =
        (21755831502/3125 : ℝ) +
    (424042204/125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (16622016/25 : ℝ)*(z-111/10)^(2 : ℕ) +
    (327232/5 : ℝ)*(z-111/10)^(3 : ℕ) +
    (3232 : ℝ)*(z-111/10)^(4 : ℕ) +
    (64 : ℝ)*(z-111/10)^(5 : ℕ) := by
      rw [laplaceCoolingJet_5]
      ring
    have hp : 0 ≤ (2*z)^(5 : ℕ)-laplaceCoolingJet 5 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_6 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 6 0 z| ≤ (2*z)^(6 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(6 : ℕ)+laplaceCoolingJet 6 0 z =
        (2080709258172/15625 : ℝ) +
    (241304307724/3125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (2362898984/125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (62431584/25 : ℝ)*(z-111/10)^(3 : ℕ) +
    (937216/5 : ℝ)*(z-111/10)^(4 : ℕ) +
    (37824/5 : ℝ)*(z-111/10)^(5 : ℕ) +
    (128 : ℝ)*(z-111/10)^(6 : ℕ) := by
      rw [laplaceCoolingJet_6]
      ring
    have hp : 0 ≤ (2*z)^(6 : ℕ)+laplaceCoolingJet 6 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(6 : ℕ)-laplaceCoolingJet 6 0 z =
        (66404793846/625 : ℝ) +
    (1304877196/25 : ℝ)*(z-111/10)^(1 : ℕ) +
    (10243760 : ℝ)*(z-111/10)^(2 : ℕ) +
    (1003872 : ℝ)*(z-111/10)^(3 : ℕ) +
    (49120 : ℝ)*(z-111/10)^(4 : ℕ) +
    (960 : ℝ)*(z-111/10)^(5 : ℕ) := by
      rw [laplaceCoolingJet_6]
      ring
    have hp : 0 ≤ (2*z)^(6 : ℕ)-laplaceCoolingJet 6 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_7 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 7 0 z| ≤ (2*z)^(7 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(7 : ℕ)+laplaceCoolingJet 7 0 z =
        (41194464115962/15625 : ℝ) +
    (4964024901704/3125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (49856305464/125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (1334880064/25 : ℝ)*(z-111/10)^(3 : ℕ) +
    (20090336/5 : ℝ)*(z-111/10)^(4 : ℕ) +
    (805504/5 : ℝ)*(z-111/10)^(5 : ℕ) +
    (2688 : ℝ)*(z-111/10)^(6 : ℕ) := by
      rw [laplaceCoolingJet_7]
      ring
    have hp : 0 ≤ (2*z)^(7 : ℕ)+laplaceCoolingJet 7 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(7 : ℕ)-laplaceCoolingJet 7 0 z =
        (209259709999932/78125 : ℝ) +
    (27551482951988/15625 : ℝ)*(z-111/10)^(1 : ℕ) +
    (1584490063968/3125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (10327988272/125 : ℝ)*(z-111/10)^(3 : ℕ) +
    (205897664/25 : ℝ)*(z-111/10)^(4 : ℕ) +
    (12531904/25 : ℝ)*(z-111/10)^(5 : ℕ) +
    (86016/5 : ℝ)*(z-111/10)^(6 : ℕ) +
    (256 : ℝ)*(z-111/10)^(7 : ℕ) := by
      rw [laplaceCoolingJet_7]
      ring
    have hp : 0 ≤ (2*z)^(7 : ℕ)-laplaceCoolingJet 7 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_8 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 8 0 z| ≤ (2*z)^(8 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(8 : ℕ)+laplaceCoolingJet 8 0 z =
        (22469875841930082/390625 : ℝ) +
    (3275441488263952/78125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (212392478880544/15625 : ℝ)*(z-111/10)^(2 : ℕ) +
    (8041769311296/3125 : ℝ)*(z-111/10)^(3 : ℕ) +
    (39041731008/125 : ℝ)*(z-111/10)^(4 : ℕ) +
    (3116569344/125 : ℝ)*(z-111/10)^(5 : ℕ) +
    (31937024/25 : ℝ)*(z-111/10)^(6 : ℕ) +
    (191488/5 : ℝ)*(z-111/10)^(7 : ℕ) +
    (512 : ℝ)*(z-111/10)^(8 : ℕ) := by
      rw [laplaceCoolingJet_8]
      ring
    have hp : 0 ≤ (2*z)^(8 : ℕ)+laplaceCoolingJet 8 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(8 : ℕ)-laplaceCoolingJet 8 0 z =
        (4724175910484256/78125 : ℝ) +
    (673654200202384/15625 : ℝ)*(z-111/10)^(1 : ℕ) +
    (41316076160704/3125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (282254070336/125 : ℝ)*(z-111/10)^(3 : ℕ) +
    (5793564672/25 : ℝ)*(z-111/10)^(4 : ℕ) +
    (357004032/25 : ℝ)*(z-111/10)^(5 : ℕ) +
    (2444288/5 : ℝ)*(z-111/10)^(6 : ℕ) +
    (7168 : ℝ)*(z-111/10)^(7 : ℕ) := by
      rw [laplaceCoolingJet_8]
      ring
    have hp : 0 ≤ (2*z)^(8 : ℕ)-laplaceCoolingJet 8 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_9 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 9 0 z| ≤ (2*z)^(9 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(9 : ℕ)+laplaceCoolingJet 9 0 z =
        (519231488106240192/390625 : ℝ) +
    (84776281417234832/78125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (6109089072954144/15625 : ℝ)*(z-111/10)^(2 : ℕ) +
    (253421451505856/3125 : ℝ)*(z-111/10)^(3 : ℕ) +
    (1321790429568/125 : ℝ)*(z-111/10)^(4 : ℕ) +
    (110786129664/125 : ℝ)*(z-111/10)^(5 : ℕ) +
    (1164086784/25 : ℝ)*(z-111/10)^(6 : ℕ) +
    (7001088/5 : ℝ)*(z-111/10)^(7 : ℕ) +
    (18432 : ℝ)*(z-111/10)^(8 : ℕ) := by
      rw [laplaceCoolingJet_9]
      ring
    have hp : 0 ≤ (2*z)^(9 : ℕ)+laplaceCoolingJet 9 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(9 : ℕ)-laplaceCoolingJet 9 0 z =
        (2519916408241800222/1953125 : ℝ) +
    (405752190012150356/390625 : ℝ)*(z-111/10)^(1 : ℕ) +
    (29247967038712128/78125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (1246729900575104/15625 : ℝ)*(z-111/10)^(3 : ℕ) +
    (34896784074432/3125 : ℝ)*(z-111/10)^(4 : ℕ) +
    (670241330304/625 : ℝ)*(z-111/10)^(5 : ℕ) +
    (8884334592/125 : ℝ)*(z-111/10)^(6 : ℕ) +
    (78544896/25 : ℝ)*(z-111/10)^(7 : ℕ) +
    (419328/5 : ℝ)*(z-111/10)^(8 : ℕ) +
    (1024 : ℝ)*(z-111/10)^(9 : ℕ) := by
      rw [laplaceCoolingJet_9]
      ring
    have hp : 0 ≤ (2*z)^(9 : ℕ)-laplaceCoolingJet 9 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_10 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 10 0 z| ≤ (2*z)^(10 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^(10 : ℕ)+laplaceCoolingJet 10 0 z =
        (284741579052881430252/9765625 : ℝ) +
    (10177814492832985508/390625 : ℝ)*(z-111/10)^(1 : ℕ) +
    (817593530849256872/78125 : ℝ)*(z-111/10)^(2 : ℕ) +
    (39026573498693184/15625 : ℝ)*(z-111/10)^(3 : ℕ) +
    (1233716259090944/3125 : ℝ)*(z-111/10)^(4 : ℕ) +
    (136181194144128/3125 : ℝ)*(z-111/10)^(5 : ℕ) +
    (430030277376/125 : ℝ)*(z-111/10)^(6 : ℕ) +
    (4847391744/25 : ℝ)*(z-111/10)^(7 : ℕ) +
    (37598208/5 : ℝ)*(z-111/10)^(8 : ℕ) +
    (181248 : ℝ)*(z-111/10)^(9 : ℕ) +
    (2048 : ℝ)*(z-111/10)^(10 : ℕ) := by
      rw [laplaceCoolingJet_10]
      ring
    have hp : 0 ≤ (2*z)^(10 : ℕ)+laplaceCoolingJet 10 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^(10 : ℕ)-laplaceCoolingJet 10 0 z =
        (11325704726436868038/390625 : ℝ) +
    (2057296180451803844/78125 : ℝ)*(z-111/10)^(1 : ℕ) +
    (168334732669478432/15625 : ℝ)*(z-111/10)^(2 : ℕ) +
    (8139595274523456/3125 : ℝ)*(z-111/10)^(3 : ℕ) +
    (256024179802688/625 : ℝ)*(z-111/10)^(4 : ℕ) +
    (5423399404416/125 : ℝ)*(z-111/10)^(5 : ℕ) +
    (77216875008/25 : ℝ)*(z-111/10)^(6 : ℕ) +
    (711066624/5 : ℝ)*(z-111/10)^(7 : ℕ) +
    (3835392 : ℝ)*(z-111/10)^(8 : ℕ) +
    (46080 : ℝ)*(z-111/10)^(9 : ℕ) := by
      rw [laplaceCoolingJet_10]
      ring
    have hp : 0 ≤ (2*z)^(10 : ℕ)-laplaceCoolingJet 10 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

/-- Every required absolute scalar score is controlled before the signed score regime begins. -/
theorem laplaceCoolingJet_abs_le_of_middle {n : ℕ} (hn : n ≤ 10) {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet n 0 z| ≤ (2*z)^n := by
  interval_cases n
  · exact absolute_score_0 hz
  · exact absolute_score_1 hz
  · exact absolute_score_2 hz
  · exact absolute_score_3 hz
  · exact absolute_score_4 hz
  · exact absolute_score_5 hz
  · exact absolute_score_6 hz
  · exact absolute_score_7 hz
  · exact absolute_score_8 hz
  · exact absolute_score_9 hz
  · exact absolute_score_10 hz

end
end HTGeometry
