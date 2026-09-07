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
    |laplaceCoolingJet 0 0 z| ≤ (2*z)^0 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^0+laplaceCoolingJet 0 0 z =
        (2 : ℝ) := by
      rw [laplaceCoolingJet_0]
      ring
    have hp : 0 ≤ (2*z)^0+laplaceCoolingJet 0 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^0-laplaceCoolingJet 0 0 z =
        (0 : ℝ) := by
      rw [laplaceCoolingJet_0]
      ring
    have hp : 0 ≤ (2*z)^0-laplaceCoolingJet 0 0 z := le_of_eq heq.symm
    linarith only [hp]

private theorem absolute_score_1 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 1 0 z| ≤ (2*z)^1 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^1+laplaceCoolingJet 1 0 z =
        (0 : ℝ) := by
      rw [laplaceCoolingJet_1]
      ring
    have hp : 0 ≤ (2*z)^1+laplaceCoolingJet 1 0 z := le_of_eq heq.symm
    linarith only [hp]
  · have heq : (2*z)^1-laplaceCoolingJet 1 0 z =
        (222/5 : ℝ) +
    (4 : ℝ)*(z-111/10)^1 := by
      rw [laplaceCoolingJet_1]
      ring
    have hp : 0 ≤ (2*z)^1-laplaceCoolingJet 1 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_2 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 2 0 z| ≤ (2*z)^2 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^2+laplaceCoolingJet 2 0 z =
        (23532/25 : ℝ) +
    (868/5 : ℝ)*(z-111/10)^1 +
    (8 : ℝ)*(z-111/10)^2 := by
      rw [laplaceCoolingJet_2]
      ring
    have hp : 0 ≤ (2*z)^2+laplaceCoolingJet 2 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^2-laplaceCoolingJet 2 0 z =
        (222/5 : ℝ) +
    (4 : ℝ)*(z-111/10)^1 := by
      rw [laplaceCoolingJet_2]
      ring
    have hp : 0 ≤ (2*z)^2-laplaceCoolingJet 2 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_3 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 3 0 z| ≤ (2*z)^3 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^3+laplaceCoolingJet 3 0 z =
        (71706/25 : ℝ) +
    (2624/5 : ℝ)*(z-111/10)^1 +
    (24 : ℝ)*(z-111/10)^2 := by
      rw [laplaceCoolingJet_3]
      ring
    have hp : 0 ≤ (2*z)^3+laplaceCoolingJet 3 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^3-laplaceCoolingJet 3 0 z =
        (2376732/125 : ℝ) +
    (134732/25 : ℝ)*(z-111/10)^1 +
    (2544/5 : ℝ)*(z-111/10)^2 +
    (16 : ℝ)*(z-111/10)^3 := by
      rw [laplaceCoolingJet_3]
      ring
    have hp : 0 ≤ (2*z)^3-laplaceCoolingJet 3 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_4 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 4 0 z| ≤ (2*z)^4 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^4+laplaceCoolingJet 4 0 z =
        (230069922/625 : ℝ) +
    (17755336/125 : ℝ)*(z-111/10)^1 +
    (514288/25 : ℝ)*(z-111/10)^2 +
    (6624/5 : ℝ)*(z-111/10)^3 +
    (32 : ℝ)*(z-111/10)^4 := by
      rw [laplaceCoolingJet_4]
      ring
    have hp : 0 ≤ (2*z)^4+laplaceCoolingJet 4 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^4-laplaceCoolingJet 4 0 z =
        (14708832/125 : ℝ) +
    (825352/25 : ℝ)*(z-111/10)^1 +
    (15424/5 : ℝ)*(z-111/10)^2 +
    (96 : ℝ)*(z-111/10)^3 := by
      rw [laplaceCoolingJet_4]
      ring
    have hp : 0 ≤ (2*z)^4-laplaceCoolingJet 4 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_5 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 5 0 z| ≤ (2*z)^5 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^5+laplaceCoolingJet 5 0 z =
        (477813264/125 : ℝ) +
    (36637192/25 : ℝ)*(z-111/10)^1 +
    (1052016/5 : ℝ)*(z-111/10)^2 +
    (13408 : ℝ)*(z-111/10)^3 +
    (320 : ℝ)*(z-111/10)^4 := by
      rw [laplaceCoolingJet_5]
      ring
    have hp : 0 ≤ (2*z)^5+laplaceCoolingJet 5 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^5-laplaceCoolingJet 5 0 z =
        (21755831502/3125 : ℝ) +
    (424042204/125 : ℝ)*(z-111/10)^1 +
    (16622016/25 : ℝ)*(z-111/10)^2 +
    (327232/5 : ℝ)*(z-111/10)^3 +
    (3232 : ℝ)*(z-111/10)^4 +
    (64 : ℝ)*(z-111/10)^5 := by
      rw [laplaceCoolingJet_5]
      ring
    have hp : 0 ≤ (2*z)^5-laplaceCoolingJet 5 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_6 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 6 0 z| ≤ (2*z)^6 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^6+laplaceCoolingJet 6 0 z =
        (2080709258172/15625 : ℝ) +
    (241304307724/3125 : ℝ)*(z-111/10)^1 +
    (2362898984/125 : ℝ)*(z-111/10)^2 +
    (62431584/25 : ℝ)*(z-111/10)^3 +
    (937216/5 : ℝ)*(z-111/10)^4 +
    (37824/5 : ℝ)*(z-111/10)^5 +
    (128 : ℝ)*(z-111/10)^6 := by
      rw [laplaceCoolingJet_6]
      ring
    have hp : 0 ≤ (2*z)^6+laplaceCoolingJet 6 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^6-laplaceCoolingJet 6 0 z =
        (66404793846/625 : ℝ) +
    (1304877196/25 : ℝ)*(z-111/10)^1 +
    (10243760 : ℝ)*(z-111/10)^2 +
    (1003872 : ℝ)*(z-111/10)^3 +
    (49120 : ℝ)*(z-111/10)^4 +
    (960 : ℝ)*(z-111/10)^5 := by
      rw [laplaceCoolingJet_6]
      ring
    have hp : 0 ≤ (2*z)^6-laplaceCoolingJet 6 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_7 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 7 0 z| ≤ (2*z)^7 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^7+laplaceCoolingJet 7 0 z =
        (41194464115962/15625 : ℝ) +
    (4964024901704/3125 : ℝ)*(z-111/10)^1 +
    (49856305464/125 : ℝ)*(z-111/10)^2 +
    (1334880064/25 : ℝ)*(z-111/10)^3 +
    (20090336/5 : ℝ)*(z-111/10)^4 +
    (805504/5 : ℝ)*(z-111/10)^5 +
    (2688 : ℝ)*(z-111/10)^6 := by
      rw [laplaceCoolingJet_7]
      ring
    have hp : 0 ≤ (2*z)^7+laplaceCoolingJet 7 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^7-laplaceCoolingJet 7 0 z =
        (209259709999932/78125 : ℝ) +
    (27551482951988/15625 : ℝ)*(z-111/10)^1 +
    (1584490063968/3125 : ℝ)*(z-111/10)^2 +
    (10327988272/125 : ℝ)*(z-111/10)^3 +
    (205897664/25 : ℝ)*(z-111/10)^4 +
    (12531904/25 : ℝ)*(z-111/10)^5 +
    (86016/5 : ℝ)*(z-111/10)^6 +
    (256 : ℝ)*(z-111/10)^7 := by
      rw [laplaceCoolingJet_7]
      ring
    have hp : 0 ≤ (2*z)^7-laplaceCoolingJet 7 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_8 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 8 0 z| ≤ (2*z)^8 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^8+laplaceCoolingJet 8 0 z =
        (22469875841930082/390625 : ℝ) +
    (3275441488263952/78125 : ℝ)*(z-111/10)^1 +
    (212392478880544/15625 : ℝ)*(z-111/10)^2 +
    (8041769311296/3125 : ℝ)*(z-111/10)^3 +
    (39041731008/125 : ℝ)*(z-111/10)^4 +
    (3116569344/125 : ℝ)*(z-111/10)^5 +
    (31937024/25 : ℝ)*(z-111/10)^6 +
    (191488/5 : ℝ)*(z-111/10)^7 +
    (512 : ℝ)*(z-111/10)^8 := by
      rw [laplaceCoolingJet_8]
      ring
    have hp : 0 ≤ (2*z)^8+laplaceCoolingJet 8 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^8-laplaceCoolingJet 8 0 z =
        (4724175910484256/78125 : ℝ) +
    (673654200202384/15625 : ℝ)*(z-111/10)^1 +
    (41316076160704/3125 : ℝ)*(z-111/10)^2 +
    (282254070336/125 : ℝ)*(z-111/10)^3 +
    (5793564672/25 : ℝ)*(z-111/10)^4 +
    (357004032/25 : ℝ)*(z-111/10)^5 +
    (2444288/5 : ℝ)*(z-111/10)^6 +
    (7168 : ℝ)*(z-111/10)^7 := by
      rw [laplaceCoolingJet_8]
      ring
    have hp : 0 ≤ (2*z)^8-laplaceCoolingJet 8 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_9 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 9 0 z| ≤ (2*z)^9 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^9+laplaceCoolingJet 9 0 z =
        (519231488106240192/390625 : ℝ) +
    (84776281417234832/78125 : ℝ)*(z-111/10)^1 +
    (6109089072954144/15625 : ℝ)*(z-111/10)^2 +
    (253421451505856/3125 : ℝ)*(z-111/10)^3 +
    (1321790429568/125 : ℝ)*(z-111/10)^4 +
    (110786129664/125 : ℝ)*(z-111/10)^5 +
    (1164086784/25 : ℝ)*(z-111/10)^6 +
    (7001088/5 : ℝ)*(z-111/10)^7 +
    (18432 : ℝ)*(z-111/10)^8 := by
      rw [laplaceCoolingJet_9]
      ring
    have hp : 0 ≤ (2*z)^9+laplaceCoolingJet 9 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^9-laplaceCoolingJet 9 0 z =
        (2519916408241800222/1953125 : ℝ) +
    (405752190012150356/390625 : ℝ)*(z-111/10)^1 +
    (29247967038712128/78125 : ℝ)*(z-111/10)^2 +
    (1246729900575104/15625 : ℝ)*(z-111/10)^3 +
    (34896784074432/3125 : ℝ)*(z-111/10)^4 +
    (670241330304/625 : ℝ)*(z-111/10)^5 +
    (8884334592/125 : ℝ)*(z-111/10)^6 +
    (78544896/25 : ℝ)*(z-111/10)^7 +
    (419328/5 : ℝ)*(z-111/10)^8 +
    (1024 : ℝ)*(z-111/10)^9 := by
      rw [laplaceCoolingJet_9]
      ring
    have hp : 0 ≤ (2*z)^9-laplaceCoolingJet 9 0 z := by
      rw [heq]
      positivity
    linarith only [hp]

private theorem absolute_score_10 {z : ℝ} (hz : 111/10 ≤ z) :
    |laplaceCoolingJet 10 0 z| ≤ (2*z)^10 := by
  have ht : 0 ≤ z-111/10 := by linarith
  apply abs_le.mpr
  constructor
  · have heq : (2*z)^10+laplaceCoolingJet 10 0 z =
        (284741579052881430252/9765625 : ℝ) +
    (10177814492832985508/390625 : ℝ)*(z-111/10)^1 +
    (817593530849256872/78125 : ℝ)*(z-111/10)^2 +
    (39026573498693184/15625 : ℝ)*(z-111/10)^3 +
    (1233716259090944/3125 : ℝ)*(z-111/10)^4 +
    (136181194144128/3125 : ℝ)*(z-111/10)^5 +
    (430030277376/125 : ℝ)*(z-111/10)^6 +
    (4847391744/25 : ℝ)*(z-111/10)^7 +
    (37598208/5 : ℝ)*(z-111/10)^8 +
    (181248 : ℝ)*(z-111/10)^9 +
    (2048 : ℝ)*(z-111/10)^10 := by
      rw [laplaceCoolingJet_10]
      ring
    have hp : 0 ≤ (2*z)^10+laplaceCoolingJet 10 0 z := by
      rw [heq]
      positivity
    linarith only [hp]
  · have heq : (2*z)^10-laplaceCoolingJet 10 0 z =
        (11325704726436868038/390625 : ℝ) +
    (2057296180451803844/78125 : ℝ)*(z-111/10)^1 +
    (168334732669478432/15625 : ℝ)*(z-111/10)^2 +
    (8139595274523456/3125 : ℝ)*(z-111/10)^3 +
    (256024179802688/625 : ℝ)*(z-111/10)^4 +
    (5423399404416/125 : ℝ)*(z-111/10)^5 +
    (77216875008/25 : ℝ)*(z-111/10)^6 +
    (711066624/5 : ℝ)*(z-111/10)^7 +
    (3835392 : ℝ)*(z-111/10)^8 +
    (46080 : ℝ)*(z-111/10)^9 := by
      rw [laplaceCoolingJet_10]
      ring
    have hp : 0 ≤ (2*z)^10-laplaceCoolingJet 10 0 z := by
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
