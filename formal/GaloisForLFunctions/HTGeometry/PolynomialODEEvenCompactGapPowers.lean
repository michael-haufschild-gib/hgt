import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates

/-!
# Expanded powers of the unit gap polynomial

The coupled-coordinate moment identities substitute `evenCompactUnitGap` into a
reflected scalar whose monomials carry `a ^ j` for `j` up to seven.  A single `ring`
call re-expands that power at every one of the ~140 occurrences.  Naming each expanded
power once, and proving it by one multiplication from the previous power, lets those
proofs rewrite instead of recomputing the same expansion over and over.
-/
namespace HTGeometry
noncomputable section

/-- Expanded `evenCompactUnitGap ^ 2`. -/
def evenCompactUnitGapPow2 (r t : ℝ) : ℝ :=
  (36481/100 : ℝ) +
    (191/50 : ℝ)*t^1 +
    (1/100 : ℝ)*t^2 +
    (-2292/25 : ℝ)*r^1 +
    (604/15 : ℝ)*r^1*t^1 +
    (16/75 : ℝ)*r^1*t^2 +
    (144/25 : ℝ)*r^2 +
    (-128/25 : ℝ)*r^2*t^1 +
    (256/225 : ℝ)*r^2*t^2

/-- Expanded `evenCompactUnitGap ^ 3`. -/
def evenCompactUnitGapPow3 (r t : ℝ) : ℝ :=
  (6967871/1000 : ℝ) +
    (109443/1000 : ℝ)*t^1 +
    (573/1000 : ℝ)*t^2 +
    (1/1000 : ℝ)*t^3 +
    (-328329/125 : ℝ)*r^1 +
    (142486/125 : ℝ)*r^1*t^1 +
    (1519/125 : ℝ)*r^1*t^2 +
    (4/125 : ℝ)*r^1*t^3 +
    (41256/125 : ℝ)*r^2 +
    (-36456/125 : ℝ)*r^2*t^1 +
    (23872/375 : ℝ)*r^2*t^2 +
    (128/375 : ℝ)*r^2*t^3 +
    (-1728/125 : ℝ)*r^3 +
    (2304/125 : ℝ)*r^3*t^1 +
    (-1024/125 : ℝ)*r^3*t^2 +
    (4096/3375 : ℝ)*r^3*t^3

/-- Expanded `evenCompactUnitGap ^ 4`. -/
def evenCompactUnitGapPow4 (r t : ℝ) : ℝ :=
  (1330863361/10000 : ℝ) +
    (6967871/2500 : ℝ)*t^1 +
    (109443/5000 : ℝ)*t^2 +
    (191/2500 : ℝ)*t^3 +
    (1/10000 : ℝ)*t^4 +
    (-41807226/625 : ℝ)*r^1 +
    (53772994/1875 : ℝ)*r^1*t^1 +
    (57682/125 : ℝ)*r^1*t^2 +
    (1522/625 : ℝ)*r^1*t^3 +
    (8/1875 : ℝ)*r^1*t^4 +
    (7879896/625 : ℝ)*r^2 +
    (-1384368/125 : ℝ)*r^2*t^1 +
    (4450184/1875 : ℝ)*r^2*t^2 +
    (9664/375 : ℝ)*r^2*t^3 +
    (128/1875 : ℝ)*r^2*t^4 +
    (-660096/625 : ℝ)*r^3 +
    (876672/625 : ℝ)*r^3*t^1 +
    (-77312/125 : ℝ)*r^3*t^2 +
    (1509376/16875 : ℝ)*r^3*t^3 +
    (8192/16875 : ℝ)*r^3*t^4 +
    (20736/625 : ℝ)*r^4 +
    (-36864/625 : ℝ)*r^4*t^1 +
    (24576/625 : ℝ)*r^4*t^2 +
    (-65536/5625 : ℝ)*r^4*t^3 +
    (65536/50625 : ℝ)*r^4*t^4

/-- Expanded `evenCompactUnitGap ^ 5`. -/
def evenCompactUnitGapPow5 (r t : ℝ) : ℝ :=
  (254194901951/100000 : ℝ) +
    (1330863361/20000 : ℝ)*t^1 +
    (6967871/10000 : ℝ)*t^2 +
    (36481/10000 : ℝ)*t^3 +
    (191/20000 : ℝ)*t^4 +
    (1/100000 : ℝ)*t^5 +
    (-3992590083/2500 : ℝ)*r^1 +
    (1268152522/1875 : ℝ)*r^1*t^1 +
    (54757981/3750 : ℝ)*r^1*t^2 +
    (72389/625 : ℝ)*r^1*t^3 +
    (3047/7500 : ℝ)*r^1*t^4 +
    (1/1875 : ℝ)*r^1*t^5 +
    (250843356/625 : ℝ)*r^2 +
    (-219031924/625 : ℝ)*r^2*t^1 +
    (414609812/5625 : ℝ)*r^2*t^2 +
    (2279884/1875 : ℝ)*r^2*t^3 +
    (12128/1875 : ℝ)*r^2*t^4 +
    (64/5625 : ℝ)*r^2*t^5 +
    (-31519584/625 : ℝ)*r^3 +
    (41696064/625 : ℝ)*r^3*t^1 +
    (-18239072/625 : ℝ)*r^3*t^2 +
    (69463424/16875 : ℝ)*r^3*t^3 +
    (768512/16875 : ℝ)*r^3*t^4 +
    (2048/16875 : ℝ)*r^3*t^5 +
    (1980288/625 : ℝ)*r^4 +
    (-3510144/625 : ℝ)*r^4*t^1 +
    (2328576/625 : ℝ)*r^4*t^2 +
    (-6148096/5625 : ℝ)*r^4*t^3 +
    (5963776/50625 : ℝ)*r^4*t^4 +
    (32768/50625 : ℝ)*r^4*t^5 +
    (-248832/3125 : ℝ)*r^5 +
    (110592/625 : ℝ)*r^5*t^1 +
    (-98304/625 : ℝ)*r^5*t^2 +
    (131072/1875 : ℝ)*r^5*t^3 +
    (-262144/16875 : ℝ)*r^5*t^4 +
    (1048576/759375 : ℝ)*r^5*t^5

/-- Expanded `evenCompactUnitGap ^ 6`. -/
def evenCompactUnitGapPow6 (r t : ℝ) : ℝ :=
  (48551226272641/1000000 : ℝ) +
    (762584705853/500000 : ℝ)*t^1 +
    (3992590083/200000 : ℝ)*t^2 +
    (6967871/50000 : ℝ)*t^3 +
    (109443/200000 : ℝ)*t^4 +
    (573/500000 : ℝ)*t^5 +
    (1/1000000 : ℝ)*t^6 +
    (-2287754117559/62500 : ℝ)*r^1 +
    (956890756559/62500 : ℝ)*r^1*t^1 +
    (2599015883/6250 : ℝ)*r^1*t^2 +
    (5508631/1250 : ℝ)*r^1*t^3 +
    (290129/12500 : ℝ)*r^1*t^4 +
    (3811/62500 : ℝ)*r^1*t^5 +
    (1/15625 : ℝ)*r^1*t^6 +
    (35933310747/3125 : ℝ)*r^2 +
    (-31188190596/3125 : ℝ)*r^2*t^1 +
    (19304796694/9375 : ℝ)*r^2*t^2 +
    (430245836/9375 : ℝ)*r^2*t^3 +
    (1149083/3125 : ℝ)*r^2*t^4 +
    (12152/9375 : ℝ)*r^2*t^5 +
    (16/9375 : ℝ)*r^2*t^6 +
    (-6020240544/3125 : ℝ)*r^3 +
    (1586485728/625 : ℝ)*r^3*t^1 +
    (-3441966688/3125 : ℝ)*r^3*t^2 +
    (2555011808/16875 : ℝ)*r^3*t^3 +
    (72083072/28125 : ℝ)*r^3*t^4 +
    (77312/5625 : ℝ)*r^3*t^5 +
    (2048/84375 : ℝ)*r^3*t^6 +
    (567352512/3125 : ℝ)*r^4 +
    (-1002685824/3125 : ℝ)*r^4*t^1 +
    (661871808/3125 : ℝ)*r^4*t^2 +
    (-576664576/9375 : ℝ)*r^4*t^3 +
    (541874176/84375 : ℝ)*r^4*t^4 +
    (6111232/84375 : ℝ)*r^4*t^5 +
    (16384/84375 : ℝ)*r^4*t^6 +
    (-142580736/15625 : ℝ)*r^5 +
    (316099584/15625 : ℝ)*r^5*t^1 +
    (-55996416/3125 : ℝ)*r^5*t^2 +
    (4947968/625 : ℝ)*r^5*t^3 +
    (-48889856/28125 : ℝ)*r^5*t^4 +
    (188481536/1265625 : ℝ)*r^5*t^5 +
    (1048576/1265625 : ℝ)*r^5*t^6 +
    (2985984/15625 : ℝ)*r^6 +
    (-7962624/15625 : ℝ)*r^6*t^1 +
    (1769472/3125 : ℝ)*r^6*t^2 +
    (-1048576/3125 : ℝ)*r^6*t^3 +
    (1048576/9375 : ℝ)*r^6*t^4 +
    (-8388608/421875 : ℝ)*r^6*t^5 +
    (16777216/11390625 : ℝ)*r^6*t^6

/-- Expanded `evenCompactUnitGap ^ 7`. -/
def evenCompactUnitGapPow7 (r t : ℝ) : ℝ :=
  (9273284218074431/10000000 : ℝ) +
    (339858583908487/10000000 : ℝ)*t^1 +
    (5338092940971/10000000 : ℝ)*t^2 +
    (9316043527/2000000 : ℝ)*t^3 +
    (48775097/2000000 : ℝ)*t^4 +
    (766101/10000000 : ℝ)*t^5 +
    (1337/10000000 : ℝ)*t^6 +
    (1/10000000 : ℝ)*t^7 +
    (-1019575751725461/1250000 : ℝ)*r^1 +
    (126334866269647/375000 : ℝ)*r^1*t^1 +
    (13815692550541/1250000 : ℝ)*r^1*t^2 +
    (2292429559/15625 : ℝ)*r^1*t^3 +
    (773506643/750000 : ℝ)*r^1*t^4 +
    (2541637/625000 : ℝ)*r^1*t^5 +
    (427/50000 : ℝ)*r^1*t^6 +
    (7/937500 : ℝ)*r^1*t^7 +
    (48042836468739/156250 : ℝ)*r^2 +
    (-41447077651623/156250 : ℝ)*r^2*t^1 +
    (12577780588681/234375 : ℝ)*r^2*t^2 +
    (71037225959/46875 : ℝ)*r^2*t^3 +
    (1524138553/93750 : ℝ)*r^2*t^4 +
    (40377967/468750 : ℝ)*r^2*t^5 +
    (53228/234375 : ℝ)*r^2*t^6 +
    (56/234375 : ℝ)*r^2*t^7 +
    (-1006132700916/15625 : ℝ)*r^3 +
    (1320439425984/15625 : ℝ)*r^3*t^1 +
    (-568297807672/15625 : ℝ)*r^3*t^2 +
    (2053715279056/421875 : ℝ)*r^3*t^3 +
    (47318826884/421875 : ℝ)*r^3*t^4 +
    (127676528/140625 : ℝ)*r^3*t^5 +
    (1356992/421875 : ℝ)*r^3*t^6 +
    (1792/421875 : ℝ)*r^3*t^7 +
    (126425051424/15625 : ℝ)*r^4 +
    (-222769913184/15625 : ℝ)*r^4*t^1 +
    (146317301088/15625 : ℝ)*r^4*t^2 +
    (-378550615072/140625 : ℝ)*r^4*t^3 +
    (344077952512/1265625 : ℝ)*r^4*t^4 +
    (1993972736/421875 : ℝ)*r^4*t^5 +
    (10780672/421875 : ℝ)*r^4*t^6 +
    (57344/1265625 : ℝ)*r^4*t^7 +
    (-47657611008/78125 : ℝ)*r^5 +
    (105406769664/78125 : ℝ)*r^5*t^1 +
    (-93030835968/78125 : ℝ)*r^5*t^2 +
    (8171297792/15625 : ℝ)*r^5*t^3 +
    (-15951781888/140625 : ℝ)*r^5*t^4 +
    (59149877248/6328125 : ℝ)*r^5*t^5 +
    (680329216/6328125 : ℝ)*r^5*t^6 +
    (1835008/6328125 : ℝ)*r^5*t^7 +
    (1996130304/78125 : ℝ)*r^6 +
    (-212502528/3125 : ℝ)*r^6*t^1 +
    (5886590976/78125 : ℝ)*r^6*t^2 +
    (-694779904/15625 : ℝ)*r^6*t^3 +
    (689963008/46875 : ℝ)*r^6*t^4 +
    (-5442633728/2109375 : ℝ)*r^6*t^5 +
    (2084569088/11390625 : ℝ)*r^6*t^6 +
    (58720256/56953125 : ℝ)*r^6*t^7 +
    (-35831808/78125 : ℝ)*r^7 +
    (111476736/78125 : ℝ)*r^7*t^1 +
    (-148635648/78125 : ℝ)*r^7*t^2 +
    (22020096/15625 : ℝ)*r^7*t^3 +
    (-29360128/46875 : ℝ)*r^7*t^4 +
    (117440512/703125 : ℝ)*r^7*t^5 +
    (-469762048/18984375 : ℝ)*r^7*t^6 +
    (268435456/170859375 : ℝ)*r^7*t^7

/-- Exact expansion of the twoth power of the unit gap. -/
theorem evenCompactUnitGap_pow_two (r t : ℝ) :
    evenCompactUnitGap r t ^ 2 = evenCompactUnitGapPow2 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow2
  ring

/-- Exact expansion of the threeth power of the unit gap. -/
theorem evenCompactUnitGap_pow_three (r t : ℝ) :
    evenCompactUnitGap r t ^ 3 = evenCompactUnitGapPow3 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow3
  ring

/-- Exact expansion of the fourth power of the unit gap. -/
theorem evenCompactUnitGap_pow_four (r t : ℝ) :
    evenCompactUnitGap r t ^ 4 = evenCompactUnitGapPow4 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow4
  ring

/-- Exact expansion of the fiveth power of the unit gap. -/
theorem evenCompactUnitGap_pow_five (r t : ℝ) :
    evenCompactUnitGap r t ^ 5 = evenCompactUnitGapPow5 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow5
  ring

/-- Exact expansion of the sixth power of the unit gap. -/
theorem evenCompactUnitGap_pow_six (r t : ℝ) :
    evenCompactUnitGap r t ^ 6 = evenCompactUnitGapPow6 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow6
  ring

/-- Exact expansion of the seventh power of the unit gap. -/
theorem evenCompactUnitGap_pow_seven (r t : ℝ) :
    evenCompactUnitGap r t ^ 7 = evenCompactUnitGapPow7 r t := by
  unfold evenCompactUnitGap evenCompactUnitGapPow7
  ring

end
end HTGeometry
