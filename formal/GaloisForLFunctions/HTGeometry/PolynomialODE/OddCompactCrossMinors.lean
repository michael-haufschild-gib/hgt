import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactScalarGrades1
import Mathlib.Tactic.LinearCombination

/-!
# Cross minors of the odd source matrix

`CrossAD = -R2*R8 + R4*R6` and `CrossBD = R4*R8 - R6^2`. Both hold grade by
grade in the drift coordinate: the grade `d` part is the sum over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 0 of the first cross minor. -/
def oddCompactCrossADGrade0 (_u a w : ℝ) : ℝ :=
  ((146313216000 : ℝ) +
    (-670602240000 : ℝ)*a^(1 : ℕ) +
    (715491532800 : ℝ)*a^(2 : ℕ) +
    (867975782400 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-251150284800 : ℝ)*a^(3 : ℕ) +
    (-730467072000 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (17398592640 : ℝ)*a^(4 : ℕ) +
    (-199297843200 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (124131985920 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-3587168160 : ℝ)*a^(5 : ℕ) +
    (256493813760 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-4507090560 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (513614160 : ℝ)*a^(6 : ℕ) +
    (11174215680 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-13694469120 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (1701861120 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (1312020 : ℝ)*a^(7 : ℕ) +
    (-34867445760 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (399098880 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-50402016 : ℝ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-141990 : ℝ)*a^(8 : ℕ) +
    (-141557760 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-705576960 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-84238848 : ℝ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (852096 : ℝ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (1425 : ℝ)*a^(9 : ℕ) +
    (1132462080 : ℝ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (3833856 : ℝ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (2760960 : ℝ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (15504 : ℝ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (30670848 : ℝ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-196608 : ℝ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-11328 : ℝ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-786432 : ℝ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (12288 : ℝ)*a^(6 : ℕ)*w^(6 : ℕ)) / (16777216 : ℝ)

/-- Drift degree 0 of the first cross minor. -/
theorem oddCompactCrossADGrade0_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossADGrade0 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar8Grade0
  ring

/-- Drift degree 1 of the first cross minor. -/
def oddCompactCrossADGrade1 (u a w : ℝ) : ℝ :=
  ((-866764800 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (5211302400 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (26952652800 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-1962564480 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-21269652480 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-1146840480 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-4841717760 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-741363840 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-50599200 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (8199383040 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (375264000 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (15930576 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (126812160 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (616565760 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (62851776 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (137286 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-835584000 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (50563584 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (850336 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-1605 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-28016640 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (1069824 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-14776 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (12582912 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-245760 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-13824 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-262144 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (12288 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ)) / (2097152 : ℝ)

/-- Drift degree 1 of the first cross minor. -/
theorem oddCompactCrossADGrade1_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossADGrade1 u a w := by
  unfold oddCompactCrossADGrade1 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1
  ring

/-- Drift degree 2 of the first cross minor. -/
def oddCompactCrossADGrade2 (u a w : ℝ) : ℝ :=
  ((-261273600000 : ℝ)*u^(2 : ℕ) +
    (765490176000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-576456652800 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-722151936000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (151767866880 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (436966410240 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-25043653440 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (196798464000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-62438595840 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (3423549120 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (-173965639680 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (5197766400 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-48472248 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ) +
    (-11435212800 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-16865280 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-616886784 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-2729156 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ) +
    (28714598400 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (115038720 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-11691360 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (1979 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ) +
    (94371840 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (2122358784 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (25947648 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-82336 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-1044381696 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (69337088 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-1407104 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-18087936 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-516096 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (393216 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ)) / (25165824 : ℝ)

/-- Drift degree 2 of the first cross minor. -/
theorem oddCompactCrossADGrade2_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade0 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade1 u a w =
      oddCompactCrossADGrade2 u a w := by
  unfold oddCompactCrossADGrade2 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2
  ring

/-- Drift degree 3 of the first cross minor. -/
def oddCompactCrossADGrade3 (u a w : ℝ) : ℝ :=
  ((-10529049600 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (8237975040 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-56209766400 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-4879834560 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (22395870720 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-64048320 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (11185643520 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (3212824320 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (226866000 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-11193569280 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (150044160 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (1053872 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-253624320 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-1013039616 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-35102144 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-17199 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (1199898624 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-60985856 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-284912 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (64421888 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-1756544 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-12582912 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-90112 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (131072 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ)) / (9437184 : ℝ)

/-- Drift degree 3 of the first cross minor. -/
theorem oddCompactCrossADGrade3_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossADGrade3 u a w := by
  unfold oddCompactCrossADGrade3 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3
  ring

/-- Drift degree 4 of the first cross minor. -/
def oddCompactCrossADGrade4 (u a w : ℝ) : ℝ :=
  ((609638400000 : ℝ)*u^(4 : ℕ) +
    (-1230938726400 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (704120417280 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (718818969600 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-175098055680 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-279143861760 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (26069215680 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (-230340096000 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (29757822720 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-959199312 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ) +
    (112708976640 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-4766909760 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-29081468 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ) +
    (13558579200 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (6584993280 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (194895168 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (82083 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ) +
    (-22080356352 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (424776960 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1256280 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-70778880 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-1758728192 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (405120 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (761266176 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-51601408 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (6488064 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ)) / (113246208 : ℝ)

/-- Drift degree 4 of the first cross minor. -/
theorem oddCompactCrossADGrade4_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade0 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade1 u a w =
      oddCompactCrossADGrade4 u a w := by
  unfold oddCompactCrossADGrade4 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4
  ring

/-- Drift degree 5 of the first cross minor. -/
def oddCompactCrossADGrade5 (u a w : ℝ) : ℝ :=
  ((5110611840 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-2683890720 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (10817953920 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-188426160 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-899664000 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (332442468 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-2566748160 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-424465776 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-8047518 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (1208393472 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-60847376 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-92263 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (47554560 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (134999616 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-672308 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-143302656 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (4636576 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-6301696 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (786432 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (10616832 : ℝ)

/-- Drift degree 5 of the first cross minor. -/
theorem oddCompactCrossADGrade5_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade0 u a w =
      oddCompactCrossADGrade5 u a w := by
  unfold oddCompactCrossADGrade5 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5
  ring

/-- Drift degree 6 of the first cross minor. -/
def oddCompactCrossADGrade6 (u a w : ℝ) : ℝ :=
  ((-408457728000 : ℝ)*u^(6 : ℕ) +
    (597404298240 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (-267435371520 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (-180460823040 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (53451838080 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (41846883840 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3702635856 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ) +
    (67382784000 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-6678204480 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-35898216 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ) +
    (-11545018368 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (1047041760 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (983551 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ) +
    (-3920486400 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-1283348224 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (5498144 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (3177824256 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-120737600 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (11796480 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (189086720 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-83361792 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ)) / (254803968 : ℝ)

/-- Drift degree 6 of the first cross minor. -/
theorem oddCompactCrossADGrade6_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade0 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade0 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade1 u a w =
      oddCompactCrossADGrade6 u a w := by
  unfold oddCompactCrossADGrade6 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6
  ring

/-- Drift degree 7 of the first cross minor. -/
def oddCompactCrossADGrade7 (u a w : ℝ) : ℝ :=
  ((-2686507200 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-606866880 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-3350211840 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (945494856 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-687184704 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-80915148 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (1168542720 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-4510544 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-486717 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-134522112 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (8295184 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-15851520 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-23452512 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (22769664 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (47775744 : ℝ)

/-- Drift degree 7 of the first cross minor. -/
theorem oddCompactCrossADGrade7_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossADGrade7 u a w := by
  unfold oddCompactCrossADGrade7 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7
  ring

/-- Drift degree 8 of the first cross minor. -/
def oddCompactCrossADGrade8 (u a w : ℝ) : ℝ :=
  ((347493888000 : ℝ)*u^(8 : ℕ) +
    (-372825607680 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (123566822400 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (48638350080 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-14701753536 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-10343507136 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (212444604 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-20177856000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (2954275248 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (6872465 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (-588490752 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-70460092 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (1112832000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-37745248 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-260327424 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-1474560 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (1146617856 : ℝ)

/-- Drift degree 8 of the first cross minor. -/
theorem oddCompactCrossADGrade8_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossADGrade8 u a w := by
  unfold oddCompactCrossADGrade8 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 9 of the first cross minor. -/
def oddCompactCrossADGrade9 (u a w : ℝ) : ℝ :=
  ((-697694400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2672211504 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (93821760 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-558347596 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (448280928 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (4374291 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-526855680 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (39109532 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-26307264 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (3962880 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (429981696 : ℝ)

/-- Drift degree 9 of the first cross minor. -/
theorem oddCompactCrossADGrade9_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade8 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade7 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade9 u a w =
      oddCompactCrossADGrade9 u a w := by
  unfold oddCompactCrossADGrade9 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 10 of the first cross minor. -/
def oddCompactCrossADGrade10 (u a w : ℝ) : ℝ :=
  ((-32514048000 : ℝ)*u^(10 : ℕ) +
    (24858552960 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-5334727072 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-1325712960 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (259615784 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (549234016 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (2313949 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (450681600 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-60460844 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (39451648 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-20759040 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (859963392 : ℝ)

/-- Drift degree 10 of the first cross minor. -/
theorem oddCompactCrossADGrade10_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade7 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade9 u a w =
      oddCompactCrossADGrade10 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 11 of the first cross minor. -/
def oddCompactCrossADGrade11 (u a w : ℝ) : ℝ :=
  ((774716400 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-426881832 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (184753440 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (18346405 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-11582376 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (23472000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (967458816 : ℝ)

/-- Drift degree 11 of the first cross minor. -/
theorem oddCompactCrossADGrade11_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade9 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade7 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade6 u a w =
      oddCompactCrossADGrade11 u a w := by
  unfold oddCompactCrossADGrade11 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 12 of the first cross minor. -/
def oddCompactCrossADGrade12 (u a w : ℝ) : ℝ :=
  ((1508220000 : ℝ)*u^(12 : ℕ) +
    (-760829040 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (84002354 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (26452740 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-633546 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (-10307963 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1839000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (483729408 : ℝ)

/-- Drift degree 12 of the first cross minor. -/
theorem oddCompactCrossADGrade12_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar6Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar2Grade0 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossADGrade12 u a w := by
  unfold oddCompactCrossADGrade12 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 13 of the first cross minor. -/
def oddCompactCrossADGrade13 (u a w : ℝ) : ℝ :=
  ((-41607300 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (6383363 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-4599180 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (725594112 : ℝ)

/-- Drift degree 13 of the first cross minor. -/
theorem oddCompactCrossADGrade13_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar6Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar2Grade1 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossADGrade13 u a w := by
  unfold oddCompactCrossADGrade13 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 14 of the first cross minor. -/
def oddCompactCrossADGrade14 (u a w : ℝ) : ℝ :=
  ((-178605000 : ℝ)*u^(14 : ℕ) +
    (51077790 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ) +
    (-1823453 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-1741665 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (1088391168 : ℝ)

/-- Drift degree 14 of the first cross minor. -/
theorem oddCompactCrossADGrade14_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade2 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade10 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar6Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade6 u a w =
      oddCompactCrossADGrade14 u a w := by
  unfold oddCompactCrossADGrade14 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 15 of the first cross minor. -/
def oddCompactCrossADGrade15 (u a w : ℝ) : ℝ :=
  ((715855 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (544195584 : ℝ)

/-- Drift degree 15 of the first cross minor. -/
theorem oddCompactCrossADGrade15_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade3 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar6Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossADGrade15 u a w := by
  unfold oddCompactCrossADGrade15 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 16 of the first cross minor. -/
def oddCompactCrossADGrade16 (u a _w : ℝ) : ℝ :=
  ((5449500 : ℝ)*u^(16 : ℕ) +
    (-624725 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)) / (1088391168 : ℝ)

/-- Drift degree 16 of the first cross minor. -/
theorem oddCompactCrossADGrade16_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade4 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar6Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade8 u a w =
      oddCompactCrossADGrade16 u a w := by
  unfold oddCompactCrossADGrade16 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- Drift degree 18 of the first cross minor. -/
def oddCompactCrossADGrade18 (u _a _w : ℝ) : ℝ :=
  ((-6125 : ℝ)*u^(18 : ℕ)) / (90699264 : ℝ)

/-- Drift degree 18 of the first cross minor. -/
theorem oddCompactCrossADGrade18_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar2Grade6 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar6Grade10 u a w =
      oddCompactCrossADGrade18 u a w := by
  unfold oddCompactCrossADGrade18 oddCompactReflectedScalar2Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- The first cross minor, stored as its drift grades. -/
def oddCompactCrossAD (u a w : ℝ) : ℝ :=
  oddCompactCrossADGrade0 u a w +
    oddCompactCrossADGrade1 u a w +
    oddCompactCrossADGrade2 u a w +
    oddCompactCrossADGrade3 u a w +
    oddCompactCrossADGrade4 u a w +
    oddCompactCrossADGrade5 u a w +
    oddCompactCrossADGrade6 u a w +
    oddCompactCrossADGrade7 u a w +
    oddCompactCrossADGrade8 u a w +
    oddCompactCrossADGrade9 u a w +
    oddCompactCrossADGrade10 u a w +
    oddCompactCrossADGrade11 u a w +
    oddCompactCrossADGrade12 u a w +
    oddCompactCrossADGrade13 u a w +
    oddCompactCrossADGrade14 u a w +
    oddCompactCrossADGrade15 u a w +
    oddCompactCrossADGrade16 u a w +
    oddCompactCrossADGrade18 u a w

/-- Exact scalar cross-minor expansion. -/
theorem oddCompactCrossAD_eq (u a w : ℝ) :
    (-oddCompactReflectedScalar2 u a w)*oddCompactReflectedScalar8 u a w - oddCompactReflectedScalar4 u a w*(-oddCompactReflectedScalar6 u a w) = oddCompactCrossAD u a w := by
  rw [oddCompactReflectedScalar2_grades, oddCompactReflectedScalar4_grades,
    oddCompactReflectedScalar6_grades, oddCompactReflectedScalar8_grades]
  unfold oddCompactCrossAD
  linear_combination oddCompactCrossADGrade0_eq u a w +
    oddCompactCrossADGrade1_eq u a w +
    oddCompactCrossADGrade2_eq u a w +
    oddCompactCrossADGrade3_eq u a w +
    oddCompactCrossADGrade4_eq u a w +
    oddCompactCrossADGrade5_eq u a w +
    oddCompactCrossADGrade6_eq u a w +
    oddCompactCrossADGrade7_eq u a w +
    oddCompactCrossADGrade8_eq u a w +
    oddCompactCrossADGrade9_eq u a w +
    oddCompactCrossADGrade10_eq u a w +
    oddCompactCrossADGrade11_eq u a w +
    oddCompactCrossADGrade12_eq u a w +
    oddCompactCrossADGrade13_eq u a w +
    oddCompactCrossADGrade14_eq u a w +
    oddCompactCrossADGrade15_eq u a w +
    oddCompactCrossADGrade16_eq u a w +
    oddCompactCrossADGrade18_eq u a w

/-- Drift degree 0 of the second cross minor. -/
def oddCompactCrossBDGrade0 (_u a w : ℝ) : ℝ :=
  ((10852260249600 : ℝ) +
    (-58785863270400 : ℝ)*a^(1 : ℕ) +
    (81809810472960 : ℝ)*a^(2 : ℕ) +
    (81825476935680 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-38683079331840 : ℝ)*a^(3 : ℕ) +
    (-112763841085440 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (3741137902080 : ℝ)*a^(4 : ℕ) +
    (-20464049848320 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (28487429222400 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-591957286272 : ℝ)*a^(5 : ℕ) +
    (57024137134080 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-719395817472 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (144190160640 : ℝ)*a^(6 : ℕ) +
    (1295182725120 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-4526136999936 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (538949146752 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (490601952 : ℝ)*a^(7 : ℕ) +
    (-11516582559744 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (135501299712 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-23397289344 : ℝ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-77792940 : ℝ)*a^(8 : ℕ) +
    (-19251855360 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-167863910400 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-66262824960 : ℝ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (421323264 : ℝ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-142260 : ℝ)*a^(9 : ℕ) +
    (801783152640 : ℝ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-19981271040 : ℝ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (2598764544 : ℝ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-39817632 : ℝ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (69075 : ℝ)*a^(10 : ℕ) +
    (25008537600 : ℝ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (3490086912 : ℝ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-101386752 : ℝ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (1261368 : ℝ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-20535312384 : ℝ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (780140544 : ℝ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-99778560 : ℝ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (1281024 : ℝ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-603979776 : ℝ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (147456 : ℝ)*a^(7 : ℕ)*w^(6 : ℕ)) / (134217728 : ℝ)

/-- Drift degree 0 of the second cross minor. -/
theorem oddCompactCrossBDGrade0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossBDGrade0 u a w := by
  unfold oddCompactCrossBDGrade0 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar8Grade0
  ring

/-- Drift degree 1 of the second cross minor. -/
def oddCompactCrossBDGrade1 (u a w : ℝ) : ℝ :=
  ((-6200478720 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (75869844480 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (344270684160 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-53738282880 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-464857666560 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-25002369216 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-70031278080 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (14648929536 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-250825164 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (280228220928 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (18670559424 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (843961392 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (2155806720 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (22274420736 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (3584250608 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (13741923 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-48404299776 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (1811922944 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (42281400 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (680112 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-3328786432 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-91336704 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-1261388 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (9834 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (2286944256 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-136372224 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-5642496 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (127782 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (111149056 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-5603328 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (151296 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-25165824 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (786432 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (18432 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ)) / (2097152 : ℝ)

/-- Drift degree 1 of the second cross minor. -/
theorem oddCompactCrossBDGrade1_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade1 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade1 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossBDGrade1 u a w := by
  unfold oddCompactCrossBDGrade1 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1
  ring

/-- Drift degree 2 of the second cross minor. -/
def oddCompactCrossBDGrade2 (u a w : ℝ) : ℝ :=
  ((-10981851955200 : ℝ)*u^(2 : ℕ) +
    (39445678080000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-38653551267840 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-41035329699840 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (13185451100160 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (39133507829760 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-2517432110208 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (12009202974720 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-8160413681664 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (440050584000 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (-20926525833216 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (873568498176 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-13639634208 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ) +
    (-806678691840 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (781294448640 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-115408974720 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-765915288 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ) +
    (5253659099136 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (66134319104 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-84765408 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-20367782 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ) +
    (8399093760 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (445795926016 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (24095399424 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (27786688 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-31419 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ) +
    (-435444252672 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (27437400064 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (235532288 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (3045096 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-27617918976 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-194691072 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (18180480 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (10166992896 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-1088421888 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (26517504 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (201326592 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (1572864 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ)) / (100663296 : ℝ)

/-- Drift degree 2 of the second cross minor. -/
theorem oddCompactCrossBDGrade2_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade0 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade1 u a w =
      oddCompactCrossBDGrade2 u a w := by
  unfold oddCompactCrossBDGrade2 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2
  ring

/-- Drift degree 3 of the second cross minor. -/
def oddCompactCrossBDGrade3 (u a w : ℝ) : ℝ :=
  ((-144036956160 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (149690027520 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-871685775360 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-105161008512 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (553309510656 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (6993889056 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (199205683200 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (78924120960 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (8946219280 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-419784689664 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (7169556096 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-102083856 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-5643141120 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-38846490624 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-2874790376 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-2519643 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (80995811328 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-3170671616 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-76295416 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (66081 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (7582900224 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (3901952 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (449958 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-3600285696 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (257155072 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (2763648 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-200278016 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (7004160 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (25165824 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-393216 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ)) / (9437184 : ℝ)

/-- Drift degree 3 of the second cross minor. -/
theorem oddCompactCrossBDGrade3_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossBDGrade3 u a w := by
  unfold oddCompactCrossBDGrade3 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3
  ring

/-- Drift degree 4 of the second cross minor. -/
def oddCompactCrossBDGrade4 (u a w : ℝ) : ℝ :=
  ((58720370688000 : ℝ)*u^(4 : ℕ) +
    (-149551628451840 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (110896114544640 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (102962023464960 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-34672666100736 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-64542139858944 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (6529489430016 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (-34572088442880 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (11453027933184 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-428956628672 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ) +
    (30942520246272 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1787155278848 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-10114059744 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ) +
    (2448011427840 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (1277659602944 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (113881022016 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-411394056 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ) +
    (-9055828967424 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (204532187136 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (3541217568 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-4067721 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ) +
    (-17553162240 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-960525631488 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-14987681280 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (104302272 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (801808318464 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-57016090624 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-2310144 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (51852607488 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-309534720 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-15200157696 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (1371537408 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-150994944 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ)) / (905969664 : ℝ)

/-- Drift degree 4 of the second cross minor. -/
theorem oddCompactCrossBDGrade4_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade0 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade1 u a w =
      oddCompactCrossBDGrade4 u a w := by
  unfold oddCompactCrossBDGrade4 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4
  ring

/-- Drift degree 5 of the second cross minor. -/
def oddCompactCrossBDGrade5 (u a w : ℝ) : ℝ :=
  ((1334608773120 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-944191466496 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (3407250309120 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (19588050816 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-572494408704 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (164977598080 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-933990727680 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-177395260928 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-11455261080 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (829354352640 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-64407227264 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-455505872 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (23587061760 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (108268965888 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (512271056 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-2761581 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-190174593024 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (8541483008 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (63911736 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-17692344320 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (166493184 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (7540310016 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-399433728 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (289406976 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-25165824 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ)) / (169869312 : ℝ)

/-- Drift degree 5 of the second cross minor. -/
theorem oddCompactCrossBDGrade5_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade0 u a w =
      oddCompactCrossBDGrade5 u a w := by
  unfold oddCompactCrossBDGrade5 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5
  ring

/-- Drift degree 6 of the second cross minor. -/
def oddCompactCrossBDGrade6 (u a w : ℝ) : ℝ :=
  ((-22878509875200 : ℝ)*u^(6 : ℕ) +
    (43113141411840 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (-25047722549760 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (-17502625382400 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (6507574626816 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (7479075981312 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-706018174496 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ) +
    (6501228503040 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-1551604876800 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (5079399328 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ) +
    (-2149932883968 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (237444861568 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-258506044 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ) +
    (-485487083520 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-187693483008 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1929517040 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-6234129 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ) +
    (767493341184 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-49800143872 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (76998492 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (2288517120 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (83837501440 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-312903360 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-70568116224 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (3710570496 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-3289841664 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (843055104 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ)) / (1019215872 : ℝ)

/-- Drift degree 6 of the second cross minor. -/
theorem oddCompactCrossBDGrade6_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade0 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade1 u a w =
      oddCompactCrossBDGrade6 u a w := by
  unfold oddCompactCrossBDGrade6 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6
  ring

/-- Drift degree 7 of the second cross minor. -/
def oddCompactCrossBDGrade7 (u a w : ℝ) : ℝ :=
  ((-118978894080 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-10060643904 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-187443072000 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (52197864032 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-23867895552 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-8882881176 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (72029675520 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-5480820000 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-201619392 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-14867489280 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1893079504 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-1275204 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-1537597440 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-3473108736 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (70514913 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (5499469824 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-222884736 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (365958144 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-164167680 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (95551488 : ℝ)

/-- Drift degree 7 of the second cross minor. -/
theorem oddCompactCrossBDGrade7_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade0 u a w =
      oddCompactCrossBDGrade7 u a w := by
  unfold oddCompactCrossBDGrade7 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7
  ring

/-- Drift degree 8 of the second cross minor. -/
def oddCompactCrossBDGrade8 (u a w : ℝ) : ℝ :=
  ((11549599488000 : ℝ)*u^(8 : ℕ) +
    (-16308321154560 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (7207788751488 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (3592069655040 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1261554718240 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-1361683309056 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (55306487900 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-1337989847040 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (347451529056 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-193396057 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (45678163968 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-24092260336 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-8518659 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (106607185920 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-18606808192 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-111034005 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-41514590208 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (3391310208 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-297861120 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-4436926464 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (4105175040 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ)) / (2293235712 : ℝ)

/-- Drift degree 8 of the second cross minor. -/
theorem oddCompactCrossBDGrade8_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade0 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade1 u a w =
      oddCompactCrossBDGrade8 u a w := by
  unfold oddCompactCrossBDGrade8 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 9 of the second cross minor. -/
def oddCompactCrossBDGrade9 (u a w : ℝ) : ℝ :=
  ((28180062720 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (552516407040 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (185452646400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-200039518752 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (92134102272 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (3525433488 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-196781137920 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (28603310144 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (87899985 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-13791747072 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-12893136 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (3202007040 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (679833600 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-2851061760 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (3439853568 : ℝ)

/-- Drift degree 9 of the second cross minor. -/
theorem oddCompactCrossBDGrade9_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade9 u a w =
      oddCompactCrossBDGrade9 u a w := by
  unfold oddCompactCrossBDGrade9 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 10 of the second cross minor. -/
def oddCompactCrossBDGrade10 (u a w : ℝ) : ℝ :=
  ((-7913411251200 : ℝ)*u^(10 : ℕ) +
    (8228529262080 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-2548732865472 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-1006735011840 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (243908649248 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (455919345408 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3547837866 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (277859128320 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-80872661280 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-16568223 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (16022911488 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (867231336 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-24647086080 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (6487339968 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-774918144 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (30965760 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (10319560704 : ℝ)

/-- Drift degree 10 of the second cross minor. -/
theorem oddCompactCrossBDGrade10_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade9 u a w =
      oddCompactCrossBDGrade10 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 11 of the second cross minor. -/
def oddCompactCrossBDGrade11 (u a w : ℝ) : ℝ :=
  ((36302817600 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-34287535920 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (9648264960 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (3428348500 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-709145376 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (32190189 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (4389350400 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-340969236 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (359900352 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-41610240 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (1934917632 : ℝ)

/-- Drift degree 11 of the second cross minor. -/
theorem oddCompactCrossBDGrade11_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade4 u a w =
      oddCompactCrossBDGrade11 u a w := by
  unfold oddCompactCrossBDGrade11 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 12 of the second cross minor. -/
def oddCompactCrossBDGrade12 (u a w : ℝ) : ℝ :=
  ((622186790400 : ℝ)*u^(12 : ℕ) +
    (-454548543360 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (86963458352 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (39337549440 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-3626486740 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (-17288997824 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (11036021 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ) +
    (-3145401600 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (1046450156 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-72539520 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (391426560 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (7739670528 : ℝ)

/-- Drift degree 12 of the second cross minor. -/
theorem oddCompactCrossBDGrade12_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar4Grade0 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade5 u a w =
      oddCompactCrossBDGrade12 u a w := by
  unfold oddCompactCrossBDGrade12 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 13 of the second cross minor. -/
def oddCompactCrossBDGrade13 (u a w : ℝ) : ℝ :=
  ((-6265118400 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2073117224 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-1171797120 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-25910949 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-27426360 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-105880320 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (2902376448 : ℝ)

/-- Drift degree 13 of the second cross minor. -/
theorem oddCompactCrossBDGrade13_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar4Grade1 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade6 u a w =
      oddCompactCrossBDGrade13 u a w := by
  unfold oddCompactCrossBDGrade13 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 14 of the second cross minor. -/
def oddCompactCrossBDGrade14 (u a w : ℝ) : ℝ :=
  ((-24977484000 : ℝ)*u^(14 : ℕ) +
    (11806087920 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ) +
    (-1159580249 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-967155360 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (15864842 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ) +
    (215331140 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-23864400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (4353564672 : ℝ)

/-- Drift degree 14 of the second cross minor. -/
theorem oddCompactCrossBDGrade14_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar4Grade2 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossBDGrade14 u a w := by
  unfold oddCompactCrossBDGrade14 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 15 of the second cross minor. -/
def oddCompactCrossBDGrade15 (u a w : ℝ) : ℝ :=
  ((314898780 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-26636873 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (26565840 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (3265173504 : ℝ)

/-- Drift degree 15 of the second cross minor. -/
theorem oddCompactCrossBDGrade15_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade3 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossBDGrade15 u a w := by
  unfold oddCompactCrossBDGrade15 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 16 of the second cross minor. -/
def oddCompactCrossBDGrade16 (u a w : ℝ) : ℝ :=
  ((5231879100 : ℝ)*u^(16 : ℕ) +
    (-1386885375 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ) +
    (50959568 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ) +
    (99019305 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (19591041024 : ℝ)

/-- Drift degree 16 of the second cross minor. -/
theorem oddCompactCrossBDGrade16_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade4 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade6 u a w =
      oddCompactCrossBDGrade16 u a w := by
  unfold oddCompactCrossBDGrade16 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 17 of the second cross minor. -/
def oddCompactCrossBDGrade17 (u a w : ℝ) : ℝ :=
  ((-4858805 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (3265173504 : ℝ)

/-- Drift degree 17 of the second cross minor. -/
theorem oddCompactCrossBDGrade17_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade5 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade7 u a w =
      oddCompactCrossBDGrade17 u a w := by
  unfold oddCompactCrossBDGrade17 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 18 of the second cross minor. -/
def oddCompactCrossBDGrade18 (u a _w : ℝ) : ℝ :=
  ((-2658250 : ℝ)*u^(18 : ℕ) +
    (288365 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)) / (362797056 : ℝ)

/-- Drift degree 18 of the second cross minor. -/
theorem oddCompactCrossBDGrade18_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade6 u a w*oddCompactReflectedScalar8Grade12 u a w +
      oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactReflectedScalar6Grade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade8 u a w =
      oddCompactCrossBDGrade18 u a w := by
  unfold oddCompactCrossBDGrade18 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- Drift degree 20 of the second cross minor. -/
def oddCompactCrossBDGrade20 (u _a _w : ℝ) : ℝ :=
  ((6125 : ℝ)*u^(20 : ℕ)) / (68024448 : ℝ)

/-- Drift degree 20 of the second cross minor. -/
theorem oddCompactCrossBDGrade20_eq (u a w : ℝ) :
    oddCompactReflectedScalar4Grade8 u a w*oddCompactReflectedScalar8Grade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactReflectedScalar6Grade10 u a w =
      oddCompactCrossBDGrade20 u a w := by
  unfold oddCompactCrossBDGrade20 oddCompactReflectedScalar4Grade8 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- The second cross minor, stored as its drift grades. -/
def oddCompactCrossBD (u a w : ℝ) : ℝ :=
  oddCompactCrossBDGrade0 u a w +
    oddCompactCrossBDGrade1 u a w +
    oddCompactCrossBDGrade2 u a w +
    oddCompactCrossBDGrade3 u a w +
    oddCompactCrossBDGrade4 u a w +
    oddCompactCrossBDGrade5 u a w +
    oddCompactCrossBDGrade6 u a w +
    oddCompactCrossBDGrade7 u a w +
    oddCompactCrossBDGrade8 u a w +
    oddCompactCrossBDGrade9 u a w +
    oddCompactCrossBDGrade10 u a w +
    oddCompactCrossBDGrade11 u a w +
    oddCompactCrossBDGrade12 u a w +
    oddCompactCrossBDGrade13 u a w +
    oddCompactCrossBDGrade14 u a w +
    oddCompactCrossBDGrade15 u a w +
    oddCompactCrossBDGrade16 u a w +
    oddCompactCrossBDGrade17 u a w +
    oddCompactCrossBDGrade18 u a w +
    oddCompactCrossBDGrade20 u a w

/-- Exact scalar cross-minor expansion. -/
theorem oddCompactCrossBD_eq (u a w : ℝ) :
    oddCompactReflectedScalar4 u a w*oddCompactReflectedScalar8 u a w - (-oddCompactReflectedScalar6 u a w)^(2 : ℕ) = oddCompactCrossBD u a w := by
  rw [oddCompactReflectedScalar4_grades, oddCompactReflectedScalar6_grades,
    oddCompactReflectedScalar8_grades]
  unfold oddCompactCrossBD
  linear_combination oddCompactCrossBDGrade0_eq u a w +
    oddCompactCrossBDGrade1_eq u a w +
    oddCompactCrossBDGrade2_eq u a w +
    oddCompactCrossBDGrade3_eq u a w +
    oddCompactCrossBDGrade4_eq u a w +
    oddCompactCrossBDGrade5_eq u a w +
    oddCompactCrossBDGrade6_eq u a w +
    oddCompactCrossBDGrade7_eq u a w +
    oddCompactCrossBDGrade8_eq u a w +
    oddCompactCrossBDGrade9_eq u a w +
    oddCompactCrossBDGrade10_eq u a w +
    oddCompactCrossBDGrade11_eq u a w +
    oddCompactCrossBDGrade12_eq u a w +
    oddCompactCrossBDGrade13_eq u a w +
    oddCompactCrossBDGrade14_eq u a w +
    oddCompactCrossBDGrade15_eq u a w +
    oddCompactCrossBDGrade16_eq u a w +
    oddCompactCrossBDGrade17_eq u a w +
    oddCompactCrossBDGrade18_eq u a w +
    oddCompactCrossBDGrade20_eq u a w

end
end HTGeometry
