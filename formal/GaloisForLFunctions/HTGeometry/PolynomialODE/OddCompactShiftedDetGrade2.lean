import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactShiftedDetGrade1

/-!
# Substituted determinant groups, drift-graded (2)

Substituting `a = 17+3t` preserves the degree in `u`, so each determinant group
splits into drift grades that no later step mixes.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 18 of the substituted determinant group 30. -/
def oddCompactShiftedDetPart30Grade18 (u t w : ℝ) : ℝ :=
  ((1211165585846564724 : ℝ)*u^(18 : ℕ) +
    (1501968325234324725 : ℝ)*u^(18 : ℕ)*t^(1 : ℕ) +
    (890513387664224076 : ℝ)*u^(18 : ℕ)*t^(2 : ℕ) +
    (3000949034554359335 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ) +
    (288547652743553862 : ℝ)*u^(18 : ℕ)*t^(3 : ℕ) +
    (3362902885599700641 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (47167646745729528 : ℝ)*u^(18 : ℕ)*t^(4 : ℕ) +
    (1346466505623904278 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (204055711857742432 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ) +
    (2999521985891085 : ℝ)*u^(18 : ℕ)*t^(5 : ℕ) +
    (236129057606643570 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (70018844948422080 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (16619310319914387 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(4 : ℕ) +
    (-3010402843155072 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (-24832115502237264 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ) +
    (231190321845789 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(5 : ℕ) +
    (-3020833032249024 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(3 : ℕ) +
    (-11858107903951248 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ) +
    (-252437867080416 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(4 : ℕ) +
    (-2076136983824112 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(2 : ℕ) +
    (506810502236160 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ) +
    (-133561443971376 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(3 : ℕ) +
    (161388167316480 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ)*t^(1 : ℕ) +
    (12697238799360 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ)*t^(2 : ℕ) +
    (-23688806400 : ℝ)*u^(18 : ℕ)*w^(10 : ℕ) +
    (-4180377600 : ℝ)*u^(18 : ℕ)*w^(10 : ℕ)*t^(1 : ℕ)) / (45137758519296 : ℝ)

/-- Group 30 of the determinant, substituted and split by drift degree. -/
theorem oddCompactScalarDetPart30_shift (u t w : ℝ) :
    oddCompactScalarDetPart30 u (17+3*t) w =
      oddCompactShiftedDetPart30Grade17 u t w +
      oddCompactShiftedDetPart30Grade18 u t w := by
  unfold oddCompactScalarDetPart30 oddCompactShiftedDetPart30Grade17 oddCompactShiftedDetPart30Grade18
  ring

/-- Drift degree 18 of the substituted determinant group 31. -/
def oddCompactShiftedDetPart31Grade18 (u t _w : ℝ) : ℝ :=
  ((2158932503104071601 : ℝ)*u^(18 : ℕ) +
    (2285928532698428754 : ℝ)*u^(18 : ℕ)*t^(1 : ℕ) +
    (1008497882072836215 : ℝ)*u^(18 : ℕ)*t^(2 : ℕ) +
    (237293619311255580 : ℝ)*u^(18 : ℕ)*t^(3 : ℕ) +
    (31406508438254415 : ℝ)*u^(18 : ℕ)*t^(4 : ℕ) +
    (2216930007406194 : ℝ)*u^(18 : ℕ)*t^(5 : ℕ) +
    (65203823747241 : ℝ)*u^(18 : ℕ)*t^(6 : ℕ)) / (180551034077184 : ℝ)

/-- Drift degree 19 of the substituted determinant group 31. -/
def oddCompactShiftedDetPart31Grade19 (u t w : ℝ) : ℝ :=
  ((906288234944827749 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ) +
    (662811048444252267 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (184199457802654674 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (57430839003461480 : ℝ)*u^(19 : ℕ)*w^(3 : ℕ) +
    (27246441324219606 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(3 : ℕ) +
    (111041421528400032 : ℝ)*u^(19 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (2686516013412153 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(4 : ℕ) +
    (53778517064889264 : ℝ)*u^(19 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (16363796960410416 : ℝ)*u^(19 : ℕ)*w^(5 : ℕ) +
    (150177949225551 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(5 : ℕ) +
    (9796181777233056 : ℝ)*u^(19 : ℕ)*w^(3 : ℕ)*t^(3 : ℕ) +
    (7875668436889392 : ℝ)*u^(19 : ℕ)*w^(5 : ℕ)*t^(1 : ℕ) +
    (608518993440168 : ℝ)*u^(19 : ℕ)*w^(3 : ℕ)*t^(4 : ℕ) +
    (1298340431927568 : ℝ)*u^(19 : ℕ)*w^(5 : ℕ)*t^(2 : ℕ) +
    (-86285440632960 : ℝ)*u^(19 : ℕ)*w^(7 : ℕ) +
    (73785141780624 : ℝ)*u^(19 : ℕ)*w^(5 : ℕ)*t^(3 : ℕ) +
    (21105720702720 : ℝ)*u^(19 : ℕ)*w^(7 : ℕ)*t^(1 : ℕ) +
    (6411628794240 : ℝ)*u^(19 : ℕ)*w^(7 : ℕ)*t^(2 : ℕ) +
    (432320716800 : ℝ)*u^(19 : ℕ)*w^(9 : ℕ) +
    (76291891200 : ℝ)*u^(19 : ℕ)*w^(9 : ℕ)*t^(1 : ℕ)) / (67706637778944 : ℝ)

/-- Drift degree 20 of the substituted determinant group 31. -/
def oddCompactShiftedDetPart31Grade20 (u t w : ℝ) : ℝ :=
  ((288093612933169173 : ℝ)*u^(20 : ℕ) +
    (353735644054689151 : ℝ)*u^(20 : ℕ)*t^(1 : ℕ) +
    (162605511154793274 : ℝ)*u^(20 : ℕ)*t^(2 : ℕ) +
    (503570122343881488 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ) +
    (30836546600246982 : ℝ)*u^(20 : ℕ)*t^(3 : ℕ) +
    (337489456585282944 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (1642381369038945 : ℝ)*u^(20 : ℕ)*t^(4 : ℕ) +
    (69068389649623200 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (-26784816192701088 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ) +
    (-78481797441525 : ℝ)*u^(20 : ℕ)*t^(5 : ℕ) +
    (3368519545660416 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (-16223983643657376 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (-190129323552048 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(4 : ℕ) +
    (-2984539967234784 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (431118384178560 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ) +
    (-168637633078752 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(3 : ℕ) +
    (-1135604747520 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ) +
    (-13626232871040 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ)*t^(2 : ℕ) +
    (-7571534745600 : ℝ)*u^(20 : ℕ)*w^(8 : ℕ) +
    (-1336153190400 : ℝ)*u^(20 : ℕ)*w^(8 : ℕ)*t^(1 : ℕ)) / (270826551115776 : ℝ)

/-- Group 31 of the determinant, substituted and split by drift degree. -/
theorem oddCompactScalarDetPart31_shift (u t w : ℝ) :
    oddCompactScalarDetPart31 u (17+3*t) w =
      oddCompactShiftedDetPart31Grade18 u t w +
      oddCompactShiftedDetPart31Grade19 u t w +
      oddCompactShiftedDetPart31Grade20 u t w := by
  unfold oddCompactScalarDetPart31 oddCompactShiftedDetPart31Grade18 oddCompactShiftedDetPart31Grade19 oddCompactShiftedDetPart31Grade20
  ring

/-- Drift degree 21 of the substituted determinant group 32. -/
def oddCompactShiftedDetPart32Grade21 (u t w : ℝ) : ℝ :=
  ((2278828352887667 : ℝ)*u^(21 : ℕ)*w^(1 : ℕ) +
    (1138047940197120 : ℝ)*u^(21 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (383417237103318 : ℝ)*u^(21 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (1820233912021513 : ℝ)*u^(21 : ℕ)*w^(3 : ℕ) +
    (90521530121736 : ℝ)*u^(21 : ℕ)*w^(1 : ℕ)*t^(3 : ℕ) +
    (1351777172139981 : ℝ)*u^(21 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (8078297754159 : ℝ)*u^(21 : ℕ)*w^(1 : ℕ)*t^(4 : ℕ) +
    (305337428483499 : ℝ)*u^(21 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (-25763945212320 : ℝ)*u^(21 : ℕ)*w^(5 : ℕ) +
    (21789529571007 : ℝ)*u^(21 : ℕ)*w^(3 : ℕ)*t^(3 : ℕ) +
    (-10363752423360 : ℝ)*u^(21 : ℕ)*w^(5 : ℕ)*t^(1 : ℕ) +
    (-1026560092320 : ℝ)*u^(21 : ℕ)*w^(5 : ℕ)*t^(2 : ℕ) +
    (1298350166400 : ℝ)*u^(21 : ℕ)*w^(7 : ℕ) +
    (229120617600 : ℝ)*u^(21 : ℕ)*w^(7 : ℕ)*t^(1 : ℕ)) / (25389989167104 : ℝ)

/-- Drift degree 22 of the substituted determinant group 32. -/
def oddCompactShiftedDetPart32Grade22 (u t w : ℝ) : ℝ :=
  ((61306641760463779 : ℝ)*u^(22 : ℕ) +
    (50689700664850788 : ℝ)*u^(22 : ℕ)*t^(1 : ℕ) +
    (10923289705362762 : ℝ)*u^(22 : ℕ)*t^(2 : ℕ) +
    (25264395205397856 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ) +
    (-187799657621004 : ℝ)*u^(22 : ℕ)*t^(3 : ℕ) +
    (2651279877676512 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (-171538068032325 : ℝ)*u^(22 : ℕ)*t^(4 : ℕ) +
    (-2176173846506592 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (-1396127322760320 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ) +
    (-327752875159776 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (-228536275167360 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (3148082599680 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (-54476296761600 : ℝ)*u^(22 : ℕ)*w^(6 : ℕ) +
    (-9613464134400 : ℝ)*u^(22 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ)) / (1828079220031488 : ℝ)

/-- Drift degree 23 of the substituted determinant group 32. -/
def oddCompactShiftedDetPart32Grade23 (u t w : ℝ) : ℝ :=
  ((832057751506 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ) +
    (2537270019562 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (1081582671558 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (3730901641735 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ) +
    (116424877374 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(3 : ℕ) +
    (1380157783680 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (127370007585 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (-37416027600 : ℝ)*u^(23 : ℕ)*w^(5 : ℕ) +
    (-6602828400 : ℝ)*u^(23 : ℕ)*w^(5 : ℕ)*t^(1 : ℕ)) / (3173748645888 : ℝ)

/-- Drift degree 24 of the substituted determinant group 32. -/
def oddCompactShiftedDetPart32Grade24 (u t w : ℝ) : ℝ :=
  ((92667230025415 : ℝ)*u^(24 : ℕ) +
    (43703197496895 : ℝ)*u^(24 : ℕ)*t^(1 : ℕ) +
    (5191952844690 : ℝ)*u^(24 : ℕ)*t^(2 : ℕ) +
    (7796170998000 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ) +
    (1375794882000 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (254740937850 : ℝ)*u^(24 : ℕ)*w^(4 : ℕ) +
    (44954283150 : ℝ)*u^(24 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ)) / (28563737812992 : ℝ)

/-- Group 32 of the determinant, substituted and split by drift degree. -/
theorem oddCompactScalarDetPart32_shift (u t w : ℝ) :
    oddCompactScalarDetPart32 u (17+3*t) w =
      oddCompactShiftedDetPart32Grade21 u t w +
      oddCompactShiftedDetPart32Grade22 u t w +
      oddCompactShiftedDetPart32Grade23 u t w +
      oddCompactShiftedDetPart32Grade24 u t w := by
  unfold oddCompactScalarDetPart32 oddCompactShiftedDetPart32Grade21 oddCompactShiftedDetPart32Grade22 oddCompactShiftedDetPart32Grade23 oddCompactShiftedDetPart32Grade24
  ring

/-- Drift degree 24 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade24 (u t w : ℝ) : ℝ :=
  ((-158474695649741 : ℝ)*u^(24 : ℕ) +
    (-83898368285157 : ℝ)*u^(24 : ℕ)*t^(1 : ℕ) +
    (-14805594403263 : ℝ)*u^(24 : ℕ)*t^(2 : ℕ) +
    (-26493573189070 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ) +
    (-870917317839 : ℝ)*u^(24 : ℕ)*t^(3 : ℕ) +
    (-9350672890260 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (-825059372670 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ)) / (57127475625984 : ℝ)

/-- Drift degree 25 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade25 (u t w : ℝ) : ℝ :=
  ((1346046238160 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ) +
    (854427144930 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (108862865910 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (135057571425 : ℝ)*u^(25 : ℕ)*w^(3 : ℕ) +
    (23833689075 : ℝ)*u^(25 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ)) / (42845606719488 : ℝ)

/-- Drift degree 26 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade26 (u t w : ℝ) : ℝ :=
  ((-1408295606765 : ℝ)*u^(26 : ℕ) +
    (-1829042716245 : ℝ)*u^(26 : ℕ)*t^(1 : ℕ) +
    (-374085486990 : ℝ)*u^(26 : ℕ)*t^(2 : ℕ) +
    (-609577107300 : ℝ)*u^(26 : ℕ)*w^(2 : ℕ) +
    (-107572430700 : ℝ)*u^(26 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ)) / (257073640316928 : ℝ)

/-- Drift degree 27 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade27 (u t w : ℝ) : ℝ :=
  ((3018794975 : ℝ)*u^(27 : ℕ)*w^(1 : ℕ) +
    (532728525 : ℝ)*u^(27 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ)) / (7140934453248 : ℝ)

/-- Drift degree 28 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade28 (u t _w : ℝ) : ℝ :=
  ((-38616544925 : ℝ)*u^(28 : ℕ) +
    (-13225203075 : ℝ)*u^(28 : ℕ)*t^(1 : ℕ)) / (171382426877952 : ℝ)

/-- Drift degree 30 of the substituted determinant group 33. -/
def oddCompactShiftedDetPart33Grade30 (u _t _w : ℝ) : ℝ :=
  ((-2786875 : ℝ)*u^(30 : ℕ)) / (1586874322944 : ℝ)

/-- Group 33 of the determinant, substituted and split by drift degree. -/
theorem oddCompactScalarDetPart33_shift (u t w : ℝ) :
    oddCompactScalarDetPart33 u (17+3*t) w =
      oddCompactShiftedDetPart33Grade24 u t w +
      oddCompactShiftedDetPart33Grade25 u t w +
      oddCompactShiftedDetPart33Grade26 u t w +
      oddCompactShiftedDetPart33Grade27 u t w +
      oddCompactShiftedDetPart33Grade28 u t w +
      oddCompactShiftedDetPart33Grade30 u t w := by
  unfold oddCompactScalarDetPart33 oddCompactShiftedDetPart33Grade24 oddCompactShiftedDetPart33Grade25 oddCompactShiftedDetPart33Grade26 oddCompactShiftedDetPart33Grade27 oddCompactShiftedDetPart33Grade28 oddCompactShiftedDetPart33Grade30
  ring

end
end HTGeometry
