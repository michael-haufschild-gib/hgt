import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactReflectedGrades
import Mathlib.Tactic.LinearCombination

/-!
# Drift grades of the odd head and determinant (0)

The leading minor and the determinant are sums of monomial groups; each group
is the sum of its parts homogeneous in the drift coordinate `u`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 0 of the leading odd minor group 0. -/
def oddCompactScalarHeadPart0Grade0 (_u a w : ℝ) : ℝ :=
  ((1045094400 : ℝ) +
    (-3744921600 : ℝ)*a^(1 : ℕ) +
    (3242903040 : ℝ)*a^(2 : ℕ) +
    (3610552320 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-953285760 : ℝ)*a^(3 : ℕ) +
    (-2643010560 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (50855040 : ℝ)*a^(4 : ℕ) +
    (-573972480 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (355397760 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-6196608 : ℝ)*a^(5 : ℕ) +
    (680140800 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-9030528 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (918180 : ℝ)*a^(6 : ℕ) +
    (17694720 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-31094784 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (2299968 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (7200 : ℝ)*a^(7 : ℕ) +
    (-61341696 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (442368 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (46944 : ℝ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-375 : ℝ)*a^(8 : ℕ) +
    (-1474560 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (135168 : ℝ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-888 : ℝ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (98304 : ℝ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-1536 : ℝ)*a^(6 : ℕ)*w^(4 : ℕ)) / (8388608 : ℝ)

/-- Drift degree 1 of the leading odd minor group 0. -/
def oddCompactScalarHeadPart0Grade1 (u a w : ℝ) : ℝ :=
  ((-47790 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (74385 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (309420 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-241785 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-30240 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (58176 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ)) / (4096 : ℝ)

/-- The leading odd minor group 0 split by drift degree. -/
theorem oddCompactScalarHeadPart0_grades (u a w : ℝ) :
    oddCompactScalarHeadPart0 u a w =
      oddCompactScalarHeadPart0Grade0 u a w +
      oddCompactScalarHeadPart0Grade1 u a w := by
  unfold oddCompactScalarHeadPart0 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1
  ring

/-- Drift degree 1 of the leading odd minor group 1. -/
def oddCompactScalarHeadPart1Grade1 (u a w : ℝ) : ℝ :=
  ((-2530800 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-1446336 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-1280064 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (56556 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (411744 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (1566 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (516096 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (22480 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-99 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-393216 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (44032 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-640 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (16384 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-768 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ)) / (524288 : ℝ)

/-- Drift degree 2 of the leading odd minor group 1. -/
def oddCompactScalarHeadPart1Grade2 (u a w : ℝ) : ℝ :=
  ((-48988800 : ℝ)*u^(2 : ℕ) +
    (114048000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-68328360 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-83540160 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (13420260 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (41590800 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1446822 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (14532480 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-4043736 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (166545 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (-12225024 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (256554 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-368640 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (36960 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (1204224 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (2176 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (66560 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-1536 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ)) / (393216 : ℝ)

/-- The leading odd minor group 1 split by drift degree. -/
theorem oddCompactScalarHeadPart1_grades (u a w : ℝ) :
    oddCompactScalarHeadPart1 u a w =
      oddCompactScalarHeadPart1Grade1 u a w +
      oddCompactScalarHeadPart1Grade2 u a w := by
  unfold oddCompactScalarHeadPart1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart1Grade2
  ring

/-- Drift degree 2 of the leading odd minor group 2. -/
def oddCompactScalarHeadPart2Grade2 (u a w : ℝ) : ℝ :=
  ((10905 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ) +
    (-111504 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-656 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ) +
    (-3660 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-17664 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ)) / (3145728 : ℝ)

/-- Drift degree 3 of the leading odd minor group 2. -/
def oddCompactScalarHeadPart2Grade3 (u a w : ℝ) : ℝ :=
  ((-2108160 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (6108480 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-76988160 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-6643392 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (30494976 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (775296 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (7741440 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (3723360 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (74900 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-8515584 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-45024 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-1583 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-632832 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-7784 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (393216 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-31232 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-8192 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ)) / (2359296 : ℝ)

/-- Drift degree 4 of the leading odd minor group 2. -/
def oddCompactScalarHeadPart2Grade4 (u a w : ℝ) : ℝ :=
  ((15876000 : ℝ)*u^(4 : ℕ) +
    (-24981480 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (10698300 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (12177720 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1814147 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-3631368 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-2352960 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (1138624 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (46080 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-120832 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ)) / (294912 : ℝ)

/-- The leading odd minor group 2 split by drift degree. -/
theorem oddCompactScalarHeadPart2_grades (u a w : ℝ) :
    oddCompactScalarHeadPart2 u a w =
      oddCompactScalarHeadPart2Grade2 u a w +
      oddCompactScalarHeadPart2Grade3 u a w +
      oddCompactScalarHeadPart2Grade4 u a w := by
  unfold oddCompactScalarHeadPart2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4
  ring

/-- Drift degree 4 of the leading odd minor group 3. -/
def oddCompactScalarHeadPart3Grade4 (u a w : ℝ) : ℝ :=
  ((37182624 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (40435776 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-137536 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ) +
    (-3391072 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-25565 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ) +
    (7123456 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-123024 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (129024 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-942080 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ)) / (56623104 : ℝ)

/-- Drift degree 5 of the leading odd minor group 3. -/
def oddCompactScalarHeadPart3Grade5 (u a w : ℝ) : ℝ :=
  ((14109120 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-11588544 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (54961920 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (1728264 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-6465216 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (594704 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-5806080 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-1414192 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-12645 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (2930688 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-88232 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (187392 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-98304 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (10616832 : ℝ)

/-- Drift degree 6 of the leading odd minor group 3. -/
def oddCompactScalarHeadPart3Grade6 (u a w : ℝ) : ℝ :=
  ((-8731800 : ℝ)*u^(6 : ℕ) +
    (9551820 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (-2992775 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (-2608920 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (396699 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (376398 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (570960 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-100448 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-7680 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (11776 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ)) / (663552 : ℝ)

/-- The leading odd minor group 3 split by drift degree. -/
theorem oddCompactScalarHeadPart3_grades (u a w : ℝ) :
    oddCompactScalarHeadPart3 u a w =
      oddCompactScalarHeadPart3Grade4 u a w +
      oddCompactScalarHeadPart3Grade5 u a w +
      oddCompactScalarHeadPart3Grade6 u a w := by
  unfold oddCompactScalarHeadPart3 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6
  ring

/-- Drift degree 6 of the leading odd minor group 4. -/
def oddCompactScalarHeadPart4Grade6 (u a w : ℝ) : ℝ :=
  ((-545018 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ) +
    (-623832 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-16331 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ) +
    (9718 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-320224 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ)) / (31850496 : ℝ)

/-- Drift degree 7 of the leading odd minor group 4. -/
def oddCompactScalarHeadPart4Grade7 (u a w : ℝ) : ℝ :=
  ((-956880 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (15204 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-2058480 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (216160 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-116472 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-10398 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (241920 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-7967 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-33408 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ)) / (5971968 : ℝ)

/-- Drift degree 8 of the leading odd minor group 4. -/
def oddCompactScalarHeadPart4Grade8 (u a w : ℝ) : ℝ :=
  ((285768000 : ℝ)*u^(8 : ℕ) +
    (-217231920 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (47014932 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (26107920 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-2982659 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-1469880 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-31208 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-6644160 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (144651 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-79680 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (46080 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (143327232 : ℝ)

/-- Drift degree 9 of the leading odd minor group 4. -/
def oddCompactScalarHeadPart4Grade9 (u a w : ℝ) : ℝ :=
  ((-1311120 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2540136 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (1363680 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-308107 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (204600 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-241920 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (214990848 : ℝ)

/-- Drift degree 10 of the leading odd minor group 4. -/
def oddCompactScalarHeadPart4Grade10 (u _a _w : ℝ) : ℝ :=
  ((-15925 : ℝ)*u^(10 : ℕ)) / (82944 : ℝ)

/-- The leading odd minor group 4 split by drift degree. -/
theorem oddCompactScalarHeadPart4_grades (u a w : ℝ) :
    oddCompactScalarHeadPart4 u a w =
      oddCompactScalarHeadPart4Grade6 u a w +
      oddCompactScalarHeadPart4Grade7 u a w +
      oddCompactScalarHeadPart4Grade8 u a w +
      oddCompactScalarHeadPart4Grade9 u a w +
      oddCompactScalarHeadPart4Grade10 u a w := by
  unfold oddCompactScalarHeadPart4 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart4Grade10
  ring

/-- Drift degree 10 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade10 (u a w : ℝ) : ℝ :=
  ((62281440 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-7579362 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-2101680 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (59575 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (155988 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (643680 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (644972544 : ℝ)

/-- Drift degree 11 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade11 (u a w : ℝ) : ℝ :=
  ((150300 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-44269 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (11580 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (80621568 : ℝ)

/-- Drift degree 12 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade12 (u a w : ℝ) : ℝ :=
  ((2778300 : ℝ)*u^(12 : ℕ) +
    (-809115 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (31244 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (225 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (241864704 : ℝ)

/-- Drift degree 13 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade13 (u a w : ℝ) : ℝ :=
  ((-3125 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (40310784 : ℝ)

/-- Drift degree 14 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade14 (u a _w : ℝ) : ℝ :=
  ((-141750 : ℝ)*u^(14 : ℕ) +
    (16945 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)) / (362797056 : ℝ)

/-- Drift degree 16 of the leading odd minor group 5. -/
def oddCompactScalarHeadPart5Grade16 (u _a _w : ℝ) : ℝ :=
  ((175 : ℝ)*u^(16 : ℕ)) / (30233088 : ℝ)

/-- The leading odd minor group 5 split by drift degree. -/
theorem oddCompactScalarHeadPart5_grades (u a w : ℝ) :
    oddCompactScalarHeadPart5 u a w =
      oddCompactScalarHeadPart5Grade10 u a w +
      oddCompactScalarHeadPart5Grade11 u a w +
      oddCompactScalarHeadPart5Grade12 u a w +
      oddCompactScalarHeadPart5Grade13 u a w +
      oddCompactScalarHeadPart5Grade14 u a w +
      oddCompactScalarHeadPart5Grade16 u a w := by
  unfold oddCompactScalarHeadPart5 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 0 of the leading odd minor. -/
def oddCompactScalarHeadGrade0 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart0Grade0 u a w

/-- Drift degree 1 of the leading odd minor. -/
def oddCompactScalarHeadGrade1 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart0Grade1 u a w +
    oddCompactScalarHeadPart1Grade1 u a w

/-- Drift degree 2 of the leading odd minor. -/
def oddCompactScalarHeadGrade2 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart1Grade2 u a w +
    oddCompactScalarHeadPart2Grade2 u a w

/-- Drift degree 3 of the leading odd minor. -/
def oddCompactScalarHeadGrade3 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart2Grade3 u a w

/-- Drift degree 4 of the leading odd minor. -/
def oddCompactScalarHeadGrade4 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart2Grade4 u a w +
    oddCompactScalarHeadPart3Grade4 u a w

/-- Drift degree 5 of the leading odd minor. -/
def oddCompactScalarHeadGrade5 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart3Grade5 u a w

/-- Drift degree 6 of the leading odd minor. -/
def oddCompactScalarHeadGrade6 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart3Grade6 u a w +
    oddCompactScalarHeadPart4Grade6 u a w

/-- Drift degree 7 of the leading odd minor. -/
def oddCompactScalarHeadGrade7 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart4Grade7 u a w

/-- Drift degree 8 of the leading odd minor. -/
def oddCompactScalarHeadGrade8 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart4Grade8 u a w

/-- Drift degree 9 of the leading odd minor. -/
def oddCompactScalarHeadGrade9 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart4Grade9 u a w

/-- Drift degree 10 of the leading odd minor. -/
def oddCompactScalarHeadGrade10 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart4Grade10 u a w +
    oddCompactScalarHeadPart5Grade10 u a w

/-- Drift degree 11 of the leading odd minor. -/
def oddCompactScalarHeadGrade11 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart5Grade11 u a w

/-- Drift degree 12 of the leading odd minor. -/
def oddCompactScalarHeadGrade12 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart5Grade12 u a w

/-- Drift degree 13 of the leading odd minor. -/
def oddCompactScalarHeadGrade13 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart5Grade13 u a w

/-- Drift degree 14 of the leading odd minor. -/
def oddCompactScalarHeadGrade14 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart5Grade14 u a w

/-- Drift degree 16 of the leading odd minor. -/
def oddCompactScalarHeadGrade16 (u a w : ℝ) : ℝ :=
  oddCompactScalarHeadPart5Grade16 u a w

/-- The leading odd minor is the sum of its drift grades. -/
theorem oddCompactScalarHead_grades (u a w : ℝ) :
    oddCompactScalarHead u a w =
      oddCompactScalarHeadGrade0 u a w +
      oddCompactScalarHeadGrade1 u a w +
      oddCompactScalarHeadGrade2 u a w +
      oddCompactScalarHeadGrade3 u a w +
      oddCompactScalarHeadGrade4 u a w +
      oddCompactScalarHeadGrade5 u a w +
      oddCompactScalarHeadGrade6 u a w +
      oddCompactScalarHeadGrade7 u a w +
      oddCompactScalarHeadGrade8 u a w +
      oddCompactScalarHeadGrade9 u a w +
      oddCompactScalarHeadGrade10 u a w +
      oddCompactScalarHeadGrade11 u a w +
      oddCompactScalarHeadGrade12 u a w +
      oddCompactScalarHeadGrade13 u a w +
      oddCompactScalarHeadGrade14 u a w +
      oddCompactScalarHeadGrade16 u a w := by
  unfold oddCompactScalarHead oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16
  linear_combination oddCompactScalarHeadPart0_grades u a w + oddCompactScalarHeadPart1_grades u a w + oddCompactScalarHeadPart2_grades u a w + oddCompactScalarHeadPart3_grades u a w + oddCompactScalarHeadPart4_grades u a w + oddCompactScalarHeadPart5_grades u a w

/-- Drift degree 0 of the odd determinant group 0. -/
def oddCompactScalarDetPart0Grade0 (_u a w : ℝ) : ℝ :=
  ((133327918080000 : ℝ) +
    (-1170322836480000 : ℝ)*a^(1 : ℕ) +
    (3056149019448000 : ℝ)*a^(2 : ℕ) +
    (2197318161024000 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-3234595163058000 : ℝ)*a^(3 : ℕ) +
    (-6828624764640000 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (1438618066429500 : ℝ)*a^(4 : ℕ) +
    (-810408001536000 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (5680480942512000 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-312458771094525 : ℝ)*a^(5 : ℕ) +
    (5514490756800000 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1728982213214400 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (84783936384000 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-3637172398075200 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1908100388390400 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (688133149380000 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-2795104972800 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (1164850041024000 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (290388194380800 : ℝ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-94027479596640 : ℝ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (25082265600 : ℝ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-205744565341440 : ℝ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-21218407280640 : ℝ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (919144428480 : ℝ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (19158464010240 : ℝ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (695721000960 : ℝ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (862994856960 : ℝ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-720369745920 : ℝ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-8918138880 : ℝ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-51523928064 : ℝ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-2024275968 : ℝ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-445906944 : ℝ)*a^(4 : ℕ)*w^(14 : ℕ)) / (4194304 : ℝ)

/-- The odd determinant group 0 split by drift degree. -/
theorem oddCompactScalarDetPart0_grades (u a w : ℝ) :
    oddCompactScalarDetPart0 u a w =
      oddCompactScalarDetPart0Grade0 u a w := by
  unfold oddCompactScalarDetPart0 oddCompactScalarDetPart0Grade0
  ring

/-- Drift degree 0 of the odd determinant group 1. -/
def oddCompactScalarDetPart1Grade0 (_u a w : ℝ) : ℝ :=
  ((17757885741883200 : ℝ)*a^(6 : ℕ) +
    (64692581013043200 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-4638252622866480 : ℝ)*a^(7 : ℕ) +
    (-20977433018219520 : ℝ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (260599999990500 : ℝ)*a^(8 : ℕ) +
    (-20424267016980480 : ℝ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (3369957115728960 : ℝ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-5811676667055 : ℝ)*a^(9 : ℕ) +
    (8571669308928000 : ℝ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-230296912903440 : ℝ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (3686132019594240 : ℝ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-1257594284237760 : ℝ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (12651601990932 : ℝ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-1988630396789760 : ℝ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (75447282917952 : ℝ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-354252146319360 : ℝ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (237013482039552 : ℝ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-3073310327880 : ℝ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (265442016301056 : ℝ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-7788855210624 : ℝ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (11645818896384 : ℝ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-17888366168064 : ℝ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-17309315432448 : ℝ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (-87882494976 : ℝ)*a^(8 : ℕ)*w^(8 : ℕ) +
    (225114587136 : ℝ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (-320101318656 : ℝ)*a^(7 : ℕ)*w^(10 : ℕ) +
    (5464129536 : ℝ)*a^(6 : ℕ)*w^(12 : ℕ) +
    (35992682496 : ℝ)*a^(8 : ℕ)*w^(10 : ℕ) +
    (-15401484288 : ℝ)*a^(5 : ℕ)*w^(14 : ℕ) +
    (476577792 : ℝ)*a^(7 : ℕ)*w^(12 : ℕ) +
    (-301989888 : ℝ)*a^(6 : ℕ)*w^(14 : ℕ) +
    (9437184 : ℝ)*a^(8 : ℕ)*w^(12 : ℕ)) / (1073741824 : ℝ)

/-- The odd determinant group 1 split by drift degree. -/
theorem oddCompactScalarDetPart1_grades (u a w : ℝ) :
    oddCompactScalarDetPart1 u a w =
      oddCompactScalarDetPart1Grade0 u a w := by
  unfold oddCompactScalarDetPart1 oddCompactScalarDetPart1Grade0
  ring

/-- Drift degree 0 of the odd determinant group 2. -/
def oddCompactScalarDetPart2Grade0 (_u a w : ℝ) : ℝ :=
  ((689981341312512 : ℝ)*a^(10 : ℕ) +
    (-11061051956352 : ℝ)*a^(11 : ℕ) +
    (-394547436089856 : ℝ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (1103561759520 : ℝ)*a^(12 : ℕ) +
    (36791516718720 : ℝ)*a^(11 : ℕ)*w^(2 : ℕ) +
    (-153225194400 : ℝ)*a^(13 : ℕ) +
    (161952879532032 : ℝ)*a^(10 : ℕ)*w^(4 : ℕ) +
    (88151040288 : ℝ)*a^(12 : ℕ)*w^(2 : ℕ) +
    (-1496578500 : ℝ)*a^(14 : ℕ) +
    (211205940019200 : ℝ)*a^(9 : ℕ)*w^(6 : ℕ) +
    (6552585179136 : ℝ)*a^(11 : ℕ)*w^(4 : ℕ) +
    (-30618222912 : ℝ)*a^(13 : ℕ)*w^(2 : ℕ) +
    (64029375 : ℝ)*a^(15 : ℕ) +
    (22959310307328 : ℝ)*a^(10 : ℕ)*w^(6 : ℕ) +
    (-221551520256 : ℝ)*a^(12 : ℕ)*w^(4 : ℕ) +
    (183403800 : ℝ)*a^(14 : ℕ)*w^(2 : ℕ) +
    (32677516541952 : ℝ)*a^(9 : ℕ)*w^(8 : ℕ) +
    (-566216073216 : ℝ)*a^(11 : ℕ)*w^(6 : ℕ) +
    (1024618752 : ℝ)*a^(13 : ℕ)*w^(4 : ℕ) +
    (-564219740160 : ℝ)*a^(10 : ℕ)*w^(8 : ℕ) +
    (3029004288 : ℝ)*a^(12 : ℕ)*w^(6 : ℕ) +
    (-148918763520 : ℝ)*a^(9 : ℕ)*w^(10 : ℕ) +
    (2297364480 : ℝ)*a^(11 : ℕ)*w^(8 : ℕ) +
    (-37748736 : ℝ)*a^(10 : ℕ)*w^(10 : ℕ)) / (549755813888 : ℝ)

/-- Drift degree 1 of the odd determinant group 2. -/
def oddCompactScalarDetPart2Grade1 (u a w : ℝ) : ℝ :=
  ((99340101000 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (460797072750 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (3346976052000 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-9631316269125 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-1138009824000 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (10539531861300 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (77926892400 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-1192060800 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (16384 : ℝ)

/-- The odd determinant group 2 split by drift degree. -/
theorem oddCompactScalarDetPart2_grades (u a w : ℝ) :
    oddCompactScalarDetPart2 u a w =
      oddCompactScalarDetPart2Grade0 u a w +
      oddCompactScalarDetPart2Grade1 u a w := by
  unfold oddCompactScalarDetPart2 oddCompactScalarDetPart2Grade0 oddCompactScalarDetPart2Grade1
  ring

/-- Drift degree 1 of the odd determinant group 3. -/
def oddCompactScalarDetPart3Grade1 (u a w : ℝ) : ℝ :=
  ((-358674263568000 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (78569772422400 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (1670326293124800 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (31646174067000 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-175926814380000 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (19854106919100 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-1407352020105600 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-38477001066120 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-916975904256000 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (34790679061920 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-51616570596705 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (540689629973760 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-8521436108520 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (117473383157760 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (29132286232320 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (17871259932810 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-94596258032640 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (5260717172160 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-6392149032960 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-7576161212160 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-2863111772736 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (7514173440000 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-720218942208 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (131861053440 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (535543345152 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-203269865472 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (24677769216 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-566231040 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (-1833369600 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (339148800 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(13 : ℕ) +
    (-160432128 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(15 : ℕ) +
    (-6291456 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(15 : ℕ)) / (4194304 : ℝ)

/-- The odd determinant group 3 split by drift degree. -/
theorem oddCompactScalarDetPart3_grades (u a w : ℝ) :
    oddCompactScalarDetPart3 u a w =
      oddCompactScalarDetPart3Grade1 u a w := by
  unfold oddCompactScalarDetPart3 oddCompactScalarDetPart3Grade1
  ring

/-- Drift degree 1 of the odd determinant group 4. -/
def oddCompactScalarDetPart4Grade1 (u a w : ℝ) : ℝ :=
  ((-28188889845626880 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (1073888421384960 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (13208656920768000 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (24634754691840 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-85255946284032 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (4367474230320 : ℝ)*u^(1 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-2382316332797952 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-9302358695040 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (102454593084 : ℝ)*u^(1 : ℕ)*a^(11 : ℕ)*w^(1 : ℕ) +
    (-59676302241792 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (2197089547104 : ℝ)*u^(1 : ℕ)*a^(10 : ℕ)*w^(3 : ℕ) +
    (-23883420915 : ℝ)*u^(1 : ℕ)*a^(12 : ℕ)*w^(1 : ℕ) +
    (163622639468544 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (10909733150208 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(5 : ℕ) +
    (-162354803400 : ℝ)*u^(1 : ℕ)*a^(11 : ℕ)*w^(3 : ℕ) +
    (491449695731712 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (25244797083648 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(7 : ℕ) +
    (67773549312 : ℝ)*u^(1 : ℕ)*a^(10 : ℕ)*w^(5 : ℕ) +
    (12004586029056 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(9 : ℕ) +
    (1330154213376 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(7 : ℕ) +
    (-30830143104 : ℝ)*u^(1 : ℕ)*a^(11 : ℕ)*w^(5 : ℕ) +
    (-17184073973760 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(11 : ℕ) +
    (1959601078272 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(9 : ℕ) +
    (-73085048832 : ℝ)*u^(1 : ℕ)*a^(10 : ℕ)*w^(7 : ℕ) +
    (760133713920 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(11 : ℕ) +
    (-59331477504 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(9 : ℕ) +
    (569195520 : ℝ)*u^(1 : ℕ)*a^(11 : ℕ)*w^(7 : ℕ) +
    (41372614656 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(13 : ℕ) +
    (-6878134272 : ℝ)*u^(1 : ℕ)*a^(8 : ℕ)*w^(11 : ℕ) +
    (290119680 : ℝ)*u^(1 : ℕ)*a^(10 : ℕ)*w^(9 : ℕ) +
    (805306368 : ℝ)*u^(1 : ℕ)*a^(7 : ℕ)*w^(13 : ℕ) +
    (-9437184 : ℝ)*u^(1 : ℕ)*a^(9 : ℕ)*w^(11 : ℕ)) / (8589934592 : ℝ)

/-- The odd determinant group 4 split by drift degree. -/
theorem oddCompactScalarDetPart4_grades (u a w : ℝ) :
    oddCompactScalarDetPart4 u a w =
      oddCompactScalarDetPart4Grade1 u a w := by
  unfold oddCompactScalarDetPart4 oddCompactScalarDetPart4Grade1
  ring

/-- Drift degree 1 of the odd determinant group 5. -/
def oddCompactScalarDetPart5Grade1 (u a w : ℝ) : ℝ :=
  ((-450854448 : ℝ)*u^(1 : ℕ)*a^(13 : ℕ)*w^(1 : ℕ) +
    (-8511608016 : ℝ)*u^(1 : ℕ)*a^(12 : ℕ)*w^(3 : ℕ) +
    (20537025 : ℝ)*u^(1 : ℕ)*a^(14 : ℕ)*w^(1 : ℕ) +
    (134476044 : ℝ)*u^(1 : ℕ)*a^(13 : ℕ)*w^(3 : ℕ) +
    (580607616 : ℝ)*u^(1 : ℕ)*a^(12 : ℕ)*w^(5 : ℕ)) / (17179869184 : ℝ)

/-- Drift degree 2 of the odd determinant group 5. -/
def oddCompactScalarDetPart5Grade2 (u a w : ℝ) : ℝ :=
  ((-71602030080000 : ℝ)*u^(2 : ℕ) +
    (459523517040000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-929225222730000 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-673139914272000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (798636655557000 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (1621061588592000 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-349247128291875 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (287676766944000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-1151323554888000 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-1293760200441600 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (358571664837000 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-34708717209600 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (725744310235200 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (547359146568000 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-116244058154400 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1105230873600 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-261623874099600 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-104501254671360 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (283288739580 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-6967296000 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (63880977611520 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (8652518184960 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-7894182366720 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-286554193920 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (403878346752 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (2925527040 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-4391043072 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ)) / (1048576 : ℝ)

/-- The odd determinant group 5 split by drift degree. -/
theorem oddCompactScalarDetPart5_grades (u a w : ℝ) :
    oddCompactScalarDetPart5 u a w =
      oddCompactScalarDetPart5Grade1 u a w +
      oddCompactScalarDetPart5Grade2 u a w := by
  unfold oddCompactScalarDetPart5 oddCompactScalarDetPart5Grade1 oddCompactScalarDetPart5Grade2
  ring

/-- Drift degree 2 of the odd determinant group 6. -/
def oddCompactScalarDetPart6Grade2 (u a w : ℝ) : ℝ :=
  ((26733689173382400 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (-6251426271843120 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ) +
    (-20246220198167040 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (719462881587240 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ) +
    (4268047390231680 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-23803355437605 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ) +
    (3177617066991360 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-572167884695760 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-2188184272951680 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (18496674396432 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-894061298737920 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (166093232771808 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (1444918963507200 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (491442849654528 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-915897554904 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (195109357277184 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-16689933339968 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-208853413134336 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-50562187201536 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (9274939200 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-15083053678592 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (412568758272 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (7249702420480 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (2408403861504 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (-63386419200 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (105611665408 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(10 : ℕ) +
    (36138123264 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-11466964992 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(12 : ℕ) +
    (4387241984 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(14 : ℕ) +
    (-181665792 : ℝ)*u^(2 : ℕ)*a^(7 : ℕ)*w^(12 : ℕ) +
    (-536870912 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(16 : ℕ) +
    (100663296 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ)*w^(14 : ℕ)) / (268435456 : ℝ)

/-- The odd determinant group 6 split by drift degree. -/
theorem oddCompactScalarDetPart6_grades (u a w : ℝ) :
    oddCompactScalarDetPart6 u a w =
      oddCompactScalarDetPart6Grade2 u a w := by
  unfold oddCompactScalarDetPart6 oddCompactScalarDetPart6Grade2
  ring

/-- Drift degree 2 of the odd determinant group 7. -/
def oddCompactScalarDetPart7Grade2 (u a w : ℝ) : ℝ :=
  ((1009767477337344 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ) +
    (-42849644525184 : ℝ)*u^(2 : ℕ)*a^(10 : ℕ) +
    (-279981399384576 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (716673781248 : ℝ)*u^(2 : ℕ)*a^(11 : ℕ) +
    (31401183857664 : ℝ)*u^(2 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (-195261333264 : ℝ)*u^(2 : ℕ)*a^(12 : ℕ) +
    (156209831378944 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (-716728962912 : ℝ)*u^(2 : ℕ)*a^(11 : ℕ)*w^(2 : ℕ) +
    (-1194679976 : ℝ)*u^(2 : ℕ)*a^(13 : ℕ) +
    (-13398046130688 : ℝ)*u^(2 : ℕ)*a^(10 : ℕ)*w^(4 : ℕ) +
    (-26811531664 : ℝ)*u^(2 : ℕ)*a^(12 : ℕ)*w^(2 : ℕ) +
    (113200375 : ℝ)*u^(2 : ℕ)*a^(14 : ℕ) +
    (-35215689228288 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ)*w^(6 : ℕ) +
    (-297926288384 : ℝ)*u^(2 : ℕ)*a^(11 : ℕ)*w^(4 : ℕ) +
    (944707728 : ℝ)*u^(2 : ℕ)*a^(13 : ℕ)*w^(2 : ℕ) +
    (3602979618816 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(8 : ℕ) +
    (-1955857162240 : ℝ)*u^(2 : ℕ)*a^(10 : ℕ)*w^(6 : ℕ) +
    (8496891776 : ℝ)*u^(2 : ℕ)*a^(12 : ℕ)*w^(4 : ℕ) +
    (-4008185298944 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ)*w^(8 : ℕ) +
    (34029201408 : ℝ)*u^(2 : ℕ)*a^(11 : ℕ)*w^(6 : ℕ) +
    (-2379688706048 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(10 : ℕ) +
    (46754856960 : ℝ)*u^(2 : ℕ)*a^(10 : ℕ)*w^(8 : ℕ) +
    (12976128000 : ℝ)*u^(2 : ℕ)*a^(9 : ℕ)*w^(10 : ℕ) +
    (-1006632960 : ℝ)*u^(2 : ℕ)*a^(8 : ℕ)*w^(12 : ℕ)) / (137438953472 : ℝ)

/-- Drift degree 3 of the odd determinant group 7. -/
def oddCompactScalarDetPart7Grade3 (u a w : ℝ) : ℝ :=
  ((-129377634750 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (242388298125 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-884784859875 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (1572038572275 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (341708560200 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-1903202541675 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-23886746100 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (331128000 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (4096 : ℝ)

/-- The odd determinant group 7 split by drift degree. -/
theorem oddCompactScalarDetPart7_grades (u a w : ℝ) :
    oddCompactScalarDetPart7 u a w =
      oddCompactScalarDetPart7Grade2 u a w +
      oddCompactScalarDetPart7Grade3 u a w := by
  unfold oddCompactScalarDetPart7 oddCompactScalarDetPart7Grade2 oddCompactScalarDetPart7Grade3
  ring

/-- Drift degree 3 of the odd determinant group 8. -/
def oddCompactScalarDetPart8Grade3 (u a w : ℝ) : ℝ :=
  ((-117314525167200 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (49658037616800 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-477254212790400 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (33429432014550 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (34229201583600 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-28285795404540 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (553755514232160 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-55164304994085 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (560135135589120 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-6334657338960 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (22438849460220 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-241451832087360 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (12639378191190 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-77847744291840 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-27606731634000 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-7279904407269 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (51458981664000 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-3991144049280 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (4272494653440 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (7032217825920 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-4686624669696 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (631412446656 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-79354920960 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (-504126624768 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (142162329600 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (-27193929728 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (235929600 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (3497787392 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (-402653184 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ) +
    (-256065536 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(13 : ℕ) +
    (55836672 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(15 : ℕ) +
    (2097152 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(15 : ℕ)) / (3145728 : ℝ)

/-- The odd determinant group 8 split by drift degree. -/
theorem oddCompactScalarDetPart8_grades (u a w : ℝ) :
    oddCompactScalarDetPart8 u a w =
      oddCompactScalarDetPart8Grade3 u a w := by
  unfold oddCompactScalarDetPart8 oddCompactScalarDetPart8Grade3
  ring

/-- Drift degree 3 of the odd determinant group 9. -/
def oddCompactScalarDetPart9Grade3 (u a w : ℝ) : ℝ :=
  ((15395623469521920 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-64475308379904 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-5237797639973376 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (21413557698240 : ℝ)*u^(3 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-96301161060096 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (1444340757104 : ℝ)*u^(3 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (489858409707520 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (4910337813376 : ℝ)*u^(3 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-126534055542 : ℝ)*u^(3 : ℕ)*a^(11 : ℕ)*w^(1 : ℕ) +
    (4367304808808448 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (68859787971584 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (132231999920 : ℝ)*u^(3 : ℕ)*a^(10 : ℕ)*w^(3 : ℕ) +
    (-641415567 : ℝ)*u^(3 : ℕ)*a^(12 : ℕ)*w^(1 : ℕ) +
    (77306531987456 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (865940344576 : ℝ)*u^(3 : ℕ)*a^(9 : ℕ)*w^(5 : ℕ) +
    (-2874800456 : ℝ)*u^(3 : ℕ)*a^(11 : ℕ)*w^(3 : ℕ) +
    (113546108 : ℝ)*u^(3 : ℕ)*a^(13 : ℕ)*w^(1 : ℕ) +
    (-259979153506304 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-4970672259072 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(7 : ℕ) +
    (-18576896 : ℝ)*u^(3 : ℕ)*a^(10 : ℕ)*w^(5 : ℕ) +
    (585235612 : ℝ)*u^(3 : ℕ)*a^(12 : ℕ)*w^(3 : ℕ) +
    (-9261461602304 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(9 : ℕ) +
    (-296882761728 : ℝ)*u^(3 : ℕ)*a^(9 : ℕ)*w^(7 : ℕ) +
    (3297055808 : ℝ)*u^(3 : ℕ)*a^(11 : ℕ)*w^(5 : ℕ) +
    (8713139126272 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(11 : ℕ) +
    (-686000013312 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(9 : ℕ) +
    (11944804352 : ℝ)*u^(3 : ℕ)*a^(10 : ℕ)*w^(7 : ℕ) +
    (-150785228800 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(11 : ℕ) +
    (11692228608 : ℝ)*u^(3 : ℕ)*a^(9 : ℕ)*w^(9 : ℕ) +
    (-30500978688 : ℝ)*u^(3 : ℕ)*a^(6 : ℕ)*w^(13 : ℕ) +
    (1460928512 : ℝ)*u^(3 : ℕ)*a^(8 : ℕ)*w^(11 : ℕ) +
    (-335544320 : ℝ)*u^(3 : ℕ)*a^(7 : ℕ)*w^(13 : ℕ)) / (12884901888 : ℝ)

/-- The odd determinant group 9 split by drift degree. -/
theorem oddCompactScalarDetPart9_grades (u a w : ℝ) :
    oddCompactScalarDetPart9 u a w =
      oddCompactScalarDetPart9Grade3 u a w := by
  unfold oddCompactScalarDetPart9 oddCompactScalarDetPart9Grade3
  ring

/-- Drift degree 4 of the odd determinant group 10. -/
def oddCompactScalarDetPart10Grade4 (u a w : ℝ) : ℝ :=
  ((314879186160000 : ℝ)*u^(4 : ℕ) +
    (-1560880349532000 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (2565566322057000 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (1668010914864000 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1936957684817250 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-3140656614871200 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (838518571523925 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (-800506847952000 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (1928198049454800 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (2260858107787200 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-618405285082500 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (109130754902400 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-929072543621400 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1065969028026720 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (121459203054000 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-3357409305600 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (341366180725440 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (235300752023040 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (15751545556950 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (15328051200 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-105265123171200 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-20720842951680 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-15402196004040 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (15666929959680 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (662668738560 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (2192963399552 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-889717751808 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-5455872000 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-78536962048 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (11177164800 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-169082880 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (2097152 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(16 : ℕ)) / (4718592 : ℝ)

/-- The odd determinant group 10 split by drift degree. -/
theorem oddCompactScalarDetPart10_grades (u a w : ℝ) :
    oddCompactScalarDetPart10 u a w =
      oddCompactScalarDetPart10Grade4 u a w := by
  unfold oddCompactScalarDetPart10 oddCompactScalarDetPart10Grade4
  ring

/-- Drift degree 4 of the odd determinant group 11. -/
def oddCompactScalarDetPart11Grade4 (u a w : ℝ) : ℝ :=
  ((-488589992700802560 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ) +
    (80519131327129920 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ) +
    (315710132013849600 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-5662228559636880 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ) +
    (-56785551842177280 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (258969318019764 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ) +
    (-95521109169792000 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (4042505729510208 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-12647069147997 : ℝ)*u^(4 : ℕ)*a^(9 : ℕ) +
    (25187277777822720 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-61051010578512 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (22085331913307136 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-587227578175808 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (11559635592520 : ℝ)*u^(4 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-4927160516014080 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (3134883514624 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-4104881185480704 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-25063249204736 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-2147706158608 : ℝ)*u^(4 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (409176014331904 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (1442251748352 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (331530868883456 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (12876724408320 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-9371942125568 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (129102345216 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ)*w^(8 : ℕ) +
    (-1008759472128 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (-643090186240 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(10 : ℕ) +
    (188371435520 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(12 : ℕ) +
    (10285760512 : ℝ)*u^(4 : ℕ)*a^(8 : ℕ)*w^(10 : ℕ) +
    (-38017171456 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ)*w^(14 : ℕ) +
    (1156055040 : ℝ)*u^(4 : ℕ)*a^(7 : ℕ)*w^(12 : ℕ) +
    (-503316480 : ℝ)*u^(4 : ℕ)*a^(6 : ℕ)*w^(14 : ℕ)) / (9663676416 : ℝ)

/-- The odd determinant group 11 split by drift degree. -/
theorem oddCompactScalarDetPart11_grades (u a w : ℝ) :
    oddCompactScalarDetPart11 u a w =
      oddCompactScalarDetPart11Grade4 u a w := by
  unfold oddCompactScalarDetPart11 oddCompactScalarDetPart11Grade4
  ring

/-- Drift degree 4 of the odd determinant group 12. -/
def oddCompactScalarDetPart12Grade4 (u a w : ℝ) : ℝ :=
  ((-1009477404512 : ℝ)*u^(4 : ℕ)*a^(10 : ℕ) +
    (-753695371368 : ℝ)*u^(4 : ℕ)*a^(11 : ℕ) +
    (-5745507693984 : ℝ)*u^(4 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (-5786561375 : ℝ)*u^(4 : ℕ)*a^(12 : ℕ) +
    (-184176659940 : ℝ)*u^(4 : ℕ)*a^(11 : ℕ)*w^(2 : ℕ) +
    (367700074 : ℝ)*u^(4 : ℕ)*a^(13 : ℕ) +
    (-1333506764224 : ℝ)*u^(4 : ℕ)*a^(10 : ℕ)*w^(4 : ℕ) +
    (5140091729 : ℝ)*u^(4 : ℕ)*a^(12 : ℕ)*w^(2 : ℕ) +
    (911001383936 : ℝ)*u^(4 : ℕ)*a^(9 : ℕ)*w^(6 : ℕ) +
    (29551540480 : ℝ)*u^(4 : ℕ)*a^(11 : ℕ)*w^(4 : ℕ) +
    (86134739968 : ℝ)*u^(4 : ℕ)*a^(10 : ℕ)*w^(6 : ℕ) +
    (296258019328 : ℝ)*u^(4 : ℕ)*a^(9 : ℕ)*w^(8 : ℕ)) / (154618822656 : ℝ)

/-- Drift degree 5 of the odd determinant group 12. -/
def oddCompactScalarDetPart12Grade5 (u a w : ℝ) : ℝ :=
  ((16420365360000 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-27934233885000 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (58043651878800 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (12429321887700 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-60960041010900 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-26374749811200 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (13131098389665 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (82255763463840 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1887046761600 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-17760960538920 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-35545782666240 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-23311411200 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (9183908514420 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (5349065954880 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-2556442258864 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-293549710080 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (265250845184 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (4832256000 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (-8267538432 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (-9830400 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ)) / (589824 : ℝ)

/-- The odd determinant group 12 split by drift degree. -/
theorem oddCompactScalarDetPart12_grades (u a w : ℝ) :
    oddCompactScalarDetPart12 u a w =
      oddCompactScalarDetPart12Grade4 u a w +
      oddCompactScalarDetPart12Grade5 u a w := by
  unfold oddCompactScalarDetPart12 oddCompactScalarDetPart12Grade4 oddCompactScalarDetPart12Grade5
  ring

/-- Drift degree 5 of the odd determinant group 13. -/
def oddCompactScalarDetPart13Grade5 (u a w : ℝ) : ℝ :=
  ((7000529525475840 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-9607430266968960 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-10258453861908480 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (2381332693558320 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (8251269990710880 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-119858875304580 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-431821772582400 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-1300315542547656 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (3095119720653 : ℝ)*u^(5 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-2174185566882240 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (13269574921022 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (2710305166537728 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (375382939227792 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (1858871809392 : ℝ)*u^(5 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (492306938270208 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (10353593501856 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-705993297754112 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-44775667328512 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-65678045908992 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-1876931821440 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (51291296956416 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (1919539977216 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (2859339087872 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (70985559552 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(9 : ℕ) +
    (-454395166720 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (-47381192704 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(11 : ℕ) +
    (38654705664 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ) +
    (16871063552 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(13 : ℕ) +
    (-286556160 : ℝ)*u^(5 : ℕ)*a^(7 : ℕ)*w^(11 : ℕ) +
    (-2290089984 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(15 : ℕ) +
    (215875584 : ℝ)*u^(5 : ℕ)*a^(6 : ℕ)*w^(13 : ℕ) +
    (-50331648 : ℝ)*u^(5 : ℕ)*a^(5 : ℕ)*w^(15 : ℕ)) / (905969664 : ℝ)

/-- The odd determinant group 13 split by drift degree. -/
theorem oddCompactScalarDetPart13_grades (u a w : ℝ) :
    oddCompactScalarDetPart13 u a w =
      oddCompactScalarDetPart13Grade5 u a w := by
  unfold oddCompactScalarDetPart13 oddCompactScalarDetPart13Grade5
  ring

/-- Drift degree 5 of the odd determinant group 14. -/
def oddCompactScalarDetPart14Grade5 (u a w : ℝ) : ℝ :=
  ((25487343162368 : ℝ)*u^(5 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-6078064311552 : ℝ)*u^(5 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (11184325180416 : ℝ)*u^(5 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (21892331996 : ℝ)*u^(5 : ℕ)*a^(11 : ℕ)*w^(1 : ℕ) +
    (-45465736194048 : ℝ)*u^(5 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (39150921696 : ℝ)*u^(5 : ℕ)*a^(10 : ℕ)*w^(3 : ℕ) +
    (7091304751 : ℝ)*u^(5 : ℕ)*a^(12 : ℕ)*w^(1 : ℕ) +
    (-8534975666688 : ℝ)*u^(5 : ℕ)*a^(9 : ℕ)*w^(5 : ℕ) +
    (32505701160 : ℝ)*u^(5 : ℕ)*a^(11 : ℕ)*w^(3 : ℕ) +
    (-15160702115840 : ℝ)*u^(5 : ℕ)*a^(8 : ℕ)*w^(7 : ℕ) +
    (132040717056 : ℝ)*u^(5 : ℕ)*a^(10 : ℕ)*w^(5 : ℕ) +
    (42578948096 : ℝ)*u^(5 : ℕ)*a^(9 : ℕ)*w^(7 : ℕ) +
    (550855016448 : ℝ)*u^(5 : ℕ)*a^(8 : ℕ)*w^(9 : ℕ)) / (231928233984 : ℝ)

/-- Drift degree 6 of the odd determinant group 14. -/
def oddCompactScalarDetPart14Grade6 (u a w : ℝ) : ℝ :=
  ((-23349746070000 : ℝ)*u^(6 : ℕ) +
    (92772976968000 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (-127737021151575 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (-68607407408400 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (85499048684700 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (104479851596400 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (35521267294800 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-59017944885060 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-60892926507360 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-5455558029600 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (17382137519040 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (29730282834000 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (161439264000 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-4776185670860 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-7461893180160 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-541900800 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (689505891200 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-20866457600 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (134348800 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (589824 : ℝ)

/-- The odd determinant group 14 split by drift degree. -/
theorem oddCompactScalarDetPart14_grades (u a w : ℝ) :
    oddCompactScalarDetPart14 u a w =
      oddCompactScalarDetPart14Grade5 u a w +
      oddCompactScalarDetPart14Grade6 u a w := by
  unfold oddCompactScalarDetPart14 oddCompactScalarDetPart14Grade5 oddCompactScalarDetPart14Grade6
  ring

/-- Drift degree 6 of the odd determinant group 15. -/
def oddCompactScalarDetPart15Grade6 (u a w : ℝ) : ℝ :=
  ((-76225277764349280 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ) +
    (17249271512490720 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ) +
    (46453586706961920 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-1973303994282435 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ) +
    (-11047646266916880 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (113302047262929 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ) +
    (-9137832646671360 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1344808579158384 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (4248993637233072 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-50424314196905 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-754622945015616 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-445517000781096 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (4631338317090816 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-926590255839984 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-141504129100 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (980357125075200 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (70802647190752 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-877578675609600 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (142432272797184 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (2552781507288 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-143950504165376 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-3389195942784 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (53836162007040 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-9999939014656 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (5034472243200 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-64993355776 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (-642470903808 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (67476783104 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (4838129664 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-2537570304 : ℝ)*u^(6 : ℕ)*a^(6 : ℕ)*w^(12 : ℕ) +
    (346554368 : ℝ)*u^(6 : ℕ)*a^(5 : ℕ)*w^(14 : ℕ) +
    (-33554432 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ)*w^(16 : ℕ)) / (1358954496 : ℝ)

/-- The odd determinant group 15 split by drift degree. -/
theorem oddCompactScalarDetPart15_grades (u a w : ℝ) :
    oddCompactScalarDetPart15 u a w =
      oddCompactScalarDetPart15Grade6 u a w := by
  unfold oddCompactScalarDetPart15 oddCompactScalarDetPart15Grade6
  ring

/-- Drift degree 6 of the odd determinant group 16. -/
def oddCompactScalarDetPart16Grade6 (u a w : ℝ) : ℝ :=
  ((-1253910333683472 : ℝ)*u^(6 : ℕ)*a^(8 : ℕ) +
    (5074985188080 : ℝ)*u^(6 : ℕ)*a^(9 : ℕ) +
    (918874791084032 : ℝ)*u^(6 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-3436564013560 : ℝ)*u^(6 : ℕ)*a^(10 : ℕ) +
    (-34678159467296 : ℝ)*u^(6 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-42740465112 : ℝ)*u^(6 : ℕ)*a^(11 : ℕ) +
    (-97723826610432 : ℝ)*u^(6 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-930943510592 : ℝ)*u^(6 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (1356846044 : ℝ)*u^(6 : ℕ)*a^(12 : ℕ) +
    (1249675567360 : ℝ)*u^(6 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (38384717135 : ℝ)*u^(6 : ℕ)*a^(11 : ℕ)*w^(2 : ℕ) +
    (-78237094912 : ℝ)*u^(6 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (206186198096 : ℝ)*u^(6 : ℕ)*a^(10 : ℕ)*w^(4 : ℕ) +
    (-76140663767040 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (727319501056 : ℝ)*u^(6 : ℕ)*a^(9 : ℕ)*w^(6 : ℕ) +
    (-648901890048 : ℝ)*u^(6 : ℕ)*a^(8 : ℕ)*w^(8 : ℕ) +
    (656296247296 : ℝ)*u^(6 : ℕ)*a^(7 : ℕ)*w^(10 : ℕ)) / (347892350976 : ℝ)

/-- Drift degree 7 of the odd determinant group 16. -/
def oddCompactScalarDetPart16Grade7 (u a w : ℝ) : ℝ :=
  ((-2427012579600 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2642073962400 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-5487027843150 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (343913180775 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (3220966737315 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (3112885717200 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-857737673130 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-4956539927400 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-228904552800 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (2422458058680 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (2472422400 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-398189281320 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (21708575200 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-307302400 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (409600 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ)) / (221184 : ℝ)

/-- The odd determinant group 16 split by drift degree. -/
theorem oddCompactScalarDetPart16_grades (u a w : ℝ) :
    oddCompactScalarDetPart16 u a w =
      oddCompactScalarDetPart16Grade6 u a w +
      oddCompactScalarDetPart16Grade7 u a w := by
  unfold oddCompactScalarDetPart16 oddCompactScalarDetPart16Grade6 oddCompactScalarDetPart16Grade7
  ring

/-- Drift degree 7 of the odd determinant group 17. -/
def oddCompactScalarDetPart17Grade7 (u a w : ℝ) : ℝ :=
  ((-13696702119429120 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (5653888221217440 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (10099662554592000 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-653746236262632 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (2820715911152640 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-3512311736628936 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (22260737255585 : ℝ)*u^(7 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-924009743140992 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (222911549159004 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-1966120430731776 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (1058914313550768 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (6749481057074 : ℝ)*u^(7 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-793563362267520 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-43061700729904 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (1057703853336576 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-208623446184960 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-3048744027336 : ℝ)*u^(7 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (239883950307328 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (3478405185984 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-132545388478464 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (23008252005376 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (242545070624 : ℝ)*u^(7 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (-17295662727168 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-15906830336 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (4055544889344 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (-832041680896 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-4126390144 : ℝ)*u^(7 : ℕ)*a^(7 : ℕ)*w^(9 : ℕ) +
    (148139671552 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (-928294912 : ℝ)*u^(7 : ℕ)*a^(6 : ℕ)*w^(11 : ℕ) +
    (-9663676416 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ) +
    (-2395340800 : ℝ)*u^(7 : ℕ)*a^(5 : ℕ)*w^(13 : ℕ) +
    (232783872 : ℝ)*u^(7 : ℕ)*a^(4 : ℕ)*w^(15 : ℕ)) / (2038431744 : ℝ)

/-- The odd determinant group 17 split by drift degree. -/
theorem oddCompactScalarDetPart17_grades (u a w : ℝ) :
    oddCompactScalarDetPart17 u a w =
      oddCompactScalarDetPart17Grade7 u a w := by
  unfold oddCompactScalarDetPart17 oddCompactScalarDetPart17Grade7
  ring

/-- Drift degree 7 of the odd determinant group 18. -/
def oddCompactScalarDetPart18Grade7 (u a w : ℝ) : ℝ :=
  ((-32155074077440 : ℝ)*u^(7 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-28114964253632 : ℝ)*u^(7 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (44076050762496 : ℝ)*u^(7 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (75435518280 : ℝ)*u^(7 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-3454638086592 : ℝ)*u^(7 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (31642846271 : ℝ)*u^(7 : ℕ)*a^(11 : ℕ)*w^(1 : ℕ) +
    (-29075579407872 : ℝ)*u^(7 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (118498727912 : ℝ)*u^(7 : ℕ)*a^(10 : ℕ)*w^(3 : ℕ) +
    (467631627392 : ℝ)*u^(7 : ℕ)*a^(9 : ℕ)*w^(5 : ℕ) +
    (3139782291456 : ℝ)*u^(7 : ℕ)*a^(8 : ℕ)*w^(7 : ℕ)) / (521838526464 : ℝ)

/-- Drift degree 8 of the odd determinant group 18. -/
def oddCompactScalarDetPart18Grade8 (u a w : ℝ) : ℝ :=
  ((509791537080000 : ℝ)*u^(8 : ℕ) +
    (-1657587381685200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (1926378818622900 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (823812365073600 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1107912356078895 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-1077730876571040 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-431634018564000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (596806463907720 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (445677140299680 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (75635353281600 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-112418201407500 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-203514724010880 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-2135436307200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (3139877697744 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (58542913621440 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (5283532800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-5746799394960 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-5683294809600 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (1947171066048 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (159183052800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-131512365056 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-754483200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (31850496 : ℝ)

/-- The odd determinant group 18 split by drift degree. -/
theorem oddCompactScalarDetPart18_grades (u a w : ℝ) :
    oddCompactScalarDetPart18 u a w =
      oddCompactScalarDetPart18Grade7 u a w +
      oddCompactScalarDetPart18Grade8 u a w := by
  unfold oddCompactScalarDetPart18 oddCompactScalarDetPart18Grade7 oddCompactScalarDetPart18Grade8
  ring

/-- Drift degree 8 of the odd determinant group 19. -/
def oddCompactScalarDetPart19Grade8 (u a w : ℝ) : ℝ :=
  ((8661797228318238720 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-1470483819176424960 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (-4940665698130329600 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (124886293915608768 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (928360671224478720 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-6080291612236688 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (1308632740567695360 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-71892662183713536 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (122066854055628 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-334558436107256832 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (3490801947278016 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-9498356082897 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (-65631397959487488 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (12448143758092288 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-158566074132528 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (70979100452563968 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (80319125976000 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-54084176611688448 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-540470646973440 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (11872614793664 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-9238252271984640 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-101639483718400 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (8664320050462720 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-95733507338240 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-358331465088 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (518752321798144 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (5210608859136 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-270548743487488 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (5608230682624 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (31837384605696 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-3081221701632 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (-95227478016 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ)) / (782757789696 : ℝ)

end
end HTGeometry
