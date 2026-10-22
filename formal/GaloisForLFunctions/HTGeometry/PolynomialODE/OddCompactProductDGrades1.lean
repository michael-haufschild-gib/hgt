import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductDGrades0
import Mathlib.Tactic.LinearCombination

/-!
# The middle determinant product, drift-graded (1)

The grade `d` part of a product is the sum of the products of the factors'
grades over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 7 of the middle determinant product, block 1. -/
theorem oddCompactProductDGrade7Part1_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade7Part1 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactCrossADGrade1 oddCompactCrossADGrade2 oddCompactCrossADGrade4 oddCompactProductDGrade7Part1 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7
  ring

/-- Drift degree 7 of the middle determinant product. -/
theorem oddCompactProductDGrade7_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade7 u a w := by
  unfold oddCompactProductDGrade7
  linear_combination oddCompactProductDGrade7Part0_eq u a w + oddCompactProductDGrade7Part1_eq u a w

/-- Drift degree 8 of the middle determinant product, block 0. -/
def oddCompactProductDGrade8Part0 (u a w : ℝ) : ℝ :=
  ((10305171985717002240000 : ℝ)*u^(8 : ℕ) +
    (-33243833170079907840000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (37687894788599296819200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (20886972083495239680000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-20551861689143090872320 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-28968469333332047953920 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (6378792794044620595200 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-6234054496894844928000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (13146149292860572139520 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-1246985900838729996288 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (13041066343546292797440 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-2926661737243401510912 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (158601609738897054720 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (345168918046310400000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-4892084921024936607744 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (384125804264203689984 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-11233499304315958272 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-3531091340984907202560 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (754952596413940236288 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-33185982892948359168 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (177487688303670688 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-1991705316714086400 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (1033208524163853582336 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-58468654561945960448 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (2924007057109611648 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (7356666456643224 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (645588459350654976000 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-71262541136315154432 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-155137302265131008 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-83069181478005792 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-38730840591876 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-203171547517355556864 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (12483028518588891136 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-239257113558877440 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-1250660201566656 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-54550963767 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-52643086272791838720 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-18052428223595151360 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (612224405045084160 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (11545453208226816 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (2527824257568 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (35951250925330366464 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-2772083031488004096 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (13714462966358016 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (35807687401152 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (1592301433179340800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (4682435309230620672 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-111473558568173568 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-255867434416128 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-2325034133467693056 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (286227445626961920 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-2395187161645056 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-9838105775308800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-186452484078698496 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (5298631007797248 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (45779164128608256 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-4231630688354304 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (11596411699200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(16 : ℕ) +
    (862549960556544 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-65558380806144 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (150289495621632 : ℝ)

/-- Drift degree 8 of the middle determinant product, block 1. -/
def oddCompactProductDGrade8Part1 (u a w : ℝ) : ℝ :=
  ((14641815183851520000 : ℝ)*u^(8 : ℕ) +
    (-72048942335139840000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (94463481541201920000 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (86858801759084544000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-50294781449192448000 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-125984812300894126080 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (11290266364300416000 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-19944077961314304000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (59760039823381278720 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-1321527512903328000 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (-83345682347641405440 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-12335384844713536512 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (198509386982837760 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (1118222982748569600 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (16734866866753609728 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-2391684183744901632 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-22568925602399040 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-73560757923926507520 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (17105777788147433472 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1129786243935090048 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (708477043645440 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-14165928522547200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-23385675187613270016 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-2795609196899292160 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (131983683469658112 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (6896505400980 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (44693874626930933760 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (497236093952507904 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-466344510755458048 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-10572371574380640 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-260154966810 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-4981678882059976704 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (1725378334046846976 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-24941309375307264 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-73807755080928 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (2127979575 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-5816119397512642560 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-2751280655573975040 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (100445388666052608 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (764750654952192 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (363706806240 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (2931244966367723520 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-383430837474164736 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (1447786929917952 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (7293502580544 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (172048350235852800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (521039869957373952 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-15268893214900224 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (32104682548224 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-284261451130994688 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (32340545158250496 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-255679713116160 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-1340110326988800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-25579414452436992 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (649845408792576 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (4769439849381888 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-535896784896000 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (158829769654272 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-13297218748416 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (18786186952704 : ℝ)

/-- Drift degree 8 of the middle determinant product. -/
def oddCompactProductDGrade8 (u a w : ℝ) : ℝ :=
  oddCompactProductDGrade8Part0 u a w +
    oddCompactProductDGrade8Part1 u a w

/-- Drift degree 8 of the middle determinant product, block 0. -/
theorem oddCompactProductDGrade8Part0_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade2 u a w =
      oddCompactProductDGrade8Part0 u a w := by
  unfold oddCompactCrossADGrade2 oddCompactCrossADGrade4 oddCompactCrossADGrade6 oddCompactCrossADGrade8 oddCompactProductDGrade8Part0 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade6
  ring

/-- Drift degree 8 of the middle determinant product, block 1. -/
theorem oddCompactProductDGrade8Part1_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade0 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade1 u a w =
      oddCompactProductDGrade8Part1 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactCrossADGrade1 oddCompactCrossADGrade3 oddCompactCrossADGrade5 oddCompactCrossADGrade7 oddCompactProductDGrade8Part1 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 8 of the middle determinant product. -/
theorem oddCompactProductDGrade8_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade8 u a w := by
  unfold oddCompactProductDGrade8
  linear_combination oddCompactProductDGrade8Part0_eq u a w + oddCompactProductDGrade8Part1_eq u a w

/-- Drift degree 9 of the middle determinant product, block 0. -/
def oddCompactProductDGrade9Part0 (u a w : ℝ) : ℝ :=
  ((185654059130054246400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-301426746643248906240 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (506234686833996595200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (146533097709578833920 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-478004258718703779840 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-17827113938311529472 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-105440995973962137600 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (140418029465234288640 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-6161621940939675648 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (274608745590929817600 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-24215506238239567872 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (2786177648704721152 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (1979326213757337600 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-47982339440027467776 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (1224274450307892224 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-322313111232893072 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-107871697886584504320 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (12049093628937093120 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (1095571691640448 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (3840434794848180 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (5963314669399572480 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-1422609184833406976 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (70346915594812368 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (90572449666380 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (19301151734161735680 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (811899434233331712 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-185217581764267776 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-679314166243344 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (113352529149 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-3677740173634830336 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (535333399935848448 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-8188236313676160 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-6940421705724 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-1072177103241216000 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-802069523297992704 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (31082853520084992 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-15519107746944 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (649822282932289536 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-72154490755055616 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (530448972979200 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (15507872305643520 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (75917467428323328 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-1869479918321664 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-25234739501727744 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (2386512125362176 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-31165356441600 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (-1197364966588416 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (159829960163328 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ)) / (28179280429056 : ℝ)

/-- Drift degree 9 of the middle determinant product, block 1. -/
def oddCompactProductDGrade9Part1 (u a w : ℝ) : ℝ :=
  ((4963334199662592000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-6814635838708838400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (16121205725976576000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (2589178498067082240 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-14028046121287065600 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-83596152501354240 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-3398682206335795200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (4708942657885393920 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-244663545390583680 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (5260156321780776960 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-507448141911567360 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (102926669664994272 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (70775961432883200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-2110098410662993920 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (652340582252160 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-11499146727719024 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-1023150099458949120 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (429256887040376832 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-11145508595155456 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (153947728651736 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (301262259060178944 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (2780910230801408 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (1874491326560704 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (6066961767638 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (169352076601589760 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-48269890680700928 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-128034760061440 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-29647725458624 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-18312994827 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-93032408266309632 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (2601313956200448 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-15252728768000 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-213480515488 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-8392952040652800 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-11078456546557952 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (28731578466304 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (72581658240 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (15547624744550400 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-1023429286821888 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (2589312096256 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (40913590026240 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (1404365686439936 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-23880827568128 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-465834300407808 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (32364176605184 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-3481809190912 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ)) / (2348273369088 : ℝ)

/-- Drift degree 9 of the middle determinant product. -/
def oddCompactProductDGrade9 (u a w : ℝ) : ℝ :=
  oddCompactProductDGrade9Part0 u a w +
    oddCompactProductDGrade9Part1 u a w

/-- Drift degree 9 of the middle determinant product, block 0. -/
theorem oddCompactProductDGrade9Part0_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade9 u a w =
      oddCompactProductDGrade9Part0 u a w := by
  unfold oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade9Part0 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4
  ring

/-- Drift degree 9 of the middle determinant product, block 1. -/
theorem oddCompactProductDGrade9Part1_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade9Part1 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactCrossADGrade1 oddCompactCrossADGrade2 oddCompactCrossADGrade3 oddCompactCrossADGrade4 oddCompactProductDGrade9Part1 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 9 of the middle determinant product. -/
theorem oddCompactProductDGrade9_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade9 u a w := by
  unfold oddCompactProductDGrade9
  linear_combination oddCompactProductDGrade9Part0_eq u a w + oddCompactProductDGrade9Part1_eq u a w

/-- Drift degree 10 of the middle determinant product, block 0. -/
def oddCompactProductDGrade10Part0 (u a w : ℝ) : ℝ :=
  ((-6362182073955778560000 : ℝ)*u^(10 : ℕ) +
    (16588638888099722035200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-15622696189111689216000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-7402754546931282739200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (7289885053310709841920 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (8093933678285132267520 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1948259767786970707968 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (2412256688715202560000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-2979742166085875097600 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (314399510369904632832 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-3156752111255723704320 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (529867745507179155456 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-28491065038144866048 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-131761867409090150400 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (1015955442884355194880 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-53844532914115360768 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (934071689051263040 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (748762492523863080960 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-153422559987858505728 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (6938757496737869312 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (12054572431554456 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (573513382703923200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-111170298187858968576 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (1371309816275980288 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-528675263292085152 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-307174323148956 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-174294268275987578880 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (28132192504341725184 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (85029642753328128 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-762871044195312 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-380605387617 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (7090828125227974656 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-1287382615018229760 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (73344752696333952 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (38670212000976 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (17353691372590202880 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (931585205986394112 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-160981410696167424 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (131689226420352 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-3893417573675433984 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (384954829942652928 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-4291560352659456 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-474913694086594560 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-578203986987319296 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (13204860728180736 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (314238042799865856 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-26146243604643840 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (2428868430397440 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (18594417875091456 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-4489746478792704 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-579820584960 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(16 : ℕ)) / (338151365148672 : ℝ)

/-- Drift degree 10 of the middle determinant product, block 1. -/
def oddCompactProductDGrade10Part1 (u a w : ℝ) : ℝ :=
  ((-27268818374246400000 : ℝ)*u^(10 : ℕ) +
    (90723611809087488000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-90109773044637696000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-78925476519751680000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (38463573320077824000 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (77418274373300551680 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-8885115756500313600 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (21223252855848960000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-24165007041683957760 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (1460422068578461440 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-21257899382737797120 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (2502062515941166080 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-165505260061766400 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-1230085640060928000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (9775746968586117120 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-45878437903912704 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (6997362825581760 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (2740625620626309120 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-1301090147403620352 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (96663655898625792 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (22416887034368 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (10530181663948800 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-285183324795273216 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-109413038034647040 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-11236775735015552 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-4300142139044 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-1098898014928896000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (401016442941898752 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (8097737978638848 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (87459163549344 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (4429366701 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (-31035651822452736 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-31056481421983744 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (1120688417384960 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (1727218035408 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (192983190711828480 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (45582741365456896 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-3317208840273920 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (9128035633280 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-90416410924154880 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (10844510997970944 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-81356125673472 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-3518568742256640 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-16264710932398080 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (347931533901824 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (10535364187914240 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-651478746267648 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (504545243299840 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-58188216926208 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ)) / (28179280429056 : ℝ)

/-- Drift degree 10 of the middle determinant product. -/
def oddCompactProductDGrade10 (u a w : ℝ) : ℝ :=
  oddCompactProductDGrade10Part0 u a w +
    oddCompactProductDGrade10Part1 u a w

/-- Drift degree 10 of the middle determinant product, block 0. -/
theorem oddCompactProductDGrade10Part0_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade7 u a w =
      oddCompactProductDGrade10Part0 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade4 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade10Part0 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade6
  ring

/-- Drift degree 10 of the middle determinant product, block 1. -/
theorem oddCompactProductDGrade10Part1_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade0 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade1 u a w =
      oddCompactProductDGrade10Part1 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactCrossADGrade1 oddCompactCrossADGrade2 oddCompactCrossADGrade3 oddCompactCrossADGrade5 oddCompactProductDGrade10Part1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 10 of the middle determinant product. -/
theorem oddCompactProductDGrade10_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade0 u a w =
      oddCompactProductDGrade10 u a w := by
  unfold oddCompactProductDGrade10
  linear_combination oddCompactProductDGrade10Part0_eq u a w + oddCompactProductDGrade10Part1_eq u a w

/-- Drift degree 11 of the middle determinant product, block 0. -/
def oddCompactProductDGrade11Part0 (u a w : ℝ) : ℝ :=
  ((-109778949341300736000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (117091272971395031040 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-232290302717207347200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-23510215090086248448 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (166467952394672209920 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-11477571056398189056 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (53548520766780211200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-38533517625011300352 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (6259355732056095616 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-66799142567937146880 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (2123040595579262976 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-990520895450150080 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-922942339625779200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (17621200780129271808 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (212009163963394816 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (34366850981018196 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (16208513163220746240 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-3309427277401227264 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (130545724239034848 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (317586358252950 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (273075647810568192 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-170190998610200064 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-7898359623241320 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-2563964948745 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-3223357183717539840 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (504287458556436480 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (5988119069347200 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-32277578833428 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (22742874758578176 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-15477056911312896 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (490106592697824 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (170982424266670080 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (35540320688013312 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-1526523669863424 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-51885995456987136 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (3535241674973184 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-1718710519726080 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (-4215055175122944 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (1518750935285760 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (1558267822080 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ)) / (63403380965376 : ℝ)

/-- Drift degree 11 of the middle determinant product, block 1. -/
def oddCompactProductDGrade11Part1 (u a w : ℝ) : ℝ :=
  ((33769913264640000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-114989405510476800 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-155113864496640000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (78839661135225600 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (222870286960588800 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-11641100319115200 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (27864327794688000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-60370958919709440 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (2160224614615680 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-72623360300175360 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (4143333439768320 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-508072689850080 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-729810321408000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (21976890664642560 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-643152541622400 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (16909080934668 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (6166904745000960 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (189215821255680 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (111824575526592 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (416389372150 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-3650210429337600 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (20399607788544 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (2032666425936 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-1463221441 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-82811195228160 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-254118878109696 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-1948801171968 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-2393701312 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (126318971191296 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-7899491786752 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (144280012672 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (1789168189440 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (66386092032 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-43316281344 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ)) / (2641807540224 : ℝ)

/-- Drift degree 11 of the middle determinant product. -/
def oddCompactProductDGrade11 (u a w : ℝ) : ℝ :=
  oddCompactProductDGrade11Part0 u a w +
    oddCompactProductDGrade11Part1 u a w

/-- Drift degree 11 of the middle determinant product, block 0. -/
theorem oddCompactProductDGrade11Part0_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade4 u a w =
      oddCompactProductDGrade11Part0 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade3 oddCompactCrossADGrade4 oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade11Part0 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 11 of the middle determinant product, block 1. -/
theorem oddCompactProductDGrade11Part1_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade2 u a w =
      oddCompactProductDGrade11Part1 u a w := by
  unfold oddCompactCrossADGrade1 oddCompactCrossADGrade2 oddCompactProductDGrade11Part1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 11 of the middle determinant product. -/
theorem oddCompactProductDGrade11_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade1 u a w =
      oddCompactProductDGrade11 u a w := by
  unfold oddCompactProductDGrade11
  linear_combination oddCompactProductDGrade11Part0_eq u a w + oddCompactProductDGrade11Part1_eq u a w

/-- Drift degree 12 of the middle determinant product. -/
def oddCompactProductDGrade12 (u a w : ℝ) : ℝ :=
  ((6458787967489966080000 : ℝ)*u^(12 : ℕ) +
    (-13962029510296962662400 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (10960210386938396344320 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (4603299586501961318400 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-4262150399757225984000 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (-3805345579576561827840 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (927620359272976465920 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ) +
    (-1587543511319248896000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (1055198175276893626368 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-112555745333033161728 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ) +
    (1452993520079052472320 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-148043919779539200000 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (6039606199181546112 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ) +
    (85790036090762035200 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-381263037071781150720 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (22715888786095318016 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-33117435340394496 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ) +
    (-207279551130131496960 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (23107745145253625856 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-2852934536919026688 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-2481275292668940 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ) +
    (-321051810594816000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (45411063643485241344 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (2181980492918415360 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (52713742491400848 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (4043668693137 : ℝ)*u^(12 : ℕ)*a^(9 : ℕ) +
    (39111952368308060160 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-9844195005749329920 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (216199919717715456 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (455574776586372 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (3485174679009755136 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-388975205990344704 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-4337654402015328 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-4577114188802949120 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (685248621632028672 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (1419845654630400 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (119952259856990208 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-14478545891598336 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (97475005419356160 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (38805429686501376 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-30735195099365376 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-233486501806080 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (1521681143169024 : ℝ)

/-- Drift degree 12 of the middle determinant product. -/
theorem oddCompactProductDGrade12_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade0 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade3 u a w =
      oddCompactProductDGrade12 u a w := by
  unfold oddCompactCrossADGrade0 oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade2 oddCompactCrossADGrade3 oddCompactCrossADGrade4 oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade12 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 13 of the middle determinant product. -/
def oddCompactProductDGrade13 (u a w : ℝ) : ℝ :=
  ((116003339452204646400 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-54308373012645396480 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (215237797040480256000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-33341865114419140608 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-114233594589971988480 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (26359426738660987392 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-56968951049256960000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (12025582172488820736 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-5838764004179953408 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (47888703468623462400 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1712146693602017280 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (374951662740254592 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (862826740973568000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-12914080653352402944 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (286806226777884672 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-1433441606815668 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-4775230736884039680 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (537923995619082240 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-69802916134683744 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-50188228909341 : ℝ)*u^(13 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (322212266918019072 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (113614785728825856 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (348014137703532 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (1081241023398543360 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-239560984703459328 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (2831722580354496 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (119463321328680960 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-6979209869681664 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-54182997582151680 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (5095334459473920 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (2973481304850432 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (306256250142720 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ)) / (570630428688384 : ℝ)

/-- Drift degree 13 of the middle determinant product. -/
theorem oddCompactProductDGrade13_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade1 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade4 u a w =
      oddCompactProductDGrade13 u a w := by
  unfold oddCompactCrossADGrade1 oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade3 oddCompactCrossADGrade4 oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade13 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 14 of the middle determinant product. -/
def oddCompactProductDGrade14 (u a w : ℝ) : ℝ :=
  ((-796575870103265280000 : ℝ)*u^(14 : ℕ) +
    (1407300328176648192000 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ) +
    (-908331450250361978880 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-303368559592808448000 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (287040089339215048704 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ) +
    (187197683176067235840 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-47911134169000137728 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ) +
    (112886051109470208000 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-41247920792907220992 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (3809086161536920064 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ) +
    (-74760459064005427200 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (7268212418378369024 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-86438521354805408 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ) +
    (-5929037139522355200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (11658990199513497600 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1245612863994682624 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-1211487936906392 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ) +
    (7803005786345963520 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (471010760496668672 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (57337992147956672 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (12193537279145 : ℝ)*u^(14 : ℕ)*a^(8 : ℕ) +
    (16735332099686400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-2418860584809529344 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-5080151295790592 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (66237271728164 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-586948742668615680 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (123201132387041280 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-4404316656877440 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-66327232958300160 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (9033747682290176 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (93801022771691520 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-16424814310359040 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (5910474818715648 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-1286594793308160 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ)) / (1141260857376768 : ℝ)

/-- Drift degree 14 of the middle determinant product. -/
theorem oddCompactProductDGrade14_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade2 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade5 u a w =
      oddCompactProductDGrade14 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade2 oddCompactCrossADGrade4 oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade14 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 15 of the middle determinant product. -/
def oddCompactProductDGrade15 (u a w : ℝ) : ℝ :=
  ((-4699992993439334400 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-4018503024660971520 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-10524113853559603200 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (5771222905079179776 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (2966431491035320320 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-1892322136822843904 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (3536441477288755200 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (422497823480051712 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (199833820598388160 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-2245293188408770560 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-43725319530713088 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-4029748207846160 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-44976205017907200 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (371463495170383872 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-22968236838909632 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-28167098089833 : ℝ)*u^(15 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (57190146850160640 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (23001684838770688 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (651009942045032 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-32931914672553984 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-632524520749696 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-13330095880273920 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (1779209128093696 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-1639580427878400 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (597752319836160 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ)) / (427972821516288 : ℝ)

/-- Drift degree 15 of the middle determinant product. -/
theorem oddCompactProductDGrade15_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade3 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade15 u a w =
      oddCompactProductDGrade15 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade3 oddCompactCrossADGrade5 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade15 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 16 of the middle determinant product. -/
def oddCompactProductDGrade16 (u a w : ℝ) : ℝ :=
  ((56969035505948160000 : ℝ)*u^(16 : ℕ) +
    (-81605620969245158400 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ) +
    (42378998266424563200 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ) +
    (10705859035467494400 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-10369787535383842176 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ) +
    (-4979552110931554560 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (1206912232505065376 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ) +
    (-4260488987632896000 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (1145391355925355456 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-52059329289540936 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ) +
    (1852565524964444160 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-256436763862399792 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (101593808342054 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ) +
    (213480159151104000 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-59389982851647360 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (22451278323074564 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (8666794379256 : ℝ)*u^(16 : ℕ)*a^(7 : ℕ) +
    (-207310613127229440 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-16370099480399872 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-196167778559889 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-427217869209600 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (44824204939026432 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-868460244400488 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-1467237494292480 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (753398074394368 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-489238146877440 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-559295811256320 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ)) / (641959232274432 : ℝ)

/-- Drift degree 16 of the middle determinant product. -/
theorem oddCompactProductDGrade16_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade4 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade7 u a w =
      oddCompactProductDGrade16 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade4 oddCompactCrossADGrade6 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade16 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 17 of the middle determinant product. -/
def oddCompactProductDGrade17 (u a w : ℝ) : ℝ :=
  ((-549070265894630400 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2148787499429617920 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (813791581363584000 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-1179870944679918528 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (121489184547924480 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (201870192530915824 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-457777874941747200 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-88629476624183616 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-8771818865076980 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (208594252585497600 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-7881956991151872 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (11255070944045 : ℝ)*u^(17 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (4592592094003200 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-7508226728848896 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (1004019283589436 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-2643524907171840 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-1436248277516672 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (1722988843994112 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (51608338513920 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (962938848411648 : ℝ)

/-- Drift degree 17 of the middle determinant product. -/
theorem oddCompactProductDGrade17_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade5 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade8 u a w =
      oddCompactProductDGrade17 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade5 oddCompactCrossADGrade7 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade17 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 18 of the middle determinant product. -/
def oddCompactProductDGrade18 (u a w : ℝ) : ℝ :=
  ((-12606818273078400000 : ℝ)*u^(18 : ℕ) +
    (14399824211846784000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ) +
    (-5805928871491622400 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ) +
    (-1071102827515104000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (1025310095655325920 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ) +
    (434966891519139840 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-72780275694973536 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ) +
    (440061387701760000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-129577080132424944 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (1198494416041182 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ) +
    (-93723589817095680 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (19820792364965720 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (9984533955876 : ℝ)*u^(18 : ℕ)*a^(6 : ℕ) +
    (-20355844552243200 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-8905872514482240 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-503294913029579 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (15566015638702080 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (140609966067520 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (25737191424000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-1014113059800576 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (236328511610880 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ)) / (1444408272617472 : ℝ)

/-- Drift degree 18 of the middle determinant product. -/
theorem oddCompactProductDGrade18_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade6 u a w +
      oddCompactReflectedScalar8Grade0 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade9 u a w =
      oddCompactProductDGrade18 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactCrossADGrade6 oddCompactCrossADGrade8 oddCompactCrossADGrade9 oddCompactProductDGrade18 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 19 of the middle determinant product. -/
def oddCompactProductDGrade19 (u a w : ℝ) : ℝ :=
  ((344758566717331200 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-426547303157675520 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (8234165291673600 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (127359559953340080 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-45737016552213120 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-10277253964128440 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (39240181645056000 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (3352068544670880 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (115147738400547 : ℝ)*u^(19 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-9978991591703040 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (625982449966720 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-276674807808000 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-424549334133888 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (196164990443520 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (2166612408926208 : ℝ)

/-- Drift degree 19 of the middle determinant product. -/
theorem oddCompactProductDGrade19_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade1 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade7 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade10 u a w =
      oddCompactProductDGrade19 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactCrossADGrade7 oddCompactCrossADGrade9 oddCompactProductDGrade19 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 20 of the middle determinant product. -/
def oddCompactProductDGrade20 (u a w : ℝ) : ℝ :=
  ((4282840220984640000 : ℝ)*u^(20 : ℕ) +
    (-3792452980642473600 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ) +
    (1124079179024347200 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ) +
    (153959596661433600 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-129147816283435488 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ) +
    (-72912861530936640 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (4502985712696248 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ) +
    (-58117479787584000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (19721861161142184 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-6013961923719 : ℝ)*u^(20 : ℕ)*a^(5 : ℕ) +
    (1197384659239680 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1111372941276926 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (2314581671808000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (801521276427600 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1014647038041600 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-1389975552000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (6499837226778624 : ℝ)

/-- Drift degree 20 of the middle determinant product. -/
theorem oddCompactProductDGrade20_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade2 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade8 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade11 u a w =
      oddCompactProductDGrade20 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactCrossADGrade8 oddCompactProductDGrade20 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 21 of the middle determinant product. -/
def oddCompactProductDGrade21 (u a w : ℝ) : ℝ :=
  ((-22678887169008000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (15364451582271840 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-2784644871523200 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-2343947440131932 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (1135261059580320 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (63286948449817 : ℝ)*u^(21 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-668341171008000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (23141617977460 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (48581191538880 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (2490372864000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (1624959306694656 : ℝ)

/-- Drift degree 21 of the middle determinant product. -/
theorem oddCompactProductDGrade21_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade3 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade9 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade12 u a w =
      oddCompactProductDGrade21 u a w := by
  unfold oddCompactCrossADGrade11 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactCrossADGrade9 oddCompactProductDGrade21 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 22 of the middle determinant product. -/
def oddCompactProductDGrade22 (u a w : ℝ) : ℝ :=
  ((-182868697887120000 : ℝ)*u^(22 : ℕ) +
    (120048017631955200 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ) +
    (-24030743250890160 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ) +
    (-2861578574971200 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (1515682823014772 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ) +
    (1632836358928320 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-16081398170601 : ℝ)*u^(22 : ℕ)*a^(4 : ℕ) +
    (711130855680000 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-206658323845934 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (61167492459840 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-19824297696000 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (4874877920083968 : ℝ)

/-- Drift degree 22 of the middle determinant product. -/
theorem oddCompactProductDGrade22_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade4 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade10 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade13 u a w =
      oddCompactProductDGrade22 u a w := by
  unfold oddCompactCrossADGrade10 oddCompactCrossADGrade12 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade22 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 23 of the middle determinant product. -/
def oddCompactProductDGrade23 (u a w : ℝ) : ℝ :=
  ((2447254796061600 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-886936500870720 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (246606298848000 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (51241366195331 : ℝ)*u^(23 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-26605497510120 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (15422517936000 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (3656158440062976 : ℝ)

/-- Drift degree 23 of the middle determinant product. -/
theorem oddCompactProductDGrade23_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade5 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade11 u a w +
      oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade15 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade14 u a w =
      oddCompactProductDGrade23 u a w := by
  unfold oddCompactCrossADGrade11 oddCompactCrossADGrade13 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade23 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 24 of the middle determinant product. -/
def oddCompactProductDGrade24 (u a w : ℝ) : ℝ :=
  ((5701741487820000 : ℝ)*u^(24 : ℕ) +
    (-2581345980927000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ) +
    (301756293597840 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ) +
    (44279207091000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-7261033777863 : ℝ)*u^(24 : ℕ)*a^(3 : ℕ) +
    (-17645443912070 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3371546430000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (3656158440062976 : ℝ)

/-- Drift degree 24 of the middle determinant product. -/
theorem oddCompactProductDGrade24_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade14 u a w +
      oddCompactReflectedScalar8Grade6 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade12 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade15 u a w =
      oddCompactProductDGrade24 u a w := by
  unfold oddCompactCrossADGrade12 oddCompactCrossADGrade14 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade24 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 25 of the middle determinant product. -/
def oddCompactProductDGrade25 (u a w : ℝ) : ℝ :=
  ((-16034266300500 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2369446851065 : ℝ)*u^(25 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-849502930500 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (914039610015744 : ℝ)

/-- Drift degree 25 of the middle determinant product. -/
theorem oddCompactProductDGrade25_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade7 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade13 u a w +
      oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade15 u a w =
      oddCompactProductDGrade25 u a w := by
  unfold oddCompactCrossADGrade13 oddCompactCrossADGrade15 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade25 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 26 of the middle determinant product. -/
def oddCompactProductDGrade26 (u a w : ℝ) : ℝ :=
  ((-13621588155000 : ℝ)*u^(26 : ℕ) +
    (3735521349000 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ) +
    (-184289382775 : ℝ)*u^(26 : ℕ)*a^(2 : ℕ) +
    (-46808805750 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (304679870005248 : ℝ)

/-- Drift degree 26 of the middle determinant product. -/
theorem oddCompactProductDGrade26_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade8 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade16 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade14 u a w =
      oddCompactProductDGrade26 u a w := by
  unfold oddCompactCrossADGrade14 oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade26 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade8
  ring

/-- Drift degree 27 of the middle determinant product. -/
def oddCompactProductDGrade27 (u a w : ℝ) : ℝ :=
  ((15043937125 : ℝ)*u^(27 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (76169967501312 : ℝ)

/-- Drift degree 27 of the middle determinant product. -/
theorem oddCompactProductDGrade27_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade9 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade15 u a w =
      oddCompactProductDGrade27 u a w := by
  unfold oddCompactCrossADGrade15 oddCompactCrossADGrade18 oddCompactProductDGrade27 oddCompactReflectedScalar8Grade12 oddCompactReflectedScalar8Grade9
  ring

/-- Drift degree 28 of the middle determinant product. -/
def oddCompactProductDGrade28 (u a _w : ℝ) : ℝ :=
  ((120431587500 : ℝ)*u^(28 : ℕ) +
    (-14754163375 : ℝ)*u^(28 : ℕ)*a^(1 : ℕ)) / (152339935002624 : ℝ)

/-- Drift degree 28 of the middle determinant product. -/
theorem oddCompactProductDGrade28_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade10 u a w*oddCompactCrossADGrade18 u a w +
      oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade16 u a w =
      oddCompactProductDGrade28 u a w := by
  unfold oddCompactCrossADGrade16 oddCompactCrossADGrade18 oddCompactProductDGrade28 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- Drift degree 30 of the middle determinant product. -/
def oddCompactProductDGrade30 (u _a _w : ℝ) : ℝ :=
  ((-82534375 : ℝ)*u^(30 : ℕ)) / (12694994583552 : ℝ)

/-- Drift degree 30 of the middle determinant product. -/
theorem oddCompactProductDGrade30_eq (u a w : ℝ) :
    oddCompactReflectedScalar8Grade12 u a w*oddCompactCrossADGrade18 u a w =
      oddCompactProductDGrade30 u a w := by
  unfold oddCompactCrossADGrade18 oddCompactProductDGrade30 oddCompactReflectedScalar8Grade12
  ring

/-- The middle determinant product, stored as its drift grades. -/
def oddCompactProductD (u a w : ℝ) : ℝ :=
  oddCompactProductDGrade0 u a w +
    oddCompactProductDGrade1 u a w +
    oddCompactProductDGrade2 u a w +
    oddCompactProductDGrade3 u a w +
    oddCompactProductDGrade4 u a w +
    oddCompactProductDGrade5 u a w +
    oddCompactProductDGrade6 u a w +
    oddCompactProductDGrade7 u a w +
    oddCompactProductDGrade8 u a w +
    oddCompactProductDGrade9 u a w +
    oddCompactProductDGrade10 u a w +
    oddCompactProductDGrade11 u a w +
    oddCompactProductDGrade12 u a w +
    oddCompactProductDGrade13 u a w +
    oddCompactProductDGrade14 u a w +
    oddCompactProductDGrade15 u a w +
    oddCompactProductDGrade16 u a w +
    oddCompactProductDGrade17 u a w +
    oddCompactProductDGrade18 u a w +
    oddCompactProductDGrade19 u a w +
    oddCompactProductDGrade20 u a w +
    oddCompactProductDGrade21 u a w +
    oddCompactProductDGrade22 u a w +
    oddCompactProductDGrade23 u a w +
    oddCompactProductDGrade24 u a w +
    oddCompactProductDGrade25 u a w +
    oddCompactProductDGrade26 u a w +
    oddCompactProductDGrade27 u a w +
    oddCompactProductDGrade28 u a w +
    oddCompactProductDGrade30 u a w

end
end HTGeometry
