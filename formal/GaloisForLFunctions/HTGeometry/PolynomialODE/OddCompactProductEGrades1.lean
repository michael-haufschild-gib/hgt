import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductEGrades0
import Mathlib.Tactic.LinearCombination

/-!
# The leading determinant product, drift-graded (1)

The grade `d` part of a product is the sum of the products of the factors'
grades over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 7 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade7Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade3 u a w =
      oddCompactProductEGrade7Part0 u a w := by
  unfold oddCompactProductEGrade7Part0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade6
  ring

/-- Drift degree 7 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade7Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade7Part1 u a w := by
  unfold oddCompactProductEGrade7Part1 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade7 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart4Grade7
  ring

/-- Drift degree 7 of the leading determinant product. -/
theorem oddCompactProductEGrade7_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade7 u a w := by
  unfold oddCompactProductEGrade7
  linear_combination oddCompactProductEGrade7Part0_eq u a w + oddCompactProductEGrade7Part1_eq u a w

/-- Drift degree 8 of the leading determinant product, block 0. -/
def oddCompactProductEGrade8Part0 (u a w : ℝ) : ℝ :=
  ((21297508675745218560000 : ℝ)*u^(8 : ℕ) +
    (-68402435627927155507200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (77550083309397863301120 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (41296234649722395033600 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-42705309978752559022080 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-55808654693977282314240 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (13428982498149279227904 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-14566860428542790860800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (25656468966699402166272 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-2608931891865735069696 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (25358533539240856780800 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-6175156059670210240512 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (320974752415255314432 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (1294593179924614348800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-8718098212495706554368 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (912950540897766088704 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-21990766313387905536 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-7659038555988201308160 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (1530901881143618174976 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-88015313343872122880 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (332503816921609632 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-23623644769733836800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (1670653026582694723584 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-177289193641342468096 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (7699737787643177856 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (11646497011642272 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (1502601801229727170560 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-137577021129361981440 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (6220517768472975360 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-144267372227918880 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-123679487985948 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (49861671203635200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-350764779368186118144 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (35806314435877306368 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-653121142368390144 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-5306233651894272 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (1038199823265 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-133815920680281047040 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-39453269709296762880 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (644529886596243456 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-2059689101296128 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (47679761889192 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (67833687353201786880 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-6350398451807551488 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-8021453122142208 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (417404872080384 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (3698344923129446400 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (8779268536324325376 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-201434366993498112 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (1315419381086208 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-4837755446183854080 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (507546147999449088 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-1553188506402816 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-30118780285747200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-406772626753585152 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (9004476761899008 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (58101211626209280 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-7444421985435648 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (23192823398400 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(16 : ℕ) +
    (1958748289499136 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-28449863368704 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (300578991243264 : ℝ)

/-- Drift degree 8 of the leading determinant product, block 1. -/
def oddCompactProductEGrade8Part1 (u a w : ℝ) : ℝ :=
  ((89290174208901120000 : ℝ)*u^(8 : ℕ) +
    (-373619343971775283200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (475741238425141248000 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (310684421618049024000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-270909007382468689920 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-448490460210149376000 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (73361861690778547200 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-48296373390861926400 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (236980629978398724096 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-9188074814812646400 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (-118404038906675527680 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-58708103948376800256 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (773193378128511744 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (1511791309357056000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-6135561225572843520 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-446819156212233728 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-87899513367016224 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-130813151238574571520 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (55150270215543570432 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (2693005381009935744 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (5635442578385520 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-49768923399821328384 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-8704298715876018176 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (141294069898165632 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-255483164700 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (101713467174121635840 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-2054395002823213056 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-1159641827184549888 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-27453254056447680 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-2788559887500 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-6202415017881501696 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (4172327928853954560 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-14231911602060288 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (112396142290944 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (25931131875 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-12969431933669867520 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-5444366960703307776 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (217666533530222592 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (4568045585157120 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (6207247981848 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (5141202772263174144 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-832531022304509952 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (1863435482947584 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-881992982400 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (440150503351910400 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (1081770015033655296 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-29419479815946240 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-176323646392320 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-440063977813180416 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (71810444628590592 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-569172261076992 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-2222162391859200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-38256980552318976 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (1313707014488064 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (9706370538405888 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-834282952065024 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (100526393917440 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-22574348107776 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (37572373905408 : ℝ)

/-- Drift degree 8 of the leading determinant product. -/
def oddCompactProductEGrade8 (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade8Part0 u a w +
    oddCompactProductEGrade8Part1 u a w

/-- Drift degree 8 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade8Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade2 u a w =
      oddCompactProductEGrade8Part0 u a w := by
  unfold oddCompactProductEGrade8Part0 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade6 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade8 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade8
  ring

/-- Drift degree 8 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade8Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade0 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade1 u a w =
      oddCompactProductEGrade8Part1 u a w := by
  unfold oddCompactProductEGrade8Part1 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade7 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart4Grade7
  ring

/-- Drift degree 8 of the leading determinant product. -/
theorem oddCompactProductEGrade8_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade8 u a w := by
  unfold oddCompactProductEGrade8
  linear_combination oddCompactProductEGrade8Part0_eq u a w + oddCompactProductEGrade8Part1_eq u a w

/-- Drift degree 9 of the leading determinant product, block 0. -/
def oddCompactProductEGrade9Part0 (u a w : ℝ) : ℝ :=
  ((598894640414672486400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-824929682434960343040 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (1086859432037449728000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (290984144709700214784 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-697808692362440540160 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (25965691376451643392 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-374115722058163814400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (159802601945968852992 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-34791024308500579072 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (610665841240084316160 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-58230860320158007296 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (8570471613565162816 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (16990798954364928000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-64459614488354684928 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (9684144611559276544 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-732481787057469600 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-258799844274607226880 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (23195925497624887296 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-626994974009930496 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (2691508871053512 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-113746937433292800 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (6294288418608513024 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-4583554691388948480 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (159928998838181184 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (342384274072572 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (47437359176661073920 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (2287088816662511616 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-313289897336033280 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-1397183704957344 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (4784358023661 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-7276104537348243456 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (1322759940413325312 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-15047579055295488 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-16499842409232 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-2664601538789376000 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-1777311314856247296 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (58702434527035392 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (44808502851840 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (1322674872366661632 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-161747071841009664 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (704037081759744 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (38200509852549120 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (158616497210523648 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-3608757728182272 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-47260679710703616 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (5049405492166656 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-65084860661760 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (-2212681419325440 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (231005352886272 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ)) / (56358560858112 : ℝ)

/-- Drift degree 9 of the leading determinant product, block 1. -/
def oddCompactProductEGrade9Part1 (u a w : ℝ) : ℝ :=
  ((-36687261498723532800 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (107633797302766141440 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (313159729587476889600 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-95549777647229583360 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-462484972775206748160 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (27475706693578137600 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-35844703068251750400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (240514604255876972544 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-430759268608082688 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (50452353035356078080 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-39977808105782525952 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (210221883287198528 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-53126477859525820416 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-973493018024236032 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-146333891124255504 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-5695576675744481280 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (17750158554908590080 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (297124304051791872 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (5595472915648428 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (56411262840471552 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-1918444384985088 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (20505058356468192 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-19678188632316 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (2787124814995783680 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-1901060432373743616 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-43019045282399232 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-1763880196606656 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-554046622377 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-857685221487673344 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (88602518545293312 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-610970047836672 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (22066380237768 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-188769600169574400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-151492423964295168 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (144045284818944 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (77809965243648 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (241085989817155584 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-19971579706343424 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (288031689480192 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (462923319214080 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (22140923922087936 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-430685353574400 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-7806094034337792 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (407034829209600 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-3044058071040 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (162934265217024 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ)) / (56358560858112 : ℝ)

/-- Drift degree 9 of the leading determinant product. -/
def oddCompactProductEGrade9 (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade9Part0 u a w +
    oddCompactProductEGrade9Part1 u a w

/-- Drift degree 9 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade9Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade4 u a w =
      oddCompactProductEGrade9Part0 u a w := by
  unfold oddCompactProductEGrade9Part0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8
  ring

/-- Drift degree 9 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade9Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade9Part1 u a w := by
  unfold oddCompactProductEGrade9Part1 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart4Grade9
  ring

/-- Drift degree 9 of the leading determinant product. -/
theorem oddCompactProductEGrade9_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade9 u a w := by
  unfold oddCompactProductEGrade9
  linear_combination oddCompactProductEGrade9Part0_eq u a w + oddCompactProductEGrade9Part1_eq u a w

/-- Drift degree 10 of the leading determinant product, block 0. -/
def oddCompactProductEGrade10Part0 (u a w : ℝ) : ℝ :=
  ((-14114189367178887168000 : ℝ)*u^(10 : ℕ) +
    (37213340167587741696000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-35301759926435258204160 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-16261103807833315737600 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (16530263069791271362560 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (17581325263600228761600 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-4380773730267770265600 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (5843363500443893760000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-6833781021220201046016 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (691059581065219748864 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-6473563057017815040000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (1388187916760862167040 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-61506459765896978688 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-523638420262826803200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (1907899654311779696640 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-174850923573642221568 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (2036092523845520832 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (1634949769434932183040 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-337839667106671312896 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (19696356739747187712 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (19125888759352032 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (8596643540631552000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-199406195609759907840 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (16183212816971612160 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-984537497567099808 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-799362940407240 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-356489967938568192000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (56274484145970216960 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-832091496157782528 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-6931949640494256 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (2665034488413 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (-13424296093286400 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (6603738006310354944 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-3165060518434627584 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (66131136743594496 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (354201857678976 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (36072399627784028160 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (846755828922580992 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-177639326493560832 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (1333121066443392 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-5692044287888326656 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (622193763549904896 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-1618704978567168 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-954128461033635840 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-904246710575824896 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (16397842405785600 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (550391458377498624 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-38514665351282688 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (5231431227801600 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (29229104360325120 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-4011947741675520 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-1159641169920 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(16 : ℕ)) / (676302730297344 : ℝ)

/-- Drift degree 10 of the leading determinant product, block 1. -/
def oddCompactProductEGrade10Part1 (u a w : ℝ) : ℝ :=
  ((-16129833758760960000 : ℝ)*u^(10 : ℕ) +
    (63043132500169113600 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-69052866949572710400 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-56158946891008819200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (31736845687566965760 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (67466845264869457920 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-6218384236963107840 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (8858607111954432000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-23405500556413166592 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (541814229635218560 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-5465226068685619200 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-612261051636536832 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-55455116959779552 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-273097714434048000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (37726322565857845248 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (2447571915388479872 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (5737919552802000 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (-10174350512312156160 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-10897400671357593600 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-57985229505778560 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-142020602887500 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (6137315087796928512 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-338442311544963072 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-52773375416653632 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-3324232063500 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-8711616847014789120 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (2669354129559453696 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (145639589125353984 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (715346849440848 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (75124081875 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (-1170200455420575744 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-312137919879045120 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (11368617787743360 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (5197181268192 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (1385319217150033920 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (296383778670379008 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-33629828519055360 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-81329549467200 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-417964083158974464 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (73434664555216896 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-809581408112640 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-39423115914117120 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-85924507056340992 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (2463484344582144 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (35618842466058240 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-4016577996914688 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (55554059796480 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (2247789442498560 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-580918620192768 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ)) / (84537841287168 : ℝ)

/-- Drift degree 10 of the leading determinant product. -/
def oddCompactProductEGrade10 (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade10Part0 u a w +
    oddCompactProductEGrade10Part1 u a w

/-- Drift degree 10 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade10Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade7 u a w =
      oddCompactProductEGrade10Part0 u a w := by
  unfold oddCompactProductEGrade10Part0 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade8 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart5Grade10
  ring

/-- Drift degree 10 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade10Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade0 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade1 u a w =
      oddCompactProductEGrade10Part1 u a w := by
  unfold oddCompactProductEGrade10Part1 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart4Grade9
  ring

/-- Drift degree 10 of the leading determinant product. -/
theorem oddCompactProductEGrade10_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade10 u a w := by
  unfold oddCompactProductEGrade10
  linear_combination oddCompactProductEGrade10Part0_eq u a w + oddCompactProductEGrade10Part1_eq u a w

/-- Drift degree 11 of the leading determinant product, block 0. -/
def oddCompactProductEGrade11Part0 (u a w : ℝ) : ℝ :=
  ((-116102394335279923200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (96134912251304509440 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-211924823503325184000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (3684388683550063104 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (133973420560593039360 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-20864818647755285760 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (70693454388333772800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-38633252132254685184 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (7140793089557509376 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-60885827575471964160 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (5392415675725989888 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-960931565792219904 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-2781172175575449600 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (15257171327561293824 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-112473637146517248 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (29078460002320962 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (17032935893400944640 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-4188627331062091776 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (135025841392481184 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (296530419179871 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (15312087731404800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (1268161421348634624 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-71168863184200704 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-8646065167552008 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (2960559301572 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-3762645905005608960 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (562312840375222272 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (6616280673106176 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (18780586439844 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-55844076993380352 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-30971818413791232 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (587621748035520 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (209169115816919040 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (40043715644227584 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-1594654486917120 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-49773919987040256 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (4032566770851840 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-2092078737653760 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (-4337579880873984 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (1419325445505024 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (1703222968320 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ)) / (63403380965376 : ℝ)

/-- Drift degree 11 of the leading determinant product, block 1. -/
def oddCompactProductEGrade11Part1 (u a w : ℝ) : ℝ :=
  ((274330143790617600 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-650782289545021440 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-277198850625177600 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (430789266480807360 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (671147298234570240 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-97956738049304160 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (29870062516224000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-280724336512692480 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (10031387480047944 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-95813328518369280 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (31504704046752000 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-1269546310618992 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (64078964924433408 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-1197120151927008 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (85298339584632 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-2831081797140480 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-3918840066034176 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (122069020658864 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (719435107063 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-1545719204216832 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-157671654960128 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-9929195419272 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-35143269620 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (213979700920320 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (272850148184064 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (8966678279296 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-112175634052 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-617314441494528 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (30265771638784 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-688429074368 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-42038803562496 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (637716105216 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (891582087168 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ)) / (2641807540224 : ℝ)

/-- Drift degree 11 of the leading determinant product. -/
def oddCompactProductEGrade11 (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade11Part0 u a w +
    oddCompactProductEGrade11Part1 u a w

/-- Drift degree 11 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade11Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade11 u a w =
      oddCompactProductEGrade11Part0 u a w := by
  unfold oddCompactProductEGrade11Part0 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11
  ring

/-- Drift degree 11 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade11Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade11Part1 u a w := by
  unfold oddCompactProductEGrade11Part1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade2 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2
  ring

/-- Drift degree 11 of the leading determinant product. -/
theorem oddCompactProductEGrade11_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade11 u a w := by
  unfold oddCompactProductEGrade11
  linear_combination oddCompactProductEGrade11Part0_eq u a w + oddCompactProductEGrade11Part1_eq u a w

/-- Drift degree 12 of the leading determinant product, block 0. -/
def oddCompactProductEGrade12Part0 (u a w : ℝ) : ℝ :=
  ((3462724000464003072000 : ℝ)*u^(12 : ℕ) +
    (-7515575781715117670400 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (5934547220930291957760 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (2304162028747579392000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-2310067302234219786240 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (-1995347162946731950080 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (494799247779895836672 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ) +
    (-826833776830296883200 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (634393791232033130496 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-58472412129371286016 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ) +
    (661982639084944588800 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-108401148685763885568 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (3116642483303594496 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ) +
    (74148948457449062400 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-189671758682374176768 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (15246962874678075648 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-22810449035605080 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ) +
    (-94521708325377146880 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (18908570004037853184 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-1546964054246518464 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-1246157115532581 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ) +
    (-1068130487815372800 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (17909441701697617920 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (616193353806400512 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (21859055128896492 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (7768427172657 : ℝ)*u^(12 : ℕ)*a^(9 : ℕ) +
    (21601551853273743360 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-5907504809262563328 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (93159206683981248 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (550262205237441 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (1198597865472000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (2640376135029620736 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-133848971846667264 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-1682338308472992 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-2731216179057131520 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (332469549196738560 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (3858936749872896 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (34826722567520256 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-11680473753391104 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (60360735640780800 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (21260653759365120 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-15409565386407936 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-136710822297600 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (760840571584512 : ℝ)

/-- Drift degree 12 of the leading determinant product, block 1. -/
def oddCompactProductEGrade12Part1 (u a w : ℝ) : ℝ :=
  ((382669287793920 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1461984789427200 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (23164623647677440 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (1985883824028336 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-12412636198217088 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-485998762545216 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (475296855091200 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (143411713903104 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (6180208689388 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (1806772629362688 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (120570598982496 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (2949519779612 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-280848357457920 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-217098586857216 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-1214680899968 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-55184390457 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (184394702094336 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-8720824653056 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-219234668456 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (38692275011584 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-765304381632 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-14265313394688 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (865226919936 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (297194029056 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ)) / (990677827584 : ℝ)

/-- Drift degree 12 of the leading determinant product. -/
def oddCompactProductEGrade12 (u a w : ℝ) : ℝ :=
  oddCompactProductEGrade12Part0 u a w +
    oddCompactProductEGrade12Part1 u a w

/-- Drift degree 12 of the leading determinant product, block 0. -/
theorem oddCompactProductEGrade12Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade12Part0 u a w := by
  unfold oddCompactProductEGrade12Part0 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12
  ring

/-- Drift degree 12 of the leading determinant product, block 1. -/
theorem oddCompactProductEGrade12Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade1 u a w =
      oddCompactProductEGrade12Part1 u a w := by
  unfold oddCompactProductEGrade12Part1 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade3 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart2Grade3
  ring

/-- Drift degree 12 of the leading determinant product. -/
theorem oddCompactProductEGrade12_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade0 u a w =
      oddCompactProductEGrade12 u a w := by
  unfold oddCompactProductEGrade12
  linear_combination oddCompactProductEGrade12Part0_eq u a w + oddCompactProductEGrade12Part1_eq u a w

/-- Drift degree 13 of the leading determinant product. -/
def oddCompactProductEGrade13 (u a w : ℝ) : ℝ :=
  ((62777579047929446400 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (3983809741749043200 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (120959107647927091200 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-46063443317761652736 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-65485603685297848320 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (21827638814834292224 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-46729044174687436800 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (12560525929186504704 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-4008822861688792832 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (28914636502003875840 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-307572611427680256 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (236425121960418368 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (1678426555967078400 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-8954015538062622720 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (284004970684466688 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-881279724356212 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-2808361270184509440 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (692274248437022720 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-51453762860399424 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-9716621009967 : ℝ)*u^(13 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-7291470348288000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-5716127267684352 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (65312238586697728 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (500095205115688 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (817179855012495360 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-191735602089099264 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (1876497594957568 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (103349969984421888 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-3452791302154240 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-44385853526507520 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (3508114686083072 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (1883501505282048 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (250109535191040 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ)) / (380420285792256 : ℝ)

/-- Drift degree 13 of the leading determinant product. -/
theorem oddCompactProductEGrade13_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade2 u a w =
      oddCompactProductEGrade13 u a w := by
  unfold oddCompactProductEGrade13 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13
  ring

/-- Drift degree 14 of the leading determinant product. -/
def oddCompactProductEGrade14 (u a w : ℝ) : ℝ :=
  ((-859565159346216960000 : ℝ)*u^(14 : ℕ) +
    (1525534149605076172800 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ) +
    (-987502658115137126400 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-311690797702513459200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (309881735999567996928 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ) +
    (215589402883823616000 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-50736581604900858880 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ) +
    (109309606067758694400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-58498881930072167424 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (3983313989186600704 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ) +
    (-68882211058141347840 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (10498816857398371328 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-94883754506600256 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ) +
    (-9793425035309875200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (13129274604504023040 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1423226111619624320 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-1086020094270596 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ) +
    (6775259397960499200 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (87269708865220608 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (55942073549179264 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (20133598033889 : ℝ)*u^(14 : ℕ)*a^(8 : ℕ) +
    (119636119624089600 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-2441359756864880640 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-5201795669195776 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (349472332065770 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-559217589729361920 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (179001993270231040 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-3852729757466592 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-91321742131200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-109686346171416576 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (9232814800051712 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (110431580706570240 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-18151294180114432 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (7323885303103488 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-1607505102766080 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ)) / (1141260857376768 : ℝ)

/-- Drift degree 14 of the leading determinant product. -/
theorem oddCompactProductEGrade14_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade0 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade3 u a w =
      oddCompactProductEGrade14 u a w := by
  unfold oddCompactProductEGrade14 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade0 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade0 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14
  ring

/-- Drift degree 15 of the leading determinant product. -/
def oddCompactProductEGrade15 (u a w : ℝ) : ℝ :=
  ((-2313825957594316800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-18155318273572331520 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-15424431418043596800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (15075534076945814016 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (5100191155555983360 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-4074962045396347392 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (8064088949558476800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-22360345464705024 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (391485092621723072 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-4130722077628170240 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (71697115608506368 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-7707565582231680 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-259413231638937600 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (834897276746809344 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-55193671867161600 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-19303741020233 : ℝ)*u^(15 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (52537706549084160 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (27807298701172736 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (1649687865441136 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (833310896947200 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-62989091463856128 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-1061033359001088 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-27652620185763840 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (4910749698859008 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-4144442941636608 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (1473845322055680 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ)) / (855945643032576 : ℝ)

/-- Drift degree 15 of the leading determinant product. -/
theorem oddCompactProductEGrade15_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade1 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade4 u a w =
      oddCompactProductEGrade15 u a w := by
  unfold oddCompactProductEGrade15 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade1 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart0Grade1 oddCompactScalarHeadPart1Grade1 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14
  ring

/-- Drift degree 16 of the leading determinant product. -/
def oddCompactProductEGrade16 (u a w : ℝ) : ℝ :=
  ((123645335726062080000 : ℝ)*u^(16 : ℕ) +
    (-177762212278881638400 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ) +
    (92179268635278090240 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ) +
    (23599083056445619200 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-22292708296804744704 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ) +
    (-13474628260689772800 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (2560003446408621056 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ) +
    (-7569663343721164800 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (3558477075327590976 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-112010161482427064 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ) +
    (3316842872294353920 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-640867976340066608 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (393960981713210 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ) +
    (668968851279052800 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-186027486092808192 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (46015247803837132 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (22409034662873 : ℝ)*u^(16 : ℕ)*a^(7 : ℕ) +
    (-382538766931476480 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-26017272015815040 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-219530465450785 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-6516205387776000 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (96124415304035328 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-1568654950607824 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-7142629165056000 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (1016186341533440 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (3032167219200 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-669251283197952 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-1270871908024320 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ)) / (1283918464548864 : ℝ)

/-- Drift degree 16 of the leading determinant product. -/
theorem oddCompactProductEGrade16_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade0 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade2 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade5 u a w =
      oddCompactProductEGrade16 u a w := by
  unfold oddCompactProductEGrade16 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade2 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart1Grade2 oddCompactScalarHeadPart2Grade2 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 17 of the leading determinant product. -/
def oddCompactProductEGrade17 (u a w : ℝ) : ℝ :=
  ((-2914177956816153600 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (5858301430640943360 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (816276273601075200 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-2654249836930599744 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (156614898203366400 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (408514195897690992 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-956700331672780800 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-63656215305699456 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-17102972896196348 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (384473293688954880 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-28104863289045248 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (63519849478949 : ℝ)*u^(17 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (26216435485900800 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-20488132619301888 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (2401001288558904 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-2803692322897920 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-2448832634259712 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-55337051750400 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (3751013054552064 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-41669664768000 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (1925877696823296 : ℝ)

/-- Drift degree 17 of the leading determinant product. -/
theorem oddCompactProductEGrade17_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade1 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade3 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade6 u a w =
      oddCompactProductEGrade17 u a w := by
  unfold oddCompactProductEGrade17 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade3 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart2Grade3 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 18 of the leading determinant product. -/
def oddCompactProductEGrade18 (u a w : ℝ) : ℝ :=
  ((-27500807018280960000 : ℝ)*u^(18 : ℕ) +
    (31462958269681574400 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ) +
    (-12617858133503786880 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ) +
    (-2710486552283078400 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (2203949139817146336 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ) +
    (1390632046697352960 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-156696541862969488 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ) +
    (703974773537280000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-364334720946051312 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (2765784219592158 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ) +
    (-153527305330679040 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (43293187191301144 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (22940175295123 : ℝ)*u^(18 : ℕ)*a^(6 : ℕ) +
    (-60092340656947200 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-14470596780197376 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-863582619213975 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (30373365044551680 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (160779537657696 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (416290362163200 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-2150352330716928 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (604607483105280 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-89181388800 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ)) / (2888816545234944 : ℝ)

/-- Drift degree 18 of the leading determinant product. -/
theorem oddCompactProductEGrade18_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade2 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade4 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade7 u a w =
      oddCompactProductEGrade18 u a w := by
  unfold oddCompactProductEGrade18 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade4 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart2Grade4 oddCompactScalarHeadPart3Grade4 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 19 of the leading determinant product. -/
def oddCompactProductEGrade19 (u a w : ℝ) : ℝ :=
  ((977113287869356800 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-998215375112697600 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (76494436213708800 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (266449456106653104 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-62477759618415360 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-20424382057775544 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (74026410283929600 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-2194475469399744 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (261045649155603 : ℝ)*u^(19 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-17518180349767680 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1659812637273472 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-1564903452672000 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-742724680369920 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (421824675409920 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (1627560345600 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (4333224817852416 : ℝ)

/-- Drift degree 19 of the leading determinant product. -/
theorem oddCompactProductEGrade19_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade3 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade5 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade8 u a w =
      oddCompactProductEGrade19 u a w := by
  unfold oddCompactProductEGrade19 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade5 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart3Grade5 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 20 of the leading determinant product. -/
def oddCompactProductEGrade20 (u a w : ℝ) : ℝ :=
  ((4692663589785696000 : ℝ)*u^(20 : ℕ) +
    (-4151940345172915200 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ) +
    (1222076483900087040 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ) +
    (240027337648022400 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-139899688501386888 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ) +
    (-117733593618534240 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (5005598428731968 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ) +
    (-40550938192396800 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (23654378103222780 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-8307469365748 : ℝ)*u^(20 : ℕ)*a^(5 : ℕ) +
    (-305769307481280 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1062141444372623 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (3196966761676800 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (682151515153536 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-984871461934080 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-11859731251200 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (6499837226778624 : ℝ)

/-- Drift degree 20 of the leading determinant product. -/
theorem oddCompactProductEGrade20_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade4 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade6 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade9 u a w =
      oddCompactProductEGrade20 u a w := by
  unfold oddCompactProductEGrade20 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade6 oddCompactScalarHeadGrade8 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart3Grade6 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade6 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 21 of the leading determinant product. -/
def oddCompactProductEGrade21 (u a w : ℝ) : ℝ :=
  ((-54876572763062400 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (33228098915907360 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-5727956707872000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-4753374865281572 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (1319369324819520 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (132298940034401 : ℝ)*u^(21 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-1113959981030400 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (141309099153928 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (66733028006400 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (13970125209600 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (3249918613389312 : ℝ)

/-- Drift degree 21 of the leading determinant product. -/
theorem oddCompactProductEGrade21_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade5 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade7 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade10 u a w =
      oddCompactProductEGrade21 u a w := by
  unfold oddCompactProductEGrade21 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade7 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade7 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 22 of the leading determinant product. -/
def oddCompactProductEGrade22 (u a w : ℝ) : ℝ :=
  ((-603571245249168000 : ℝ)*u^(22 : ℕ) +
    (395111712818491200 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ) +
    (-78716977530695280 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ) +
    (-16216219394575200 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (5014495570387650 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ) +
    (6829178065559280 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-55628335195615 : ℝ)*u^(22 : ℕ)*a^(4 : ℕ) +
    (1211536885305600 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-642233197670385 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (195286007221200 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-76347150566400 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (14624633760251904 : ℝ)

/-- Drift degree 22 of the leading determinant product. -/
theorem oddCompactProductEGrade22_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade6 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade8 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade11 u a w =
      oddCompactProductEGrade22 u a w := by
  unfold oddCompactProductEGrade22 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade8 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart4Grade8 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 23 of the leading determinant product. -/
def oddCompactProductEGrade23 (u a w : ℝ) : ℝ :=
  ((5457725383773600 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-1838218421576400 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (412048917302400 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (105313898160599 : ℝ)*u^(23 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-19429980727920 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (22004212204800 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (7312316880125952 : ℝ)

/-- Drift degree 23 of the leading determinant product. -/
theorem oddCompactProductEGrade23_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade7 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade9 u a w +
      (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade13 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade12 u a w =
      oddCompactProductEGrade23 u a w := by
  unfold oddCompactProductEGrade23 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadGrade9 oddCompactScalarHeadPart4Grade9 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 24 of the leading determinant product. -/
def oddCompactProductEGrade24 (u a w : ℝ) : ℝ :=
  ((37777331517660000 : ℝ)*u^(24 : ℕ) +
    (-17045085054841200 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ) +
    (1996894869182400 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ) +
    (504098329203000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-49183643367887 : ℝ)*u^(24 : ℕ)*a^(3 : ℕ) +
    (-122754021131610 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-7262136453600 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (21936950640377856 : ℝ)

/-- Drift degree 24 of the leading determinant product. -/
theorem oddCompactProductEGrade24_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade12 u a w +
      (-1)*oddCompactReflectedScalar10Grade8 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade10 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade13 u a w =
      oddCompactProductEGrade24 u a w := by
  unfold oddCompactProductEGrade24 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade8 oddCompactScalarHeadGrade10 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart4Grade10 oddCompactScalarHeadPart5Grade10 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 25 of the leading determinant product. -/
def oddCompactProductEGrade25 (u a w : ℝ) : ℝ :=
  ((-102025629159300 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (14586546970255 : ℝ)*u^(25 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-3728523619800 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (5484237660094464 : ℝ)

/-- Drift degree 25 of the leading determinant product. -/
theorem oddCompactProductEGrade25_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade9 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade11 u a w +
      (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade13 u a w =
      oddCompactProductEGrade25 u a w := by
  unfold oddCompactProductEGrade25 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactReflectedScalar10Grade9 oddCompactScalarHeadGrade11 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart5Grade11 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 26 of the leading determinant product. -/
def oddCompactProductEGrade26 (u a w : ℝ) : ℝ :=
  ((-814968185220000 : ℝ)*u^(26 : ℕ) +
    (223186355664300 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ) +
    (-11147895648005 : ℝ)*u^(26 : ℕ)*a^(2 : ℕ) +
    (-3945404039850 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (16452712980283392 : ℝ)

/-- Drift degree 26 of the leading determinant product. -/
theorem oddCompactProductEGrade26_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade10 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade12 u a w*oddCompactScalarHeadGrade14 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade12 u a w =
      oddCompactProductEGrade26 u a w := by
  unfold oddCompactProductEGrade26 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14 oddCompactScalarHeadGrade12 oddCompactScalarHeadGrade14 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart5Grade12 oddCompactScalarHeadPart5Grade14 oddCompactScalarHeadPart5Grade16
  ring

/-- Drift degree 27 of the leading determinant product. -/
def oddCompactProductEGrade27 (u a w : ℝ) : ℝ :=
  ((92853976075 : ℝ)*u^(27 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (457019805007872 : ℝ)

/-- Drift degree 27 of the leading determinant product. -/
theorem oddCompactProductEGrade27_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar10Grade11 u a w*oddCompactScalarHeadGrade16 u a w +
      (-1)*oddCompactReflectedScalar10Grade14 u a w*oddCompactScalarHeadGrade13 u a w =
      oddCompactProductEGrade27 u a w := by
  unfold oddCompactProductEGrade27 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade14 oddCompactScalarHeadGrade13 oddCompactScalarHeadGrade16 oddCompactScalarHeadPart5Grade13 oddCompactScalarHeadPart5Grade16
  ring

end
end HTGeometry
