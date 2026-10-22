import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactScalarGrades0

/-!
# Drift grades of the odd head and determinant (1)

The leading minor and the determinant are sums of monomial groups; each group
is the sum of its parts homogeneous in the drift coordinate `u`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- The odd determinant group 19 split by drift degree. -/
theorem oddCompactScalarDetPart19_grades (u a w : ℝ) :
    oddCompactScalarDetPart19 u a w =
      oddCompactScalarDetPart19Grade8 u a w := by
  unfold oddCompactScalarDetPart19 oddCompactScalarDetPart19Grade8
  ring

/-- Drift degree 8 of the odd determinant group 20. -/
def oddCompactScalarDetPart20Grade8 (u a w : ℝ) : ℝ :=
  ((-586633899604 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-10456807555568 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (16003829619 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (816989168652 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (3063863702368 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ)) / (3131031158784 : ℝ)

/-- Drift degree 9 of the odd determinant group 20. -/
def oddCompactScalarDetPart20Grade9 (u a w : ℝ) : ℝ :=
  ((106301027095200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-23028635723760 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (172216327273200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-111819624784380 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-52705092319080 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (79362328588100 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-137355392563200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (52326890211550 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (99211855638240 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-43501640150795 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (10449265680000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (2681981203420 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-54531736295040 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (8918294236272 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-96424473600 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-3744362199348 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (10034425444800 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (535053144112 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-1136293304080 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-540320390400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-388577132900 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (224704315904 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (6230630400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (27265000640 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-6402379776 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (-4915200 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ) +
    (8388608 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ)) / (47775744 : ℝ)

/-- The odd determinant group 20 split by drift degree. -/
theorem oddCompactScalarDetPart20_grades (u a w : ℝ) :
    oddCompactScalarDetPart20 u a w =
      oddCompactScalarDetPart20Grade8 u a w +
      oddCompactScalarDetPart20Grade9 u a w := by
  unfold oddCompactScalarDetPart20 oddCompactScalarDetPart20Grade8 oddCompactScalarDetPart20Grade9
  ring

/-- Drift degree 9 of the odd determinant group 21. -/
def oddCompactScalarDetPart21Grade9 (u a w : ℝ) : ℝ :=
  ((-411646619439796224 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (26807772097798400 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (177398599122658816 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-457318082731264 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-2303472624885376 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-73696046330320 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-54728547885388800 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (44290128731488 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (45739709296 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-673524739000064 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-18618006812608 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (90753561071 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (10310981973172224 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (1161888251136 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (454335051224 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (122493384753152 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (3290943056256 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (-905274502840320 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (398769721344 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (-7864785281024 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (20371616038912 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-3923259686912 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ)) / (1174136684544 : ℝ)

/-- Drift degree 10 of the odd determinant group 21. -/
def oddCompactScalarDetPart21Grade10 (u a w : ℝ) : ℝ :=
  ((-37300939830000 : ℝ)*u^(10 : ℕ) +
    (100016761994100 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-97245016607175 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-33657325581600 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (40602093546680 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (15912926341200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-10340263786800 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-3290655211200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (87554376000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-158054400 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ)) / (7962624 : ℝ)

/-- The odd determinant group 21 split by drift degree. -/
theorem oddCompactScalarDetPart21_grades (u a w : ℝ) :
    oddCompactScalarDetPart21 u a w =
      oddCompactScalarDetPart21Grade9 u a w +
      oddCompactScalarDetPart21Grade10 u a w := by
  unfold oddCompactScalarDetPart21 oddCompactScalarDetPart21Grade9 oddCompactScalarDetPart21Grade10
  ring

/-- Drift degree 10 of the odd determinant group 22. -/
def oddCompactScalarDetPart22Grade10 (u a w : ℝ) : ℝ :=
  ((1277296146684311040 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (-317578603396630080 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (-607528882985472000 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (40107381243235968 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (176818375152035328 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-2622330978812442 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (103899586846150656 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-23955106274446112 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (87542836911901 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (102005441924935680 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-49866162928832512 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1472120912271248 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (8991022103294976 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (5849964505691040 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-34553083532083200 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (6145508298528384 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-22074806460624 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-1825332898848768 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-1111243805352224 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (3574713962004480 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (480290738480640 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-31473352575136 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (-550590328553472 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (123929740356096 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-89390705541120 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-113284864475136 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (2248722823296 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (45975201644544 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-4726526840832 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (277830696960 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (2551655563264 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-283002273792 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ)) / (220150628352 : ℝ)

/-- The odd determinant group 22 split by drift degree. -/
theorem oddCompactScalarDetPart22_grades (u a w : ℝ) :
    oddCompactScalarDetPart22 u a w =
      oddCompactScalarDetPart22Grade10 u a w := by
  unfold oddCompactScalarDetPart22 oddCompactScalarDetPart22Grade10
  ring

/-- Drift degree 10 of the odd determinant group 23. -/
def oddCompactScalarDetPart23Grade10 (u a w : ℝ) : ℝ :=
  ((-87466936973372 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (-1982519233315264 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-843672497142 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-20619048284224 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (50577812155 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (30505011601280 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (2684865351628 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (4092763151520 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (13005328051968 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ)) / (7044820107264 : ℝ)

/-- Drift degree 11 of the odd determinant group 23. -/
def oddCompactScalarDetPart23Grade11 (u a w : ℝ) : ℝ :=
  ((-225920153440800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-518821275984480 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-325944891972000 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (745774002611820 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (55158602163840 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-274614668793396 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (511914355142400 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-252304660344864 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-147508502657760 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (111122420642300 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-40723349788800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (15048862273860 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (85202739972000 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-29728769552031 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (311525222400 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (17332844917860 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-18631909529280 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-556290210192 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (984947892480 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-194951205888 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-8315781120 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (4499361792 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (2949120 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(15 : ℕ)) / (1289945088 : ℝ)

/-- The odd determinant group 23 split by drift degree. -/
theorem oddCompactScalarDetPart23_grades (u a w : ℝ) :
    oddCompactScalarDetPart23 u a w =
      oddCompactScalarDetPart23Grade10 u a w +
      oddCompactScalarDetPart23Grade11 u a w := by
  unfold oddCompactScalarDetPart23 oddCompactScalarDetPart23Grade10 oddCompactScalarDetPart23Grade11
  ring

/-- Drift degree 11 of the odd determinant group 24. -/
def oddCompactScalarDetPart24Grade11 (u a w : ℝ) : ℝ :=
  ((33667534055137280 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-1151097116522624 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-9121838725921728 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-49229675345152 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (182021861612352 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (321676509492 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (2121327198411904 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-25746865211752 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (98449101355 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (2202912418780160 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (48739366710976 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (838226725860 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-405847052599296 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (2979062379360 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (270276933689344 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-6026495699712 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (23880159735808 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-18567501250560 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ)) / (1320903770112 : ℝ)

/-- Drift degree 12 of the odd determinant group 24. -/
def oddCompactScalarDetPart24Grade12 (u a w : ℝ) : ℝ :=
  ((220864550445000 : ℝ)*u^(12 : ℕ) +
    (-487229752960650 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (389149800407245 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (117716413071600 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-136163661677700 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-40770435358800 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (18929189207320 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (10728279500400 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-3870410017700 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-264058099200 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (1606019783520 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (338688000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-184714765120 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (3827005440 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ)) / (214990848 : ℝ)

/-- The odd determinant group 24 split by drift degree. -/
theorem oddCompactScalarDetPart24_grades (u a w : ℝ) :
    oddCompactScalarDetPart24 u a w =
      oddCompactScalarDetPart24Grade11 u a w +
      oddCompactScalarDetPart24Grade12 u a w := by
  unfold oddCompactScalarDetPart24 oddCompactScalarDetPart24Grade11 oddCompactScalarDetPart24Grade12
  ring

/-- Drift degree 12 of the odd determinant group 25. -/
def oddCompactScalarDetPart25Grade12 (u a w : ℝ) : ℝ :=
  ((-43447114187401175040 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (8194174366164762624 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ) +
    (19699887230979735552 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-770149737888983040 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ) +
    (-4466047351461888000 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (36825566366680512 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ) +
    (-3270778678565240832 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (433568283876807680 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-956799894643312 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ) +
    (973990790256492544 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-19533577109288704 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (2359307358140 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ) +
    (-66841770493083648 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-42789453830253568 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-31555930765376 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (574298429605 : ℝ)*u^(12 : ℕ)*a^(9 : ℕ) +
    (-149841763281530880 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-356437550431232 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (22761691391248 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (82487644236546048 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (4520810997382144 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (19647128419136 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (3399918641823744 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (250108040091648 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (594724243636224 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-479359772467200 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (493305080315904 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-255611891613696 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-1727382159360 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (63403380965376 : ℝ)

/-- Drift degree 13 of the odd determinant group 25. -/
def oddCompactScalarDetPart25Grade13 (u a w : ℝ) : ℝ :=
  ((-34566963200 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-8873325475 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-55541264800 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (1492992 : ℝ)

/-- The odd determinant group 25 split by drift degree. -/
theorem oddCompactScalarDetPart25_grades (u a w : ℝ) :
    oddCompactScalarDetPart25 u a w =
      oddCompactScalarDetPart25Grade12 u a w +
      oddCompactScalarDetPart25Grade13 u a w := by
  unfold oddCompactScalarDetPart25 oddCompactScalarDetPart25Grade12 oddCompactScalarDetPart25Grade13
  ring

/-- Drift degree 13 of the odd determinant group 26. -/
def oddCompactScalarDetPart26Grade13 (u a w : ℝ) : ℝ :=
  ((643279076987904000 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-444124633653116928 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-17033744461639680 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (95524747738663936 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (120703804941143040 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-6296301878251648 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (25231027249152000 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-29403205551663104 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-71094076976 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (18742761986457600 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-18664616362733568 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (1713958401392928 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (2498167660732 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-10335903759728640 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (6961924555648512 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-101446902974456 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (360818317999 : ℝ)*u^(13 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-113929224192000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-3183503916275712 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-95965940452672 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (3813939197106 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (3229703424737280 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-766259545865216 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (2801774094960 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (401567952248832 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (14362029897216 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-166387032391680 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (3345631950848 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (7359637487616 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (781210091520 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ)) / (5944066965504 : ℝ)

/-- Drift degree 14 of the odd determinant group 26. -/
def oddCompactScalarDetPart26Grade14 (u a _w : ℝ) : ℝ :=
  ((-1542172314375 : ℝ)*u^(14 : ℕ) +
    (2771326436900 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)) / (8957952 : ℝ)

/-- The odd determinant group 26 split by drift degree. -/
theorem oddCompactScalarDetPart26_grades (u a w : ℝ) :
    oddCompactScalarDetPart26 u a w =
      oddCompactScalarDetPart26Grade13 u a w +
      oddCompactScalarDetPart26Grade14 u a w := by
  unfold oddCompactScalarDetPart26 oddCompactScalarDetPart26Grade13 oddCompactScalarDetPart26Grade14
  ring

/-- Drift degree 14 of the odd determinant group 27. -/
def oddCompactScalarDetPart27Grade14 (u a w : ℝ) : ℝ :=
  ((-1767593644404088320 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-531130130076672000 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (516539804202785280 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ) +
    (570890189298401280 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-72313660021076864 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ) +
    (91570959870566400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-229425692715976704 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (4946372934163104 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ) +
    (-38598593804697600 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (37457623010366976 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-162390337235841 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ) +
    (-37324935464140800 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (30126167581777920 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-2367787195659568 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (1698637848374 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ) +
    (3186419775344640 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-4535743239746560 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (24185167439232 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (825409983283200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-1660190399695872 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (49895819658896 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (2137421774589 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-1415881267937280 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (617664593988672 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (2181242295336 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-713451110400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (-381576860209152 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (6922027380144 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (211456329154560 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-26406635261184 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (12317870481408 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-2919204126720 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ)) / (8916100448256 : ℝ)

/-- The odd determinant group 27 split by drift degree. -/
theorem oddCompactScalarDetPart27_grades (u a w : ℝ) :
    oddCompactScalarDetPart27 u a w =
      oddCompactScalarDetPart27Grade14 u a w := by
  unfold oddCompactScalarDetPart27 oddCompactScalarDetPart27Grade14
  ring

/-- Drift degree 14 of the odd determinant group 28. -/
def oddCompactScalarDetPart28Grade14 (u a _w : ℝ) : ℝ :=
  ((379049160887 : ℝ)*u^(14 : ℕ)*a^(8 : ℕ)) / (47552535724032 : ℝ)

/-- Drift degree 15 of the odd determinant group 28. -/
def oddCompactScalarDetPart28Grade15 (u a w : ℝ) : ℝ :=
  ((111119990936371200 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-190256034608455680 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (39730142366208000 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (77799555854705664 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (9453352670668800 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-9661288390145024 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (30727515790540800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-18501437355743232 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (277288582250336 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-2028007264296960 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (2880122878045440 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (1604173567576 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-2878924330598400 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (2790988637684736 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-173191045663384 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (535551463777 : ℝ)*u^(15 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (15831613071360 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-326642819528064 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (5830150975644 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (13020482764800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-4218645321216 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (3157156066832 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-115812842987520 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (28159826329984 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-17487919613952 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (5744792862720 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ)) / (13374150672384 : ℝ)

/-- Drift degree 16 of the odd determinant group 28. -/
def oddCompactScalarDetPart28Grade16 (u a w : ℝ) : ℝ :=
  ((1794057457500 : ℝ)*u^(16 : ℕ) +
    (-2584197577675 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ) +
    (441238812175 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-10040610650 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (19269552925 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (80621568 : ℝ)

/-- The odd determinant group 28 split by drift degree. -/
theorem oddCompactScalarDetPart28_grades (u a w : ℝ) :
    oddCompactScalarDetPart28 u a w =
      oddCompactScalarDetPart28Grade14 u a w +
      oddCompactScalarDetPart28Grade15 u a w +
      oddCompactScalarDetPart28Grade16 u a w := by
  unfold oddCompactScalarDetPart28 oddCompactScalarDetPart28Grade14 oddCompactScalarDetPart28Grade15 oddCompactScalarDetPart28Grade16
  ring

/-- Drift degree 16 of the odd determinant group 29. -/
def oddCompactScalarDetPart29Grade16 (u a w : ℝ) : ℝ :=
  ((1286585231480651520 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ) +
    (-281446552088777280 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ) +
    (-400943756177280000 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (28462316479001200 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ) +
    (119251822687004160 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-1326950212961588 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ) +
    (10198654661744640 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-12452834302552320 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (22826445445652 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ) +
    (-9565713123823872 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (317728709284976 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (334198342481 : ℝ)*u^(16 : ℕ)*a^(7 : ℕ) +
    (-811178662348800 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (657902429209216 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (8773788217340 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-362504927232000 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (831401357119488 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (1564131531632 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-5631350722560 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-35819740570176 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (189510451200 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (18636847746048 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-19826952192000 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ)) / (80244904034304 : ℝ)

/-- Drift degree 17 of the odd determinant group 29. -/
def oddCompactScalarDetPart29Grade17 (u a w : ℝ) : ℝ :=
  ((-29703333252600 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (29630095973650 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-7153544878200 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-2581234622755 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-2219844614400 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (99254503900 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (251167467600 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (9857889840 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-750556800 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (26121388032 : ℝ)

/-- The odd determinant group 29 split by drift degree. -/
theorem oddCompactScalarDetPart29_grades (u a w : ℝ) :
    oddCompactScalarDetPart29 u a w =
      oddCompactScalarDetPart29Grade16 u a w +
      oddCompactScalarDetPart29Grade17 u a w := by
  unfold oddCompactScalarDetPart29 oddCompactScalarDetPart29Grade16 oddCompactScalarDetPart29Grade17
  ring

/-- Drift degree 17 of the odd determinant group 30. -/
def oddCompactScalarDetPart30Grade17 (u a w : ℝ) : ℝ :=
  ((-8373364969950144 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (556026407405056 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (2038163797378464 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-7532065208420 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-215040238989328 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (617031546325 : ℝ)*u^(17 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-154252681656384 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (7384546927950 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (6566963876112 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (7495006007808 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (47372820480 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (30091839012864 : ℝ)

/-- Drift degree 18 of the odd determinant group 30. -/
def oddCompactScalarDetPart30Grade18 (u a w : ℝ) : ℝ :=
  ((-100238521299840000 : ℝ)*u^(18 : ℕ) +
    (113189614004073600 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ) +
    (-42798057357618000 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ) +
    (-18139534119302400 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (6762746822174472 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ) +
    (12619876470399360 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-466898882977587 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ) +
    (-1044267523488000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-2456945500693056 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (12343711876095 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ) +
    (-32511520638720 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (124307627995272 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-398324841062400 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (100040442774336 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (951400501423 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (21600840409920 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-3116516877536 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (5828709196800 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-4946720147088 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (1410804311040 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-1393459200 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ)) / (45137758519296 : ℝ)

/-- The odd determinant group 30 split by drift degree. -/
theorem oddCompactScalarDetPart30_grades (u a w : ℝ) :
    oddCompactScalarDetPart30 u a w =
      oddCompactScalarDetPart30Grade17 u a w +
      oddCompactScalarDetPart30Grade18 u a w := by
  unfold oddCompactScalarDetPart30 oddCompactScalarDetPart30Grade17 oddCompactScalarDetPart30Grade18
  ring

/-- Drift degree 18 of the odd determinant group 31. -/
def oddCompactScalarDetPart31Grade18 (u a _w : ℝ) : ℝ :=
  ((89442830929 : ℝ)*u^(18 : ℕ)*a^(6 : ℕ)) / (180551034077184 : ℝ)

/-- Drift degree 19 of the odd determinant group 31. -/
def oddCompactScalarDetPart31Grade19 (u a w : ℝ) : ℝ :=
  ((6277360961491200 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-3850689509573760 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (779576579107200 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (539847647916624 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (498305880155520 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-19364517053232 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (89704066636800 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-148033903978176 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (618016251957 : ℝ)*u^(19 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (4888113517440 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (7512580165928 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-17186468544000 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (2732783028912 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (712403199360 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (25430630400 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (67706637778944 : ℝ)

/-- Drift degree 20 of the odd determinant group 31. -/
def oddCompactScalarDetPart31Grade20 (u a w : ℝ) : ℝ :=
  ((137986679476800000 : ℝ)*u^(20 : ℕ) +
    (-118571925476188800 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ) +
    (32541388909984800 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ) +
    (17601070360204800 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-3510237956638632 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ) +
    (-8276008543655040 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (143186381353660 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ) +
    (1355377331750400 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (853124171797056 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-968911079525 : ℝ)*u^(20 : ℕ)*a^(5 : ℕ) +
    (-39233401632000 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-7041826798224 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (153295034457600 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-18737514786528 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-4542077623680 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-1336153190400 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (812479653347328 : ℝ)

/-- The odd determinant group 31 split by drift degree. -/
theorem oddCompactScalarDetPart31_grades (u a w : ℝ) :
    oddCompactScalarDetPart31 u a w =
      oddCompactScalarDetPart31Grade18 u a w +
      oddCompactScalarDetPart31Grade19 u a w +
      oddCompactScalarDetPart31Grade20 u a w := by
  unfold oddCompactScalarDetPart31 oddCompactScalarDetPart31Grade18 oddCompactScalarDetPart31Grade19 oddCompactScalarDetPart31Grade20
  ring

/-- Drift degree 21 of the odd determinant group 32. -/
def oddCompactScalarDetPart32Grade21 (u a w : ℝ) : ℝ :=
  ((-122303552918400 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (44552213963160 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-3218556222000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-3429131566884 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-7231619358180 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (99732071039 : ℝ)*u^(21 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (423531763200 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (807019613741 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-114062232480 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (76373539200 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (25389989167104 : ℝ)

/-- Drift degree 22 of the odd determinant group 32. -/
def oddCompactScalarDetPart32Grade22 (u a w : ℝ) : ℝ :=
  ((-17880369449040000 : ℝ)*u^(22 : ℕ) +
    (11218450266777600 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ) +
    (-2103753765478680 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ) +
    (-1419647834102400 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (137051724115248 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ) +
    (377291670134400 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-2117753926325 : ℝ)*u^(22 : ℕ)*a^(4 : ℕ) +
    (-88071514876800 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-12138995376288 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (349786955520 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-3204488044800 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (1828079220031488 : ℝ)

/-- Drift degree 23 of the odd determinant group 32. -/
def oddCompactScalarDetPart32Grade23 (u a w : ℝ) : ℝ :=
  ((1494929595600 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-299213414600 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-63368968950 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (12936097486 : ℝ)*u^(23 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (42456669195 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-6602828400 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (9521245937664 : ℝ)

/-- Drift degree 24 of the odd determinant group 32. -/
def oddCompactScalarDetPart32Grade24 (u a w : ℝ) : ℝ :=
  ((11735152222500 : ℝ)*u^(24 : ℕ) +
    (-5046311580975 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ) +
    (576883649410 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ) +
    (458598294000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (14984761050 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (28563737812992 : ℝ)

/-- The odd determinant group 32 split by drift degree. -/
theorem oddCompactScalarDetPart32_grades (u a w : ℝ) :
    oddCompactScalarDetPart32 u a w =
      oddCompactScalarDetPart32Grade21 u a w +
      oddCompactScalarDetPart32Grade22 u a w +
      oddCompactScalarDetPart32Grade23 u a w +
      oddCompactScalarDetPart32Grade24 u a w := by
  unfold oddCompactScalarDetPart32 oddCompactScalarDetPart32Grade21 oddCompactScalarDetPart32Grade22 oddCompactScalarDetPart32Grade23 oddCompactScalarDetPart32Grade24
  ring

/-- Drift degree 24 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade24 (u a w : ℝ) : ℝ :=
  ((-32256196957 : ℝ)*u^(24 : ℕ)*a^(3 : ℕ) +
    (-91673263630 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ)) / (57127475625984 : ℝ)

/-- Drift degree 25 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade25 (u a w : ℝ) : ℝ :=
  ((-126450667350 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (12095873990 : ℝ)*u^(25 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (7944563025 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (42845606719488 : ℝ)

/-- Drift degree 26 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade26 (u a w : ℝ) : ℝ :=
  ((-3056020852500 : ℝ)*u^(26 : ℕ) +
    (803530934325 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ) +
    (-41565054110 : ℝ)*u^(26 : ℕ)*a^(2 : ℕ) +
    (-35857476900 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (257073640316928 : ℝ)

/-- Drift degree 27 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade27 (u a w : ℝ) : ℝ :=
  ((177576175 : ℝ)*u^(27 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (7140934453248 : ℝ)

/-- Drift degree 28 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade28 (u a _w : ℝ) : ℝ :=
  ((36326272500 : ℝ)*u^(28 : ℕ) +
    (-4408401025 : ℝ)*u^(28 : ℕ)*a^(1 : ℕ)) / (171382426877952 : ℝ)

/-- Drift degree 30 of the odd determinant group 33. -/
def oddCompactScalarDetPart33Grade30 (u _a _w : ℝ) : ℝ :=
  ((-2786875 : ℝ)*u^(30 : ℕ)) / (1586874322944 : ℝ)

/-- The odd determinant group 33 split by drift degree. -/
theorem oddCompactScalarDetPart33_grades (u a w : ℝ) :
    oddCompactScalarDetPart33 u a w =
      oddCompactScalarDetPart33Grade24 u a w +
      oddCompactScalarDetPart33Grade25 u a w +
      oddCompactScalarDetPart33Grade26 u a w +
      oddCompactScalarDetPart33Grade27 u a w +
      oddCompactScalarDetPart33Grade28 u a w +
      oddCompactScalarDetPart33Grade30 u a w := by
  unfold oddCompactScalarDetPart33 oddCompactScalarDetPart33Grade24 oddCompactScalarDetPart33Grade25 oddCompactScalarDetPart33Grade26 oddCompactScalarDetPart33Grade27 oddCompactScalarDetPart33Grade28 oddCompactScalarDetPart33Grade30
  ring

/-- Drift degree 0 of the odd determinant. -/
def oddCompactScalarDetGrade0 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart0Grade0 u a w +
    oddCompactScalarDetPart1Grade0 u a w +
    oddCompactScalarDetPart2Grade0 u a w

/-- Drift degree 1 of the odd determinant. -/
def oddCompactScalarDetGrade1 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart2Grade1 u a w +
    oddCompactScalarDetPart3Grade1 u a w +
    oddCompactScalarDetPart4Grade1 u a w +
    oddCompactScalarDetPart5Grade1 u a w

/-- Drift degree 2 of the odd determinant. -/
def oddCompactScalarDetGrade2 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart5Grade2 u a w +
    oddCompactScalarDetPart6Grade2 u a w +
    oddCompactScalarDetPart7Grade2 u a w

/-- Drift degree 3 of the odd determinant. -/
def oddCompactScalarDetGrade3 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart7Grade3 u a w +
    oddCompactScalarDetPart8Grade3 u a w +
    oddCompactScalarDetPart9Grade3 u a w

/-- Drift degree 4 of the odd determinant. -/
def oddCompactScalarDetGrade4 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart10Grade4 u a w +
    oddCompactScalarDetPart11Grade4 u a w +
    oddCompactScalarDetPart12Grade4 u a w

/-- Drift degree 5 of the odd determinant. -/
def oddCompactScalarDetGrade5 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart12Grade5 u a w +
    oddCompactScalarDetPart13Grade5 u a w +
    oddCompactScalarDetPart14Grade5 u a w

/-- Drift degree 6 of the odd determinant. -/
def oddCompactScalarDetGrade6 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart14Grade6 u a w +
    oddCompactScalarDetPart15Grade6 u a w +
    oddCompactScalarDetPart16Grade6 u a w

/-- Drift degree 7 of the odd determinant. -/
def oddCompactScalarDetGrade7 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart16Grade7 u a w +
    oddCompactScalarDetPart17Grade7 u a w +
    oddCompactScalarDetPart18Grade7 u a w

/-- Drift degree 8 of the odd determinant. -/
def oddCompactScalarDetGrade8 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart18Grade8 u a w +
    oddCompactScalarDetPart19Grade8 u a w +
    oddCompactScalarDetPart20Grade8 u a w

/-- Drift degree 9 of the odd determinant. -/
def oddCompactScalarDetGrade9 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart20Grade9 u a w +
    oddCompactScalarDetPart21Grade9 u a w

/-- Drift degree 10 of the odd determinant. -/
def oddCompactScalarDetGrade10 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart21Grade10 u a w +
    oddCompactScalarDetPart22Grade10 u a w +
    oddCompactScalarDetPart23Grade10 u a w

/-- Drift degree 11 of the odd determinant. -/
def oddCompactScalarDetGrade11 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart23Grade11 u a w +
    oddCompactScalarDetPart24Grade11 u a w

/-- Drift degree 12 of the odd determinant. -/
def oddCompactScalarDetGrade12 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart24Grade12 u a w +
    oddCompactScalarDetPart25Grade12 u a w

/-- Drift degree 13 of the odd determinant. -/
def oddCompactScalarDetGrade13 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart25Grade13 u a w +
    oddCompactScalarDetPart26Grade13 u a w

/-- Drift degree 14 of the odd determinant. -/
def oddCompactScalarDetGrade14 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart26Grade14 u a w +
    oddCompactScalarDetPart27Grade14 u a w +
    oddCompactScalarDetPart28Grade14 u a w

/-- Drift degree 15 of the odd determinant. -/
def oddCompactScalarDetGrade15 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart28Grade15 u a w

/-- Drift degree 16 of the odd determinant. -/
def oddCompactScalarDetGrade16 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart28Grade16 u a w +
    oddCompactScalarDetPart29Grade16 u a w

/-- Drift degree 17 of the odd determinant. -/
def oddCompactScalarDetGrade17 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart29Grade17 u a w +
    oddCompactScalarDetPart30Grade17 u a w

/-- Drift degree 18 of the odd determinant. -/
def oddCompactScalarDetGrade18 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart30Grade18 u a w +
    oddCompactScalarDetPart31Grade18 u a w

/-- Drift degree 19 of the odd determinant. -/
def oddCompactScalarDetGrade19 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart31Grade19 u a w

/-- Drift degree 20 of the odd determinant. -/
def oddCompactScalarDetGrade20 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart31Grade20 u a w

/-- Drift degree 21 of the odd determinant. -/
def oddCompactScalarDetGrade21 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart32Grade21 u a w

/-- Drift degree 22 of the odd determinant. -/
def oddCompactScalarDetGrade22 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart32Grade22 u a w

/-- Drift degree 23 of the odd determinant. -/
def oddCompactScalarDetGrade23 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart32Grade23 u a w

/-- Drift degree 24 of the odd determinant. -/
def oddCompactScalarDetGrade24 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart32Grade24 u a w +
    oddCompactScalarDetPart33Grade24 u a w

/-- Drift degree 25 of the odd determinant. -/
def oddCompactScalarDetGrade25 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart33Grade25 u a w

/-- Drift degree 26 of the odd determinant. -/
def oddCompactScalarDetGrade26 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart33Grade26 u a w

/-- Drift degree 27 of the odd determinant. -/
def oddCompactScalarDetGrade27 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart33Grade27 u a w

/-- Drift degree 28 of the odd determinant. -/
def oddCompactScalarDetGrade28 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart33Grade28 u a w

/-- Drift degree 30 of the odd determinant. -/
def oddCompactScalarDetGrade30 (u a w : ℝ) : ℝ :=
  oddCompactScalarDetPart33Grade30 u a w

/-- The odd determinant is the sum of its drift grades. -/
theorem oddCompactScalarDet_grades (u a w : ℝ) :
    oddCompactScalarDet u a w =
      oddCompactScalarDetGrade0 u a w +
      oddCompactScalarDetGrade1 u a w +
      oddCompactScalarDetGrade2 u a w +
      oddCompactScalarDetGrade3 u a w +
      oddCompactScalarDetGrade4 u a w +
      oddCompactScalarDetGrade5 u a w +
      oddCompactScalarDetGrade6 u a w +
      oddCompactScalarDetGrade7 u a w +
      oddCompactScalarDetGrade8 u a w +
      oddCompactScalarDetGrade9 u a w +
      oddCompactScalarDetGrade10 u a w +
      oddCompactScalarDetGrade11 u a w +
      oddCompactScalarDetGrade12 u a w +
      oddCompactScalarDetGrade13 u a w +
      oddCompactScalarDetGrade14 u a w +
      oddCompactScalarDetGrade15 u a w +
      oddCompactScalarDetGrade16 u a w +
      oddCompactScalarDetGrade17 u a w +
      oddCompactScalarDetGrade18 u a w +
      oddCompactScalarDetGrade19 u a w +
      oddCompactScalarDetGrade20 u a w +
      oddCompactScalarDetGrade21 u a w +
      oddCompactScalarDetGrade22 u a w +
      oddCompactScalarDetGrade23 u a w +
      oddCompactScalarDetGrade24 u a w +
      oddCompactScalarDetGrade25 u a w +
      oddCompactScalarDetGrade26 u a w +
      oddCompactScalarDetGrade27 u a w +
      oddCompactScalarDetGrade28 u a w +
      oddCompactScalarDetGrade30 u a w := by
  unfold oddCompactScalarDet oddCompactScalarDetGrade0 oddCompactScalarDetGrade1 oddCompactScalarDetGrade2 oddCompactScalarDetGrade3 oddCompactScalarDetGrade4 oddCompactScalarDetGrade5 oddCompactScalarDetGrade6 oddCompactScalarDetGrade7 oddCompactScalarDetGrade8 oddCompactScalarDetGrade9 oddCompactScalarDetGrade10 oddCompactScalarDetGrade11 oddCompactScalarDetGrade12 oddCompactScalarDetGrade13 oddCompactScalarDetGrade14 oddCompactScalarDetGrade15 oddCompactScalarDetGrade16 oddCompactScalarDetGrade17 oddCompactScalarDetGrade18 oddCompactScalarDetGrade19 oddCompactScalarDetGrade20 oddCompactScalarDetGrade21 oddCompactScalarDetGrade22 oddCompactScalarDetGrade23 oddCompactScalarDetGrade24 oddCompactScalarDetGrade25 oddCompactScalarDetGrade26 oddCompactScalarDetGrade27 oddCompactScalarDetGrade28 oddCompactScalarDetGrade30
  linear_combination oddCompactScalarDetPart0_grades u a w + oddCompactScalarDetPart1_grades u a w + oddCompactScalarDetPart2_grades u a w + oddCompactScalarDetPart3_grades u a w + oddCompactScalarDetPart4_grades u a w + oddCompactScalarDetPart5_grades u a w + oddCompactScalarDetPart6_grades u a w + oddCompactScalarDetPart7_grades u a w + oddCompactScalarDetPart8_grades u a w + oddCompactScalarDetPart9_grades u a w + oddCompactScalarDetPart10_grades u a w + oddCompactScalarDetPart11_grades u a w + oddCompactScalarDetPart12_grades u a w + oddCompactScalarDetPart13_grades u a w + oddCompactScalarDetPart14_grades u a w + oddCompactScalarDetPart15_grades u a w + oddCompactScalarDetPart16_grades u a w + oddCompactScalarDetPart17_grades u a w + oddCompactScalarDetPart18_grades u a w + oddCompactScalarDetPart19_grades u a w + oddCompactScalarDetPart20_grades u a w + oddCompactScalarDetPart21_grades u a w + oddCompactScalarDetPart22_grades u a w + oddCompactScalarDetPart23_grades u a w + oddCompactScalarDetPart24_grades u a w + oddCompactScalarDetPart25_grades u a w + oddCompactScalarDetPart26_grades u a w + oddCompactScalarDetPart27_grades u a w + oddCompactScalarDetPart28_grades u a w + oddCompactScalarDetPart29_grades u a w + oddCompactScalarDetPart30_grades u a w + oddCompactScalarDetPart31_grades u a w + oddCompactScalarDetPart32_grades u a w + oddCompactScalarDetPart33_grades u a w

end
end HTGeometry
