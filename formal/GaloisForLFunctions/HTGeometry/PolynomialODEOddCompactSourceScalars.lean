import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactModel

/-!
# Real scalar source jets in the compact chart

Each modular polynomial evaluates to a real scalar polynomial. This normalization
separates complex source incidence from the real polynomial determinant proof.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar normalized source derivative of order 0. -/
def oddCompactSourceScalar0 (u a w : ℝ) : ℝ :=
  (((-18 : ℝ) +
    ((3 : ℝ)*a^1 +
    (2 : ℝ)*u^2))) / (48 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar0_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 0) =
      (oddCompactSourceScalar0 u a w : ℂ) := by
  rw [oddCompactSourceJet0_eq]
  simp only [oddCompactSourceJet0, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar0
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 1. -/
def oddCompactSourceScalar1 (u a w : ℝ) : ℝ :=
  ((((-36 : ℝ)*a^1*w^1 +
    (-90 : ℝ)*u^1) +
    ((21 : ℝ)*u^1*a^1 +
    (10 : ℝ)*u^3))) / (288 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar1_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 1) =
      (oddCompactSourceScalar1 u a w : ℂ) := by
  rw [oddCompactSourceJet1_eq]
  simp only [oddCompactSourceJet1, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar1
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 2. -/
def oddCompactSourceScalar2 (u a w : ℝ) : ℝ :=
  (((((3240 : ℝ) +
    (-2430 : ℝ)*a^1) +
    ((864 : ℝ)*a^1*w^2 +
    (-27 : ℝ)*a^2)) +
    (((-864 : ℝ)*u^1*a^1*w^1 +
    (-1620 : ℝ)*u^2) +
    ((300 : ℝ)*u^2*a^1 +
    (140 : ℝ)*u^4)))) / (3456 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar2_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 2) =
      (oddCompactSourceScalar2 u a w : ℂ) := by
  rw [oddCompactSourceJet2_eq]
  simp only [oddCompactSourceJet2, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar2
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 3. -/
def oddCompactSourceScalar3 (u a w : ℝ) : ℝ :=
  (((((21816 : ℝ)*a^1*w^1 +
    (-3456 : ℝ)*a^1*w^3) +
    ((648 : ℝ)*a^2*w^1 +
    ((20520 : ℝ)*u^1 +
    (-12726 : ℝ)*u^1*a^1))) +
    (((6048 : ℝ)*u^1*a^1*w^2 +
    ((27 : ℝ)*u^1*a^2 +
    (-2448 : ℝ)*u^2*a^1*w^1)) +
    ((-6060 : ℝ)*u^3 +
    ((956 : ℝ)*u^3*a^1 +
    (420 : ℝ)*u^5))))) / (6912 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar3_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 3) =
      (oddCompactSourceScalar3 u a w : ℂ) := by
  rw [oddCompactSourceJet3_eq]
  simp only [oddCompactSourceJet3, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar3
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 4. -/
def oddCompactSourceScalar4 (u a w : ℝ) : ℝ :=
  ((((((-738720 : ℝ) +
    (1166400 : ℝ)*a^1) +
    ((-990144 : ℝ)*a^1*w^2 +
    (82944 : ℝ)*a^1*w^4)) +
    (((30942 : ℝ)*a^2 +
    (-38880 : ℝ)*a^2*w^2) +
    ((4131 : ℝ)*a^3 +
    ((990144 : ℝ)*u^1*a^1*w^1 +
    (-235008 : ℝ)*u^1*a^1*w^3)))) +
    ((((33696 : ℝ)*u^1*a^2*w^1 +
    (777600 : ℝ)*u^2) +
    ((-343800 : ℝ)*u^2*a^1 +
    (164160 : ℝ)*u^2*a^1*w^2)) +
    (((13014 : ℝ)*u^2*a^2 +
    (-34752 : ℝ)*u^3*a^1*w^1) +
    ((-160440 : ℝ)*u^4 +
    ((25756 : ℝ)*u^4*a^1 +
    (9240 : ℝ)*u^6)))))) / (82944 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar4_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 4) =
      (oddCompactSourceScalar4 u a w : ℂ) := by
  rw [oddCompactSourceJet4_eq]
  simp only [oddCompactSourceJet4, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar4
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 5. -/
def oddCompactSourceScalar5 (u a w : ℝ) : ℝ :=
  ((((((-55582848 : ℝ)*a^1*w^1 +
    ((20093184 : ℝ)*a^1*w^3 +
    (-995328 : ℝ)*a^1*w^5)) +
    ((-3767472 : ℝ)*a^2*w^1 +
    ((870912 : ℝ)*a^2*w^3 +
    (-230364 : ℝ)*a^3*w^1))) +
    (((-28732320 : ℝ)*u^1 +
    ((32423328 : ℝ)*u^1*a^1 +
    (-35163072 : ℝ)*u^1*a^1*w^2)) +
    ((4230144 : ℝ)*u^1*a^1*w^4 +
    ((-156978 : ℝ)*u^1*a^2 +
    (-1796256 : ℝ)*u^1*a^2*w^2)))) +
    ((((222345 : ℝ)*u^1*a^3 +
    ((14232672 : ℝ)*u^2*a^1*w^1 +
    (-5052672 : ℝ)*u^2*a^1*w^3)) +
    ((335664 : ℝ)*u^2*a^2*w^1 +
    ((15439680 : ℝ)*u^3 +
    (-5558184 : ℝ)*u^3*a^1))) +
    (((1611072 : ℝ)*u^3*a^1*w^2 +
    ((469350 : ℝ)*u^3*a^2 +
    (-253584 : ℝ)*u^4*a^1*w^1)) +
    ((-2441880 : ℝ)*u^5 +
    ((434948 : ℝ)*u^5*a^1 +
    (120120 : ℝ)*u^7)))))) / (497664 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar5_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 5) =
      (oddCompactSourceScalar5 u a w : ℂ) := by
  rw [oddCompactSourceJet5_eq]
  simp only [oddCompactSourceJet5, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar5
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 6. -/
def oddCompactSourceScalar6 (u a w : ℝ) : ℝ :=
  (((((((1034363520 : ℝ) +
    (-2759819040 : ℝ)*a^1) +
    ((4046568192 : ℝ)*a^1*w^2 +
    (-753960960 : ℝ)*a^1*w^4)) +
    (((23887872 : ℝ)*a^1*w^6 +
    (-126455256 : ℝ)*a^2) +
    ((353419200 : ℝ)*a^2*w^2 +
    (-33592320 : ℝ)*a^2*w^4))) +
    ((((-37550790 : ℝ)*a^3 +
    (16096320 : ℝ)*a^3*w^2) +
    ((618921 : ℝ)*a^4 +
    (-4046568192 : ℝ)*u^1*a^1*w^1)) +
    (((2136222720 : ℝ)*u^1*a^1*w^3 +
    (-143327232 : ℝ)*u^1*a^1*w^5) +
    ((-306296640 : ℝ)*u^1*a^2*w^1 +
    ((119439360 : ℝ)*u^1*a^2*w^3 +
    (-33825600 : ℝ)*u^1*a^3*w^1))))) +
    (((((-1839879360 : ℝ)*u^2 +
    (1405058400 : ℝ)*u^2*a^1) +
    ((-1492214400 : ℝ)*u^2*a^1*w^2 +
    (268738560 : ℝ)*u^2*a^1*w^4)) +
    (((-118297260 : ℝ)*u^2*a^2 +
    (-96111360 : ℝ)*u^2*a^2*w^2) +
    ((15406200 : ℝ)*u^2*a^3 +
    ((315895680 : ℝ)*u^3*a^1*w^1 +
    (-165335040 : ℝ)*u^3*a^1*w^3)))) +
    ((((-15863040 : ℝ)*u^3*a^2*w^1 +
    (655693920 : ℝ)*u^4) +
    ((-234122040 : ℝ)*u^4*a^1 +
    (13996800 : ℝ)*u^4*a^1*w^2)) +
    (((25517160 : ℝ)*u^4*a^2 +
    (-8439552 : ℝ)*u^5*a^1*w^1) +
    ((-83991600 : ℝ)*u^6 +
    ((16460192 : ℝ)*u^6*a^1 +
    (3603600 : ℝ)*u^8))))))) / (5971968 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar6_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 6) =
      (oddCompactSourceScalar6 u a w : ℂ) := by
  rw [oddCompactSourceJet6_eq]
  simp only [oddCompactSourceJet6, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar6
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 7. -/
def oddCompactSourceScalar7 (u a w : ℝ) : ℝ :=
  (((((((203073692544 : ℝ)*a^1*w^1 +
    (-123200953344 : ℝ)*a^1*w^3) +
    ((13347348480 : ℝ)*a^1*w^5 +
    ((-286654464 : ℝ)*a^1*w^7 +
    (23100178752 : ℝ)*a^2*w^1))) +
    (((-11678929920 : ℝ)*a^2*w^3 +
    ((591224832 : ℝ)*a^2*w^5 +
    (3089181240 : ℝ)*a^3*w^1)) +
    ((-445098240 : ℝ)*a^3*w^3 +
    ((-85345488 : ℝ)*a^4*w^1 +
    (67270020480 : ℝ)*u^1)))) +
    ((((-118459653984 : ℝ)*u^1*a^1 +
    (215601668352 : ℝ)*u^1*a^1*w^2) +
    ((-56726231040 : ℝ)*u^1*a^1*w^4 +
    ((2317123584 : ℝ)*u^1*a^1*w^6 +
    (962507448 : ℝ)*u^1*a^2))) +
    (((24087792960 : ℝ)*u^1*a^2*w^2 +
    ((-3168875520 : ℝ)*u^1*a^2*w^4 +
    (-2981646450 : ℝ)*u^1*a^3)) +
    ((1572540480 : ℝ)*u^1*a^3*w^2 +
    ((37797921 : ℝ)*u^1*a^4 +
    (-87267341952 : ℝ)*u^2*a^1*w^1))))) +
    (((((67756331520 : ℝ)*u^2*a^1*w^3 +
    (-6330286080 : ℝ)*u^2*a^1*w^5) +
    ((-4501254240 : ℝ)*u^2*a^2*w^1 +
    ((4911943680 : ℝ)*u^2*a^2*w^3 +
    (-1539298080 : ℝ)*u^2*a^3*w^1))) +
    (((-56409359040 : ℝ)*u^3 +
    ((34079893344 : ℝ)*u^3*a^1 +
    (-21604475520 : ℝ)*u^3*a^1*w^2)) +
    ((6672015360 : ℝ)*u^3*a^1*w^4 +
    ((-6293983500 : ℝ)*u^3*a^2 +
    (-1627050240 : ℝ)*u^3*a^2*w^2)))) +
    ((((443649960 : ℝ)*u^3*a^3 +
    ((3400561440 : ℝ)*u^4*a^1*w^1 +
    (-1876055040 : ℝ)*u^4*a^1*w^3)) +
    ((-1149111360 : ℝ)*u^4*a^2*w^1 +
    ((14972338080 : ℝ)*u^5 +
    (-5832652680 : ℝ)*u^5*a^1))) +
    (((-322119936 : ℝ)*u^5*a^1*w^2 +
    ((627610248 : ℝ)*u^5*a^2 +
    (-286790784 : ℝ)*u^6*a^1*w^1)) +
    ((-1610809200 : ℝ)*u^7 +
    ((332459360 : ℝ)*u^7*a^1 +
    (61261200 : ℝ)*u^9))))))) / (35831808 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar7_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 7) =
      (oddCompactSourceScalar7 u a w : ℂ) := by
  rw [oddCompactSourceJet7_eq]
  simp only [oddCompactSourceJet7, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar7
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 8. -/
def oddCompactSourceScalar8 (u a w : ℝ) : ℝ :=
  (((((((-2421720737280 : ℝ) +
    ((9743746348800 : ℝ)*a^1 +
    (-21505897322496 : ℝ)*a^1*w^2)) +
    (((6600649015296 : ℝ)*a^1*w^4 +
    (-451910762496 : ℝ)*a^1*w^6) +
    ((6879707136 : ℝ)*a^1*w^8 +
    (672059291328 : ℝ)*a^2))) +
    ((((-3094054225920 : ℝ)*a^2*w^2 +
    (635499509760 : ℝ)*a^2*w^4) +
    ((-19564167168 : ℝ)*a^2*w^6 +
    (328743261504 : ℝ)*a^3)) +
    (((-304510181760 : ℝ)*a^3*w^2 +
    (21263938560 : ℝ)*a^3*w^4) +
    ((-11708747478 : ℝ)*a^4 +
    (14334262848 : ℝ)*a^4*w^2)))) +
    ((((-171891639 : ℝ)*a^5 +
    ((21505897322496 : ℝ)*u^1*a^1*w^1 +
    (-18701838876672 : ℝ)*u^1*a^1*w^3)) +
    (((2711464574976 : ℝ)*u^1*a^1*w^5 +
    (-72236924928 : ℝ)*u^1*a^1*w^7) +
    ((2681513662464 : ℝ)*u^1*a^2*w^1 +
    (-2259553812480 : ℝ)*u^1*a^2*w^3))) +
    ((((146408767488 : ℝ)*u^1*a^2*w^5 +
    (639912700800 : ℝ)*u^1*a^3*w^1) +
    ((-112433495040 : ℝ)*u^1*a^3*w^3 +
    (-13318934976 : ℝ)*u^1*a^4*w^1)) +
    (((6495830899200 : ℝ)*u^2 +
    (-7467325459200 : ℝ)*u^2*a^1) +
    ((13063784509440 : ℝ)*u^2*a^1*w^2 +
    (-5083996078080 : ℝ)*u^2*a^1*w^4))))) +
    (((((271700656128 : ℝ)*u^2*a^1*w^6 +
    ((1035648706176 : ℝ)*u^2*a^2 +
    (1818234708480 : ℝ)*u^2*a^2*w^2)) +
    (((-358071736320 : ℝ)*u^2*a^2*w^4 +
    (-291454491600 : ℝ)*u^2*a^3) +
    ((186349196160 : ℝ)*u^2*a^3*w^2 +
    (2741959998 : ℝ)*u^2*a^4))) +
    ((((-2765549703168 : ℝ)*u^3*a^1*w^1 +
    (3127808286720 : ℝ)*u^3*a^1*w^3) +
    ((-439568695296 : ℝ)*u^3*a^1*w^5 +
    (300096990720 : ℝ)*u^3*a^2*w^1)) +
    (((303893544960 : ℝ)*u^3*a^2*w^3 +
    (-112155891840 : ℝ)*u^3*a^3*w^1) +
    ((-3484751880960 : ℝ)*u^4 +
    (2049651765504 : ℝ)*u^4*a^1)))) +
    (((((-264791462400 : ℝ)*u^4*a^1*w^2 +
    (267534213120 : ℝ)*u^4*a^1*w^4) +
    ((-482733632880 : ℝ)*u^4*a^2 +
    (-2623000320 : ℝ)*u^4*a^2*w^2)) +
    (((23454097560 : ℝ)*u^4*a^3 +
    (159659444736 : ℝ)*u^5*a^1*w^1) +
    ((104730624 : ℝ)*u^5*a^1*w^3 +
    (-88031930112 : ℝ)*u^5*a^2*w^1))) +
    ((((735315356160 : ℝ)*u^6 +
    (-311393912256 : ℝ)*u^6*a^1) +
    ((-20366019072 : ℝ)*u^6*a^1*w^2 +
    (29967323472 : ℝ)*u^6*a^2)) +
    (((-19447884288 : ℝ)*u^7*a^1*w^1 +
    (-68172904800 : ℝ)*u^8) +
    ((14171162576 : ℝ)*u^8*a^1 +
    (2327925600 : ℝ)*u^10))))))) / (429981696 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar8_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 8) =
      (oddCompactSourceScalar8 u a w : ℂ) := by
  rw [oddCompactSourceJet8_eq]
  simp only [oddCompactSourceJet8, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar8
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 9. -/
def oddCompactSourceScalar9 (u a w : ℝ) : ℝ :=
  ((((((((-1020172643730432 : ℝ)*a^1*w^1 +
    (911535020384256 : ℝ)*a^1*w^3) +
    ((-160551725432832 : ℝ)*a^1*w^5 +
    (7383645683712 : ℝ)*a^1*w^7)) +
    (((-82556485632 : ℝ)*a^1*w^9 +
    (-170912816322048 : ℝ)*a^2*w^1) +
    ((140482759753728 : ℝ)*a^2*w^3 +
    ((-15228769222656 : ℝ)*a^2*w^5 +
    (309586821120 : ℝ)*a^2*w^7)))) +
    ((((-37158944265216 : ℝ)*a^3*w^1 +
    (11464840465920 : ℝ)*a^3*w^3) +
    ((-458817343488 : ℝ)*a^3*w^5 +
    ((2198329079904 : ℝ)*a^4*w^1 +
    (-938828081664 : ℝ)*a^4*w^3))) +
    (((36383868036 : ℝ)*a^5*w^1 +
    (-236271633108480 : ℝ)*u^1) +
    ((595100708842752 : ℝ)*u^1*a^1 +
    ((-1595186285672448 : ℝ)*u^1*a^1*w^2 +
    (682344833089536 : ℝ)*u^1*a^1*w^4))))) +
    (((((-59684469276672 : ℝ)*u^1*a^1*w^6 +
    (1093873434624 : ℝ)*u^1*a^1*w^8) +
    ((-7121367346752 : ℝ)*u^1*a^2 +
    (-289745691992064 : ℝ)*u^1*a^2*w^2)) +
    (((81623895644160 : ℝ)*u^1*a^2*w^4 +
    (-3074584117248 : ℝ)*u^1*a^2*w^6) +
    ((35865436711680 : ℝ)*u^1*a^3 +
    ((-40505497683840 : ℝ)*u^1*a^3*w^2 +
    (3382578662400 : ℝ)*u^1*a^3*w^4)))) +
    ((((-973598849118 : ℝ)*u^1*a^4 +
    (1433558554560 : ℝ)*u^1*a^4*w^2) +
    ((-15451056585 : ℝ)*u^1*a^5 +
    ((645670639438848 : ℝ)*u^2*a^1*w^1 +
    (-815022995079168 : ℝ)*u^2*a^1*w^3))) +
    (((163055508848640 : ℝ)*u^2*a^1*w^5 +
    (-5426369003520 : ℝ)*u^2*a^1*w^7) +
    ((54144396988416 : ℝ)*u^2*a^2*w^1 +
    ((-126521845309440 : ℝ)*u^2*a^2*w^3 +
    (10761044410368 : ℝ)*u^2*a^2*w^5)))))) +
    ((((((39649239944640 : ℝ)*u^2*a^3*w^1 +
    (-8475963793920 : ℝ)*u^2*a^3*w^3) +
    ((-582631286688 : ℝ)*u^2*a^4*w^1 +
    (283381289925120 : ℝ)*u^3)) +
    (((-252149154944256 : ℝ)*u^3*a^1 +
    (259874523168768 : ℝ)*u^3*a^1*w^2) +
    ((-171857771642880 : ℝ)*u^3*a^1*w^4 +
    ((12479932071936 : ℝ)*u^3*a^1*w^6 +
    (75708663206400 : ℝ)*u^3*a^2)))) +
    ((((41909560081920 : ℝ)*u^3*a^2*w^2 +
    (-15614807685120 : ℝ)*u^3*a^2*w^4) +
    ((-11427535669680 : ℝ)*u^3*a^3 +
    ((8698245575040 : ℝ)*u^3*a^3*w^2 +
    (81657300582 : ℝ)*u^3*a^4))) +
    (((-40904454352896 : ℝ)*u^4*a^1*w^1 +
    (48323425720320 : ℝ)*u^4*a^1*w^3) +
    ((-12905160081408 : ℝ)*u^4*a^1*w^5 +
    ((29598810410880 : ℝ)*u^4*a^2*w^1 +
    (7139980431360 : ℝ)*u^4*a^2*w^3))))) +
    (((((-3577587562080 : ℝ)*u^4*a^3*w^1 +
    (-110776825393920 : ℝ)*u^5) +
    ((70159436762112 : ℝ)*u^5*a^1 +
    (8297165311488 : ℝ)*u^5*a^1*w^2)) +
    (((3756640591872 : ℝ)*u^5*a^1*w^4 +
    (-16165984767984 : ℝ)*u^5*a^2) +
    ((2734809557760 : ℝ)*u^5*a^2*w^2 +
    ((606567632328 : ℝ)*u^5*a^3 +
    (7387157014272 : ℝ)*u^6*a^1*w^1)))) +
    ((((1673650169856 : ℝ)*u^6*a^1*w^3 +
    (-2781493852032 : ℝ)*u^6*a^2*w^1) +
    ((19375997921280 : ℝ)*u^7 +
    ((-8563488194880 : ℝ)*u^7*a^1 +
    (-193892866560 : ℝ)*u^7*a^1*w^2))) +
    (((724017498192 : ℝ)*u^7*a^2 +
    (-593873136576 : ℝ)*u^8*a^1*w^1) +
    ((-1577965989600 : ℝ)*u^9 +
    ((319735903408 : ℝ)*u^9*a^1 +
    (48886437600 : ℝ)*u^11)))))))) / (2579890176 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar9_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 9) =
      (oddCompactSourceScalar9 u a w : ℂ) := by
  rw [oddCompactSourceJet9_eq]
  simp only [oddCompactSourceJet9, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar9
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 10. -/
def oddCompactSourceScalar10 (u a w : ℝ) : ℝ :=
  ((((((((8505778791905280 : ℝ) +
    ((-48034213665845760 : ℝ)*a^1 +
    (147541371201404928 : ℝ)*a^1*w^2)) +
    ((-65707461532385280 : ℝ)*a^1*w^4 +
    ((7242334779211776 : ℝ)*a^1*w^6 +
    (-234419140952064 : ℝ)*a^1*w^8))) +
    (((1981355655168 : ℝ)*a^1*w^10 +
    ((-4610667850043904 : ℝ)*a^2 +
    (30800372593305600 : ℝ)*a^2*w^2)) +
    ((-10184533283266560 : ℝ)*a^2*w^4 +
    ((666629432082432 : ℝ)*a^2*w^6 +
    (-9473356726272 : ℝ)*a^2*w^8)))) +
    ((((-3272539588038720 : ℝ)*a^3 +
    ((4880088864898560 : ℝ)*a^3*w^2 +
    (-724547442493440 : ℝ)*a^3*w^4)) +
    ((18366238162944 : ℝ)*a^3*w^6 +
    ((187644721299768 : ℝ)*a^4 +
    (-488425672282752 : ℝ)*a^4*w^2))) +
    (((106806183496704 : ℝ)*a^4*w^4 +
    ((5857035707286 : ℝ)*a^5 +
    (-8362942643232 : ℝ)*a^5*w^2)) +
    ((79243698951 : ℝ)*a^6 +
    ((-147541371201404928 : ℝ)*u^1*a^1*w^1 +
    (186171141008424960 : ℝ)*u^1*a^1*w^3))))) +
    (((((-43454008675270656 : ℝ)*u^1*a^1*w^5 +
    ((2461400979996672 : ℝ)*u^1*a^1*w^7 +
    (-32362142367744 : ℝ)*u^1*a^1*w^9)) +
    ((-26693656247531520 : ℝ)*u^1*a^2*w^1 +
    ((36211673896058880 : ℝ)*u^1*a^2*w^3 +
    (-4988732343386112 : ℝ)*u^1*a^2*w^5))) +
    (((120367356051456 : ℝ)*u^1*a^2*w^7 +
    ((-10255259208844800 : ℝ)*u^1*a^3*w^1 +
    (3831058909992960 : ℝ)*u^1*a^3*w^3)) +
    ((-179802220953600 : ℝ)*u^1*a^3*w^5 +
    ((453829390372224 : ℝ)*u^1*a^4*w^1 +
    (-233416611753984 : ℝ)*u^1*a^4*w^3)))) +
    ((((8933304964896 : ℝ)*u^1*a^5*w^1 +
    ((-32022809110563840 : ℝ)*u^2 +
    (51229642778265600 : ℝ)*u^2*a^1)) +
    ((-130046017616179200 : ℝ)*u^2*a^1*w^2 +
    ((81476266266132480 : ℝ)*u^2*a^1*w^4 +
    (-9257928156905472 : ℝ)*u^2*a^1*w^6))) +
    (((204822640852992 : ℝ)*u^2*a^1*w^8 +
    ((-10309569159703680 : ℝ)*u^2*a^2 +
    (-29139081338234880 : ℝ)*u^2*a^2*w^2)) +
    (((12200936343367680 : ℝ)*u^2*a^2*w^4 +
    (-567728052240384 : ℝ)*u^2*a^2*w^6) +
    ((4670858001729600 : ℝ)*u^2*a^3 +
    (-6349662509955840 : ℝ)*u^2*a^3*w^2)))))) +
    ((((((633921342566400 : ℝ)*u^2*a^3*w^4 +
    ((-93429544971852 : ℝ)*u^2*a^4 +
    (162245549304576 : ℝ)*u^2*a^4*w^2)) +
    ((-1286723295828 : ℝ)*u^2*a^5 +
    ((27530209577226240 : ℝ)*u^3*a^1*w^1 +
    (-50126344883896320 : ℝ)*u^3*a^1*w^3))) +
    (((14977863723515904 : ℝ)*u^3*a^1*w^5 +
    ((-634322757353472 : ℝ)*u^3*a^1*w^7 +
    (-4809362939320320 : ℝ)*u^3*a^2*w^1)) +
    ((-10354868650967040 : ℝ)*u^3*a^2*w^3 +
    ((1223061435187200 : ℝ)*u^3*a^2*w^5 +
    (3821599858556160 : ℝ)*u^3*a^3*w^1)))) +
    ((((-996091700244480 : ℝ)*u^3*a^3*w^3 +
    ((-35095023726336 : ℝ)*u^3*a^4*w^1 +
    (23907166629857280 : ℝ)*u^4)) +
    ((-20403662461758720 : ℝ)*u^4*a^1 +
    ((4243555534694400 : ℝ)*u^4*a^1*w^2 +
    (-9115960777850880 : ℝ)*u^4*a^1*w^4))) +
    (((982187409014784 : ℝ)*u^4*a^1*w^6 +
    ((7736302979801280 : ℝ)*u^4*a^2 +
    (89376112903680 : ℝ)*u^4*a^2*w^2)) +
    ((-1135625597890560 : ℝ)*u^4*a^2*w^4 +
    ((-799174920259440 : ℝ)*u^4*a^3 +
    (702312039233280 : ℝ)*u^4*a^3*w^2))))) +
    (((((5419536859260 : ℝ)*u^4*a^4 +
    ((-2558706818697216 : ℝ)*u^5*a^1*w^1 +
    (-3568591282176 : ℝ)*u^5*a^1*w^3)) +
    ((-638979745775616 : ℝ)*u^5*a^1*w^5 +
    ((2999599986636288 : ℝ)*u^5*a^2*w^1 +
    (182586854080512 : ℝ)*u^5*a^2*w^3))) +
    (((-207682456391424 : ℝ)*u^5*a^3*w^1 +
    ((-7319841634828800 : ℝ)*u^6 +
    (4990407726318336 : ℝ)*u^6*a^1)) +
    ((693951733859328 : ℝ)*u^6*a^1*w^2 +
    ((-9377813200896 : ℝ)*u^6*a^1*w^4 +
    (-1021106579984928 : ℝ)*u^6*a^2)))) +
    ((((312464764007424 : ℝ)*u^6*a^2*w^2 +
    ((32728393686240 : ℝ)*u^6*a^3 +
    (662667209229312 : ℝ)*u^7*a^1*w^1)) +
    ((128406770270208 : ℝ)*u^7*a^1*w^3 +
    ((-159823560139776 : ℝ)*u^7*a^2*w^1 +
    (1092540918268800 : ℝ)*u^8))) +
    (((-482868193614624 : ℝ)*u^8*a^1 +
    ((18723084774912 : ℝ)*u^8*a^1*w^2 +
    (36638577363600 : ℝ)*u^8*a^2)) +
    (((-33650428706304 : ℝ)*u^9*a^1*w^1 +
    (-79321736894400 : ℝ)*u^10) +
    ((15406059954368 : ℝ)*u^10*a^1 +
    (2248776129600 : ℝ)*u^12)))))))) / (30958682112 : ℝ)

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar10_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 10) =
      (oddCompactSourceScalar10 u a w : ℂ) := by
  rw [oddCompactSourceJet10_eq]
  simp only [oddCompactSourceJet10, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar10
  push_cast
  ring

end
end HTGeometry
