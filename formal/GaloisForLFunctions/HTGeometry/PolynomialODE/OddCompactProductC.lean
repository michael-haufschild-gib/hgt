import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactProductCGrades0
import Mathlib.Tactic.LinearCombination

/-!
# The trailing determinant product, drift-graded (1)

The grade `d` part of a product is the sum of the products of the factors'
grades over `i+j = d`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 8 of the trailing determinant product, block 0. -/
def oddCompactProductCGrade8Part0 (u a w : ℝ) : ℝ :=
  ((3632566926736097280000 : ℝ)*u^(8 : ℕ) +
    (-11829794489228486246400 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (13618218214407695892480 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (7071901760373837004800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-7440275263844305797120 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-10578558739309142999040 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (2239327107039209742336 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-1886249023045632000000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (5251895802243057844224 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-396222304740311101440 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (4591109182648095866880 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1284933952966945603584 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (40945476108215210496 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (113988456448996147200 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-1885213522192936992768 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (178982554308528216064 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-2449758997373476608 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-1344959159439835791360 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (311799800925095657472 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-11728068869470159360 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (35744792140491488 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-719035054424064000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (464017207968547209216 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-36892014118653394944 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (484416501512876928 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-478636550725632 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (203370339629971537920 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-18727352501574303744 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (796974096089196544 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-20926172058061344 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (7956128872692 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-114584179205587599360 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (6508087517054566400 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-75072079412387328 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-29995934135424 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (225110931525 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-11652212155565998080 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-10680727724073418752 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (51753741798924288 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (3776458059643392 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-6821618147784 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (19891803240265678848 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-1324565607256424448 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (3156139566120960 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (33892678963584 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (171374526238556160 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (2326365145367838720 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-35609840561160192 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-15089976649728 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-1414506439451344896 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (136194649831243776 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-468782942257152 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-342094145126400 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (-111826040556355584 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (2368797394599936 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (27731427009232896 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-2742451106217984 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (824253616226304 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-82875688943616 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (300578991243264 : ℝ)

/-- Drift degree 8 of the trailing determinant product, block 1. -/
def oddCompactProductCGrade8Part1 (u a w : ℝ) : ℝ :=
  ((934379607490560000 : ℝ)*u^(8 : ℕ) +
    (-5185138802805964800 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (7713767974839091200 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (7045173564162048000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-4262945000558100480 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (-12358594432747929600 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (762957239794513920 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ) +
    (-1761954691940352000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (6368485534342299648 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-93602776926090240 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ) +
    (-3989288625277501440 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1512534655007993856 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (19160915384555136 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ) +
    (111515232632832000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (6256083389981196288 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-156948551492304384 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-1600998305973120 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ) +
    (-9104815051324784640 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (184063835264335872 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (191430916981793408 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-12289035512976 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ) +
    (-1657584746496000 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-1220083204639162368 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-526824854371934208 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-1190487571072384 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (874305689220 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ) +
    (3256606851764060160 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (1080647672307384320 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-61004735049660416 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-947175322952576 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (7568599880 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ) +
    (-2109606811014266880 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (344588297662365696 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-390343179218944 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-20753130171712 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (-787201725 : ℝ)*u^(8 : ℕ)*a^(11 : ℕ) +
    (-229566120418344960 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-600394803022135296 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (15534866972688384 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (135405611404288 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-100850832552 : ℝ)*u^(8 : ℕ)*a^(10 : ℕ)*w^(2 : ℕ) +
    (693593347561881600 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-74278008125390848 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (126815396331520 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (3183393694464 : ℝ)*u^(8 : ℕ)*a^(9 : ℕ)*w^(4 : ℕ) +
    (4057729408696320 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (105734469599625216 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-2634252442533888 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (-2116621996032 : ℝ)*u^(8 : ℕ)*a^(8 : ℕ)*w^(6 : ℕ) +
    (-55548680349941760 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (5906679208083456 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (-25418866163712 : ℝ)*u^(8 : ℕ)*a^(7 : ℕ)*w^(8 : ℕ) +
    (-5117650430590976 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (105451572166656 : ℝ)*u^(8 : ℕ)*a^(6 : ℕ)*w^(10 : ℕ) +
    (1384276549435392 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ) +
    (-113305196691456 : ℝ)*u^(8 : ℕ)*a^(5 : ℕ)*w^(12 : ℕ) +
    (53549652246528 : ℝ)*u^(8 : ℕ)*a^(4 : ℕ)*w^(14 : ℕ) +
    (-4329327034368 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ)*w^(16 : ℕ)) / (25048249270272 : ℝ)

/-- Drift degree 8 of the trailing determinant product. -/
def oddCompactProductCGrade8 (u a w : ℝ) : ℝ :=
  oddCompactProductCGrade8Part0 u a w +
    oddCompactProductCGrade8Part1 u a w

/-- Drift degree 8 of the trailing determinant product, block 0. -/
theorem oddCompactProductCGrade8Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade2 u a w =
      oddCompactProductCGrade8Part0 u a w := by
  unfold oddCompactCrossBDGrade2 oddCompactCrossBDGrade4 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactProductCGrade8Part0 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade6
  ring

/-- Drift degree 8 of the trailing determinant product, block 1. -/
theorem oddCompactProductCGrade8Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade0 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade1 u a w =
      oddCompactProductCGrade8Part1 u a w := by
  unfold oddCompactCrossBDGrade0 oddCompactCrossBDGrade1 oddCompactCrossBDGrade3 oddCompactCrossBDGrade5 oddCompactProductCGrade8Part1 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 8 of the trailing determinant product. -/
theorem oddCompactProductCGrade8_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade1 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade0 u a w =
      oddCompactProductCGrade8 u a w := by
  unfold oddCompactProductCGrade8
  linear_combination oddCompactProductCGrade8Part0_eq u a w + oddCompactProductCGrade8Part1_eq u a w

/-- Drift degree 9 of the trailing determinant product, block 0. -/
def oddCompactProductCGrade9Part0 (u a w : ℝ) : ℝ :=
  ((26931528575233228800 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-38913745649802854400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (99122694925595443200 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (14622549991542448128 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-93803294204428124160 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (1269108422571005952 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-21826339050907238400 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (26859482925048594432 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-1365958950432701824 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (63802749645477642240 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-6900303409227669504 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (265541304010491040 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (483101677191168000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-12677012313097273344 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (1120776424471547904 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-31159257396249176 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-19757922009431408640 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (1988439878916341760 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-19438842371335808 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-211483408911294 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (4135419663612641280 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-408438618049341440 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (3729905942685696 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (3773241540468 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (2125438284390727680 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (349945434673152000 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-24987983492744448 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (96573687091392 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-35164702881 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-1392936459797790720 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (108044940881534976 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-521474556981888 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-1299806017992 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-64744884220723200 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-199504144771842048 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (4941007676092416 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (3010661845632 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (186951103244402688 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-15293952359792640 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (74869548355584 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (342094145126400 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (18471160312233984 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (-325095159103488 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ) +
    (-7067641483100160 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ) +
    (535580868870144 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(11 : ℕ) +
    (-308431332311040 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(13 : ℕ) +
    (49275086045184 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(15 : ℕ)) / (28179280429056 : ℝ)

/-- Drift degree 9 of the trailing determinant product, block 1. -/
def oddCompactProductCGrade9Part1 (u a w : ℝ) : ℝ :=
  ((-5093812575129600 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (32352894625582080 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (88925117718528000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-28766341884003840 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-144892240537743360 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-427880365257600 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-18089079128064000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (32121292751032320 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-10525549781520 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (78596175377940480 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1726761696543744 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (366506774797596 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (556844875776000 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-10481874984161280 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (565278958319232 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-29642060998332 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-12833059332096000 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-45068839440384 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-148320712377872 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-537710737431 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (2465732663181312 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-64509390700544 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-1798330704744 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (-27189181644 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (593388613140480 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (220346038337536 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (9327590873088 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (84967851716 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (-346205868 : ℝ)*u^(9 : ℕ)*a^(10 : ℕ)*w^(1 : ℕ) +
    (-187949808353280 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (11940183564288 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (306890320128 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (-3400398270 : ℝ)*u^(9 : ℕ)*a^(9 : ℕ)*w^(3 : ℕ) +
    (-6500332339200 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (-12379437924352 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (134421405696 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (608733696 : ℝ)*u^(9 : ℕ)*a^(8 : ℕ)*w^(5 : ℕ) +
    (4093498097664 : ℝ)*u^(9 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (-373005484032 : ℝ)*u^(9 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (7802394624 : ℝ)*u^(9 : ℕ)*a^(7 : ℕ)*w^(7 : ℕ) +
    (64021856256 : ℝ)*u^(9 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (500170752 : ℝ)*u^(9 : ℕ)*a^(6 : ℕ)*w^(9 : ℕ)) / (1174136684544 : ℝ)

/-- Drift degree 9 of the trailing determinant product. -/
def oddCompactProductCGrade9 (u a w : ℝ) : ℝ :=
  oddCompactProductCGrade9Part0 u a w +
    oddCompactProductCGrade9Part1 u a w

/-- Drift degree 9 of the trailing determinant product, block 0. -/
theorem oddCompactProductCGrade9Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade4 u a w =
      oddCompactProductCGrade9Part0 u a w := by
  unfold oddCompactCrossBDGrade3 oddCompactCrossBDGrade4 oddCompactCrossBDGrade5 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade9Part0 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6
  ring

/-- Drift degree 9 of the trailing determinant product, block 1. -/
theorem oddCompactProductCGrade9Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade1 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade2 u a w =
      oddCompactProductCGrade9Part1 u a w := by
  unfold oddCompactCrossBDGrade1 oddCompactCrossBDGrade2 oddCompactProductCGrade9Part1 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 9 of the trailing determinant product. -/
theorem oddCompactProductCGrade9_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade1 u a w =
      oddCompactProductCGrade9 u a w := by
  unfold oddCompactProductCGrade9
  linear_combination oddCompactProductCGrade9Part0_eq u a w + oddCompactProductCGrade9Part1_eq u a w

/-- Drift degree 10 of the trailing determinant product, block 0. -/
def oddCompactProductCGrade10Part0 (u a w : ℝ) : ℝ :=
  ((-2303114921426092032000 : ℝ)*u^(10 : ℕ) +
    (6128515347783775027200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-5808677486253722173440 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-2843379012986162380800 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (2640398463027568558080 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (3367258472540484403200 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-654630856681873483776 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (770037701748011827200 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-1383425429973367062528 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (91631366684480114176 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-1179719328541055385600 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (279845884510520967168 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-7051780801000444416 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-46639819718708428800 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (374660425304169578496 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-27092992750354361856 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (223043617772589760 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (322063555498396876800 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-66387781945690324992 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1468517595873757696 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-1743810593460000 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (238416811366809600 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-50446247277429522432 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (4594358433072250880 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-110407150072229280 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (27404113412640 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-54869772177411932160 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (7213228974463647744 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-30669932910147072 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-194310754922544 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (938453401557 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (10430412594383683584 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-1065305155973234688 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (19577746222667520 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-19296166180032 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (3164382896345579520 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (1200012119245062144 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (-51597299070676992 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (192065409599616 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-2605485581949468672 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (200716578696462336 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (-1197191217623040 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-39367897063096320 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (-302738071407820800 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (5548752948953088 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (187169278670143488 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-11799809985871872 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ) +
    (35369055682560 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ) +
    (9925187579412480 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(12 : ℕ) +
    (-2586096445685760 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(14 : ℕ)) / (676302730297344 : ℝ)

/-- Drift degree 10 of the trailing determinant product, block 1. -/
def oddCompactProductCGrade10Part1 (u a w : ℝ) : ℝ :=
  ((-17092309893120000 : ℝ)*u^(10 : ℕ) +
    (92587734650880000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (-128850451494912000 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (-128875126173696000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (60925849947648000 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ) +
    (169785876024852480 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-5892292195776000 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ) +
    (32230878511104000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-36743723851714560 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (932332725878400 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ) +
    (-137121146386513920 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-4574249841444864 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-227099503008000 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ) +
    (-2039912792064000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (37157879537221632 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-469272559287168 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-772698074400 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ) +
    (28949908370227200 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (4069955345694720 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (522379943480960 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (122523880500 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ) +
    (30321672192000 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-22518169018564608 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (493470097754112 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-6203879173632 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (224059500 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ) +
    (-1569073020272640 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-2076806237257728 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-160113677443072 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-74033294496 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-108793125 : ℝ)*u^(10 : ℕ)*a^(10 : ℕ) +
    (4356416225673216 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-177575576829952 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-3981020682752 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (1599693432 : ℝ)*u^(10 : ℕ)*a^(9 : ℕ)*w^(2 : ℕ) +
    (32343117004800 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (410310439600128 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (368917970944 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (22402507776 : ℝ)*u^(10 : ℕ)*a^(8 : ℕ)*w^(4 : ℕ) +
    (-194443437146112 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (13956320067584 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (149756461056 : ℝ)*u^(10 : ℕ)*a^(7 : ℕ)*w^(6 : ℕ) +
    (-10869488484352 : ℝ)*u^(10 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (380129771520 : ℝ)*u^(10 : ℕ)*a^(6 : ℕ)*w^(8 : ℕ) +
    (1365799600128 : ℝ)*u^(10 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-21340618752 : ℝ)*u^(10 : ℕ)*a^(5 : ℕ)*w^(10 : ℕ)) / (18786186952704 : ℝ)

/-- Drift degree 10 of the trailing determinant product. -/
def oddCompactProductCGrade10 (u a w : ℝ) : ℝ :=
  oddCompactProductCGrade10Part0 u a w +
    oddCompactProductCGrade10Part1 u a w

/-- Drift degree 10 of the trailing determinant product, block 0. -/
theorem oddCompactProductCGrade10Part0_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade5 u a w =
      oddCompactProductCGrade10Part0 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade2 oddCompactCrossBDGrade4 oddCompactCrossBDGrade5 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade10Part0 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 10 of the trailing determinant product, block 1. -/
theorem oddCompactProductCGrade10Part1_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade0 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade3 u a w =
      oddCompactProductCGrade10Part1 u a w := by
  unfold oddCompactCrossBDGrade0 oddCompactCrossBDGrade3 oddCompactProductCGrade10Part1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade7
  ring

/-- Drift degree 10 of the trailing determinant product. -/
theorem oddCompactProductCGrade10_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade0 u a w =
      oddCompactProductCGrade10 u a w := by
  unfold oddCompactProductCGrade10
  linear_combination oddCompactProductCGrade10Part0_eq u a w + oddCompactProductCGrade10Part1_eq u a w

/-- Drift degree 11 of the trailing determinant product. -/
def oddCompactProductCGrade11 (u a w : ℝ) : ℝ :=
  ((-10554427920566476800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (8314286579730432000 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-33456282877005004800 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (1014889474445902848 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (24447039177060679680 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-2039037303651368448 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (7968543129088819200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-7013063095795777536 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (545696368374801344 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-12607093677862748160 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (1535841244695994368 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-66566624352562240 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-160919700583219200 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (2093261348817764352 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-100070235087020288 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (1284024354530802 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (3579414021934940160 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-483435086065606656 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (4011065520772032 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (29223313890783 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (-193649569538310144 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (7075280403740160 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-201059301568416 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (9353771019 : ℝ)*u^(11 : ℕ)*a^(9 : ℕ)*w^(1 : ℕ) +
    (-383629877402664960 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (35067157651611648 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (1449356491537536 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (-8188516046232 : ℝ)*u^(11 : ℕ)*a^(8 : ℕ)*w^(3 : ℕ) +
    (69091377245061120 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-4901863344500736 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (65464856960544 : ℝ)*u^(11 : ℕ)*a^(7 : ℕ)*w^(5 : ℕ) +
    (10225467260928000 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (9521769182920704 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (-234852896848896 : ℝ)*u^(11 : ℕ)*a^(6 : ℕ)*w^(7 : ℕ) +
    (-11694317141753856 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (626485010595840 : ℝ)*u^(11 : ℕ)*a^(5 : ℕ)*w^(9 : ℕ) +
    (-35369055682560 : ℝ)*u^(11 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ) +
    (-768715354275840 : ℝ)*u^(11 : ℕ)*a^(4 : ℕ)*w^(11 : ℕ) +
    (320578120581120 : ℝ)*u^(11 : ℕ)*a^(3 : ℕ)*w^(13 : ℕ)) / (63403380965376 : ℝ)

/-- Drift degree 11 of the trailing determinant product. -/
theorem oddCompactProductCGrade11_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade1 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade4 u a w =
      oddCompactProductCGrade11 u a w := by
  unfold oddCompactCrossBDGrade1 oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade3 oddCompactCrossBDGrade4 oddCompactCrossBDGrade5 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade11 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 12 of the trailing determinant product. -/
def oddCompactProductCGrade12 (u a w : ℝ) : ℝ :=
  ((1096594517782020096000 : ℝ)*u^(12 : ℕ) +
    (-2379435568589876428800 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ) +
    (1845474647582646927360 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ) +
    (828159116489323315200 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-684746535786414612480 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ) +
    (-778990180733802086400 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (134682048501139095552 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ) +
    (-222444532839481344000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (261453494992901197824 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-14094514783626182656 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ) +
    (227426061126550487040 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-41477076396804264960 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (690134825374689408 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ) +
    (13425699912391065600 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-61352398792137129984 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (3374095949052002816 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (-10459734740623824 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ) +
    (-46360519068155904000 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (8446103710778572800 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-237305079595818624 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (67662314991582 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ) +
    (-53764486594560000 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (5212774989554909184 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-262549546657585152 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (3707827513754808 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (2289976658343 : ℝ)*u^(12 : ℕ)*a^(9 : ℕ) +
    (7707459892354744320 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-1291924276568260608 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (23192755001754240 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-13905816756606 : ℝ)*u^(12 : ℕ)*a^(8 : ℕ)*w^(2 : ℕ) +
    (-99104391789281280 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (617388307255296 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (-164702252261664 : ℝ)*u^(12 : ℕ)*a^(7 : ℕ)*w^(4 : ℕ) +
    (-422072250154352640 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (42476236224528384 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (880072647270912 : ℝ)*u^(12 : ℕ)*a^(6 : ℕ)*w^(6 : ℕ) +
    (86483717943459840 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-3951221473050624 : ℝ)*u^(12 : ℕ)*a^(5 : ℕ)*w^(8 : ℕ) +
    (3840650017505280 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ) +
    (7666954066722816 : ℝ)*u^(12 : ℕ)*a^(4 : ℕ)*w^(10 : ℕ) +
    (-6050749725278208 : ℝ)*u^(12 : ℕ)*a^(3 : ℕ)*w^(12 : ℕ) +
    (-1522029035520 : ℝ)*u^(12 : ℕ)*a^(2 : ℕ)*w^(14 : ℕ)) / (1521681143169024 : ℝ)

/-- Drift degree 12 of the trailing determinant product. -/
theorem oddCompactProductCGrade12_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade2 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade5 u a w =
      oddCompactProductCGrade12 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade2 oddCompactCrossBDGrade4 oddCompactCrossBDGrade5 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade12 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 13 of the trailing determinant product. -/
def oddCompactProductCGrade13 (u a w : ℝ) : ℝ :=
  ((17250543605411020800 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2941407531139645440 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (60815395516022784000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-13765329936951773184 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-35280857060685250560 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (5576688598642573824 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-16207173550787788800 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (9544717106117591040 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-859949383917844736 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (13877854663072481280 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-1298404244432240640 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (40614309536474688 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (288984115445760000 : ℝ)*u^(13 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-2549721034161782784 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (50677554569811456 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (256604150297844 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (-3109871185082449920 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (335714760611610624 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (-4722349059264768 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-1949477732973 : ℝ)*u^(13 : ℕ)*a^(8 : ℕ)*w^(1 : ℕ) +
    (50340163714154496 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (12867395130645504 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-71981014095648 : ℝ)*u^(13 : ℕ)*a^(7 : ℕ)*w^(3 : ℕ) +
    (331045539309158400 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (-51036995945742336 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (571893002068608 : ℝ)*u^(13 : ℕ)*a^(6 : ℕ)*w^(5 : ℕ) +
    (5977779535872000 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (-842536092635136 : ℝ)*u^(13 : ℕ)*a^(5 : ℕ)*w^(7 : ℕ) +
    (-7154744803983360 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ) +
    (308686195261440 : ℝ)*u^(13 : ℕ)*a^(4 : ℕ)*w^(9 : ℕ) +
    (1709508491476992 : ℝ)*u^(13 : ℕ)*a^(3 : ℕ)*w^(11 : ℕ) +
    (12176232284160 : ℝ)*u^(13 : ℕ)*a^(2 : ℕ)*w^(13 : ℕ)) / (1141260857376768 : ℝ)

/-- Drift degree 13 of the trailing determinant product. -/
theorem oddCompactProductCGrade13_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade3 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade6 u a w =
      oddCompactProductCGrade13 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade3 oddCompactCrossBDGrade5 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade13 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 14 of the trailing determinant product. -/
def oddCompactProductCGrade14 (u a w : ℝ) : ℝ :=
  ((-66743261639147520000 : ℝ)*u^(14 : ℕ) +
    (117419332472141414400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ) +
    (-73540389309474078720 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ) +
    (-29831209270054502400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (21637724138801783808 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ) +
    (22341112261219491840 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3215350523398558720 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ) +
    (7648763952572006400 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-6057763765240035840 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (229453953961598336 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ) +
    (-5409434006432686080 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (781985653153485312 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-6170365007196400 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ) +
    (-456601921811251200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (1192932522738524160 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-62731756709741504 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (45978900978038 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ) +
    (717804059814789120 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-98417041528055808 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (2245810015499552 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (578559553272 : ℝ)*u^(14 : ℕ)*a^(8 : ℕ) +
    (1375845167923200 : ℝ)*u^(14 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-95002599552860160 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (3254154644871936 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (-4822536595107 : ℝ)*u^(14 : ℕ)*a^(7 : ℕ)*w^(2 : ℕ) +
    (-104481977617612800 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (11630103573680128 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-136193942803920 : ℝ)*u^(14 : ℕ)*a^(6 : ℕ)*w^(4 : ℕ) +
    (-2741362446827520 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (343476193448448 : ℝ)*u^(14 : ℕ)*a^(5 : ℕ)*w^(6 : ℕ) +
    (5217926098452480 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ) +
    (-826784721838080 : ℝ)*u^(14 : ℕ)*a^(4 : ℕ)*w^(8 : ℕ) +
    (81638468616192 : ℝ)*u^(14 : ℕ)*a^(3 : ℕ)*w^(10 : ℕ) +
    (-26373909381120 : ℝ)*u^(14 : ℕ)*a^(2 : ℕ)*w^(12 : ℕ)) / (570630428688384 : ℝ)

/-- Drift degree 14 of the trailing determinant product. -/
theorem oddCompactProductCGrade14_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade4 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade7 u a w =
      oddCompactProductCGrade14 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade4 oddCompactCrossBDGrade6 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade14 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 15 of the trailing determinant product. -/
def oddCompactProductCGrade15 (u a w : ℝ) : ℝ :=
  ((25519390643404800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-2058073990690775040 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-3081067177638297600 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (1446083307913708032 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (1437686397437460480 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-328004685218621952 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (975355015613644800 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-316735998342758400 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (25929017839074752 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-489656764104376320 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (25180109524975616 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-249263725135776 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-14790335555174400 : ℝ)*u^(15 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (86652986405781504 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-1827028733114240 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-2755161477705 : ℝ)*u^(15 : ℕ)*a^(7 : ℕ)*w^(1 : ℕ) +
    (62855810387804160 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-2709069473427456 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (25461681090144 : ℝ)*u^(15 : ℕ)*a^(6 : ℕ)*w^(3 : ℕ) +
    (-3144731181809664 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (-1957694221056 : ℝ)*u^(15 : ℕ)*a^(5 : ℕ)*w^(5 : ℕ) +
    (-6419593525985280 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ) +
    (449897442447360 : ℝ)*u^(15 : ℕ)*a^(4 : ℕ)*w^(7 : ℕ) +
    (-253944769413120 : ℝ)*u^(15 : ℕ)*a^(3 : ℕ)*w^(9 : ℕ) +
    (89326060830720 : ℝ)*u^(15 : ℕ)*a^(2 : ℕ)*w^(11 : ℕ)) / (855945643032576 : ℝ)

/-- Drift degree 15 of the trailing determinant product. -/
theorem oddCompactProductCGrade15_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade5 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade8 u a w =
      oddCompactProductCGrade15 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade5 oddCompactCrossBDGrade7 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade15 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 16 of the trailing determinant product. -/
def oddCompactProductCGrade16 (u a w : ℝ) : ℝ :=
  ((18863545222771200000 : ℝ)*u^(16 : ℕ) +
    (-26603016965082316800 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ) +
    (13164091601261460480 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ) +
    (4839472525601664000 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-2950011607383376128 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ) +
    (-2899576060009816320 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (309218082265528896 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ) +
    (-1111213846217318400 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (640334799515186496 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-13339700504040216 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ) +
    (551466652222448640 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-71250900225570096 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (174449762101330 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ) +
    (64863876202905600 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-85803889591668480 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (3970968190871612 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (271727575335 : ℝ)*u^(16 : ℕ)*a^(7 : ℕ) +
    (-45061317920563200 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (3803511922362752 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-32424480191553 : ℝ)*u^(16 : ℕ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (-138309186355200 : ℝ)*u^(16 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (6826416287929344 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-143239433687040 : ℝ)*u^(16 : ℕ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (4118052564910080 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-82506041867520 : ℝ)*u^(16 : ℕ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-11035446620160 : ℝ)*u^(16 : ℕ)*a^(3 : ℕ)*w^(8 : ℕ) +
    (-164950949560320 : ℝ)*u^(16 : ℕ)*a^(2 : ℕ)*w^(10 : ℕ)) / (1283918464548864 : ℝ)

/-- Drift degree 16 of the trailing determinant product. -/
theorem oddCompactProductCGrade16_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade6 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade9 u a w =
      oddCompactProductCGrade16 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade6 oddCompactCrossBDGrade8 oddCompactCrossBDGrade9 oddCompactProductCGrade16 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 17 of the trailing determinant product. -/
def oddCompactProductCGrade17 (u a w : ℝ) : ℝ :=
  ((-373929929020800000 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (623841284163559680 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (283890332346163200 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-241387410506046528 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-103945795373998080 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (30811879238064240 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-122520121941196800 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (16839745089553920 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (-922717007296492 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (40033047545579520 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-1421625988575488 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-1519688626059 : ℝ)*u^(17 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (1486823753318400 : ℝ)*u^(17 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-4400492464404480 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (79648282008768 : ℝ)*u^(17 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-1756554989322240 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-3378232702464 : ℝ)*u^(17 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (174645017935872 : ℝ)*u^(17 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (147918202306560 : ℝ)*u^(17 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (1925877696823296 : ℝ)

/-- Drift degree 17 of the trailing determinant product. -/
theorem oddCompactProductCGrade17_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade7 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade17 u a w =
      oddCompactProductCGrade17 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade7 oddCompactCrossBDGrade9 oddCompactProductCGrade17 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 18 of the trailing determinant product. -/
def oddCompactProductCGrade18 (u a w : ℝ) : ℝ :=
  ((-4128094891065600000 : ℝ)*u^(18 : ℕ) +
    (4580825450272704000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ) +
    (-1733075280367009920 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ) +
    (-592649286382483200 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (279486848112671712 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ) +
    (286973830446485760 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-18745538037543152 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ) +
    (109314880363008000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-52063951363154160 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (421202172560286 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ) +
    (-36000611624390400 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (4304085730327704 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-1540022088507 : ℝ)*u^(18 : ℕ)*a^(6 : ℕ) +
    (-6112138275532800 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (3061440088790400 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-82117574754111 : ℝ)*u^(18 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (2141120019087360 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-79016685684960 : ℝ)*u^(18 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (8221409280000 : ℝ)*u^(18 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-194463878297856 : ℝ)*u^(18 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-41658983976960 : ℝ)*u^(18 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ)) / (2888816545234944 : ℝ)

/-- Drift degree 18 of the trailing determinant product. -/
theorem oddCompactProductCGrade18_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade8 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade17 u a w =
      oddCompactProductCGrade18 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade8 oddCompactProductCGrade18 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 19 of the trailing determinant product. -/
def oddCompactProductCGrade19 (u a w : ℝ) : ℝ :=
  ((114154947100742400 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-101323359815374080 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-10133204567500800 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (22819913266690992 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (2895302843942400 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-1369454961888184 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (10195013270937600 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-575557295861760 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (8802867770739 : ℝ)*u^(19 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-2126963568522240 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (72957393279360 : ℝ)*u^(19 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (-88380149760000 : ℝ)*u^(19 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (68524125952512 : ℝ)*u^(19 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (16099110236160 : ℝ)*u^(19 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (4333224817852416 : ℝ)

/-- Drift degree 19 of the trailing determinant product. -/
theorem oddCompactProductCGrade19_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade9 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade17 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade12 u a w =
      oddCompactProductCGrade19 u a w := by
  unfold oddCompactCrossBDGrade11 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade9 oddCompactProductCGrade19 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 20 of the trailing determinant product. -/
def oddCompactProductCGrade20 (u a w : ℝ) : ℝ :=
  ((231356689004448000 : ℝ)*u^(20 : ℕ) +
    (-196362679759689600 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ) +
    (54111268801379520 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ) +
    (18246940631683200 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-5776677145052552 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ) +
    (-7129112087214240 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (214292778264520 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ) +
    (-2241174313728000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (964158810765284 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-1819260398057 : ℝ)*u^(20 : ℕ)*a^(5 : ℕ) +
    (396428917888320 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-35188703763365 : ℝ)*u^(20 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (114658395264000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-10176785672720 : ℝ)*u^(20 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-22037399032320 : ℝ)*u^(20 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-73156608000 : ℝ)*u^(20 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (2166612408926208 : ℝ)

/-- Drift degree 20 of the trailing determinant product. -/
theorem oddCompactProductCGrade20_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade10 u a w +
      (-1)*oddCompactReflectedScalar6Grade0 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade17 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade13 u a w =
      oddCompactProductCGrade20 u a w := by
  unfold oddCompactCrossBDGrade10 oddCompactCrossBDGrade12 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade20 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 21 of the trailing determinant product. -/
def oddCompactProductCGrade21 (u a w : ℝ) : ℝ :=
  ((-6136056348508800 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (3203487635920800 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-253308231590400 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-373448855543444 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (25505516494080 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (7040661958225 : ℝ)*u^(21 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-168510295296000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (8272647359840 : ℝ)*u^(21 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (15829389313920 : ℝ)*u^(21 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (786433536000 : ℝ)*u^(21 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (3249918613389312 : ℝ)

/-- Drift degree 21 of the trailing determinant product. -/
theorem oddCompactProductCGrade21_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade11 u a w +
      (-1)*oddCompactReflectedScalar6Grade1 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade17 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade14 u a w =
      oddCompactProductCGrade21 u a w := by
  unfold oddCompactCrossBDGrade11 oddCompactCrossBDGrade13 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade21 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 22 of the trailing determinant product. -/
def oddCompactProductCGrade22 (u a w : ℝ) : ℝ :=
  ((-29359268001504000 : ℝ)*u^(22 : ℕ) +
    (18259980737198400 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ) +
    (-3401760781934880 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ) +
    (-1241899667719200 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (209655563859550 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ) +
    (362554790766960 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3185963575596 : ℝ)*u^(22 : ℕ)*a^(4 : ℕ) +
    (72427854240000 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-24951245625907 : ℝ)*u^(22 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-2995078065840 : ℝ)*u^(22 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-2920548960000 : ℝ)*u^(22 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (4874877920083968 : ℝ)

/-- Drift degree 22 of the trailing determinant product. -/
theorem oddCompactProductCGrade22_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade2 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade12 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade17 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade15 u a w =
      oddCompactProductCGrade22 u a w := by
  unfold oddCompactCrossBDGrade12 oddCompactCrossBDGrade14 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade22 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 23 of the trailing determinant product. -/
def oddCompactProductCGrade23 (u a w : ℝ) : ℝ :=
  ((584890137770400 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-165450482577840 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (32496312240000 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (7103757099311 : ℝ)*u^(23 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-1174292350560 : ℝ)*u^(23 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (3769851456000 : ℝ)*u^(23 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (7312316880125952 : ℝ)

/-- Drift degree 23 of the trailing determinant product. -/
theorem oddCompactProductCGrade23_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade3 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade13 u a w +
      (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade17 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade16 u a w =
      oddCompactProductCGrade23 u a w := by
  unfold oddCompactCrossBDGrade13 oddCompactCrossBDGrade15 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade23 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 24 of the trailing determinant product. -/
def oddCompactProductCGrade24 (u a w : ℝ) : ℝ :=
  ((5445714316140000 : ℝ)*u^(24 : ℕ) +
    (-2318558124909600 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ) +
    (256689535151520 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ) +
    (113780403135000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-6768938930779 : ℝ)*u^(24 : ℕ)*a^(3 : ℕ) +
    (-18321175574730 : ℝ)*u^(24 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1458845640000 : ℝ)*u^(24 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (21936950640377856 : ℝ)

/-- Drift degree 24 of the trailing determinant product. -/
theorem oddCompactProductCGrade24_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade16 u a w +
      (-1)*oddCompactReflectedScalar6Grade4 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade14 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade17 u a w =
      oddCompactProductCGrade24 u a w := by
  unfold oddCompactCrossBDGrade14 oddCompactCrossBDGrade16 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade24 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 25 of the trailing determinant product. -/
def oddCompactProductCGrade25 (u a w : ℝ) : ℝ :=
  ((-3455218021500 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (392802002285 : ℝ)*u^(25 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-117196632000 : ℝ)*u^(25 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (1828079220031488 : ℝ)

/-- Drift degree 25 of the trailing determinant product. -/
theorem oddCompactProductCGrade25_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade5 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade15 u a w +
      (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade17 u a w =
      oddCompactProductCGrade25 u a w := by
  unfold oddCompactCrossBDGrade15 oddCompactCrossBDGrade17 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade25 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 26 of the trailing determinant product. -/
def oddCompactProductCGrade26 (u a w : ℝ) : ℝ :=
  ((-4303070730000 : ℝ)*u^(26 : ℕ) +
    (1109547295500 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ) +
    (-54218314255 : ℝ)*u^(26 : ℕ)*a^(2 : ℕ) +
    (-32487036750 : ℝ)*u^(26 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (609359740010496 : ℝ)

/-- Drift degree 26 of the trailing determinant product. -/
theorem oddCompactProductCGrade26_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade6 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade18 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade16 u a w =
      oddCompactProductCGrade26 u a w := by
  unfold oddCompactCrossBDGrade16 oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade26 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 27 of the trailing determinant product. -/
def oddCompactProductCGrade27 (u a w : ℝ) : ℝ :=
  ((974946875 : ℝ)*u^(27 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (50779978334208 : ℝ)

/-- Drift degree 27 of the trailing determinant product. -/
theorem oddCompactProductCGrade27_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade7 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade17 u a w =
      oddCompactProductCGrade27 u a w := by
  unfold oddCompactCrossBDGrade17 oddCompactCrossBDGrade20 oddCompactProductCGrade27 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade7
  ring

/-- Drift degree 28 of the trailing determinant product. -/
def oddCompactProductCGrade28 (u a _w : ℝ) : ℝ :=
  ((18888581250 : ℝ)*u^(28 : ℕ) +
    (-2200155125 : ℝ)*u^(28 : ℕ)*a^(1 : ℕ)) / (152339935002624 : ℝ)

/-- Drift degree 28 of the trailing determinant product. -/
theorem oddCompactProductCGrade28_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade8 u a w*oddCompactCrossBDGrade20 u a w +
      (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade18 u a w =
      oddCompactProductCGrade28 u a w := by
  unfold oddCompactCrossBDGrade18 oddCompactCrossBDGrade20 oddCompactProductCGrade28 oddCompactReflectedScalar6Grade10 oddCompactReflectedScalar6Grade8
  ring

/-- Drift degree 30 of the trailing determinant product. -/
def oddCompactProductCGrade30 (u _a _w : ℝ) : ℝ :=
  ((-1071875 : ℝ)*u^(30 : ℕ)) / (1057916215296 : ℝ)

/-- Drift degree 30 of the trailing determinant product. -/
theorem oddCompactProductCGrade30_eq (u a w : ℝ) :
    (-1)*oddCompactReflectedScalar6Grade10 u a w*oddCompactCrossBDGrade20 u a w =
      oddCompactProductCGrade30 u a w := by
  unfold oddCompactCrossBDGrade20 oddCompactProductCGrade30 oddCompactReflectedScalar6Grade10
  ring

/-- The trailing determinant product, stored as its drift grades. -/
def oddCompactProductC (u a w : ℝ) : ℝ :=
  oddCompactProductCGrade0 u a w +
    oddCompactProductCGrade1 u a w +
    oddCompactProductCGrade2 u a w +
    oddCompactProductCGrade3 u a w +
    oddCompactProductCGrade4 u a w +
    oddCompactProductCGrade5 u a w +
    oddCompactProductCGrade6 u a w +
    oddCompactProductCGrade7 u a w +
    oddCompactProductCGrade8 u a w +
    oddCompactProductCGrade9 u a w +
    oddCompactProductCGrade10 u a w +
    oddCompactProductCGrade11 u a w +
    oddCompactProductCGrade12 u a w +
    oddCompactProductCGrade13 u a w +
    oddCompactProductCGrade14 u a w +
    oddCompactProductCGrade15 u a w +
    oddCompactProductCGrade16 u a w +
    oddCompactProductCGrade17 u a w +
    oddCompactProductCGrade18 u a w +
    oddCompactProductCGrade19 u a w +
    oddCompactProductCGrade20 u a w +
    oddCompactProductCGrade21 u a w +
    oddCompactProductCGrade22 u a w +
    oddCompactProductCGrade23 u a w +
    oddCompactProductCGrade24 u a w +
    oddCompactProductCGrade25 u a w +
    oddCompactProductCGrade26 u a w +
    oddCompactProductCGrade27 u a w +
    oddCompactProductCGrade28 u a w +
    oddCompactProductCGrade30 u a w

/-- Exact product expansion used in the determinant. -/
theorem oddCompactProductC_eq (u a w : ℝ) :
    (-oddCompactReflectedScalar6 u a w)*oddCompactCrossBD u a w = oddCompactProductC u a w := by
  rw [oddCompactReflectedScalar6_grades]
  unfold oddCompactProductC oddCompactCrossBD
  linear_combination oddCompactProductCGrade0_eq u a w +
    oddCompactProductCGrade1_eq u a w +
    oddCompactProductCGrade2_eq u a w +
    oddCompactProductCGrade3_eq u a w +
    oddCompactProductCGrade4_eq u a w +
    oddCompactProductCGrade5_eq u a w +
    oddCompactProductCGrade6_eq u a w +
    oddCompactProductCGrade7_eq u a w +
    oddCompactProductCGrade8_eq u a w +
    oddCompactProductCGrade9_eq u a w +
    oddCompactProductCGrade10_eq u a w +
    oddCompactProductCGrade11_eq u a w +
    oddCompactProductCGrade12_eq u a w +
    oddCompactProductCGrade13_eq u a w +
    oddCompactProductCGrade14_eq u a w +
    oddCompactProductCGrade15_eq u a w +
    oddCompactProductCGrade16_eq u a w +
    oddCompactProductCGrade17_eq u a w +
    oddCompactProductCGrade18_eq u a w +
    oddCompactProductCGrade19_eq u a w +
    oddCompactProductCGrade20_eq u a w +
    oddCompactProductCGrade21_eq u a w +
    oddCompactProductCGrade22_eq u a w +
    oddCompactProductCGrade23_eq u a w +
    oddCompactProductCGrade24_eq u a w +
    oddCompactProductCGrade25_eq u a w +
    oddCompactProductCGrade26_eq u a w +
    oddCompactProductCGrade27_eq u a w +
    oddCompactProductCGrade28_eq u a w +
    oddCompactProductCGrade30_eq u a w

end
end HTGeometry
