import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactRemainderGrade1

/-!
# Remainder groups, drift-graded (2)

On the unit cube `oddCompactUnitSlack u t w i j k = 1 - u^i t^j w^k`, so each
remainder group is a polynomial with exact drift grades.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 16 of remainder group 44 with its complements expanded. -/
def oddCompactRemainderPart44Grade16 (u t w : ℝ) : ℝ :=
  ((131223060102010071825 : ℝ)*u^(16 : ℕ) +
    (164981953974887473761 : ℝ)*u^(16 : ℕ)*t^(1 : ℕ) +
    (-296881542720000000 : ℝ)*u^(16 : ℕ)*w^(1 : ℕ) +
    (87961525784043592833 : ℝ)*u^(16 : ℕ)*t^(2 : ℕ) +
    (-214135997760000000 : ℝ)*u^(16 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (100318160464771427052 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ) +
    (28052235203306216985 : ℝ)*u^(16 : ℕ)*t^(3 : ℕ) +
    (-28543259520000000 : ℝ)*u^(16 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (158717862998070411720 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (5839392494604527595 : ℝ)*u^(16 : ℕ)*t^(4 : ℕ) +
    (96206665436207030340 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (12950681598399129584 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ) +
    (28425802234937096880 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (16876724898941015184 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (4259666710616002740 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(4 : ℕ) +
    (6659962917701290848 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (1184595616701056448 : ℝ)*u^(16 : ℕ)*w^(6 : ℕ) +
    (1071683789098120992 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ)*t^(3 : ℕ) +
    (25484657974117632 : ℝ)*u^(16 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ) +
    (64059142361232816 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ)*t^(4 : ℕ) +
    (-184690256381460864 : ℝ)*u^(16 : ℕ)*w^(6 : ℕ)*t^(2 : ℕ) +
    (83772788854569984 : ℝ)*u^(16 : ℕ)*w^(8 : ℕ) +
    (-43317207044616960 : ℝ)*u^(16 : ℕ)*w^(6 : ℕ)*t^(3 : ℕ) +
    (46812528432073728 : ℝ)*u^(16 : ℕ)*w^(8 : ℕ)*t^(1 : ℕ) +
    (-2901398986184256 : ℝ)*u^(16 : ℕ)*w^(6 : ℕ)*t^(4 : ℕ) +
    (8503630958932992 : ℝ)*u^(16 : ℕ)*w^(8 : ℕ)*t^(2 : ℕ) +
    (-5726767505817600 : ℝ)*u^(16 : ℕ)*w^(10 : ℕ) +
    (503194889143296 : ℝ)*u^(16 : ℕ)*w^(8 : ℕ)*t^(3 : ℕ) +
    (-2021780592230400 : ℝ)*u^(16 : ℕ)*w^(10 : ℕ)*t^(1 : ℕ) +
    (-178442569728000 : ℝ)*u^(16 : ℕ)*w^(10 : ℕ)*t^(2 : ℕ)) / (80244904034304 : ℝ)

/-- Remainder group 44, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart44_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart44 u t w =
      oddCompactRemainderPart44Grade3 u t w +
      oddCompactRemainderPart44Grade15 u t w +
      oddCompactRemainderPart44Grade16 u t w := by
  unfold oddCompactRemainderPart44 oddCompactRemainderPart44Grade3 oddCompactRemainderPart44Grade15 oddCompactRemainderPart44Grade16
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 45 with its complements expanded. -/
def oddCompactRemainderPart45Grade3 (u t w : ℝ) : ℝ :=
  ((557824612500000 : ℝ)*u^(3 : ℕ) +
    (185828512500000 : ℝ)*u^(3 : ℕ)*t^(1 : ℕ) +
    (4579039097798065 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) +
    (209547593110344 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ)) / (626913312768 : ℝ)

/-- Drift degree 16 of remainder group 45 with its complements expanded. -/
def oddCompactRemainderPart45Grade16 (u t w : ℝ) : ℝ :=
  ((3029596963012105 : ℝ)*u^(16 : ℕ)*t^(5 : ℕ) +
    (187788144602673 : ℝ)*u^(16 : ℕ)*t^(6 : ℕ) +
    (3007785082329 : ℝ)*u^(16 : ℕ)*t^(7 : ℕ) +
    (1212655107453656 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(5 : ℕ) +
    (26321364652020 : ℝ)*u^(16 : ℕ)*w^(2 : ℕ)*t^(6 : ℕ) +
    (1564131531632 : ℝ)*u^(16 : ℕ)*w^(4 : ℕ)*t^(5 : ℕ)) / (330225942528 : ℝ)

/-- Drift degree 17 of remainder group 45 with its complements expanded. -/
def oddCompactRemainderPart45Grade17 (u t w : ℝ) : ℝ :=
  ((-26775581400000000 : ℝ)*u^(17 : ℕ) +
    (-8919768600000000 : ℝ)*u^(17 : ℕ)*t^(1 : ℕ) +
    (18577154003373841489 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ) +
    (20677974476478998142 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (8767962544986313515 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (1538663279991787454 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ) +
    (1844053614625167828 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(3 : ℕ) +
    (1546794822454979826 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (209841242058666711 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(4 : ℕ) +
    (818062087892189868 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (-219792868535054640 : ℝ)*u^(17 : ℕ)*w^(5 : ℕ) +
    (13463452061565390 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(5 : ℕ) +
    (236432740532750820 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ)*t^(3 : ℕ) +
    (-10058284469296512 : ℝ)*u^(17 : ℕ)*w^(5 : ℕ)*t^(1 : ℕ) +
    (33424346240800182 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ)*t^(4 : ℕ) +
    (32711128066758816 : ℝ)*u^(17 : ℕ)*w^(5 : ℕ)*t^(2 : ℕ) +
    (45023795750490624 : ℝ)*u^(17 : ℕ)*w^(7 : ℕ) +
    (1794444903491850 : ℝ)*u^(17 : ℕ)*w^(3 : ℕ)*t^(5 : ℕ) +
    (7892123271819264 : ℝ)*u^(17 : ℕ)*w^(5 : ℕ)*t^(3 : ℕ) +
    (21520886882093568 : ℝ)*u^(17 : ℕ)*w^(7 : ℕ)*t^(1 : ℕ) +
    (531924073965072 : ℝ)*u^(17 : ℕ)*w^(5 : ℕ)*t^(4 : ℕ) +
    (3542414359444992 : ℝ)*u^(17 : ℕ)*w^(7 : ℕ)*t^(2 : ℕ) +
    (-1008159252480 : ℝ)*u^(17 : ℕ)*w^(9 : ℕ) +
    (202365162210816 : ℝ)*u^(17 : ℕ)*w^(7 : ℕ)*t^(3 : ℕ) +
    (2238103388160 : ℝ)*u^(17 : ℕ)*w^(9 : ℕ)*t^(1 : ℕ) +
    (426355384320 : ℝ)*u^(17 : ℕ)*w^(9 : ℕ)*t^(2 : ℕ)) / (30091839012864 : ℝ)

/-- Remainder group 45, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart45_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart45 u t w =
      oddCompactRemainderPart45Grade3 u t w +
      oddCompactRemainderPart45Grade16 u t w +
      oddCompactRemainderPart45Grade17 u t w := by
  unfold oddCompactRemainderPart45 oddCompactRemainderPart45Grade3 oddCompactRemainderPart45Grade16 oddCompactRemainderPart45Grade17
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 46 with its complements expanded. -/
def oddCompactRemainderPart46Grade3 (u t w : ℝ) : ℝ :=
  ((9709875000000 : ℝ)*u^(3 : ℕ) +
    (66027150000000 : ℝ)*u^(3 : ℕ)*w^(1 : ℕ) +
    (11651850000000 : ℝ)*u^(3 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (517336233146743 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) +
    (247044001756851 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (105969579728733 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (70975673818767 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(3 : ℕ)) / (940369969152 : ℝ)

/-- Drift degree 17 of remainder group 46 with its complements expanded. -/
def oddCompactRemainderPart46Grade17 (u t w : ℝ) : ℝ :=
  ((617031546325 : ℝ)*u^(17 : ℕ)*w^(1 : ℕ)*t^(6 : ℕ)) / (41278242816 : ℝ)

/-- Drift degree 18 of remainder group 46 with its complements expanded. -/
def oddCompactRemainderPart46Grade18 (u t w : ℝ) : ℝ :=
  ((7562468926490330497 : ℝ)*u^(18 : ℕ) +
    (8474554953635727654 : ℝ)*u^(18 : ℕ)*t^(1 : ℕ) +
    (-12677212800000000 : ℝ)*u^(18 : ℕ)*w^(1 : ℕ) +
    (4570551432729732519 : ℝ)*u^(18 : ℕ)*t^(2 : ℕ) +
    (-2237155200000000 : ℝ)*u^(18 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (12003796138217437340 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ) +
    (1391484230285471028 : ℝ)*u^(18 : ℕ)*t^(3 : ℕ) +
    (13451611542398802564 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (220077095421172527 : ℝ)*u^(18 : ℕ)*t^(4 : ℕ) +
    (5385866022495617112 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (816222847430969728 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ) +
    (14215017950970534 : ℝ)*u^(18 : ℕ)*t^(5 : ℕ) +
    (944516230426574280 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (280075379793688320 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (65203823747241 : ℝ)*u^(18 : ℕ)*t^(6 : ℕ) +
    (66477241279657548 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(4 : ℕ) +
    (-12041611372620288 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (-99328462008949056 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ) +
    (924761287383156 : ℝ)*u^(18 : ℕ)*w^(2 : ℕ)*t^(5 : ℕ) +
    (-12083332128996096 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(3 : ℕ) +
    (-47432431615804992 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ) +
    (-1009751468321664 : ℝ)*u^(18 : ℕ)*w^(4 : ℕ)*t^(4 : ℕ) +
    (-8304547935296448 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(2 : ℕ) +
    (2027242008944640 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ) +
    (-534245775885504 : ℝ)*u^(18 : ℕ)*w^(6 : ℕ)*t^(3 : ℕ) +
    (645552669265920 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ)*t^(1 : ℕ) +
    (50788955197440 : ℝ)*u^(18 : ℕ)*w^(8 : ℕ)*t^(2 : ℕ) +
    (-94755225600 : ℝ)*u^(18 : ℕ)*w^(10 : ℕ) +
    (-16721510400 : ℝ)*u^(18 : ℕ)*w^(10 : ℕ)*t^(1 : ℕ)) / (180551034077184 : ℝ)

/-- Drift degree 19 of remainder group 46 with its complements expanded. -/
def oddCompactRemainderPart46Grade19 (u _t w : ℝ) : ℝ :=
  ((-233037000000000 : ℝ)*u^(19 : ℕ) +
    (302096078314942583 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)) / (22568879259648 : ℝ)

/-- Remainder group 46, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart46_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart46 u t w =
      oddCompactRemainderPart46Grade3 u t w +
      oddCompactRemainderPart46Grade17 u t w +
      oddCompactRemainderPart46Grade18 u t w +
      oddCompactRemainderPart46Grade19 u t w := by
  unfold oddCompactRemainderPart46 oddCompactRemainderPart46Grade3 oddCompactRemainderPart46Grade17 oddCompactRemainderPart46Grade18 oddCompactRemainderPart46Grade19
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 47 with its complements expanded. -/
def oddCompactRemainderPart47Grade3 (u t w : ℝ) : ℝ :=
  ((282682598853943 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) +
    (169025577099951 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (31088957992029 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ)) / (2821109907456 : ℝ)

/-- Drift degree 19 of remainder group 47 with its complements expanded. -/
def oddCompactRemainderPart47Grade19 (u t w : ℝ) : ℝ :=
  ((662811048444252267 : ℝ)*u^(19 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
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

/-- Drift degree 20 of remainder group 47 with its complements expanded. -/
def oddCompactRemainderPart47Grade20 (u t w : ℝ) : ℝ :=
  ((296258412933169173 : ℝ)*u^(20 : ℕ) +
    (353735644054689151 : ℝ)*u^(20 : ℕ)*t^(1 : ℕ) +
    (162605511154793274 : ℝ)*u^(20 : ℕ)*t^(2 : ℕ) +
    (503570122343881488 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ) +
    (337489456585282944 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (69068389649623200 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (-26784816192701088 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ) +
    (-16223983643657376 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (-2984539967234784 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (431118384178560 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ) +
    (-1135604747520 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ) +
    (-7571534745600 : ℝ)*u^(20 : ℕ)*w^(8 : ℕ) +
    (-1336153190400 : ℝ)*u^(20 : ℕ)*w^(8 : ℕ)*t^(1 : ℕ)) / (270826551115776 : ℝ)

/-- Remainder group 47, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart47_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart47 u t w =
      oddCompactRemainderPart47Grade3 u t w +
      oddCompactRemainderPart47Grade19 u t w +
      oddCompactRemainderPart47Grade20 u t w := by
  unfold oddCompactRemainderPart47 oddCompactRemainderPart47Grade3 oddCompactRemainderPart47Grade19 oddCompactRemainderPart47Grade20
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 48 with its complements expanded. -/
def oddCompactRemainderPart48Grade3 (u t w : ℝ) : ℝ :=
  ((235445392324575 : ℝ)*u^(3 : ℕ)*t^(3 : ℕ) +
    (1469158966581760 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) +
    (967188376225152 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (437484406126080 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (570387970656144 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (73728621567360 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (505912899236256 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(3 : ℕ)) / (812479653347328 : ℝ)

/-- Drift degree 20 of remainder group 48 with its complements expanded. -/
def oddCompactRemainderPart48Grade20 (u t w : ℝ) : ℝ :=
  ((1142094318527666 : ℝ)*u^(20 : ℕ)*t^(3 : ℕ) +
    (60828939594035 : ℝ)*u^(20 : ℕ)*t^(4 : ℕ) +
    (-2906733238575 : ℝ)*u^(20 : ℕ)*t^(5 : ℕ) +
    (124759983172608 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ) +
    (-7041826798224 : ℝ)*u^(20 : ℕ)*w^(2 : ℕ)*t^(4 : ℕ) +
    (-6245838262176 : ℝ)*u^(20 : ℕ)*w^(4 : ℕ)*t^(3 : ℕ) +
    (-504675291520 : ℝ)*u^(20 : ℕ)*w^(6 : ℕ)*t^(2 : ℕ)) / (10030613004288 : ℝ)

/-- Drift degree 21 of remainder group 48 with its complements expanded. -/
def oddCompactRemainderPart48Grade21 (u t w : ℝ) : ℝ :=
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

/-- Drift degree 22 of remainder group 48 with its complements expanded. -/
def oddCompactRemainderPart48Grade22 (u t w : ℝ) : ℝ :=
  ((61306641760463779 : ℝ)*u^(22 : ℕ) +
    (50689700664850788 : ℝ)*u^(22 : ℕ)*t^(1 : ℕ) +
    (10923289705362762 : ℝ)*u^(22 : ℕ)*t^(2 : ℕ) +
    (25264395205397856 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ) +
    (2651279877676512 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (-2176173846506592 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (-1396127322760320 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ) +
    (-228536275167360 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ) +
    (3148082599680 : ℝ)*u^(22 : ℕ)*w^(4 : ℕ)*t^(2 : ℕ) +
    (-54476296761600 : ℝ)*u^(22 : ℕ)*w^(6 : ℕ) +
    (-9613464134400 : ℝ)*u^(22 : ℕ)*w^(6 : ℕ)*t^(1 : ℕ)) / (1828079220031488 : ℝ)

/-- Remainder group 48, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart48_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart48 u t w =
      oddCompactRemainderPart48Grade3 u t w +
      oddCompactRemainderPart48Grade20 u t w +
      oddCompactRemainderPart48Grade21 u t w +
      oddCompactRemainderPart48Grade22 u t w := by
  unfold oddCompactRemainderPart48 oddCompactRemainderPart48Grade3 oddCompactRemainderPart48Grade20 oddCompactRemainderPart48Grade21 oddCompactRemainderPart48Grade22
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade3 (u t w : ℝ) : ℝ :=
  ((90130918832960 : ℝ)*u^(3 : ℕ) +
    (117058733839680 : ℝ)*u^(3 : ℕ)*t^(1 : ℕ) +
    (1297387820765664 : ℝ)*u^(3 : ℕ)*t^(2 : ℕ) +
    (3178567518471360 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ) +
    (3484863718417593 : ℝ)*u^(3 : ℕ)*t^(3 : ℕ) +
    (1907420575927680 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (193964687078400 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) +
    (237617099328960 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (34229062425600 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (2949775876437984 : ℝ)*u^(3 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ)) / (16452712980283392 : ℝ)

/-- Drift degree 22 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade22 (u t w : ℝ) : ℝ :=
  ((-6955542874852 : ℝ)*u^(22 : ℕ)*t^(3 : ℕ) +
    (-6353261778975 : ℝ)*u^(22 : ℕ)*t^(4 : ℕ) +
    (-12138995376288 : ℝ)*u^(22 : ℕ)*w^(2 : ℕ)*t^(3 : ℕ)) / (67706637778944 : ℝ)

/-- Drift degree 23 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade23 (u t w : ℝ) : ℝ :=
  ((832057751506 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ) +
    (2537270019562 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (1081582671558 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (3730901641735 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ) +
    (116424877374 : ℝ)*u^(23 : ℕ)*w^(1 : ℕ)*t^(3 : ℕ) +
    (1380157783680 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ) +
    (127370007585 : ℝ)*u^(23 : ℕ)*w^(3 : ℕ)*t^(2 : ℕ) +
    (-37416027600 : ℝ)*u^(23 : ℕ)*w^(5 : ℕ) +
    (-6602828400 : ℝ)*u^(23 : ℕ)*w^(5 : ℕ)*t^(1 : ℕ)) / (3173748645888 : ℝ)

/-- Drift degree 24 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade24 (u t w : ℝ) : ℝ :=
  ((26859764401089 : ℝ)*u^(24 : ℕ) +
    (3508026708633 : ℝ)*u^(24 : ℕ)*t^(1 : ℕ) +
    (-4421688713883 : ℝ)*u^(24 : ℕ)*t^(2 : ℕ) +
    (-10901231193070 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ) +
    (-870917317839 : ℝ)*u^(24 : ℕ)*t^(3 : ℕ) +
    (-6599083126260 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ) +
    (-825059372670 : ℝ)*u^(24 : ℕ)*w^(2 : ℕ)*t^(2 : ℕ) +
    (509481875700 : ℝ)*u^(24 : ℕ)*w^(4 : ℕ) +
    (89908566300 : ℝ)*u^(24 : ℕ)*w^(4 : ℕ)*t^(1 : ℕ)) / (57127475625984 : ℝ)

/-- Drift degree 25 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade25 (u t w : ℝ) : ℝ :=
  ((1346046238160 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ) +
    (854427144930 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (108862865910 : ℝ)*u^(25 : ℕ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (135057571425 : ℝ)*u^(25 : ℕ)*w^(3 : ℕ) +
    (23833689075 : ℝ)*u^(25 : ℕ)*w^(3 : ℕ)*t^(1 : ℕ)) / (42845606719488 : ℝ)

/-- Drift degree 26 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade26 (u t w : ℝ) : ℝ :=
  ((-1408295606765 : ℝ)*u^(26 : ℕ) +
    (-1829042716245 : ℝ)*u^(26 : ℕ)*t^(1 : ℕ) +
    (-374085486990 : ℝ)*u^(26 : ℕ)*t^(2 : ℕ) +
    (-609577107300 : ℝ)*u^(26 : ℕ)*w^(2 : ℕ) +
    (-107572430700 : ℝ)*u^(26 : ℕ)*w^(2 : ℕ)*t^(1 : ℕ)) / (257073640316928 : ℝ)

/-- Drift degree 27 of remainder group 49 with its complements expanded. -/
def oddCompactRemainderPart49Grade27 (u _t w : ℝ) : ℝ :=
  ((3018794975 : ℝ)*u^(27 : ℕ)*w^(1 : ℕ)) / (7140934453248 : ℝ)

/-- Remainder group 49, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart49_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart49 u t w =
      oddCompactRemainderPart49Grade3 u t w +
      oddCompactRemainderPart49Grade22 u t w +
      oddCompactRemainderPart49Grade23 u t w +
      oddCompactRemainderPart49Grade24 u t w +
      oddCompactRemainderPart49Grade25 u t w +
      oddCompactRemainderPart49Grade26 u t w +
      oddCompactRemainderPart49Grade27 u t w := by
  unfold oddCompactRemainderPart49 oddCompactRemainderPart49Grade3 oddCompactRemainderPart49Grade22 oddCompactRemainderPart49Grade23 oddCompactRemainderPart49Grade24 oddCompactRemainderPart49Grade25 oddCompactRemainderPart49Grade26 oddCompactRemainderPart49Grade27
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

/-- Drift degree 3 of remainder group 50 with its complements expanded. -/
def oddCompactRemainderPart50Grade3 (u t _w : ℝ) : ℝ :=
  ((38917527425 : ℝ)*u^(3 : ℕ) +
    (13225203075 : ℝ)*u^(3 : ℕ)*t^(1 : ℕ)) / (171382426877952 : ℝ)

/-- Drift degree 27 of remainder group 50 with its complements expanded. -/
def oddCompactRemainderPart50Grade27 (u t w : ℝ) : ℝ :=
  ((177576175 : ℝ)*u^(27 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ)) / (2380311484416 : ℝ)

/-- Drift degree 28 of remainder group 50 with its complements expanded. -/
def oddCompactRemainderPart50Grade28 (u t _w : ℝ) : ℝ :=
  ((-38616544925 : ℝ)*u^(28 : ℕ) +
    (-13225203075 : ℝ)*u^(28 : ℕ)*t^(1 : ℕ)) / (171382426877952 : ℝ)

/-- Drift degree 30 of remainder group 50 with its complements expanded. -/
def oddCompactRemainderPart50Grade30 (u _t _w : ℝ) : ℝ :=
  ((-2786875 : ℝ)*u^(30 : ℕ)) / (1586874322944 : ℝ)

/-- Remainder group 50, drift-graded on the unit cube. -/
theorem oddCompactRemainderPart50_grades {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactRemainderPart50 u t w =
      oddCompactRemainderPart50Grade3 u t w +
      oddCompactRemainderPart50Grade27 u t w +
      oddCompactRemainderPart50Grade28 u t w +
      oddCompactRemainderPart50Grade30 u t w := by
  unfold oddCompactRemainderPart50 oddCompactRemainderPart50Grade3 oddCompactRemainderPart50Grade27 oddCompactRemainderPart50Grade28 oddCompactRemainderPart50Grade30
  simp only [oddCompactUnitSlack_eq hu0 hu1 ht0 ht1 hw0 hw1]
  ring

end
end HTGeometry
