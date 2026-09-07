import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactSourceEleven

/-! # Exact arbitrary-center modular source jet of order 12 -/
open MvPolynomial
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

private theorem states_univ : (Finset.univ : Finset ModularThetaLyapunovState) =
    {.S, .A, .W} := by
  ext i
  cases i <;> simp

/-- Exact normalized source polynomial at every modular state. -/
def evenCompactSourceJet12 : ModularThetaLyapunovPolynomial :=
  (((((((C (-9603111885 / 512 : ℂ) +
    C (72410457375 / 512 : ℂ) * X ModularThetaLyapunovState.A^1) +
    (C (-146977580081 / 256 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (5525348741 / 16 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4)) +
    ((C (-216717083 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (2784672 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8) +
    (C (-49520 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^10 +
    (C (256 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^12 +
    C (146977580081 / 8192 : ℂ) * X ModularThetaLyapunovState.A^2)))) +
    (((C (-82880231115 / 512 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (9752268735 / 128 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4) +
    (C (-7918911 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6 +
    C (473535 / 2 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^8)) +
    ((C (-1848 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^10 +
    C (281792785791 / 16384 : ℂ) * X ModularThetaLyapunovState.A^3) +
    (C (-74767393635 / 2048 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    (C (275421465 / 32 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4 +
    C (-7344435 / 16 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^6))))) +
    ((((C (22455 / 4 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^8 +
    C (-183992803467 / 131072 : ℂ) * X ModularThetaLyapunovState.A^4) +
    (C (2970635877 / 512 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (-5466943005 / 2048 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^4)) +
    ((C (8077905 / 32 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^6 +
    C (-2279863179 / 32768 : ℂ) * X ModularThetaLyapunovState.A^5) +
    (C (13698002655 / 65536 : ℂ) * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^2 +
    (C (-102788325 / 2048 : ℂ) * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^4 +
    C (-4153486905 / 2097152 : ℂ) * X ModularThetaLyapunovState.A^6)))) +
    (((C (246236679 / 131072 : ℂ) * X ModularThetaLyapunovState.A^6 * X ModularThetaLyapunovState.W^2 +
    C (82018251 / 4194304 : ℂ) * X ModularThetaLyapunovState.A^7) +
    (C (-146977580081 / 256 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    (C (93930928597 / 96 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-650151249 / 2 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5))) +
    ((C (29239056 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (-2426480 / 3 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^9) +
    (C (6016 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^11 +
    (C (-71829533633 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (1083585415 / 4 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3)))))) +
    (((((C (-59261301 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5 +
    C (3008340 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^7) +
    (C (-35560 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^9 +
    C (-157119885175 / 2048 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1)) +
    ((C (1456296435 / 32 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (-287602875 / 64 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^5) +
    (C (175425 / 2 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^7 +
    (C (2760219099 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (-2986894745 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^3)))) +
    (((C (28522755 / 32 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^5 +
    C (14632222215 / 65536 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^1) +
    (C (-940378995 / 8192 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^3 +
    C (368880669 / 131072 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^6 * X ModularThetaLyapunovState.W^1)) +
    ((C (24136819125 / 256 : ℂ) * X ModularThetaLyapunovState.S^2 +
    C (-3674439502025 / 18432 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1) +
    (C (524908130395 / 768 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    (C (-9752268735 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (109975206 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6))))) +
    ((((C (-5119130 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8 +
    C (172720 / 3 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^10) +
    (C (1331609046581 / 24576 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 +
    C (111609297745 / 512 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2)) +
    ((C (-2318964615 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (227027535 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6) +
    (C (-543585 / 2 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^8 +
    (C (-1717482882775 / 49152 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 +
    C (19309524795 / 256 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2)))) +
    (((C (-8111917625 / 512 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4 +
    C (8528765 / 16 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^6) +
    (C (18183821139 / 16384 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 +
    (C (-33218570005 / 8192 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (2524109475 / 2048 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^4))) +
    ((C (16860609835 / 524288 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^5 +
    C (-6389085105 / 65536 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^2) +
    (C (3473399655 / 2097152 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^6 +
    (C (1000088122121 / 6912 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (-323992039085 / 864 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3))))))) +
    ((((((C (177922492 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (-47560865 / 3 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7) +
    (C (7820080 / 27 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^9 +
    C (-18420952055 / 512 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1)) +
    ((C (-123005795 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (489087375 / 16 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5) +
    (C (-3165820 / 3 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^7 +
    (C (11621606205 / 256 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-114717583225 / 4608 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3)))) +
    (((C (308899045 / 192 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^5 +
    C (-64669006745 / 73728 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1) +
    (C (1192845475 / 1536 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^3 +
    C (-1732754155 / 65536 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^1)) +
    ((C (-5144215302835 / 55296 : ℂ) * X ModularThetaLyapunovState.S^4 +
    C (35577720543299 / 331776 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1) +
    (C (-16253781225 / 512 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    (C (433155085 / 4 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-392764785 / 16 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6))))) +
    ((((C (7385545 / 9 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8 +
    C (-25601872600205 / 442368 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2) +
    (C (-135897795 / 128 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (130787380325 / 4608 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4)) +
    ((C (-630408275 / 288 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6 +
    C (38885059895 / 4096 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3) +
    (C (-431379506075 / 24576 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    (C (23494129925 / 9216 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4 +
    C (-1917405873275 / 14155776 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^4)))) +
    (((C (8157692075 / 49152 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (13260308795 / 3145728 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^5) +
    (C (-88203852781 / 4608 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    (C (-3052181 / 72 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-3449522965 / 216 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5))) +
    ((C (69224363 / 54 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (13682817841 / 384 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1) +
    (C (985692505 / 216 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    (C (-649026413 / 288 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5 +
    C (-1148078851115 / 221184 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1)))))) +
    (((((C (56832283585 / 27648 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (200496515 / 147456 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1) +
    (C (2127259265285 / 55296 : ℂ) * X ModularThetaLyapunovState.S^6 +
    C (-111475149870623 / 2985984 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1)) +
    ((C (-14244722107 / 1728 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (3645071255 / 15552 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4) +
    (C (3630922211 / 3888 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    (C (670726969099 / 55296 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 +
    C (-1295490457555 / 165888 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2)))) +
    (((C (-28854659645 / 41472 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (-13026540439675 / 15925248 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^3) +
    (C (502235572825 / 663552 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (623972345345 / 42467328 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^4)) +
    ((C (13602545803 / 1728 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (299463308065 / 93312 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3) +
    (C (77647475 / 1944 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    (C (-1987903158085 / 497664 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (4104612295 / 7776 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3))))) +
    ((((C (251229740465 / 1990656 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-5423345002075 / 663552 : ℂ) * X ModularThetaLyapunovState.S^8) +
    (C (2854603561403 / 497664 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 +
    C (-465759607915 / 995328 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2)) +
    ((C (-51152909165 / 186624 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-87497219861375 / 95551488 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^2) +
    (C (830849303585 / 1990656 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    (C (5995417822985 / 191102976 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^3 +
    C (-67804737529955 / 80621568 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1)))) +
    (((C (-393903466045 / 10077696 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (5453415829225 / 53747712 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1) +
    (C (26051750725 / 27648 : ℂ) * X ModularThetaLyapunovState.S^10 +
    (C (-745027430605765 / 1934917632 : ℂ) * X ModularThetaLyapunovState.S^10 * X ModularThetaLyapunovState.A^1 +
    C (4418747660713 / 80621568 : ℂ) * X ModularThetaLyapunovState.S^10 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2))) +
    ((C (70230994693447 / 2579890176 : ℂ) * X ModularThetaLyapunovState.S^10 * X ModularThetaLyapunovState.A^2 +
    C (5171233601449 / 241864704 : ℂ) * X ModularThetaLyapunovState.S^11 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1) +
    (C (-4027755857125 / 71663616 : ℂ) * X ModularThetaLyapunovState.S^12 +
    (C (352472595269635 / 34828517376 : ℂ) * X ModularThetaLyapunovState.S^12 * X ModularThetaLyapunovState.A^1 +
    C (32534376875 / 23887872 : ℂ) * X ModularThetaLyapunovState.S^14))))))))

/-- The literal covariant recurrence supplies the new source derivative. -/
theorem evenCompactSourceJet12_eq : modularThetaLyapunovNormalizedSourceJet 12 =
    evenCompactSourceJet12 := by
  rw [show (12 : ℕ) = 11+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, evenCompactSourceJet11_eq]
  apply MvPolynomial.funext
  intro v
  simp [evenCompactSourceJet11, evenCompactSourceJet12,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ]
  ring

end
end HTGeometry
