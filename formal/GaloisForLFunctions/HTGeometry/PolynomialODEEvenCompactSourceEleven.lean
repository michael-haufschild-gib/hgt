import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactSourceJets

/-! # Exact arbitrary-center modular source jet of order 11 -/
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
def evenCompactSourceJet11 : ModularThetaLyapunovPolynomial :=
  ((((((C (18669247841 / 512 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    (C (-178206017 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (45051655 / 4 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5)) +
    ((C (-827541 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (19560 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^9) +
    (C (-128 : ℂ) * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^11 +
    C (534618051 / 64 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1))) +
    ((C (-315361585 / 32 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    (C (27308853 / 16 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5 +
    C (-73350 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^7)) +
    ((C (760 : ℂ) * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^9 +
    C (10677242235 / 4096 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1) +
    (C (-657895095 / 512 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (13914495 / 128 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^5)))) +
    (((C (-3735 / 2 : ℂ) * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^7 +
    (C (-2018372499 / 8192 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (227773755 / 1024 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^3)) +
    ((C (-965625 / 32 : ℂ) * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^5 +
    C (-1129890735 / 131072 : ℂ) * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^1) +
    (C (32329965 / 8192 : ℂ) * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^3 +
    C (-11066607 / 131072 : ℂ) * X ModularThetaLyapunovState.A^6 * X ModularThetaLyapunovState.W^1))) +
    (((C (-3201037295 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 +
    C (130684734887 / 6144 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1) +
    (C (-1247442119 / 16 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (765878135 / 16 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4)) +
    ((C (-26757159 / 4 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (259170 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8) +
    (C (-2528 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^10 +
    C (-178206017 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2))))) +
    ((((C (-10406932305 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    (C (1170970515 / 128 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (-11655315 / 16 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6)) +
    ((C (12015 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^8 +
    C (41222264325 / 16384 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3) +
    (C (-9297423135 / 2048 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2 +
    C (410332125 / 512 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4))) +
    (((C (-187355 / 8 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^6 +
    C (-14302391103 / 131072 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4) +
    (C (2782422225 / 8192 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (-88357725 / 1024 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^4)) +
    ((C (-1919312775 / 524288 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^5 +
    C (220827255 / 32768 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^2) +
    (C (-86361321 / 1048576 : ℂ) * X ModularThetaLyapunovState.S^1 * X ModularThetaLyapunovState.A^6 +
    C (-3029502289 / 96 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1)))) +
    (((C (32932759805 / 576 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    (C (-73099455 / 4 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5 +
    C (2571325 / 2 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7)) +
    ((C (-178960 / 9 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^9 +
    C (-11668378645 / 3072 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1) +
    (C (453768315 / 32 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (-81587205 / 32 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5))) +
    (((C (73260 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^7 +
    C (-18201764295 / 4096 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1) +
    (C (2056395775 / 1024 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3 +
    C (-7069195 / 64 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^5)) +
    ((C (2261681235 / 16384 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (-136932625 / 1536 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^3) +
    (C (217730835 / 65536 : ℂ) * X ModularThetaLyapunovState.S^2 * X ModularThetaLyapunovState.A^5 * X ModularThetaLyapunovState.W^1 +
    C (93346239205 / 9216 : ℂ) * X ModularThetaLyapunovState.S^3)))))) +
    (((((C (-42591238063 / 3456 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 +
    (C (126009479035 / 6912 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-924547195 / 48 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4)) +
    ((C (70964495 / 24 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6 +
    C (-239060 / 3 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^8) +
    (C (1174721904125 / 221184 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 +
    C (2404926095 / 512 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2))) +
    (((C (-2841289675 / 768 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4 +
    C (5211535 / 24 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^6) +
    (C (-20984141035 / 16384 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 +
    C (25323895975 / 12288 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2)) +
    ((C (-63227675 / 256 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^4 +
    C (5071688765 / 262144 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^4) +
    (C (-1297296175 / 36864 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^2 +
    C (28653545 / 2359296 : ℂ) * X ModularThetaLyapunovState.S^3 * X ModularThetaLyapunovState.A^5)))) +
    (((C (26445321485 / 9216 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    (C (-6239199395 / 1152 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (440294785 / 144 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5)) +
    ((C (-1027265 / 6 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^7 +
    C (-20381875085 / 6144 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1) +
    (C (-216533275 / 128 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3 +
    C (30511985 / 96 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^5))) +
    (((C (124988591525 / 147456 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (-7493880275 / 27648 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^3) +
    (C (-533861125 / 147456 : ℂ) * X ModularThetaLyapunovState.S^4 * X ModularThetaLyapunovState.A^4 * X ModularThetaLyapunovState.W^1 +
    C (-6237210595 / 1152 : ℂ) * X ModularThetaLyapunovState.S^5)) +
    ((C (4898781809735 / 995328 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 +
    C (4285099247 / 4608 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2) +
    (C (1538016655 / 1728 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    C (-13240717 / 72 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^6))))) +
    ((((C (-267167290247 / 147456 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 +
    (C (1327011525 / 2048 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2 +
    C (1282170995 / 6912 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^4)) +
    ((C (254296615405 / 1769472 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^3 +
    C (-15188791135 / 110592 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^2) +
    (C (-30018487325 / 21233664 : ℂ) * X ModularThetaLyapunovState.S^5 * X ModularThetaLyapunovState.A^4 +
    C (-68672202599 / 82944 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1))) +
    (((C (-8222565155 / 20736 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-123894869 / 1944 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^5) +
    (C (218645591185 / 331776 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1 +
    C (-454125595 / 15552 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^3)) +
    ((C (-19934129495 / 663552 : ℂ) * X ModularThetaLyapunovState.S^6 * X ModularThetaLyapunovState.A^3 * X ModularThetaLyapunovState.W^1 +
    C (225483533275 / 165888 : ℂ) * X ModularThetaLyapunovState.S^7) +
    (C (-955290802895 / 995328 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 +
    C (-11431039225 / 248832 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2)))) +
    (((C (84738995 / 2592 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^4 +
    (C (455304213755 / 2654208 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^2 +
    C (-1928649895 / 27648 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^2)) +
    ((C (-127067551535 / 23887872 : ℂ) * X ModularThetaLyapunovState.S^7 * X ModularThetaLyapunovState.A^3 +
    C (840289247065 / 5971968 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1) +
    (C (19243650995 / 1119744 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^3 +
    C (-139314492755 / 5971968 : ℂ) * X ModularThetaLyapunovState.S^8 * X ModularThetaLyapunovState.A^2 * X ModularThetaLyapunovState.W^1))) +
    (((C (-39117403325 / 221184 : ℂ) * X ModularThetaLyapunovState.S^9 +
    C (16286547579845 / 214990848 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^1) +
    (C (-300674771035 / 40310784 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^2 +
    C (-6958882964045 / 1289945088 : ℂ) * X ModularThetaLyapunovState.S^9 * X ModularThetaLyapunovState.A^2)) +
    ((C (-394489736819 / 80621568 : ℂ) * X ModularThetaLyapunovState.S^10 * X ModularThetaLyapunovState.A^1 * X ModularThetaLyapunovState.W^1 +
    C (46113942875 / 3981312 : ℂ) * X ModularThetaLyapunovState.S^11) +
    (C (-6251467683829 / 2902376448 : ℂ) * X ModularThetaLyapunovState.S^11 * X ModularThetaLyapunovState.A^1 +
    C (-32534376875 / 107495424 : ℂ) * X ModularThetaLyapunovState.S^13)))))))

/-- The literal covariant recurrence supplies the new source derivative. -/
theorem evenCompactSourceJet11_eq : modularThetaLyapunovNormalizedSourceJet 11 =
    evenCompactSourceJet11 := by
  rw [show (11 : ℕ) = 10+1 by norm_num,
    modularThetaLyapunovNormalizedSourceJet_succ, oddCompactSourceJet10_eq]
  apply MvPolynomial.funext
  intro v
  simp [oddCompactSourceJet10, evenCompactSourceJet11,
    modularThetaLyapunovNormalizedLie, modularThetaLyapunovLie,
    modularThetaLyapunovVectorField, states_univ]
  ring

end
end HTGeometry
