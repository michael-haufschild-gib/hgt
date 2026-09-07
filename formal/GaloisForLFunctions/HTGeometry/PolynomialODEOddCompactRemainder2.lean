import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactRemainder1

/-!
# Nonnegative compact remainder, group 2

Every summand is a nonnegative monomial or a nonnegative monomial times
an exact unit-cube complement. This module proves only the remainder sign.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart16 (u t w : ℝ) : ℝ :=
  ((((((385706709876420009 / 2097152 : ℝ)*(u^4*t^4*w^6) +
    (81731203125 / 512 : ℝ)*(u^4*t^4*w^7)) +
    ((67455186639149421 / 1048576 : ℝ)*(u^4*t^4*w^8) +
    (8020464330771 / 16384 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 1 7)) +
    (((13197178413 / 2048 : ℝ)*(u^4*t^4*w^12) +
    (772425 / 16 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 1 11) +
    ((36 / 1 : ℝ)*(u^4*t^4*w^16) +
    (119310419304804142832499 / 8589934592 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 2 0))) +
    ((((34883574299296875 / 2097152 : ℝ)*(u^4*t^5*w^1) +
    (427019639330413614501 / 536870912 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 1 2 0) +
    ((836906321390625 / 131072 : ℝ)*(u^4*t^5*w^3) +
    (54163680870972485583 / 67108864 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 2 1)) +
    (((147285703125 / 8192 : ℝ)*(u^4*t^5*w^5) +
    (482442838946316999 / 8388608 : ℝ)*(u^4*t^5*w^6)) +
    ((2562328125 / 512 : ℝ)*(u^4*t^5*w^7) +
    (9127179674543925 / 1048576 : ℝ)*(u^4*t^5*w^8))))) +
    (((((1398631681881 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 2 7 +
    (1298853063 / 2048 : ℝ)*(u^4*t^5*w^12)) +
    ((71901 / 32 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 2 11 +
    (9079272526961138138739 / 4294967296 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 3 0)) +
    (((5987597828765625 / 2097152 : ℝ)*(u^4*t^6*w^1) +
    (661636995115113597447 / 4294967296 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 1 3 0) +
    ((5517694265625 / 16384 : ℝ)*(u^4*t^6*w^3) +
    (11709644687915903235 / 134217728 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 3 1))) +
    ((((4681546875 / 4096 : ℝ)*(u^4*t^6*w^5) +
    (77001088784406939 / 8388608 : ℝ)*(u^4*t^6*w^6)) +
    ((420332238197649 / 524288 : ℝ)*(u^4*t^6*w^8) +
    (6593362983 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 3 7)) +
    (((50356485 / 2048 : ℝ)*(u^4*t^6*w^12) +
    (1215 / 32 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 3 11) +
    ((219382759862869332249 / 1073741824 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 4 0 +
    (391300853484375 / 2097152 : ℝ)*(u^4*t^7*w^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart16_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart16 u t w := by
  unfold oddCompactRemainderPart16 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart17 (u t w : ℝ) : ℝ :=
  ((((((12668679447443746839 / 1073741824 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 1 4 0 +
    (904578890625 / 131072 : ℝ)*(u^4*t^7*w^3)) +
    ((19682919940724523 / 4194304 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 4 1 +
    (3737369871388575 / 4194304 : ℝ)*(u^4*t^7*w^6))) +
    (((26468540118873 / 524288 : ℝ)*(u^4*t^7*w^8) +
    (5604641667 / 32768 : ℝ)*(u^4*t^7*w^10)) +
    ((535815 / 2048 : ℝ)*(u^4*t^7*w^12) +
    (160085717384473727019 / 17179869184 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 5 0))) +
    ((((17392986984375 / 4194304 : ℝ)*(u^4*t^8*w^1) +
    (11522011464470927187 / 17179869184 : ℝ)*(u^4*t^8*w^2)) +
    ((16016659933315005 / 268435456 : ℝ)*(u^4*t^8*w^4) +
    (456565272244515 / 8388608 : ℝ)*(u^4*t^8*w^6))) +
    (((4217478083055 / 2097152 : ℝ)*(u^4*t^8*w^8) +
    (457661097 / 65536 : ℝ)*(u^4*t^8*w^10)) +
    ((3662918561698086123 / 8589934592 : ℝ)*(u^4*t^9) +
    (125509838542080255 / 536870912 : ℝ)*(u^4*t^9*w^2))))) +
    (((((3565190802384243 / 134217728 : ℝ)*(u^4*t^9*w^4) +
    (33219135741573 / 16777216 : ℝ)*(u^4*t^9*w^6)) +
    ((79091343783 / 2097152 : ℝ)*(u^4*t^9*w^8) +
    (867162807026755947 / 8589934592 : ℝ)*(u^4*t^10))) +
    (((189795186021945051 / 8589934592 : ℝ)*(u^4*t^10*w^2) +
    (429810218681589 / 268435456 : ℝ)*(u^4*t^10*w^4)) +
    ((551884793877 / 16777216 : ℝ)*(u^4*t^10*w^6) +
    (7817277123245745 / 1073741824 : ℝ)*(u^4*t^11)))) +
    ((((2126753200598751 / 2147483648 : ℝ)*(u^4*t^11*w^2) +
    (2272120981515 / 67108864 : ℝ)*(u^4*t^11*w^4)) +
    ((4456732426354971 / 17179869184 : ℝ)*(u^4*t^12) +
    (303517276505721 / 17179869184 : ℝ)*(u^4*t^12*w^2))) +
    (((32568482504439 / 8589934592 : ℝ)*(u^4*t^13) +
    (296601048119374140625 / 226492416 : ℝ)*(u^3)*oddCompactUnitSlack u t w 2 0 0) +
    ((2730582813584466795425675 / 231928233984 : ℝ)*(u^5*w^1) +
    (19538274729440640625 / 21233664 : ℝ)*(u^3*w^2)*oddCompactUnitSlack u t w 2 0 0)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart17_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart17 u t w := by
  unfold oddCompactRemainderPart17 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart18 (u t w : ℝ) : ℝ :=
  ((((((74722246358559492974555 / 9663676416 : ℝ)*(u^5*w^3) +
    (273220995581234375 / 1327104 : ℝ)*(u^5*w^4)) +
    ((630105825516951486169 / 100663296 : ℝ)*(u^5*w^5) +
    (366943884640625 / 27648 : ℝ)*(u^5*w^6))) +
    (((79017992577028067087 / 56623104 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 2 0 4 +
    (136719578125 / 864 : ℝ)*(u^5*w^8)) +
    ((614572376716613875 / 7077888 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 2 0 6 +
    (364334055555101 / 36864 : ℝ)*(u^5*w^11)))) +
    ((((175555315471 / 2304 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 2 0 10 +
    (3067157 / 36 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 2 0 12) +
    ((87100288767389453125 / 75497472 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 2 0 0 +
    (56989032918580855561373 / 9663676416 : ℝ)*(u^5*t^1*w^1))) +
    (((1109370083709015625 / 1179648 : ℝ)*(u^3*t^1*w^2)*oddCompactUnitSlack u t w 2 0 0 +
    (20302544616870089528343 / 1073741824 : ℝ)*(u^5*t^1*w^3)) +
    ((3777643863171875 / 13824 : ℝ)*(u^5*t^1*w^4) +
    (156858116464522154239 / 25165824 : ℝ)*(u^5*t^1*w^5))))) +
    (((((1573434296875 / 384 : ℝ)*(u^5*t^1*w^6) +
    (38342838301105313069 / 18874368 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 2 0 4) +
    ((19177859375 / 72 : ℝ)*(u^5*t^1*w^8) +
    (17610090325574081 / 589824 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 2 0 6)) +
    (((127434922405723 / 18432 : ℝ)*(u^5*t^1*w^11) +
    (41209712869 / 1152 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 2 0 10) +
    ((218705 / 2 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 2 0 12 +
    (3073015193469921875 / 8388608 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 2 0 0))) +
    ((((12644474331398905893583 / 12884901888 : ℝ)*(u^3*t^2*w^1)*oddCompactUnitSlack u t w 2 0 0 +
    (293963533407578125 / 786432 : ℝ)*(u^3*t^2*w^2)*oddCompactUnitSlack u t w 2 0 0) +
    ((58040014069260479561327 / 3221225472 : ℝ)*(u^5*t^2*w^3) +
    (5077613239234375 / 36864 : ℝ)*(u^5*t^2*w^4))) +
    (((71360584963733605909 / 33554432 : ℝ)*(u^5*t^2*w^5) +
    (85100546875 / 96 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 2 0 3) +
    ((1877350345597368905 / 1572864 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 2 0 4 +
    (1783140625 / 16 : ℝ)*(u^5*t^2*w^8))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart18_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart18 u t w := by
  unfold oddCompactRemainderPart18 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart19 (u t w : ℝ) : ℝ :=
  ((((((216908779605117 / 16384 : ℝ)*(u^5*t^2*w^9) +
    (22197524787929 / 12288 : ℝ)*(u^5*t^2*w^11)) +
    ((2508676471 / 768 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 2 0 10 +
    (89159 / 2 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 2 0 12)) +
    (((319512463986953125 / 8388608 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 2 0 0 +
    (33727365825997682921 / 536870912 : ℝ)*(u^3*t^3*w^1)*oddCompactUnitSlack u t w 2 0 0) +
    ((26527563002609375 / 393216 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 2 0 0 +
    (10000439235160094522105 / 1073741824 : ℝ)*(u^5*t^3*w^3)))) +
    ((((35255453703125 / 1024 : ℝ)*(u^5*t^3*w^4) +
    (67230472870423959 / 524288 : ℝ)*(u^5*t^3*w^5)) +
    ((244748359375 / 512 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 0 3 +
    (197544201573563655 / 524288 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 0 4)) +
    (((143421875 / 8 : ℝ)*(u^5*t^3*w^8) +
    (635683176084043 / 65536 : ℝ)*(u^5*t^3*w^9)) +
    ((50852786741 / 256 : ℝ)*(u^5*t^3*w^11) +
    (50299641 / 64 : ℝ)*(u^5*t^3*w^13))))) +
    (((((7824 / 1 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 0 12 +
    (39632197787109375 / 8388608 : ℝ)*(u^5*t^4)) +
    ((9863045219257505364843 / 8589934592 : ℝ)*(u^5*t^4*w^1) +
    (923099173546875 / 262144 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 2 1 0)) +
    (((1603292821417459913871 / 536870912 : ℝ)*(u^5*t^4*w^3) +
    (74580229109375 / 16384 : ℝ)*(u^5*t^4*w^4)) +
    ((1752319829089279809 / 16777216 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 1 2 +
    (61553671875 / 1024 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 1 3))) +
    ((((73961472587220975 / 1048576 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 1 4 +
    (32109375 / 32 : ℝ)*(u^5*t^4*w^8)) +
    ((314287529959299 / 131072 : ℝ)*(u^5*t^4*w^9) +
    (14524982139 / 4096 : ℝ)*(u^5*t^4*w^11))) +
    (((43841535 / 256 : ℝ)*(u^5*t^4*w^13) +
    (2349 / 4 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 1 12) +
    ((12904902144140625 / 8388608 : ℝ)*(u^5*t^5) +
    (410688248850195896007 / 536870912 : ℝ)*(u^5*t^5*w^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart19_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart19 u t w := by
  unfold oddCompactRemainderPart19 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart20 (u t w : ℝ) : ℝ :=
  ((((((75820156171875 / 131072 : ℝ)*(u^5*t^5*w^2) +
    (343230400509207959043 / 536870912 : ℝ)*(u^5*t^5*w^3)) +
    ((312071015625 / 1024 : ℝ)*(u^5*t^5*w^4) +
    (130753229607129555 / 4194304 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 2 2)) +
    (((1175203125 / 512 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 2 3 +
    (8440049844824895 / 1048576 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 2 4) +
    ((20266534114389 / 65536 : ℝ)*(u^5*t^5*w^9) +
    (2039420601 / 2048 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 2 8))) +
    ((((1335195 / 128 : ℝ)*(u^5*t^5*w^13) +
    (27 / 2 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 2 12) +
    ((1107471641484375 / 8388608 : ℝ)*(u^5*t^6) +
    (536114048364332047881 / 2147483648 : ℝ)*(u^5*t^6*w^1))) +
    (((24137265796875 / 262144 : ℝ)*(u^5*t^6*w^2) +
    (51487908613096398741 / 536870912 : ℝ)*(u^5*t^6*w^3)) +
    ((67179234375 / 8192 : ℝ)*(u^5*t^6*w^4) +
    (61319464651600011 / 16777216 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 3 2)))) +
    (((((286330900097115 / 524288 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 3 4 +
    (732454216245 / 32768 : ℝ)*(u^5*t^6*w^9)) +
    ((268554339 / 4096 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 3 8 +
    (44469 / 256 : ℝ)*(u^5*t^6*w^13))) +
    (((28988311640625 / 8388608 : ℝ)*(u^5*t^7) +
    (3373347894820953363 / 67108864 : ℝ)*(u^5*t^7*w^1)) +
    ((502659421875 / 131072 : ℝ)*(u^5*t^7*w^2) +
    (5586361873742805273 / 536870912 : ℝ)*(u^5*t^7*w^3)))) +
    ((((143221109844087 / 1048576 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 4 2 +
    (10378909381239 / 524288 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 4 4) +
    ((57526973145 / 65536 : ℝ)*(u^5*t^7*w^9) +
    (708345 / 1024 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 4 8)) +
    (((57486185591376208311 / 8589934592 : ℝ)*(u^5*t^8*w^1) +
    (882296999225372655 / 1073741824 : ℝ)*(u^5*t^8*w^3)) +
    ((347293048610079 / 33554432 : ℝ)*(u^5*t^8*w^5) +
    (512941382541 / 2097152 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 2 5 4)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart20_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart20 u t w := by
  unfold oddCompactRemainderPart20 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart21 (u t w : ℝ) : ℝ :=
  ((((((4085014923 / 262144 : ℝ)*(u^5*t^8*w^9) +
    (638321756755168629 / 1073741824 : ℝ)*(u^5*t^9*w^1)) +
    ((48707962027157043 / 1073741824 : ℝ)*(u^5*t^9*w^3) +
    (9904110159897 / 8388608 : ℝ)*(u^5*t^9*w^5))) +
    (((7578137979 / 2097152 : ℝ)*(u^5*t^9*w^7) +
    (145736593685651619 / 4294967296 : ℝ)*(u^5*t^10*w^1)) +
    ((1672430895431649 / 1073741824 : ℝ)*(u^5*t^10*w^3) +
    (1128019719537 / 33554432 : ℝ)*(u^5*t^10*w^5)))) +
    ((((602184367898325 / 536870912 : ℝ)*(u^5*t^11*w^1) +
    (26658738163845 / 1073741824 : ℝ)*(u^5*t^11*w^3)) +
    ((139578151413933 / 8589934592 : ℝ)*(u^5*t^12*w^1) +
    (2351664567520157510069093 / 86973087744 : ℝ)*(u^3)*oddCompactUnitSlack u t w 3 0 0)) +
    (((60565846712179046875 / 169869312 : ℝ)*(u^3*w^1)*oddCompactUnitSlack u t w 3 0 0 +
    (1055230487827940543311423 / 347892350976 : ℝ)*(u^6*w^2)) +
    ((946676613047796875 / 7962624 : ℝ)*(u^6*w^3) +
    (90996092084359828362203 / 21743271936 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 3 0 1)))) +
    (((((9004215059640625 / 1990656 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 3 0 2 +
    (1651265108505563877533 / 1358954496 : ℝ)*(u^6*w^6)) +
    ((9896394078125 / 6912 : ℝ)*(u^6*w^7) +
    (186045682901667581 / 3145728 : ℝ)*(u^6*w^8))) +
    (((19915781901837799 / 884736 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 3 0 7 +
    (43069077679183 / 82944 : ℝ)*(u^6*w^12)) +
    ((4140585943 / 2592 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 3 0 11 +
    (167042 / 81 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 3 0 13))) +
    ((((26461053085844419296085 / 536870912 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 3 0 0 +
    (34983153147981859375 / 169869312 : ℝ)*(u^3*t^1*w^1)*oddCompactUnitSlack u t w 3 0 0) +
    ((61719039164180938317559 / 38654705664 : ℝ)*(u^6*t^1*w^2) +
    (51037568317140625 / 442368 : ℝ)*(u^6*t^1*w^3))) +
    (((17266586733315957228335 / 3623878656 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 3 0 1 +
    (554097499671875 / 663552 : ℝ)*(u^6*t^1*w^5)) +
    ((796180212206455908857 / 452984832 : ℝ)*(u^6*t^1*w^6) +
    (197346359375 / 288 : ℝ)*(u^6*t^1*w^7))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart21_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart21 u t w := by
  unfold oddCompactRemainderPart21 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart22 (u t w : ℝ) : ℝ :=
  ((((((428879803811801 / 36864 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 3 0 5 +
    (15297486568712383 / 884736 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 3 0 7) +
    ((4594101758249 / 13824 : ℝ)*(u^6*t^1*w^12) +
    (584976511 / 864 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 3 0 11)) +
    (((39304 / 27 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 3 0 13 +
    (62732610704315014154995 / 1610612736 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 3 0 0) +
    ((175639114554640625 / 18874368 : ℝ)*(u^6*t^2*w^1) +
    (10625783709371463242813 / 12884901888 : ℝ)*(u^3*t^2*w^2)*oddCompactUnitSlack u t w 3 0 0))) +
    ((((6647823018484375 / 147456 : ℝ)*(u^6*t^2*w^3) +
    (4809045408355605105439 / 2415919104 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 3 0 1) +
    ((207902960734375 / 110592 : ℝ)*(u^6*t^2*w^5) +
    (39679787163966499619 / 37748736 : ℝ)*(u^6*t^2*w^6))) +
    (((11463046875 / 128 : ℝ)*(u^6*t^2*w^7) +
    (30785564298533725 / 786432 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 3 0 5) +
    ((1541131172643721 / 294912 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 3 0 7 +
    (705772157425 / 9216 : ℝ)*(u^6*t^2*w^12))))) +
    (((((6714767 / 144 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 3 0 11 +
    (1156 / 3 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 3 0 13) +
    ((28569857686424056396933 / 1610612736 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 3 0 0 +
    (215708948667359375 / 6291456 : ℝ)*(u^6*t^3*w^1))) +
    (((4036708306762819200519 / 4294967296 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 3 0 0 +
    (83997609109375 / 9216 : ℝ)*(u^6*t^3*w^3)) +
    ((26981036459199924533 / 100663296 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 0 1 +
    (20595841484375 / 36864 : ℝ)*(u^6*t^3*w^5)))) +
    ((((1449984450402397077 / 4194304 : ℝ)*(u^6*t^3*w^6) +
    (14984375 / 16 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 0 4) +
    ((74958005168625 / 4096 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 0 5 +
    (75113498726459 / 98304 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 0 7)) +
    (((5216163935 / 768 : ℝ)*(u^6*t^3*w^12) +
    (656189 / 48 : ℝ)*(u^6*t^3*w^14)) +
    ((136 / 3 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 0 13 +
    (5565516611375297362735 / 1073741824 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 3 1 0)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart22_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart22 u t w := by
  unfold oddCompactRemainderPart22 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart23 (u t w : ℝ) : ℝ :=
  ((((((67064043432828125 / 6291456 : ℝ)*(u^6*t^4*w^1) +
    (694246057482038761701 / 2147483648 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 3 1 0) +
    ((32621877015625 / 32768 : ℝ)*(u^6*t^4*w^3) +
    (8876128109853414285 / 134217728 : ℝ)*(u^6*t^4*w^4))) +
    (((1513993421875 / 24576 : ℝ)*(u^6*t^4*w^5) +
    (586385057080522423 / 8388608 : ℝ)*(u^6*t^4*w^6)) +
    ((147703125 / 256 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 1 4 +
    (2111505087957555 / 524288 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 1 5))) +
    ((((1630581720943 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 1 7 +
    (14060575 / 1024 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 1 9) +
    ((65413 / 32 : ℝ)*(u^6*t^4*w^14) +
    (2 / 1 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 1 13)) +
    (((272616840964705822641 / 268435456 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 3 2 0 +
    (3056646565171875 / 2097152 : ℝ)*(u^6*t^5*w^1)) +
    ((97409849986156823205 / 2147483648 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 3 2 0 +
    (870311765625 / 16384 : ℝ)*(u^6*t^5*w^3))))) +
    (((((2307871737300495801 / 67108864 : ℝ)*(u^6*t^5*w^4) +
    (18184609375 / 8192 : ℝ)*(u^6*t^5*w^5)) +
    ((77404008329589873 / 8388608 : ℝ)*(u^6*t^5*w^6) +
    (3963459721923 / 8192 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 2 5)) +
    (((6272025351 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 2 7 +
    (17519109 / 512 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 2 9) +
    ((1983 / 32 : ℝ)*(u^6*t^5*w^14) +
    (35875384495041480363 / 268435456 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 3 3 0))) +
    ((((190770280171875 / 2097152 : ℝ)*(u^6*t^6*w^1) +
    (3468509714499420897 / 2147483648 : ℝ)*(u^6*t^6*w^2)) +
    ((3654046875 / 4096 : ℝ)*(u^6*t^6*w^3) +
    (906460603613836245 / 134217728 : ℝ)*(u^6*t^6*w^4))) +
    (((3475364576454747 / 4194304 : ℝ)*(u^6*t^6*w^6) +
    (8338231518255 / 262144 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 3 5) +
    ((4220188821 / 32768 : ℝ)*(u^6*t^6*w^10) +
    (1393929 / 1024 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 3 3 9)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart23_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart23 u t w := by
  unfold oddCompactRemainderPart23 oddCompactUnitSlack
  positivity

end
end HTGeometry
