import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactRemainder3

/-!
# Nonnegative compact remainder, group 4

Every summand is a nonnegative monomial or a nonnegative monomial times
an exact unit-cube complement. This module proves only the remainder sign.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart32 (u t w : ℝ) : ℝ :=
  ((((((128 / 27 : ℝ)*(u^9*t^3*w^15) +
    (60191966796875 / 3538944 : ℝ)*(u^9*t^4)) +
    ((6410349402682887917 / 2415919104 : ℝ)*(u^9*t^4*w^1) +
    (318290629390625 / 21233664 : ℝ)*(u^9*t^4*w^2))) +
    (((999389944714887017 / 905969664 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 1 0 +
    (66359375 / 12288 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 1 1) +
    ((15739208371953649 / 18874368 : ℝ)*(u^9*t^4*w^5) +
    (121188330414059 / 1179648 : ℝ)*(u^9*t^4*w^7)))) +
    ((((4906894879265 / 589824 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 1 6 +
    (4580787695 / 27648 : ℝ)*(u^9*t^4*w^11)) +
    ((467689 / 1728 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 1 10 +
    (858401328125 / 2359296 : ℝ)*(u^9*t^5))) +
    (((3041456059691304265 / 1207959552 : ℝ)*(u^9*t^5*w^1) +
    (1193738796875 / 1769472 : ℝ)*(u^9*t^5*w^2)) +
    ((901614938959861 / 33554432 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 2 0 +
    (1027414075148893 / 6291456 : ℝ)*(u^9*t^5*w^5))))) +
    (((((2052851615953 / 393216 : ℝ)*(u^9*t^5*w^7) +
    (34738822459 / 98304 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 2 6) +
    ((19427887 / 4608 : ℝ)*(u^9*t^5*w^11) +
    (493339421020460743 / 805306368 : ℝ)*(u^9*t^6*w^1))) +
    (((51836695997751 / 2097152 : ℝ)*(u^9*t^6*w^3) +
    (50966896824431 / 3145728 : ℝ)*(u^9*t^6*w^5)) +
    ((41490962303 / 393216 : ℝ)*(u^9*t^6*w^7) +
    (960056797 / 196608 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 6 3 6))) +
    ((((5437570627109945 / 67108864 : ℝ)*(u^9*t^7*w^1) +
    (34986610549239 / 8388608 : ℝ)*(u^9*t^7*w^3)) +
    ((1752852124617 / 2097152 : ℝ)*(u^9*t^7*w^5) +
    (97355889 / 131072 : ℝ)*(u^9*t^7*w^7))) +
    (((3340656572760969 / 536870912 : ℝ)*(u^9*t^8*w^1) +
    (19085721009249 / 67108864 : ℝ)*(u^9*t^8*w^3)) +
    ((77131477881 / 4194304 : ℝ)*(u^9*t^8*w^5) +
    (69632302911147 / 268435456 : ℝ)*(u^9*t^9*w^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart32_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart32 u t w := by
  unfold oddCompactRemainderPart32 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart33 (u t w : ℝ) : ℝ :=
  ((((((511126932627 / 67108864 : ℝ)*(u^9*t^9*w^3) +
    (2450346148917 / 536870912 : ℝ)*(u^9*t^10*w^1)) +
    ((418721678955996189261719 / 7044820107264 : ℝ)*(u^3)*oddCompactUnitSlack u t w 7 0 0 +
    (2459960882644796875 / 2579890176 : ℝ)*(u^10*w^1))) +
    (((49017614509005533514077 / 1761205026816 : ℝ)*(u^3*w^2)*oddCompactUnitSlack u t w 7 0 0 +
    (6267604979078125 / 143327232 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 7 0 0) +
    ((5206455389518560872305 / 220150628352 : ℝ)*(u^10*w^4) +
    (46272681171875 / 4478976 : ℝ)*(u^10*w^5)))) +
    ((((197435283169316835241 / 27518828544 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 7 0 3 +
    (3093203125 / 46656 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 7 0 4) +
    ((218266514509881001 / 191102976 : ℝ)*(u^10*w^8) +
    (1452204559222967 / 17915904 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 7 0 7)) +
    (((3152153595563 / 1679616 : ℝ)*(u^10*w^12) +
    (34705721 / 5832 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 7 0 11) +
    ((285219050263662852991 / 3623878656 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 7 0 0 +
    (205460009916203125 / 214990848 : ℝ)*(u^10*t^1*w^1))))) +
    (((((13928636541275493373573 / 587068342272 : ℝ)*(u^3*t^1*w^2)*oddCompactUnitSlack u t w 7 0 0 +
    (428457291359375 / 11943936 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 7 0 0) +
    ((479325742607622549395 / 18345885696 : ℝ)*(u^10*t^1*w^4) +
    (1659744296875 / 497664 : ℝ)*(u^10*t^1*w^5))) +
    (((66358009521818033795 / 9172942848 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 7 0 3 +
    (181953125 / 7776 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 7 0 4) +
    ((101034627740004527 / 95551488 : ℝ)*(u^10*t^1*w^8) +
    (370761825200747 / 5971968 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 7 0 7))) +
    ((((165875150617 / 139968 : ℝ)*(u^10*t^1*w^12) +
    (6249659 / 1944 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 7 0 11) +
    ((34269267263046837041641 / 782757789696 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 7 0 0 +
    (24747816569734375 / 71663616 : ℝ)*(u^10*t^2*w^1))) +
    (((63142360006956197611 / 16307453952 : ℝ)*(u^3*t^2*w^2)*oddCompactUnitSlack u t w 7 0 0 +
    (28512330828125 / 2654208 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 7 0 0) +
    ((12177343565351569387 / 1019215872 : ℝ)*(u^10*t^2*w^4) +
    (27218046875 / 165888 : ℝ)*(u^10*t^2*w^5))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart33_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart33 u t w := by
  unfold oddCompactRemainderPart33 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart34 (u t w : ℝ) : ℝ :=
  ((((((8833657868357409065 / 3057647616 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 7 0 3 +
    (10703125 / 5184 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 7 0 4) +
    ((25028856527902693 / 63700992 : ℝ)*(u^10*t^2*w^8) +
    (18438949035001 / 995328 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 7 0 7)) +
    (((8493951575 / 31104 : ℝ)*(u^10*t^2*w^12) +
    (374987 / 648 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 7 0 11) +
    ((215187992152455797021 / 16307453952 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 7 0 0 +
    (2590897567703125 / 47775744 : ℝ)*(u^10*t^3*w^1)))) +
    ((((1838658579956016449 / 603979776 : ℝ)*(u^10*t^3*w^2) +
    (1948514609375 / 1327104 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 0 0) +
    ((677656115958156395 / 226492416 : ℝ)*(u^10*t^3*w^4) +
    (3007578125 / 165888 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 0 2)) +
    (((195380403873863833 / 339738624 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 0 3 +
    (397103445028657 / 5308416 : ℝ)*(u^10*t^3*w^8)) +
    ((891667630325 / 331776 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 0 7 +
    (418639717 / 15552 : ℝ)*(u^10*t^3*w^12))))) +
    (((((833 / 24 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 0 11 +
    (97944629577315949307 / 43486543872 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 7 1 0) +
    ((102584728765625 / 31850496 : ℝ)*(u^10*t^4*w^1) +
    (252669994257750069 / 134217728 : ℝ)*(u^10*t^4*w^2))) +
    (((140315828125 / 1769472 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 1 0 +
    (210560809072419083 / 452984832 : ℝ)*(u^10*t^4*w^4)) +
    ((19357731129108787 / 339738624 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 1 3 +
    (54069094030565 / 7077888 : ℝ)*(u^10*t^4*w^8)))) +
    ((((41914033687 / 221184 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 1 7 +
    (19467587 / 20736 : ℝ)*(u^10*t^4*w^12)) +
    ((26852399771019371 / 150994944 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 7 2 0 +
    (72886140625 / 5308416 : ℝ)*(u^10*t^5*w^1))) +
    (((1823528128967169461 / 3623878656 : ℝ)*(u^10*t^5*w^2) +
    (3714362894932811 / 75497472 : ℝ)*(u^10*t^5*w^4)) +
    ((231873002457505 / 113246208 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 2 3 +
    (460025349391 / 1179648 : ℝ)*(u^10*t^5*w^8))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart34_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart34 u t w := by
  unfold oddCompactRemainderPart34 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart35 (u t w : ℝ) : ℝ :=
  ((((((384645739 / 73728 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 7 2 7 +
    (40297085874498463 / 4831838208 : ℝ)*(u^10*t^6)) +
    ((47022574587892843 / 603979776 : ℝ)*(u^10*t^6*w^2) +
    (35197599605383 / 9437184 : ℝ)*(u^10*t^6*w^4))) +
    (((2111276389765 / 37748736 : ℝ)*(u^10*t^6*w^6) +
    (5856049019 / 786432 : ℝ)*(u^10*t^6*w^8)) +
    ((248894867221639 / 67108864 : ℝ)*(u^10*t^7) +
    (1446664332397999 / 201326592 : ℝ)*(u^10*t^7*w^2)))) +
    ((((4586881251625 / 25165824 : ℝ)*(u^10*t^7*w^4) +
    (16934020901 / 4194304 : ℝ)*(u^10*t^7*w^6)) +
    ((441215618039677 / 1073741824 : ℝ)*(u^10*t^8) +
    (97541337628715 / 268435456 : ℝ)*(u^10*t^8*w^2))) +
    (((127898848485 / 33554432 : ℝ)*(u^10*t^8*w^4) +
    (2907958338453 / 134217728 : ℝ)*(u^10*t^9)) +
    ((2013649013721 / 268435456 : ℝ)*(u^10*t^9*w^2) +
    (455200309395 / 1073741824 : ℝ)*(u^10*t^10))))) +
    (((((170347033931171875 / 1289945088 : ℝ)*(u^11) +
    (7031147444749479783409 / 1320903770112 : ℝ)*(u^3*w^1)*oddCompactUnitSlack u t w 8 0 0) +
    ((157773762106421875 / 2579890176 : ℝ)*(u^11*w^2) +
    (421947355810112208331 / 110075314176 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 8 0 0)) +
    (((17646723828125 / 4478976 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 8 0 1 +
    (30192997799158522103 / 13759414272 : ℝ)*(u^11*w^5)) +
    ((3457109375 / 15552 : ℝ)*(u^11*w^6) +
    (1664119620073872295 / 5159780352 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 8 0 4))) +
    ((((3920339754178867 / 107495424 : ℝ)*(u^11*w^9) +
    (3797873761589 / 2239488 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 8 0 8) +
    ((534453769 / 34992 : ℝ)*(u^11*w^13) +
    (1445 / 2187 : ℝ)*(u^11*w^15))) +
    (((85605502534609375 / 859963392 : ℝ)*(u^11*t^1) +
    (691422705689869856543 / 146767085568 : ℝ)*(u^3*t^1*w^1)*oddCompactUnitSlack u t w 8 0 0) +
    ((48128474294703125 / 859963392 : ℝ)*(u^11*t^1*w^2) +
    (25563790407405717607 / 6115295232 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 8 0 0)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart35_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart35 u t w := by
  unfold oddCompactRemainderPart35 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart36 (u t w : ℝ) : ℝ :=
  ((((((7192425078125 / 2985984 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 8 0 1 +
    (37914479182499959957 / 13759414272 : ℝ)*(u^11*t^1*w^5)) +
    ((2493828125 / 31104 : ℝ)*(u^11*t^1*w^6) +
    (310976054510899057 / 859963392 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 8 0 4)) +
    (((3452565417007147 / 107495424 : ℝ)*(u^11*t^1*w^9) +
    (640456935817 / 559872 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 8 0 8) +
    ((98150231 / 11664 : ℝ)*(u^11*t^1*w^13) +
    (170 / 729 : ℝ)*(u^11*t^1*w^15)))) +
    ((((2395226645546875 / 95551488 : ℝ)*(u^11*t^2) +
    (20386765507532753249 / 36691771392 : ℝ)*(u^3*t^2*w^1)*oddCompactUnitSlack u t w 8 0 0) +
    ((1722582547109375 / 95551488 : ℝ)*(u^11*t^2*w^2) +
    (9858464726266265065 / 6115295232 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 8 0 0)) +
    (((13368203125 / 31104 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 8 0 1 +
    (6309224464248364537 / 4586471424 : ℝ)*(u^11*t^2*w^5)) +
    ((74921875 / 10368 : ℝ)*(u^11*t^2*w^6) +
    (29527424051239135 / 191102976 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 8 0 4)))) +
    (((((194550985783999 / 17915904 : ℝ)*(u^11*t^2*w^9) +
    (35068590209 / 124416 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 8 0 8) +
    ((5999123 / 3888 : ℝ)*(u^11*t^2*w^13) +
    (5 / 243 : ℝ)*(u^11*t^2*w^15))) +
    (((205501295078125 / 95551488 : ℝ)*(u^11*t^3) +
    (11127426728034645823 / 12230590464 : ℝ)*(u^11*t^3*w^1)) +
    ((240188620484375 / 95551488 : ℝ)*(u^11*t^3*w^2) +
    (1199962900552742267 / 6115295232 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 0 0))) +
    ((((7460078125 / 331776 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 0 1 +
    (549175048265023249 / 1528823808 : ℝ)*(u^11*t^3*w^5)) +
    ((1560072824016335 / 47775744 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 0 4 +
    (3532830889979 / 1990656 : ℝ)*(u^11*t^3*w^9))) +
    (((619769677 / 20736 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 0 8 +
    (122053 / 1296 : ℝ)*(u^11*t^3*w^13)) +
    ((364430703125 / 31850496 : ℝ)*(u^11*t^4) +
    (4284297577359561473 / 8153726976 : ℝ)*(u^11*t^4*w^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart36_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart36 u t w := by
  unfold oddCompactRemainderPart36 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart37 (u t w : ℝ) : ℝ :=
  ((((((1038594859375 / 7962624 : ℝ)*(u^11*t^4*w^2) +
    (18776969861744165 / 509607936 : ℝ)*(u^11*t^4*w^3)) +
    ((27294386811833183 / 509607936 : ℝ)*(u^11*t^4*w^5) +
    (228199007462545 / 63700992 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 1 4)) +
    (((561545534969 / 3981312 : ℝ)*(u^11*t^4*w^9) +
    (94439195 / 82944 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 1 8) +
    ((371013217440878725 / 2717908992 : ℝ)*(u^11*t^5*w^1) +
    (3491929534201057 / 226492416 : ℝ)*(u^11*t^5*w^3)))) +
    ((((786646005727103 / 169869312 : ℝ)*(u^11*t^5*w^5) +
    (664420321595 / 3538944 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 2 4) +
    ((5830117123 / 1327104 : ℝ)*(u^11*t^5*w^9) +
    (9055683592152803 / 452984832 : ℝ)*(u^11*t^6*w^1))) +
    (((487634445884123 / 226492416 : ℝ)*(u^11*t^6*w^3) +
    (12601493432963 / 56623104 : ℝ)*(u^11*t^6*w^5)) +
    ((7846999609 / 2359296 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 8 3 4 +
    (254695695110795 / 150994944 : ℝ)*(u^11*t^7*w^1))))) +
    (((((11031496188151 / 75497472 : ℝ)*(u^11*t^7*w^3) +
    (10343966595 / 2097152 : ℝ)*(u^11*t^7*w^5)) +
    ((5128129672269 / 67108864 : ℝ)*(u^11*t^8*w^1) +
    (69852227155 / 16777216 : ℝ)*(u^11*t^8*w^3))) +
    (((98449101355 / 67108864 : ℝ)*(u^11*t^9*w^1) +
    (44256474578483655071359 / 63403380965376 : ℝ)*(u^3)*oddCompactUnitSlack u t w 9 0 0) +
    ((38841027800453125 / 1289945088 : ℝ)*(u^12*w^1) +
    (1169189167156941935 / 16307453952 : ℝ)*(u^12*w^2)))) +
    ((((50194571609375 / 53747712 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 9 0 0 +
    (82240620952815905533 / 990677827584 : ℝ)*(u^12*w^4)) +
    ((384466953125 / 2239488 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 9 0 2 +
    (646195853667374791 / 61917364224 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 9 0 3)) +
    (((1955303121937961 / 859963392 : ℝ)*(u^12*w^8) +
    (12029754723991 / 26873856 : ℝ)*(u^12*w^10)) +
    ((4617607609 / 314928 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 9 0 9 +
    (206635 / 26244 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 9 0 11)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart37_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart37 u t w := by
  unfold oddCompactRemainderPart37 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart38 (u t w : ℝ) : ℝ :=
  ((((((6771952150155646837859 / 21134460321792 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 9 0 0 +
    (7927912962453125 / 429981696 : ℝ)*(u^12*t^1*w^1)) +
    ((64189614113537989345 / 110075314176 : ℝ)*(u^12*t^1*w^2) +
    (225474171875 / 497664 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 0)) +
    (((17140309044535476853 / 330225942528 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 1 +
    (24863359375 / 373248 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 2) +
    ((957459446182937615 / 20639121408 : ℝ)*(u^12*t^1*w^6) +
    (621546085118237 / 286654464 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 5))) +
    ((((1771295507893 / 4478976 : ℝ)*(u^12*t^1*w^10) +
    (37923889 / 4374 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 9) +
    ((12155 / 4374 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 9 0 11 +
    (328369369047354962213 / 1761205026816 : ℝ)*(u^12*t^2))) +
    (((157492346546875 / 47775744 : ℝ)*(u^12*t^2*w^1) +
    (35261596625857009927 / 55037657088 : ℝ)*(u^12*t^2*w^2)) +
    ((154127140625 / 1990656 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 0 +
    (6789061481037951791 / 110075314176 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 1)))) +
    (((((1594765625 / 248832 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 2 +
    (33089669233928341 / 859963392 : ℝ)*(u^12*t^2*w^6)) +
    ((87992230454711 / 47775744 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 5 +
    (88082138155 / 746496 : ℝ)*(u^12*t^2*w^10))) +
    (((19715191 / 11664 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 9 +
    (715 / 2916 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 9 0 11) +
    ((37227332961192600671 / 195689447424 : ℝ)*(u^12*t^3) +
    (3789023984375 / 47775744 : ℝ)*(u^12*t^3*w^1)))) +
    ((((11996989190395209787 / 36691771392 : ℝ)*(u^12*t^3*w^2) +
    (4664421875 / 995328 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 0 0) +
    ((22159321048389115 / 1358954496 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 0 1 +
    (13371424867286399 / 1146617856 : ℝ)*(u^12*t^3*w^6))) +
    (((7267711253185 / 15925248 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 0 5 +
    (2411698921 / 165888 : ℝ)*(u^12*t^3*w^10)) +
    ((634819 / 5832 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 0 9 +
    (27248041751868625847 / 391378894848 : ℝ)*(u^12*t^4))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart38_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart38 u t w := by
  unfold oddCompactRemainderPart38 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart39 (u t w : ℝ) : ℝ :=
  ((((((131684828125 / 7962624 : ℝ)*(u^3*t^3*w^1)*oddCompactUnitSlack u t w 9 1 0 +
    (2354954556335303045 / 24461180928 : ℝ)*(u^12*t^4*w^2)) +
    ((12966368736280009 / 12230590464 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 1 1 +
    (1287739770794185 / 764411904 : ℝ)*(u^12*t^4*w^6))) +
    (((506532959227 / 10616832 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 1 5 +
    (209089949 / 331776 : ℝ)*(u^12*t^4*w^10)) +
    ((1936032178635725203 / 130459631616 : ℝ)*(u^12*t^5) +
    (23500047416695691 / 1358954496 : ℝ)*(u^12*t^5*w^2)))) +
    ((((626442787523393 / 4076863488 : ℝ)*(u^12*t^5*w^4) +
    (29327960045635 / 254803968 : ℝ)*(u^12*t^5*w^6)) +
    ((6501733025 / 3538944 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 9 2 5 +
    (1658020940340203 / 805306368 : ℝ)*(u^12*t^6))) +
    (((628511226045353 / 339738624 : ℝ)*(u^12*t^6*w^2) +
    (30962042678843 / 1358954496 : ℝ)*(u^12*t^6*w^4)) +
    ((40707688817 / 14155776 : ℝ)*(u^12*t^6*w^6) +
    (1334766691918537 / 7247757312 : ℝ)*(u^12*t^7))))) +
    (((((47875532788193 / 452984832 : ℝ)*(u^12*t^7*w^2) +
    (306986381549 / 452984832 : ℝ)*(u^12*t^7*w^4)) +
    ((90226967087705 / 9663676416 : ℝ)*(u^12*t^8) +
    (1422605711953 / 603979776 : ℝ)*(u^12*t^8*w^2))) +
    (((574298429605 / 3221225472 : ℝ)*(u^12*t^9) +
    (415624574140625 / 143327232 : ℝ)*(u^13)) +
    ((12003314495210891041 / 220150628352 : ℝ)*(u^13*w^1) +
    (430019318265625 / 241864704 : ℝ)*(u^13*w^2)))) +
    ((((152021080859419500707 / 2972033482752 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 10 0 0 +
    (2413972109375 / 40310784 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 10 0 1) +
    ((26504883112167264019 / 371504185344 : ℝ)*(u^13*w^5) +
    (120929177382600895 / 11609505792 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 10 0 4)) +
    (((1554580746339403 / 2902376448 : ℝ)*(u^13*w^9) +
    (10111451369 / 5038848 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 10 0 8) +
    ((5980855 / 157464 : ℝ)*(u^13*w^13) +
    (500955966015625 / 429981696 : ℝ)*(u^13*t^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart39_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart39 u t w := by
  unfold oddCompactRemainderPart39 oddCompactUnitSlack
  positivity

end
end HTGeometry
