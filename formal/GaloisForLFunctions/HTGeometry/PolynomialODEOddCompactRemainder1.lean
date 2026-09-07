import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactRemainder0

/-!
# Nonnegative compact remainder, group 1

Every summand is a nonnegative monomial or a nonnegative monomial times
an exact unit-cube complement. This module proves only the remainder sign.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart8 (u t w : ℝ) : ℝ :=
  ((((((16926656728450094991 / 4194304 : ℝ)*(u^2*t^2*w^3)*oddCompactUnitSlack u t w 0 0 5 +
    (150747214855833 / 2048 : ℝ)*(u^2*t^2*w^10)) +
    ((55403761293 / 256 : ℝ)*(u^2*t^2*w^3)*oddCompactUnitSlack u t w 0 0 9 +
    (186542631 / 16 : ℝ)*(u^2*t^2*w^14))) +
    (((31212 / 1 : ℝ)*(u^2*t^2*w^3)*oddCompactUnitSlack u t w 0 0 13 +
    (19826346634611607989747 / 268435456 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 1) +
    ((6256686246046875 / 16384 : ℝ)*(u^2*t^3*w^5) +
    (1704859309789791223077 / 67108864 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 3))) +
    ((((565349765625 / 64 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 4 +
    (733025364555908601 / 524288 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 5) +
    ((275854675788837 / 16384 : ℝ)*(u^2*t^3*w^10) +
    (144292049109 / 1024 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 9)) +
    (((38468655 / 16 : ℝ)*(u^2*t^3*w^14) +
    (3672 / 1 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 0 13) +
    ((34992914615863136853173577 / 137438953472 : ℝ)*(u^2*t^3)*oddCompactUnitSlack u t w 0 1 0 +
    (16343963214205921875 / 4194304 : ℝ)*(u^2*t^3*w^1)*oddCompactUnitSlack u t w 0 1 0)))) +
    (((((645459458650261027119 / 268435456 : ℝ)*(u^2*t^4*w^2) +
    (358349869205578125 / 524288 : ℝ)*(u^2*t^4*w^3)) +
    ((28392895559303499832839 / 1073741824 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 1 +
    (1123376532328125 / 16384 : ℝ)*(u^2*t^4*w^5))) +
    (((237118863551056133391 / 33554432 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 3 +
    (94035515625 / 512 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 4) +
    ((649723248991143243 / 2097152 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 5 +
    (88409201320359 / 65536 : ℝ)*(u^2*t^4*w^10)))) +
    ((((27988482825 / 1024 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 9 +
    (8163423 / 32 : ℝ)*(u^2*t^4*w^14)) +
    ((162 / 1 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 1 13 +
    (5250954585847310095750551 / 68719476736 : ℝ)*(u^2*t^3)*oddCompactUnitSlack u t w 0 2 0)) +
    (((1262057369292703125 / 4194304 : ℝ)*(u^2*t^3*w^1)*oddCompactUnitSlack u t w 0 2 0 +
    (8860850463479611793769 / 8589934592 : ℝ)*(u^2*t^5*w^2)) +
    ((3426599455734375 / 32768 : ℝ)*(u^2*t^5*w^3) +
    (825438473755336898973 / 134217728 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 2 1)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart8_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart8 u t w := by
  unfold oddCompactRemainderPart8 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart9 (u t w : ℝ) : ℝ :=
  ((((((126851714296875 / 16384 : ℝ)*(u^2*t^5*w^5) +
    (42510048564876461523 / 33554432 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 2 3) +
    ((3294421875 / 64 : ℝ)*(u^2*t^5*w^7) +
    (47681643233271069 / 1048576 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 2 5)) +
    (((8335648340127 / 65536 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 2 7 +
    (2666405709 / 1024 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 2 9) +
    ((424521 / 32 : ℝ)*(u^2*t^5*w^14) +
    (2002461335819741925298683 / 137438953472 : ℝ)*(u^2*t^3)*oddCompactUnitSlack u t w 0 3 0))) +
    ((((6566607616078125 / 1048576 : ℝ)*(u^2*t^6*w^1) +
    (670884388068506456673 / 2147483648 : ℝ)*(u^2*t^6*w^2)) +
    ((2478843178453125 / 262144 : ℝ)*(u^2*t^6*w^3) +
    (245205863205912217053 / 268435456 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 3 1)) +
    (((8136008296875 / 16384 : ℝ)*(u^2*t^6*w^5) +
    (4849678677330928233 / 33554432 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 3 3) +
    ((1560515625 / 512 : ℝ)*(u^2*t^6*w^7) +
    (8962207612548363 / 2097152 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 3 5)))) +
    (((((541712240397 / 16384 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 3 7 +
    (34062525 / 256 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 3 9) +
    ((2187 / 8 : ℝ)*(u^2*t^6*w^14) +
    (29514898266004739444211 / 17179869184 : ℝ)*(u^2*t^3)*oddCompactUnitSlack u t w 0 4 0)) +
    (((1642562855015625 / 524288 : ℝ)*(u^2*t^7*w^1) +
    (23549187371744528001 / 268435456 : ℝ)*(u^2*t^7*w^2)) +
    ((15004357734375 / 32768 : ℝ)*(u^2*t^7*w^3) +
    (10504348264266512931 / 134217728 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 4 1))) +
    ((((220032703125 / 16384 : ℝ)*(u^2*t^7*w^5) +
    (314737985923156341 / 33554432 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 4 3) +
    ((112085801884953 / 524288 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 4 5 +
    (4385182131 / 2048 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 4 7)) +
    (((3746331 / 1024 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 4 9 +
    (12718233007721230648347 / 137438953472 : ℝ)*(u^2*t^3)*oddCompactUnitSlack u t w 0 5 0) +
    ((1864299641203125 / 8388608 : ℝ)*(u^2*t^8*w^1) +
    (84010016751062399109 / 4294967296 : ℝ)*(u^2*t^8*w^2))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart9_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart9 u t w := by
  unfold oddCompactRemainderPart9 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart10 (u t w : ℝ) : ℝ :=
  ((((((9086882484375 / 1048576 : ℝ)*(u^2*t^8*w^3) +
    (2103455410933875867 / 1073741824 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 5 1) +
    ((10359114533771103 / 67108864 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 5 3 +
    (320853153807 / 4194304 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 5 5)) +
    (((2467414953 / 131072 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 5 7 +
    (98415 / 2048 : ℝ)*(u^2*t^3*w^3)*oddCompactUnitSlack u t w 0 5 9) +
    ((433711440641711378601 / 68719476736 : ℝ)*(u^2*t^9) +
    (42119877234375 / 8388608 : ℝ)*(u^2*t^9*w^1)))) +
    ((((25959292122689323047 / 8589934592 : ℝ)*(u^2*t^9*w^2) +
    (89455931958313251 / 268435456 : ℝ)*(u^2*t^9*w^4)) +
    ((1664431669827837 / 67108864 : ℝ)*(u^2*t^9*w^6) +
    (1183376818593 / 2097152 : ℝ)*(u^2*t^9*w^8))) +
    (((243577125 / 131072 : ℝ)*(u^2*t^9*w^10) +
    (245180333237004091287 / 137438953472 : ℝ)*(u^2*t^10)) +
    ((1316415425210328141 / 4294967296 : ℝ)*(u^2*t^10*w^2) +
    (21442041648714537 / 536870912 : ℝ)*(u^2*t^10*w^4))))) +
    (((((127082314030203 / 67108864 : ℝ)*(u^2*t^10*w^6) +
    (84253770405 / 4194304 : ℝ)*(u^2*t^10*w^8)) +
    ((6040391125090758075 / 34359738368 : ℝ)*(u^2*t^11) +
    (41821417848712509 / 2147483648 : ℝ)*(u^2*t^11*w^2))) +
    (((496648095371145 / 268435456 : ℝ)*(u^2*t^11*w^4) +
    (2943442842687 / 67108864 : ℝ)*(u^2*t^11*w^6)) +
    ((1338046766796501765 / 137438953472 : ℝ)*(u^2*t^12) +
    (1511026899208731 / 2147483648 : ℝ)*(u^2*t^12*w^2)))) +
    ((((35278098924447 / 1073741824 : ℝ)*(u^2*t^12*w^4) +
    (20524524533375751 / 68719476736 : ℝ)*(u^2*t^13)) +
    ((94135578689259 / 8589934592 : ℝ)*(u^2*t^13*w^2) +
    (541433884413375 / 137438953472 : ℝ)*(u^2*t^14))) +
    (((805872856490140625 / 589824 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 0 0 1 +
    (1177950057265152837415 / 67108864 : ℝ)*(u^3*w^5)) +
    ((8827360552328125 / 18432 : ℝ)*(u^3*w^6) +
    (13406546379343542245 / 3145728 : ℝ)*(u^3*w^7))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart10_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart10 u t w := by
  unfold oddCompactRemainderPart10 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart11 (u t w : ℝ) : ℝ :=
  ((((((3144550296875 / 576 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 0 0 5 +
    (131289520536938071 / 262144 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 0 0 6) +
    ((332181014887981 / 16384 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 0 0 8 +
    (15898282173 / 128 : ℝ)*(u^3*w^13))) +
    (((21862561 / 12 : ℝ)*(u^3*w^15) +
    (175775811339390625 / 196608 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 0 0 1) +
    ((2978384580597938562471 / 67108864 : ℝ)*(u^3*t^1*w^5) +
    (136496355890625 / 256 : ℝ)*(u^3*t^1*w^6)))) +
    ((((4831707586481075429 / 1048576 : ℝ)*(u^3*t^1*w^7) +
    (828359796875 / 192 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 0 0 5) +
    ((212373506749037519 / 262144 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 0 0 6 +
    (5912315073897 / 512 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 0 0 8)) +
    (((310148017 / 64 : ℝ)*(u^3*t^1*w^13) +
    (1556401 / 1 : ℝ)*(u^3*t^1*w^15)) +
    ((2313241465828125 / 65536 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 0 0 1 +
    (2727444663384021457677 / 67108864 : ℝ)*(u^3*t^2*w^5))))) +
    (((((480534977203125 / 2048 : ℝ)*(u^3*t^2*w^6) +
    (125845866479458347 / 65536 : ℝ)*(u^3*t^2*w^7)) +
    ((35189734375 / 32 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 0 0 5 +
    (16143707395346787 / 32768 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 0 0 6)) +
    (((3729499156281 / 2048 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 0 0 8 +
    (4070853123 / 128 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 0 0 10) +
    ((1027419 / 2 : ℝ)*(u^3*t^2*w^15) +
    (7352947098328125 / 65536 : ℝ)*(u^3*t^3*w^4)))) +
    ((((1330710856548532444269 / 67108864 : ℝ)*(u^3*t^3*w^5) +
    (27029549859375 / 512 : ℝ)*(u^3*t^3*w^6)) +
    ((52385802029748369 / 131072 : ℝ)*(u^3*t^3*w^7) +
    (2433890625 / 32 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 0 5)) +
    (((5068392071500827 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 0 6 +
    (214651486953 / 2048 : ℝ)*(u^3*t^3*w^11)) +
    ((731241639 / 64 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 0 10 +
    (81153 / 1 : ℝ)*(u^3*t^3*w^15))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart11_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart11 u t w := by
  unfold oddCompactRemainderPart11 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart12 (u t w : ℝ) : ℝ :=
  ((((((1941879180583828125 / 8388608 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 0 1 0 +
    (93955151363988184021485 / 4294967296 : ℝ)*(u^3*t^4*w^1)) +
    ((288230882978109375 / 2097152 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 0 1 0 +
    (13861248438588719106591 / 1073741824 : ℝ)*(u^3*t^4*w^3))) +
    (((2507753945953125 / 65536 : ℝ)*(u^3*t^4*w^4) +
    (201112517376933952203 / 33554432 : ℝ)*(u^3*t^4*w^5)) +
    ((13242015421875 / 2048 : ℝ)*(u^3*t^4*w^6) +
    (29956928228855649 / 524288 : ℝ)*(u^3*t^4*w^7)))) +
    ((((481640625 / 64 : ℝ)*(u^3*t^4*w^8) +
    (3617119471474071 / 131072 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 1 6) +
    ((455849408583 / 8192 : ℝ)*(u^3*t^4*w^11) +
    (213030513 / 128 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 1 10)) +
    (((24111 / 4 : ℝ)*(u^3*t^4*w^15) +
    (22748479811015625 / 4194304 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 0 2 0) +
    ((2109571084324754543529 / 536870912 : ℝ)*(u^3*t^5*w^1) +
    (1276539291421875 / 2097152 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 0 2 0)))) +
    (((((1038736476384281851743 / 268435456 : ℝ)*(u^3*t^5*w^3) +
    (359580078984375 / 65536 : ℝ)*(u^3*t^5*w^4)) +
    ((40860828929245560075 / 33554432 : ℝ)*(u^3*t^5*w^5) +
    (212056734375 / 512 : ℝ)*(u^3*t^5*w^6))) +
    (((6721700363629497 / 524288 : ℝ)*(u^3*t^5*w^7) +
    (57796875 / 64 : ℝ)*(u^3*t^5*w^8)) +
    ((360486474673167 / 131072 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 2 6 +
    (5101831413 / 1024 : ℝ)*(u^3*t^5*w^11)))) +
    ((((7478973 / 64 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 2 10 +
    (162 / 1 : ℝ)*(u^3*t^5*w^15)) +
    ((6736805772890625 / 4194304 : ℝ)*(u^3*t^6) +
    (537679663396878817701 / 536870912 : ℝ)*(u^3*t^6*w^1))) +
    (((3555917998453125 / 2097152 : ℝ)*(u^3*t^6*w^2) +
    (26818331151998449899 / 33554432 : ℝ)*(u^3*t^6*w^3)) +
    ((24263763890625 / 65536 : ℝ)*(u^3*t^6*w^4) +
    (5891265043039280853 / 33554432 : ℝ)*(u^3*t^6*w^5))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart12_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart12 u t w := by
  unfold oddCompactRemainderPart12 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart13 (u t w : ℝ) : ℝ :=
  ((((((22714171875 / 2048 : ℝ)*(u^3*t^6*w^6) +
    (894754096746939 / 262144 : ℝ)*(u^3*t^6*w^7)) +
    ((60482452383 / 512 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 3 6 +
    (150142167 / 1024 : ℝ)*(u^3*t^6*w^11))) +
    (((510057 / 128 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 3 10 +
    (665754978515625 / 4194304 : ℝ)*(u^3*t^7)) +
    ((284875916936236204275 / 1073741824 : ℝ)*(u^3*t^7*w^1) +
    (361754050640625 / 2097152 : ℝ)*(u^3*t^7*w^2)))) +
    ((((31385509846089532605 / 268435456 : ℝ)*(u^3*t^7*w^3) +
    (630968484375 / 65536 : ℝ)*(u^3*t^7*w^4)) +
    ((624925579986971829 / 33554432 : ℝ)*(u^3*t^7*w^5) +
    (37316596363983 / 65536 : ℝ)*(u^3*t^7*w^7))) +
    (((3317714721 / 1024 : ℝ)*(u^3*t^7*w^9) +
    (16651089 / 2048 : ℝ)*(u^3*t^7*w^11)) +
    ((3645 / 64 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 0 4 10 +
    (70199795390625 / 16777216 : ℝ)*(u^3*t^8))))) +
    (((((219253537896777263511 / 4294967296 : ℝ)*(u^3*t^8*w^1) +
    (366721171875 / 65536 : ℝ)*(u^3*t^8*w^2)) +
    ((13252973702721935481 / 1073741824 : ℝ)*(u^3*t^8*w^3) +
    (98204804478759411 / 67108864 : ℝ)*(u^3*t^8*w^5))) +
    (((56035705798863 / 1048576 : ℝ)*(u^3*t^8*w^7) +
    (147220842141 / 262144 : ℝ)*(u^3*t^8*w^9)) +
    ((12188151 / 16384 : ℝ)*(u^3*t^8*w^11) +
    (14247551528745192315 / 2147483648 : ℝ)*(u^3*t^9*w^1)))) +
    ((((503763903846657567 / 536870912 : ℝ)*(u^3*t^9*w^3) +
    (5460954480585459 / 67108864 : ℝ)*(u^3*t^9*w^5)) +
    ((2777106599217 / 1048576 : ℝ)*(u^3*t^9*w^7) +
    (4682172357 / 262144 : ℝ)*(u^3*t^9*w^9))) +
    (((307777638557288511 / 536870912 : ℝ)*(u^3*t^10*w^1) +
    (13233653922682143 / 268435456 : ℝ)*(u^3*t^10*w^3)) +
    ((189612139088025 / 67108864 : ℝ)*(u^3*t^10*w^5) +
    (14349950199 / 262144 : ℝ)*(u^3*t^10*w^7))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart13_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart13 u t w := by
  unfold oddCompactRemainderPart13 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart14 (u t w : ℝ) : ℝ :=
  ((((((67970522543732487 / 2147483648 : ℝ)*(u^3*t^11*w^1) +
    (859998968635401 / 536870912 : ℝ)*(u^3*t^11*w^3)) +
    ((3041997631353 / 67108864 : ℝ)*(u^3*t^11*w^5) +
    (4331647035599247 / 4294967296 : ℝ)*(u^3*t^12*w^1))) +
    (((25918183239741 / 1073741824 : ℝ)*(u^3*t^12*w^3) +
    (15085764295407 / 1073741824 : ℝ)*(u^3*t^13*w^1)) +
    ((21240273938850927511305709 / 154618822656 : ℝ)*(u^3)*oddCompactUnitSlack u t w 1 0 0 +
    (1132061086774363328125 / 113246208 : ℝ)*(u^3*w^1)*oddCompactUnitSlack u t w 1 0 0))) +
    ((((8113522613998268913646925 / 154618822656 : ℝ)*(u^4*w^2) +
    (1595687520902546875 / 884736 : ℝ)*(u^4*w^3)) +
    ((7763451786599818175341 / 805306368 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 1 0 1 +
    (21065865008140625 / 221184 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 1 0 2)) +
    (((509455434247423413035 / 75497472 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 1 0 3 +
    (304853108546875 / 13824 : ℝ)*(u^4*w^7)) +
    ((5777209292838973325 / 6291456 : ℝ)*(u^4*w^8) +
    (34964578902848747 / 589824 : ℝ)*(u^4*w^10))))) +
    (((((11701511678443 / 6144 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 1 0 9 +
    (105678341 / 72 : ℝ)*(u^4*w^14)) +
    ((334084 / 9 : ℝ)*(u^4*w^16) +
    (2884142159654103806631247 / 8589934592 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 1 0 0)) +
    (((22416477474715984375 / 2097152 : ℝ)*(u^3*t^1*w^1)*oddCompactUnitSlack u t w 1 0 0 +
    (1111509889246189781755 / 16777216 : ℝ)*(u^4*t^1*w^2)) +
    ((931944783860640625 / 393216 : ℝ)*(u^4*t^1*w^3) +
    (4276033842993181119405 / 134217728 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 1 0 1))) +
    ((((8105727424484375 / 73728 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 1 0 2 +
    (336241170450096223169 / 50331648 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 1 0 3) +
    ((114973741515625 / 4608 : ℝ)*(u^4*t^1*w^7) +
    (3087989168650576679 / 2097152 : ℝ)*(u^4*t^1*w^8))) +
    (((1000480807367181 / 32768 : ℝ)*(u^4*t^1*w^10) +
    (6324241576817 / 6144 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 1 0 9) +
    ((223596835 / 96 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 1 0 11 +
    (78608 / 3 : ℝ)*(u^4*t^1*w^16))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart14_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart14 u t w := by
  unfold oddCompactRemainderPart14 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart15 (u t w : ℝ) : ℝ :=
  ((((((2827094978186857625643221 / 8589934592 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 1 0 0 +
    (27898334880549296875 / 6291456 : ℝ)*(u^3*t^2*w^1)*oddCompactUnitSlack u t w 1 0 0) +
    ((267747549587123777901219 / 8589934592 : ℝ)*(u^4*t^2*w^2) +
    (21071098707828125 / 16384 : ℝ)*(u^4*t^2*w^3))) +
    (((8470452166688458988303 / 268435456 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 1 0 1 +
    (64657263453125 / 1536 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 1 0 2) +
    ((36175916109574707635 / 16777216 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 1 0 3 +
    (7718851859375 / 768 : ℝ)*(u^4*t^2*w^7)))) +
    ((((483624280733910897 / 524288 : ℝ)*(u^4*t^2*w^8) +
    (52035519038671 / 32768 : ℝ)*(u^4*t^2*w^10)) +
    ((285283604025 / 2048 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 1 0 9 +
    (57892195 / 32 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 1 0 11)) +
    (((6936 / 1 : ℝ)*(u^4*t^2*w^16) +
    (48034605031712972621151 / 268435456 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 0 0) +
    ((1700522464478796875 / 2097152 : ℝ)*(u^3*t^3*w^1)*oddCompactUnitSlack u t w 1 0 0 +
    (10005307159221346612071 / 2147483648 : ℝ)*(u^4*t^3*w^2))))) +
    (((((49284985238171875 / 131072 : ℝ)*(u^4*t^3*w^3) +
    (1047069997945792101615 / 67108864 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 0 1) +
    ((26722387296875 / 4096 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 0 2 +
    (16728617259823785 / 4194304 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 0 3)) +
    (((476590890625 / 256 : ℝ)*(u^4*t^3*w^7) +
    (163229486241066585 / 524288 : ℝ)*(u^4*t^3*w^8)) +
    ((62927721659703 / 32768 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 0 7 +
    (35556618669 / 2048 : ℝ)*(u^4*t^3*w^12)))) +
    ((((7151745 / 16 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 0 11 +
    (816 / 1 : ℝ)*(u^4*t^3*w^16)) +
    ((1050982184964867418407051 / 17179869184 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 1 1 0 +
    (5713881191859375 / 262144 : ℝ)*(u^3*t^3*w^1)*oddCompactUnitSlack u t w 1 1 0)) +
    (((24615429715115785010385 / 17179869184 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 1 1 0 +
    (2103845301421875 / 32768 : ℝ)*(u^4*t^4*w^3)) +
    ((606050279836348680423 / 134217728 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 1 1 +
    (2351440171875 / 8192 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 1 1 2)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart15_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart15 u t w := by
  unfold oddCompactRemainderPart15 oddCompactUnitSlack
  positivity

end
end HTGeometry
