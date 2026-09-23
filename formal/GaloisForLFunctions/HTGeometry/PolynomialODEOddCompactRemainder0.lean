import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactCubic

/-!
# Nonnegative compact remainder, group 0

Every summand is a nonnegative monomial or a nonnegative monomial times
an exact unit-cube complement. This module proves only the remainder sign.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart0 (u t w : ℝ) : ℝ :=
  ((((((1438490331509574760999983 / 2147483648 : ℝ)*(w^(4 : ℕ)) +
    (176557056857671875 / 32768 : ℝ)*(w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2) +
    ((12668573045069802182061 / 134217728 : ℝ)*(w^(6 : ℕ)) +
    (100544567578125 / 256 : ℝ)*(w^(7 : ℕ)))) +
    (((25265573720436567501 / 8388608 : ℝ)*(w^(8 : ℕ)) +
    (2099650798663659 / 8192 : ℝ)*(w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 7) +
    ((2371403360151 / 2048 : ℝ)*(w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 9 +
    (624315429 / 16 : ℝ)*(w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 11))) +
    ((((2529888274479309121913535 / 2147483648 : ℝ)*(t^(1 : ℕ)*w^(4 : ℕ)) +
    (95531689514671875 / 16384 : ℝ)*(t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2) +
    ((10318051427935034970981 / 67108864 : ℝ)*(t^(1 : ℕ)*w^(6 : ℕ)) +
    (142167654984375 / 512 : ℝ)*(t^(1 : ℕ)*w^(7 : ℕ)))) +
    (((36645440763363298695 / 8388608 : ℝ)*(t^(1 : ℕ)*w^(8 : ℕ)) +
    (32397820999345485 / 131072 : ℝ)*(t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 7) +
    ((921146895279 / 2048 : ℝ)*(t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 9 +
    (1052737155 / 32 : ℝ)*(t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 11)))) +
    (((((1002343977994398655883769 / 1073741824 : ℝ)*(t^(2 : ℕ)*w^(4 : ℕ)) +
    (45454560470296875 / 16384 : ℝ)*(t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2) +
    ((1848474533105404835067 / 16777216 : ℝ)*(t^(2 : ℕ)*w^(6 : ℕ)) +
    (29235219890625 / 512 : ℝ)*(t^(2 : ℕ)*w^(7 : ℕ)))) +
    (((24350555899150553979 / 8388608 : ℝ)*(t^(2 : ℕ)*w^(8 : ℕ)) +
    (11012583182236245 / 131072 : ℝ)*(t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 7) +
    ((109776766563 / 2048 : ℝ)*(t^(2 : ℕ)*w^(12 : ℕ)) +
    (365226813 / 32 : ℝ)*(t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 11))) +
    ((((467696895498240223601241 / 1073741824 : ℝ)*(t^(3 : ℕ)*w^(4 : ℕ)) +
    (12443386005703125 / 16384 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2) +
    ((3059972568546496650459 / 67108864 : ℝ)*(t^(3 : ℕ)*w^(6 : ℕ)) +
    (449255109375 / 256 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 4)) +
    (((9713528435917047321 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(8 : ℕ)) +
    (129557631680001 / 16384 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 7) +
    ((115853997789 / 2048 : ℝ)*(t^(3 : ℕ)*w^(12 : ℕ)) +
    (33178005 / 16 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 11)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart0_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart0 u t w := by
  unfold oddCompactRemainderPart0 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart1 (u t w : ℝ) : ℝ :=
  ((((((431354425606266921302767545 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 0 +
    (275353895955028359375 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 1 0) +
    ((20839360168513756705718511 / 68719476736 : ℝ)*(t^(4 : ℕ)*w^(2 : ℕ)) +
    (4604265149160515625 / 1048576 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 0)) +
    (((281588548110570524514645 / 2147483648 : ℝ)*(t^(4 : ℕ)*w^(4 : ℕ)) +
    (518451666609375 / 4096 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 2) +
    ((1608915875015900502045 / 134217728 : ℝ)*(t^(4 : ℕ)*w^(6 : ℕ)) +
    (32770828125 / 16 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 4))) +
    ((((1256402671461860697 / 4194304 : ℝ)*(t^(4 : ℕ)*w^(8 : ℕ)) +
    (2252034567495 / 1024 : ℝ)*(t^(4 : ℕ)*w^(10 : ℕ))) +
    ((25762971537 / 2048 : ℝ)*(t^(4 : ℕ)*w^(12 : ℕ)) +
    (824499 / 4 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 11)) +
    (((187800395941971009114924249 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 0 +
    (4638722663719828125 / 1048576 : ℝ)*(t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 2 0) +
    ((1855558328066594432364717 / 34359738368 : ℝ)*(t^(5 : ℕ)*w^(2 : ℕ)) +
    (499575240467578125 / 1048576 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 0)))) +
    (((((56084150395291936204773 / 2147483648 : ℝ)*(t^(5 : ℕ)*w^(4 : ℕ)) +
    (194210851078125 / 16384 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 2) +
    ((68978265941179065393 / 33554432 : ℝ)*(t^(5 : ℕ)*w^(6 : ℕ)) +
    (126401765625 / 512 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 4)) +
    (((210129923362432347 / 4194304 : ℝ)*(t^(5 : ℕ)*w^(8 : ℕ)) +
    (46255720938795 / 65536 : ℝ)*(t^(5 : ℕ)*w^(10 : ℕ))) +
    ((2906630163 / 2048 : ℝ)*(t^(5 : ℕ)*w^(12 : ℕ)) +
    (334611 / 32 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 11))) +
    ((((50948294877947941964094177 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 0 +
    (2417282886003890625 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 3 0) +
    ((326390995103568531230745 / 68719476736 : ℝ)*(t^(6 : ℕ)*w^(2 : ℕ)) +
    (13355203261359375 / 524288 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 0)) +
    (((1789453551137882619267 / 536870912 : ℝ)*(t^(6 : ℕ)*w^(4 : ℕ)) +
    (6680567390625 / 16384 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 2) +
    ((3720130064593603587 / 16777216 : ℝ)*(t^(6 : ℕ)*w^(6 : ℕ)) +
    (4681546875 / 512 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 4)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart1_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart1 u t w := by
  unfold oddCompactRemainderPart1 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart2 (u t w : ℝ) : ℝ :=
  ((((((21015798464432835 / 4194304 : ℝ)*(t^(6 : ℕ)*w^(8 : ℕ)) +
    (5095699688295 / 65536 : ℝ)*(t^(6 : ℕ)*w^(10 : ℕ))) +
    ((192637521 / 2048 : ℝ)*(t^(6 : ℕ)*w^(12 : ℕ)) +
    (6561 / 32 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 11)) +
    (((9308156794912659028115745 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 0 +
    (9056223033890625 / 2097152 : ℝ)*(t^(7 : ℕ)*w^(1 : ℕ))) +
    ((2598701300964007872255 / 8589934592 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 4 0 +
    (16305827765625 / 524288 : ℝ)*(t^(7 : ℕ)*w^(3 : ℕ))))) +
    ((((122972052865433702499 / 536870912 : ℝ)*(t^(7 : ℕ)*w^(4 : ℕ)) +
    (294937453125 / 16384 : ℝ)*(t^(7 : ℕ)*w^(5 : ℕ))) +
    ((415463722075802979 / 33554432 : ℝ)*(t^(7 : ℕ)*w^(6 : ℕ)) +
    (923992378073793 / 4194304 : ℝ)*(t^(7 : ℕ)*w^(8 : ℕ)))) +
    (((12558836565 / 4096 : ℝ)*(t^(7 : ℕ)*w^(10 : ℕ)) +
    (7341759 / 2048 : ℝ)*(t^(7 : ℕ)*w^(12 : ℕ))) +
    ((1153674304057139134563135 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 0 +
    (35898733446328125 / 16777216 : ℝ)*(t^(8 : ℕ)*w^(1 : ℕ)))))) +
    (((((11075869895968272700827 / 68719476736 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 5 0 +
    (146752449890625 / 2097152 : ℝ)*(t^(8 : ℕ)*w^(3 : ℕ))) +
    ((1858657565633523543 / 2147483648 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 1 +
    (42133921875 / 32768 : ℝ)*(t^(8 : ℕ)*w^(5 : ℕ)))) +
    (((10988356612143753 / 134217728 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 3 +
    (52125440918031 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 5) +
    ((947795499 / 16384 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 7 +
    (59049 / 1024 : ℝ)*(t^(8 : ℕ)*w^(12 : ℕ))))) +
    ((((90103077219715620281055 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 0 +
    (571967989453125 / 4194304 : ℝ)*(t^(9 : ℕ)*w^(1 : ℕ))) +
    ((846745891849524179043 / 34359738368 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 6 0 +
    (4676865328125 / 2097152 : ℝ)*(t^(9 : ℕ)*w^(3 : ℕ)))) +
    (((3703379088304133415 / 2147483648 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 1 +
    (3872654797948695 / 67108864 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 3) +
    ((8026021626669 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 5 +
    (728959905 / 131072 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 7)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart2_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart2 u t w := by
  unfold oddCompactRemainderPart2 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart3 (u t w : ℝ) : ℝ :=
  ((((((2835940367480564027943 / 549755813888 : ℝ)*(t^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 0 +
    (47400662109375 / 16777216 : ℝ)*(t^(10 : ℕ)*w^(1 : ℕ))) +
    ((144094101999589893285 / 68719476736 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 7 0 +
    (161332609585107663 / 1073741824 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 1)) +
    (((22658636987343 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 3 +
    (121288122225 / 8388608 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 5) +
    ((531441 / 131072 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 7 +
    (245070028482603934041 / 549755813888 : ℝ)*(t^(11 : ℕ))))) +
    ((((1701910836104753097 / 17179869184 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 8 0 +
    (5379099463874799 / 1073741824 : ℝ)*(t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 8 1) +
    ((1117998277551 / 67108864 : ℝ)*(t^(11 : ℕ)*w^(6 : ℕ)) +
    (6209888085 / 8388608 : ℝ)*(t^(11 : ℕ)*w^(8 : ℕ)))) +
    (((37740017501004384045 / 549755813888 : ℝ)*(t^(12 : ℕ)) +
    (123237161304122403 / 68719476736 : ℝ)*(t^(3 : ℕ)*w^(2 : ℕ))*oddCompactUnitSlack u t w 0 9 0) +
    ((10149742413171 / 2147483648 : ℝ)*(t^(12 : ℕ)*w^(4 : ℕ)) +
    (393002213823 / 134217728 : ℝ)*(t^(12 : ℕ)*w^(6 : ℕ)))))) +
    (((((2285558488161902925 / 549755813888 : ℝ)*(t^(13 : ℕ)) +
    (1298564274349539 / 34359738368 : ℝ)*(t^(13 : ℕ)*w^(2 : ℕ))) +
    ((6381145478691 / 2147483648 : ℝ)*(t^(13 : ℕ)*w^(4 : ℕ)) +
    (70935792935599125 / 549755813888 : ℝ)*(t^(14 : ℕ)))) +
    (((109651836235275 / 68719476736 : ℝ)*(t^(14 : ℕ)*w^(2 : ℕ)) +
    (918751547143125 / 549755813888 : ℝ)*(t^(15 : ℕ))) +
    ((240024548301828125 / 16384 : ℝ)*(u^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1 +
    (2634363969518168151783 / 134217728 : ℝ)*(u^(1 : ℕ)*w^(5 : ℕ))))) +
    ((((11035800959046875 / 4096 : ℝ)*(u^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3 +
    (152368506587260825653 / 8388608 : ℝ)*(u^(1 : ℕ)*w^(7 : ℕ))) +
    ((809800578125 / 64 : ℝ)*(u^(1 : ℕ)*w^(8 : ℕ)) +
    (2408988147080913951 / 1048576 : ℝ)*(u^(1 : ℕ)*w^(9 : ℕ)))) +
    (((158727676441659 / 16384 : ℝ)*(u^(1 : ℕ)*w^(11 : ℕ)) +
    (1027043865 / 256 : ℝ)*(u^(1 : ℕ)*w^(13 : ℕ))) +
    ((21453915 / 4 : ℝ)*(u^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 12 +
    (599189394003328125 / 32768 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart3_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart3 u t w := by
  unfold oddCompactRemainderPart3 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart4 (u t w : ℝ) : ℝ :=
  ((((((809087621636378798235 / 67108864 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2 +
    (10761226222640625 / 4096 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3) +
    ((224043599466578670759 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(7 : ℕ)) +
    (302515265625 / 64 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(8 : ℕ)))) +
    (((1498954803477852483 / 524288 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(9 : ℕ)) +
    (41274949495149 / 8192 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(11 : ℕ))) +
    ((15782530023 / 128 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(13 : ℕ)) +
    (8296119 / 2 : ℝ)*(u^(1 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 12))) +
    ((((150829560495421875 / 16384 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1 +
    (167435665477038146691 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2) +
    ((4164745309171875 / 4096 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3 +
    (138066877239703065747 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(7 : ℕ)))) +
    (((42904546875 / 32 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 5 +
    (1542084928277809923 / 1048576 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(9 : ℕ))) +
    ((3229492169943 / 2048 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(11 : ℕ)) +
    (22127367375 / 256 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(13 : ℕ)))))) +
    (((((2522799 / 2 : ℝ)*(u^(1 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 12 +
    (76194546276234375 / 32768 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1) +
    ((2118116286995359965129 / 67108864 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 2 +
    (795570689953125 / 4096 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3)) +
    (((44863005600460586601 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(7 : ℕ)) +
    (28725046875 / 32 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 5) +
    ((52598444870550375 / 131072 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(9 : ℕ)) +
    (655142006115 / 1024 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(11 : ℕ))))) +
    ((((1560056031 / 64 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(13 : ℕ)) +
    (187272 / 1 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 12) +
    ((40789476608888671875 / 16777216 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 0 +
    (6392245230889995477317985 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 1 0)) +
    (((53015915939484375 / 131072 : ℝ)*(u^(1 : ℕ)*t^(4 : ℕ)*w^(2 : ℕ)) +
    (806392127761221781526355 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 0) +
    ((4574847659484375 / 16384 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 1 +
    (1847148348106306584441 / 134217728 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 2)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart4_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart4 u t w := by
  unfold oddCompactRemainderPart4 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart5 (u t w : ℝ) : ℝ :=
  ((((((71481498890625 / 4096 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 3 +
    (3797756635268054889 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(4 : ℕ)*w^(7 : ℕ))) +
    ((9536484375 / 64 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 5 +
    (31475529767854503 / 524288 : ℝ)*(u^(1 : ℕ)*t^(4 : ℕ)*w^(9 : ℕ)))) +
    (((1522349301663 / 8192 : ℝ)*(u^(1 : ℕ)*t^(4 : ℕ)*w^(11 : ℕ)) +
    (900685575 / 256 : ℝ)*(u^(1 : ℕ)*t^(4 : ℕ)*w^(13 : ℕ))) +
    ((53703 / 4 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 1 12 +
    (3716498630713359375 / 16777216 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 0))) +
    ((((1046529424988670670595613 / 8589934592 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 2 0 +
    (309343857163734375 / 2097152 : ℝ)*(u^(1 : ℕ)*t^(5 : ℕ)*w^(2 : ℕ))) +
    ((225168740684493604754841 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 0 +
    (145172167734375 / 32768 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 1)) +
    (((130441494212121894111 / 33554432 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 2 +
    (1153221046875 / 4096 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 3) +
    ((183884022246110067 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(5 : ℕ)*w^(7 : ℕ)) +
    (520171875 / 64 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 5)))) +
    (((((1038744348097581 / 262144 : ℝ)*(u^(1 : ℕ)*t^(5 : ℕ)*w^(9 : ℕ)) +
    (106524675207 / 4096 : ℝ)*(u^(1 : ℕ)*t^(5 : ℕ)*w^(11 : ℕ))) +
    ((35492823 / 128 : ℝ)*(u^(1 : ℕ)*t^(5 : ℕ)*w^(13 : ℕ)) +
    (729 / 2 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 2 12)) +
    (((6889106896171875 / 2097152 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 0 +
    (466747656476722676472213 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 3 0) +
    ((60507097332890625 / 2097152 : ℝ)*(u^(1 : ℕ)*t^(6 : ℕ)*w^(2 : ℕ)) +
    (10833184156431982205763 / 1073741824 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 0))) +
    ((((43302748078125 / 16384 : ℝ)*(u^(1 : ℕ)*t^(6 : ℕ)*w^(4 : ℕ)) +
    (12522772438549554393 / 16777216 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 2) +
    ((260606109375 / 4096 : ℝ)*(u^(1 : ℕ)*t^(6 : ℕ)*w^(6 : ℕ)) +
    (50424470833673277 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 4)) +
    (((72081776652633 / 524288 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 3 6 +
    (1192258359 / 1024 : ℝ)*(u^(1 : ℕ)*t^(6 : ℕ)*w^(11 : ℕ))) +
    ((2980881 / 256 : ℝ)*(u^(1 : ℕ)*t^(6 : ℕ)*w^(13 : ℕ)) +
    (5095044502734375 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(7 : ℕ)))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart5_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart5 u t w := by
  unfold oddCompactRemainderPart5 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart6 (u t w : ℝ) : ℝ :=
  ((((((8791837300022189896413 / 2147483648 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 4 0 +
    (6552091699734375 / 2097152 : ℝ)*(u^(1 : ℕ)*t^(7 : ℕ)*w^(2 : ℕ))) +
    ((1445154952116353976729 / 1073741824 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 0 +
    (8918346796875 / 32768 : ℝ)*(u^(1 : ℕ)*t^(7 : ℕ)*w^(4 : ℕ)))) +
    (((3250327619633823585 / 33554432 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 2 +
    (14044640625 / 4096 : ℝ)*(u^(1 : ℕ)*t^(7 : ℕ)*w^(6 : ℕ))) +
    ((10640326131666711 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 4 +
    (5597359823781 / 131072 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 6))) +
    ((((71298387 / 1024 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 4 8 +
    (6561 / 32 : ℝ)*(u^(1 : ℕ)*t^(7 : ℕ)*w^(13 : ℕ))) +
    ((3365447009765625 / 33554432 : ℝ)*(u^(1 : ℕ)*t^(8 : ℕ)) +
    (6727837445955051050007 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 5 0)) +
    (((737385766734375 / 4194304 : ℝ)*(u^(1 : ℕ)*t^(8 : ℕ)*w^(2 : ℕ)) +
    (517498267907326166667 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 0) +
    ((70223203125 / 8192 : ℝ)*(u^(1 : ℕ)*t^(8 : ℕ)*w^(4 : ℕ)) +
    (1076351899665323547 / 134217728 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 2)))) +
    (((((1667782916264151 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 4 +
    (2679108537645 / 1048576 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 6) +
    ((104142753 / 16384 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 5 8 +
    (79001103515625 / 33554432 : ℝ)*(u^(1 : ℕ)*t^(9 : ℕ)))) +
    (((151779086769379712445 / 8589934592 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(1 : ℕ))*oddCompactUnitSlack u t w 0 6 0 +
    (4171258265625 / 1048576 : ℝ)*(u^(1 : ℕ)*t^(9 : ℕ)*w^(2 : ℕ))) +
    ((27566705490867887265 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 0 +
    (23655908090631447 / 67108864 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 2))) +
    ((((39345649962813 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 4 +
    (12026923173 / 524288 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 6) +
    ((177147 / 8192 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 6 8 +
    (12957279307672879053 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(10 : ℕ)*w^(1 : ℕ)))) +
    (((219383411364630477 / 2147483648 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 0 +
    (18476844675363 / 16777216 : ℝ)*(u^(1 : ℕ)*t^(3 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 7 2) +
    ((1923389318583 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(10 : ℕ)*w^(7 : ℕ)) +
    (2091220335 / 1048576 : ℝ)*(u^(1 : ℕ)*t^(10 : ℕ)*w^(9 : ℕ)))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart6_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart6 u t w := by
  unfold oddCompactRemainderPart6 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart7 (u t w : ℝ) : ℝ :=
  ((((((753952312098019701 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(11 : ℕ)*w^(1 : ℕ)) +
    (21485303606626281 / 2147483648 : ℝ)*(u^(1 : ℕ)*t^(11 : ℕ)*w^(3 : ℕ))) +
    ((39293188823547 / 67108864 : ℝ)*(u^(1 : ℕ)*t^(11 : ℕ)*w^(5 : ℕ)) +
    (98468045685 / 8388608 : ℝ)*(u^(1 : ℕ)*t^(11 : ℕ)*w^(7 : ℕ)))) +
    (((208695576350872917 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(12 : ℕ)*w^(1 : ℕ)) +
    (2817646733384307 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(12 : ℕ)*w^(3 : ℕ))) +
    ((2410614781677 / 134217728 : ℝ)*(u^(1 : ℕ)*t^(12 : ℕ)*w^(5 : ℕ)) +
    (3536971697730573 / 8589934592 : ℝ)*(u^(1 : ℕ)*t^(13 : ℕ)*w^(1 : ℕ))))) +
    ((((53599562474553 / 4294967296 : ℝ)*(u^(1 : ℕ)*t^(13 : ℕ)*w^(3 : ℕ)) +
    (98227953927225 / 17179869184 : ℝ)*(u^(1 : ℕ)*t^(14 : ℕ)*w^(1 : ℕ))) +
    ((78706066742185645779805 / 1073741824 : ℝ)*(u^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1 +
    (115611774595515625 / 49152 : ℝ)*(u^(2 : ℕ)*w^(5 : ℕ)))) +
    (((2405231604171744158707 / 67108864 : ℝ)*(u^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3 +
    (383139605078125 / 1536 : ℝ)*(u^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 4) +
    ((19937604299662202459 / 4194304 : ℝ)*(u^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 5 +
    (11672306170579587 / 131072 : ℝ)*(u^(2 : ℕ)*w^(10 : ℕ)))))) +
    (((((4861659002321 / 2048 : ℝ)*(u^(2 : ℕ)*w^(12 : ℕ)) +
    (759484775 / 32 : ℝ)*(u^(2 : ℕ)*w^(14 : ℕ))) +
    ((167042 / 1 : ℝ)*(u^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 13 +
    (37645168179993161399097 / 268435456 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1)) +
    (((44360976794953125 / 16384 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(5 : ℕ)) +
    (4693101176153517056391 / 67108864 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3) +
    ((6939437453125 / 32 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 4 +
    (14015343875371794207 / 2097152 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 5))) +
    ((((18480028742161329 / 131072 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(10 : ℕ)) +
    (781752079293 / 1024 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(12 : ℕ))) +
    ((876455961 / 32 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(14 : ℕ)) +
    (117912 / 1 : ℝ)*(u^(2 : ℕ)*t^(1 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 13)) +
    (((70550195278491646861887 / 536870912 : ℝ)*(u^(2 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 1 +
    (21988715306203125 / 16384 : ℝ)*(u^(2 : ℕ)*t^(2 : ℕ)*w^(5 : ℕ))) +
    ((3795277913820698620473 / 67108864 : ℝ)*(u^(2 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 3 +
    (35039464640625 / 512 : ℝ)*(u^(2 : ℕ)*t^(2 : ℕ)*w^(3 : ℕ))*oddCompactUnitSlack u t w 0 0 4)))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart7_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart7 u t w := by
  unfold oddCompactRemainderPart7 oddCompactUnitSlack
  positivity

end
end HTGeometry
