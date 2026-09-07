import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactRemainder5

/-!
# Nonnegative compact remainder, group 6

Every summand is a nonnegative monomial or a nonnegative monomial times
an exact unit-cube complement. This module proves only the remainder sign.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart48 (u t w : ℝ) : ℝ :=
  ((((((3942775715 / 78364164096 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 17 0 3 +
    (571047159263833 / 5015306502144 : ℝ)*(u^20*t^3)) +
    ((4512441521 / 362797056 : ℝ)*(u^20*t^3*w^2) +
    (65060815231 / 104485552128 : ℝ)*(u^3*t^3*w^3)*oddCompactUnitSlack u t w 17 0 1)) +
    (((60828939594035 / 10030613004288 : ℝ)*(u^20*t^4) +
    (146704724963 / 208971104256 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 17 1 0) +
    ((968911079525 / 3343537668096 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 17 2 0 +
    (2278828352887667 / 25389989167104 : ℝ)*(u^21*w^1)))) +
    ((((1820233912021513 / 25389989167104 : ℝ)*(u^21*w^3) +
    (268374429295 / 264479053824 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 18 0 2) +
    ((4638025 / 90699264 : ℝ)*(u^21*w^7) +
    (1481833255465 / 33059881728 : ℝ)*(u^21*t^1*w^1))) +
    (((150197463571109 / 2821109907456 : ℝ)*(u^21*t^1*w^3) +
    (17992625735 / 44079842304 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 18 0 2) +
    ((272825 / 30233088 : ℝ)*(u^21*t^1*w^7) +
    (2366773068539 / 156728328192 : ℝ)*(u^21*t^2*w^1))))) +
    (((((11308793647537 / 940369969152 : ℝ)*(u^21*t^2*w^3) +
    (1188148255 / 29386561536 : ℝ)*(u^3*t^2*w^3)*oddCompactUnitSlack u t w 18 0 2) +
    ((419081157971 / 117546246144 : ℝ)*(u^21*t^3*w^1) +
    (807019613741 / 940369969152 : ℝ)*(u^21*t^3*w^3))) +
    (((99732071039 / 313456656384 : ℝ)*(u^21*t^4*w^1) +
    (61306641760463779 / 1828079220031488 : ℝ)*(u^22)) +
    ((87723594463187 / 6347497291776 : ℝ)*(u^22*w^2) +
    (1211916078785 / 1586874322944 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 19 0 1))) +
    ((((291904025 / 9795520512 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 19 0 3 +
    (4224141722070899 / 152339935002624 : ℝ)*(u^22*t^1)) +
    ((3068610969533 / 2115832430592 : ℝ)*(u^22*t^1*w^2) +
    (66127394435 / 528958107648 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 19 0 1)) +
    (((17170825 / 3265173504 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 19 0 3 +
    (202283142691903 / 33853318889472 : ℝ)*(u^22*t^2)) +
    ((839573243251 / 705277476864 : ℝ)*(u^3*t^2*w^2)*oddCompactUnitSlack u t w 19 0 0 +
    (151817255 / 88159684608 : ℝ)*(u^22*t^2*w^4))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart48_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart48 u t w := by
  unfold oddCompactRemainderPart48 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart49 (u t w : ℝ) : ℝ :=
  ((((((1738885718713 / 16926659444736 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 19 0 0 +
    (4683254389 / 26121388032 : ℝ)*(u^3*t^3*w^2)*oddCompactUnitSlack u t w 19 0 0) +
    ((2117753926325 / 22568879259648 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 19 1 0 +
    (416028875753 / 1586874322944 : ℝ)*(u^23*w^1))) +
    (((3730901641735 / 3173748645888 : ℝ)*(u^23*w^3) +
    (86611175 / 7346640384 : ℝ)*(u^3*w^3)*oddCompactUnitSlack u t w 20 0 2) +
    ((1268635009781 / 1586874322944 : ℝ)*(u^23*t^1*w^1) +
    (3594160895 / 8264970432 : ℝ)*(u^23*t^1*w^3)))) +
    ((((5094775 / 2448880128 : ℝ)*(u^3*t^1*w^3)*oddCompactUnitSlack u t w 20 0 2 +
    (180263778593 / 528958107648 : ℝ)*(u^23*t^2*w^1)) +
    ((14152223065 / 352638738432 : ℝ)*(u^23*t^2*w^3) +
    (6468048743 / 176319369216 : ℝ)*(u^23*t^3*w^1))) +
    (((8953254800363 / 19042491875328 : ℝ)*(u^24) +
    (5450615596535 / 28563737812992 : ℝ)*(u^3*w^2)*oddCompactUnitSlack u t w 21 0 0) +
    ((1572474925 / 176319369216 : ℝ)*(u^24*w^4) +
    (1169342236211 / 19042491875328 : ℝ)*(u^24*t^1))))) +
    (((((549923593855 / 4760622968832 : ℝ)*(u^3*t^1*w^2)*oddCompactUnitSlack u t w 21 0 0 +
    (92498525 / 58773123072 : ℝ)*(u^24*t^1*w^4)) +
    ((491298745987 / 6347497291776 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 21 0 0 +
    (45836631815 / 3173748645888 : ℝ)*(u^3*t^2*w^2)*oddCompactUnitSlack u t w 21 0 0)) +
    (((32256196957 / 2115832430592 : ℝ)*(u^3*t^3)*oddCompactUnitSlack u t w 21 0 0 +
    (84127889885 / 2677850419968 : ℝ)*(u^25*w^1)) +
    ((555792475 / 176319369216 : ℝ)*(u^25*w^3) +
    (142404524155 / 7140934453248 : ℝ)*(u^25*t^1*w^1)))) +
    ((((32693675 / 58773123072 : ℝ)*(u^25*t^1*w^3) +
    (6047936995 / 2380311484416 : ℝ)*(u^25*t^2*w^1)) +
    ((1408295606765 / 257073640316928 : ℝ)*(u^3)*oddCompactUnitSlack u t w 23 0 0 +
    (1881410825 / 793437161472 : ℝ)*(u^3*w^2)*oddCompactUnitSlack u t w 23 0 0)) +
    (((609680905415 / 85691213438976 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 23 0 0 +
    (110671225 / 264479053824 : ℝ)*(u^3*t^1*w^2)*oddCompactUnitSlack u t w 23 0 0) +
    ((20782527055 / 14281868906496 : ℝ)*(u^3*t^2)*oddCompactUnitSlack u t w 23 0 0 +
    (3018794975 / 7140934453248 : ℝ)*(u^27*w^1))))))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart49_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart49 u t w := by
  unfold oddCompactRemainderPart49 oddCompactUnitSlack
  positivity

/-- A group of explicitly nonnegative discarded monomials and complements. -/
def oddCompactRemainderPart50 (u t w : ℝ) : ℝ :=
  (((177576175 / 2380311484416 : ℝ)*(u^27*t^1*w^1) +
    (38616544925 / 171382426877952 : ℝ)*(u^3)*oddCompactUnitSlack u t w 25 0 0) +
    ((4408401025 / 57127475625984 : ℝ)*(u^3*t^1)*oddCompactUnitSlack u t w 25 0 0 +
    (2786875 / 1586874322944 : ℝ)*(u^3)*oddCompactUnitSlack u t w 27 0 0))

/-- The remainder group is nonnegative for nonnegative coordinates. -/
theorem oddCompactRemainderPart50_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainderPart50 u t w := by
  unfold oddCompactRemainderPart50 oddCompactUnitSlack
  positivity

end
end HTGeometry
