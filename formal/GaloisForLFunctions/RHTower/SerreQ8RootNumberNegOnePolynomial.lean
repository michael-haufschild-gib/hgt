import GaloisForLFunctions.RHTower.SerreQ8RootNumberNegOneTopRadicand

/-!
# Serre's displayed Q8 witness polynomial

Example 1.3 of Fiorilli--Jouve records Serre's actual quaternionic witness as
the root field of

`X^8 - 205 X^6 + 13940 X^4 - 378225 X^2 + 3404025`.

This leaf proves that the explicitly constructed radical tower contains that
literal root: it is one half of the top radical.  This identifies the exact
published polynomial without treating a paper citation as an unproved Lean
assumption.  It does not yet prove that this polynomial alone presents the
whole tower, nor the global epsilon-factor calculation of root number `-1`.
-/

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => SerreQ8TopField

/-- The published Serre generator is half the literal top radical. -/
def serreQ8PublishedRoot : K3 := serreQ8TopRoot / 2

/-- The unscaled top radical satisfies the integral eliminant before the
standard `1/2` normalization of Serre's displayed root. -/
theorem serreQ8_topRoot_raw_eliminant :
    serreQ8TopRoot ^ 8 - 820 * serreQ8TopRoot ^ 6 + 223040 * serreQ8TopRoot ^ 4 -
      24206400 * serreQ8TopRoot ^ 2 + 871430400 = 0 := by
  let e : K2 →+* K3 := AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
  let x : K3 := e (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)
  let y : K3 := e deningerQ8RootNumberNegOneSecondQuadraticRoot
  have hx : x ^ 2 = 5 := by
    unfold x e
    rw [← map_pow]
    change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (deningerQ8RootNumberNegOneFirstQuadraticRoot ^ 2 : K2) = (5 : K3)
    rw [show (deningerQ8RootNumberNegOneFirstQuadraticRoot ^ 2 : K2) = 5 by
      rw [← map_pow, deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
      exact (map_natCast
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm]
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 5).symm
  have hy : y ^ 2 = 41 := by
    unfold y e
    rw [← map_pow, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 41).symm
  have h5K2 :
      AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (5 : K1) =
        (5 : K2) := by
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm
  have h41K2 :
      AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (41 : K1) =
        (41 : K2) := by
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm
  have h5K3 : e (5 : K2) = (5 : K3) := by
    unfold e
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 5).symm
  have h41K3 : e (41 : K2) = (41 : K3) := by
    unfold e
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 41).symm
  have hz : serreQ8TopRoot ^ 2 = (5 + x) * (41 + x * y) := by
    rw [serreQ8TopRoot_sq]
    change e ((serreQ8TopR : K2) * serreQ8TopS) = (5 + x) * (41 + x * y)
    dsimp [e, serreQ8TopR, serreQ8TopS, x, y]
    simp only [map_add, map_mul]
    rw [h5K2, h41K2, h5K3, h41K3]
  rw [show serreQ8TopRoot ^ 8 = (serreQ8TopRoot ^ 2) ^ 4 by ring,
    show serreQ8TopRoot ^ 6 = (serreQ8TopRoot ^ 2) ^ 3 by ring,
    show serreQ8TopRoot ^ 4 = (serreQ8TopRoot ^ 2) ^ 2 by ring, hz]
  have hx3 : x ^ 3 = 5 * x := by
    calc x ^ 3 = x * x ^ 2 := by ring
      _ = 5 * x := by rw [hx]; ring
  have hx4 : x ^ 4 = 25 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = 25 := by rw [hx]; norm_num
  have hx5 : x ^ 5 = 25 * x := by
    calc x ^ 5 = x * x ^ 4 := by ring
      _ = 25 * x := by rw [hx4]; ring
  have hx6 : x ^ 6 = 125 := by
    calc x ^ 6 = x ^ 2 * x ^ 4 := by ring
      _ = 125 := by rw [hx, hx4]; norm_num
  have hx7 : x ^ 7 = 125 * x := by
    calc x ^ 7 = x * x ^ 6 := by ring
      _ = 125 * x := by rw [hx6]; ring
  have hx8 : x ^ 8 = 625 := by
    calc x ^ 8 = x ^ 4 * x ^ 4 := by ring
      _ = 625 := by rw [hx4]; norm_num
  have hy3 : y ^ 3 = 41 * y := by
    calc y ^ 3 = y * y ^ 2 := by ring
      _ = 41 * y := by rw [hy]; ring
  have hy4 : y ^ 4 = 1681 := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = 1681 := by rw [hy]; norm_num
  ring_nf
  simp only [hx8, hx7, hx6, hx5, hx4, hx3, hx, hy4, hy3, hy]
  ring

/-- The literal published Serre polynomial vanishes at the normalized radical
generator. -/
theorem serreQ8_publishedRoot_eliminant :
    serreQ8PublishedRoot ^ 8 - 205 * serreQ8PublishedRoot ^ 6 +
      13940 * serreQ8PublishedRoot ^ 4 - 378225 * serreQ8PublishedRoot ^ 2 +
        3404025 = 0 := by
  unfold serreQ8PublishedRoot
  have h := serreQ8_topRoot_raw_eliminant
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  calc
    (serreQ8TopRoot / 2) ^ 8 - 205 * (serreQ8TopRoot / 2) ^ 6 +
        13940 * (serreQ8TopRoot / 2) ^ 4 - 378225 * (serreQ8TopRoot / 2) ^ 2 +
          3404025 =
        (serreQ8TopRoot ^ 8 - 820 * serreQ8TopRoot ^ 6 + 223040 * serreQ8TopRoot ^ 4 -
          24206400 * serreQ8TopRoot ^ 2 + 871430400) / 256 := by ring
    _ = 0 := by rw [h]; norm_num

end

end RHTower
