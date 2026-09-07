import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactModel

/-!
# Real scalar source jets in the compact chart

Each modular polynomial evaluates to a real scalar polynomial. This normalization
separates complex source incidence from the real polynomial determinant proof.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar normalized source derivative of order 0. -/
def oddCompactSourceScalar0 (u a w : ℝ) : ℝ :=
  ((-3 / 8 : ℝ) +
    ((1 / 16 : ℝ)*a^1 +
    (1 / 24 : ℝ)*u^2))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar0_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 0) =
      (oddCompactSourceScalar0 u a w : ℂ) := by
  rw [oddCompactSourceJet0_eq]
  simp only [oddCompactSourceJet0, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar0
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 1. -/
def oddCompactSourceScalar1 (u a w : ℝ) : ℝ :=
  (((-1 / 8 : ℝ)*a^1*w^1 +
    (-5 / 16 : ℝ)*u^1) +
    ((7 / 96 : ℝ)*u^1*a^1 +
    (5 / 144 : ℝ)*u^3))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar1_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 1) =
      (oddCompactSourceScalar1 u a w : ℂ) := by
  rw [oddCompactSourceJet1_eq]
  simp only [oddCompactSourceJet1, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar1
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 2. -/
def oddCompactSourceScalar2 (u a w : ℝ) : ℝ :=
  ((((15 / 16 : ℝ) +
    (-45 / 64 : ℝ)*a^1) +
    ((1 / 4 : ℝ)*a^1*w^2 +
    (-1 / 128 : ℝ)*a^2)) +
    (((-1 / 4 : ℝ)*u^1*a^1*w^1 +
    (-15 / 32 : ℝ)*u^2) +
    ((25 / 288 : ℝ)*u^2*a^1 +
    (35 / 864 : ℝ)*u^4)))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar2_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 2) =
      (oddCompactSourceScalar2 u a w : ℂ) := by
  rw [oddCompactSourceJet2_eq]
  simp only [oddCompactSourceJet2, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar2
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 3. -/
def oddCompactSourceScalar3 (u a w : ℝ) : ℝ :=
  ((((101 / 32 : ℝ)*a^1*w^1 +
    (-1 / 2 : ℝ)*a^1*w^3) +
    ((3 / 32 : ℝ)*a^2*w^1 +
    ((95 / 32 : ℝ)*u^1 +
    (-707 / 384 : ℝ)*u^1*a^1))) +
    (((7 / 8 : ℝ)*u^1*a^1*w^2 +
    ((1 / 256 : ℝ)*u^1*a^2 +
    (-17 / 48 : ℝ)*u^2*a^1*w^1)) +
    ((-505 / 576 : ℝ)*u^3 +
    ((239 / 1728 : ℝ)*u^3*a^1 +
    (35 / 576 : ℝ)*u^5))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar3_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 3) =
      (oddCompactSourceScalar3 u a w : ℂ) := by
  rw [oddCompactSourceJet3_eq]
  simp only [oddCompactSourceJet3, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar3
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 4. -/
def oddCompactSourceScalar4 (u a w : ℝ) : ℝ :=
  (((((-285 / 32 : ℝ) +
    (225 / 16 : ℝ)*a^1) +
    ((-191 / 16 : ℝ)*a^1*w^2 +
    (1 / 1 : ℝ)*a^1*w^4)) +
    (((191 / 512 : ℝ)*a^2 +
    (-15 / 32 : ℝ)*a^2*w^2) +
    ((51 / 1024 : ℝ)*a^3 +
    ((191 / 16 : ℝ)*u^1*a^1*w^1 +
    (-17 / 6 : ℝ)*u^1*a^1*w^3)))) +
    ((((13 / 32 : ℝ)*u^1*a^2*w^1 +
    (75 / 8 : ℝ)*u^2) +
    ((-4775 / 1152 : ℝ)*u^2*a^1 +
    (95 / 48 : ℝ)*u^2*a^1*w^2)) +
    (((241 / 1536 : ℝ)*u^2*a^2 +
    (-181 / 432 : ℝ)*u^3*a^1*w^1) +
    ((-6685 / 3456 : ℝ)*u^4 +
    ((6439 / 20736 : ℝ)*u^4*a^1 +
    (385 / 3456 : ℝ)*u^6)))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar4_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 4) =
      (oddCompactSourceScalar4 u a w : ℂ) := by
  rw [oddCompactSourceJet4_eq]
  simp only [oddCompactSourceJet4, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar4
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 5. -/
def oddCompactSourceScalar5 (u a w : ℝ) : ℝ :=
  (((((-1787 / 16 : ℝ)*a^1*w^1 +
    ((323 / 8 : ℝ)*a^1*w^3 +
    (-2 / 1 : ℝ)*a^1*w^5)) +
    ((-969 / 128 : ℝ)*a^2*w^1 +
    ((7 / 4 : ℝ)*a^2*w^3 +
    (-237 / 512 : ℝ)*a^3*w^1))) +
    (((-3695 / 64 : ℝ)*u^1 +
    ((12509 / 192 : ℝ)*u^1*a^1 +
    (-2261 / 32 : ℝ)*u^1*a^1*w^2)) +
    ((17 / 2 : ℝ)*u^1*a^1*w^4 +
    ((-323 / 1024 : ℝ)*u^1*a^2 +
    (-231 / 64 : ℝ)*u^1*a^2*w^2)))) +
    ((((915 / 2048 : ℝ)*u^1*a^3 +
    ((5491 / 192 : ℝ)*u^2*a^1*w^1 +
    (-731 / 72 : ℝ)*u^2*a^1*w^3)) +
    ((259 / 384 : ℝ)*u^2*a^2*w^1 +
    ((8935 / 288 : ℝ)*u^3 +
    (-77197 / 6912 : ℝ)*u^3*a^1))) +
    (((2797 / 864 : ℝ)*u^3*a^1*w^2 +
    ((26075 / 27648 : ℝ)*u^3*a^2 +
    (-587 / 1152 : ℝ)*u^4*a^1*w^1)) +
    ((-11305 / 2304 : ℝ)*u^5 +
    ((108737 / 124416 : ℝ)*u^5*a^1 +
    (5005 / 20736 : ℝ)*u^7)))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar5_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 5) =
      (oddCompactSourceScalar5 u a w : ℂ) := by
  rw [oddCompactSourceJet5_eq]
  simp only [oddCompactSourceJet5, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar5
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 6. -/
def oddCompactSourceScalar6 (u a w : ℝ) : ℝ :=
  ((((((11085 / 64 : ℝ) +
    (-118305 / 256 : ℝ)*a^1) +
    ((21683 / 32 : ℝ)*a^1*w^2 +
    (-505 / 4 : ℝ)*a^1*w^4)) +
    (((4 / 1 : ℝ)*a^1*w^6 +
    (-21683 / 1024 : ℝ)*a^2) +
    ((7575 / 128 : ℝ)*a^2*w^2 +
    (-45 / 8 : ℝ)*a^2*w^4))) +
    ((((-25755 / 4096 : ℝ)*a^3 +
    (345 / 128 : ℝ)*a^3*w^2) +
    ((849 / 8192 : ℝ)*a^4 +
    (-21683 / 32 : ℝ)*u^1*a^1*w^1)) +
    (((8585 / 24 : ℝ)*u^1*a^1*w^3 +
    (-24 / 1 : ℝ)*u^1*a^1*w^5) +
    ((-6565 / 128 : ℝ)*u^1*a^2*w^1 +
    ((20 / 1 : ℝ)*u^1*a^2*w^3 +
    (-725 / 128 : ℝ)*u^1*a^3*w^1))))) +
    (((((-39435 / 128 : ℝ)*u^2 +
    (542075 / 2304 : ℝ)*u^2*a^1) +
    ((-47975 / 192 : ℝ)*u^2*a^1*w^2 +
    (45 / 1 : ℝ)*u^2*a^1*w^4)) +
    (((-121705 / 6144 : ℝ)*u^2*a^2 +
    (-515 / 32 : ℝ)*u^2*a^2*w^2) +
    ((7925 / 3072 : ℝ)*u^2*a^3 +
    ((91405 / 1728 : ℝ)*u^3*a^1*w^1 +
    (-1495 / 54 : ℝ)*u^3*a^1*w^3)))) +
    ((((-85 / 32 : ℝ)*u^3*a^2*w^1 +
    (758905 / 6912 : ℝ)*u^4) +
    ((-3251695 / 82944 : ℝ)*u^4*a^1 +
    (75 / 32 : ℝ)*u^4*a^1*w^2)) +
    (((118135 / 27648 : ℝ)*u^4*a^2 +
    (-407 / 288 : ℝ)*u^5*a^1*w^1) +
    ((-194425 / 13824 : ℝ)*u^6 +
    ((514381 / 186624 : ℝ)*u^6*a^1 +
    (25025 / 41472 : ℝ)*u^8))))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar6_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 6) =
      (oddCompactSourceScalar6 u a w : ℂ) := by
  rw [oddCompactSourceJet6_eq]
  simp only [oddCompactSourceJet6, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar6
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 7. -/
def oddCompactSourceScalar7 (u a w : ℝ) : ℝ :=
  ((((((725429 / 128 : ℝ)*a^1*w^1 +
    (-55013 / 16 : ℝ)*a^1*w^3) +
    ((745 / 2 : ℝ)*a^1*w^5 +
    ((-8 / 1 : ℝ)*a^1*w^7 +
    (165039 / 256 : ℝ)*a^2*w^1))) +
    (((-5215 / 16 : ℝ)*a^2*w^3 +
    ((33 / 2 : ℝ)*a^2*w^5 +
    (176565 / 2048 : ℝ)*a^3*w^1)) +
    ((-795 / 64 : ℝ)*a^3*w^3 +
    ((-2439 / 1024 : ℝ)*a^4*w^1 +
    (240305 / 128 : ℝ)*u^1)))) +
    ((((-5078003 / 1536 : ℝ)*u^1*a^1 +
    (385091 / 64 : ℝ)*u^1*a^1*w^2) +
    ((-12665 / 8 : ℝ)*u^1*a^1*w^4 +
    ((194 / 3 : ℝ)*u^1*a^1*w^6 +
    (55013 / 2048 : ℝ)*u^1*a^2))) +
    (((172095 / 256 : ℝ)*u^1*a^2*w^2 +
    ((-1415 / 16 : ℝ)*u^1*a^2*w^4 +
    (-681675 / 8192 : ℝ)*u^1*a^3)) +
    ((11235 / 256 : ℝ)*u^1*a^3*w^2 +
    ((17283 / 16384 : ℝ)*u^1*a^4 +
    (-935221 / 384 : ℝ)*u^2*a^1*w^1))))) +
    (((((544595 / 288 : ℝ)*u^2*a^1*w^3 +
    (-530 / 3 : ℝ)*u^2*a^1*w^5) +
    ((-192955 / 1536 : ℝ)*u^2*a^2*w^1 +
    ((1645 / 12 : ℝ)*u^2*a^2*w^3 +
    (-21995 / 512 : ℝ)*u^2*a^3*w^1))) +
    (((-3627145 / 2304 : ℝ)*u^3 +
    ((13148107 / 13824 : ℝ)*u^3*a^1 +
    (-2083765 / 3456 : ℝ)*u^3*a^1*w^2)) +
    ((10055 / 54 : ℝ)*u^3*a^1*w^4 +
    ((-19425875 / 110592 : ℝ)*u^3*a^2 +
    (-26155 / 576 : ℝ)*u^3*a^2*w^2)))) +
    ((((228215 / 18432 : ℝ)*u^3*a^3 +
    ((437315 / 4608 : ℝ)*u^4*a^1*w^1 +
    (-67855 / 1296 : ℝ)*u^4*a^1*w^3)) +
    ((-221665 / 6912 : ℝ)*u^4*a^2*w^1 +
    ((1925455 / 4608 : ℝ)*u^5 +
    (-81009065 / 497664 : ℝ)*u^5*a^1))) +
    (((-46603 / 5184 : ℝ)*u^5*a^1*w^2 +
    ((2905603 / 165888 : ℝ)*u^5*a^2 +
    (-746851 / 93312 : ℝ)*u^6*a^1*w^1)) +
    ((-3728725 / 82944 : ℝ)*u^7 +
    ((10389355 / 1119744 : ℝ)*u^7*a^1 +
    (425425 / 248832 : ℝ)*u^9))))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar7_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 7) =
      (oddCompactSourceScalar7 u a w : ℂ) := by
  rw [oddCompactSourceJet7_eq]
  simp only [oddCompactSourceJet7, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar7
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 8. -/
def oddCompactSourceScalar8 (u a w : ℝ) : ℝ :=
  ((((((-720915 / 128 : ℝ) +
    ((5801175 / 256 : ℝ)*a^1 +
    (-1600507 / 32 : ℝ)*a^1*w^2)) +
    (((15351 / 1 : ℝ)*a^1*w^4 +
    (-1051 / 1 : ℝ)*a^1*w^6) +
    ((16 / 1 : ℝ)*a^1*w^8 +
    (1600507 / 1024 : ℝ)*a^2))) +
    ((((-230265 / 32 : ℝ)*a^2*w^2 +
    (47295 / 32 : ℝ)*a^2*w^4) +
    ((-91 / 2 : ℝ)*a^2*w^6 +
    (782901 / 1024 : ℝ)*a^3)) +
    (((-362595 / 512 : ℝ)*a^3*w^2 +
    (3165 / 64 : ℝ)*a^3*w^4) +
    ((-892299 / 32768 : ℝ)*a^4 +
    (34137 / 1024 : ℝ)*a^4*w^2)))) +
    ((((-26199 / 65536 : ℝ)*a^5 +
    ((1600507 / 32 : ℝ)*u^1*a^1*w^1 +
    (-86989 / 2 : ℝ)*u^1*a^1*w^3)) +
    (((6306 / 1 : ℝ)*u^1*a^1*w^5 +
    (-168 / 1 : ℝ)*u^1*a^1*w^7) +
    ((199563 / 32 : ℝ)*u^1*a^2*w^1 +
    (-5255 / 1 : ℝ)*u^1*a^2*w^3))) +
    ((((681 / 2 : ℝ)*u^1*a^2*w^5 +
    (761975 / 512 : ℝ)*u^1*a^3*w^1) +
    ((-16735 / 64 : ℝ)*u^1*a^3*w^3 +
    (-31719 / 1024 : ℝ)*u^1*a^4*w^1)) +
    (((1933725 / 128 : ℝ)*u^2 +
    (-40012675 / 2304 : ℝ)*u^2*a^1) +
    ((486115 / 16 : ℝ)*u^2*a^1*w^2 +
    (-47295 / 4 : ℝ)*u^2*a^1*w^4))))) +
    (((((5687 / 9 : ℝ)*u^2*a^1*w^6 +
    ((1233197 / 512 : ℝ)*u^2*a^2 +
    (541265 / 128 : ℝ)*u^2*a^2*w^2)) +
    (((-79945 / 96 : ℝ)*u^2*a^2*w^4 +
    (-8329175 / 12288 : ℝ)*u^2*a^3) +
    ((221895 / 512 : ℝ)*u^2*a^3*w^2 +
    (208959 / 32768 : ℝ)*u^2*a^4))) +
    ((((-926177 / 144 : ℝ)*u^3*a^1*w^1 +
    (1571245 / 216 : ℝ)*u^3*a^1*w^3) +
    ((-27602 / 27 : ℝ)*u^3*a^1*w^5 +
    (89335 / 128 : ℝ)*u^3*a^2*w^1)) +
    (((38165 / 54 : ℝ)*u^3*a^2*w^3 +
    (-1201945 / 4608 : ℝ)*u^3*a^3*w^1) +
    ((-56017745 / 6912 : ℝ)*u^4 +
    (32948363 / 6912 : ℝ)*u^4*a^1)))) +
    (((((-78825 / 128 : ℝ)*u^4*a^1*w^2 +
    (134395 / 216 : ℝ)*u^4*a^1*w^4) +
    ((-124159885 / 110592 : ℝ)*u^4*a^2 +
    (-4685 / 768 : ℝ)*u^4*a^2*w^2)) +
    (((12064865 / 221184 : ℝ)*u^4*a^3 +
    (427757 / 1152 : ℝ)*u^5*a^1*w^1) +
    ((947 / 3888 : ℝ)*u^5*a^1*w^3 +
    (-4245367 / 20736 : ℝ)*u^5*a^2*w^1))) +
    ((((1970045 / 1152 : ℝ)*u^6 +
    (-540614431 / 746496 : ℝ)*u^6*a^1) +
    ((-4419709 / 93312 : ℝ)*u^6*a^1*w^2 +
    (208106413 / 2985984 : ℝ)*u^6*a^2)) +
    (((-4220461 / 93312 : ℝ)*u^7*a^1*w^1 +
    (-26301275 / 165888 : ℝ)*u^8) +
    ((885697661 / 26873856 : ℝ)*u^8*a^1 +
    (8083075 / 1492992 : ℝ)*u^10))))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar8_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 8) =
      (oddCompactSourceScalar8 u a w : ℂ) := by
  rw [oddCompactSourceJet8_eq]
  simp only [oddCompactSourceJet8, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar8
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 9. -/
def oddCompactSourceScalar9 (u a w : ℝ) : ℝ :=
  (((((((-50615371 / 128 : ℝ)*a^1*w^1 +
    (5653171 / 16 : ℝ)*a^1*w^3) +
    ((-62232 / 1 : ℝ)*a^1*w^5 +
    (2862 / 1 : ℝ)*a^1*w^7)) +
    (((-32 / 1 : ℝ)*a^1*w^9 +
    (-16959513 / 256 : ℝ)*a^2*w^1) +
    ((54453 / 1 : ℝ)*a^2*w^3 +
    ((-47223 / 8 : ℝ)*a^2*w^5 +
    (120 / 1 : ℝ)*a^2*w^7)))) +
    ((((-1843623 / 128 : ℝ)*a^3*w^1 +
    (1137645 / 256 : ℝ)*a^3*w^3) +
    ((-5691 / 32 : ℝ)*a^3*w^5 +
    ((3490209 / 4096 : ℝ)*a^4*w^1 +
    (-93159 / 256 : ℝ)*a^4*w^3))) +
    (((462123 / 32768 : ℝ)*a^5*w^1 +
    (-23445005 / 256 : ℝ)*u^1) +
    ((354307597 / 1536 : ℝ)*u^1*a^1 +
    ((-39572197 / 64 : ℝ)*u^1*a^1*w^2 +
    (264486 / 1 : ℝ)*u^1*a^1*w^4))))) +
    (((((-46269 / 2 : ℝ)*u^1*a^1*w^6 +
    (424 / 1 : ℝ)*u^1*a^1*w^8) +
    ((-5653171 / 2048 : ℝ)*u^1*a^2 +
    (-1796949 / 16 : ℝ)*u^1*a^2*w^2)) +
    (((2024865 / 64 : ℝ)*u^1*a^2*w^4 +
    (-4767 / 4 : ℝ)*u^1*a^2*w^6) +
    ((7117785 / 512 : ℝ)*u^1*a^3 +
    ((-16077285 / 1024 : ℝ)*u^1*a^3*w^2 +
    (167825 / 128 : ℝ)*u^1*a^3*w^4)))) +
    ((((-24731973 / 65536 : ℝ)*u^1*a^4 +
    (1138005 / 2048 : ℝ)*u^1*a^4*w^2) +
    ((-784995 / 131072 : ℝ)*u^1*a^5 +
    ((96103907 / 384 : ℝ)*u^2*a^1*w^1 +
    (-1895483 / 6 : ℝ)*u^2*a^1*w^3))) +
    (((126405 / 2 : ℝ)*u^2*a^1*w^5 +
    (-6310 / 3 : ℝ)*u^2*a^1*w^7) +
    ((671587 / 32 : ℝ)*u^2*a^2*w^1 +
    ((-784665 / 16 : ℝ)*u^2*a^2*w^3 +
    (33369 / 8 : ℝ)*u^2*a^2*w^5)))))) +
    ((((((31474845 / 2048 : ℝ)*u^2*a^3*w^1 +
    (-2523185 / 768 : ℝ)*u^2*a^3*w^3) +
    ((-925023 / 4096 : ℝ)*u^2*a^4*w^1 +
    (253076855 / 2304 : ℝ)*u^3)) +
    (((-1351107869 / 13824 : ℝ)*u^3*a^1 +
    (7252621 / 72 : ℝ)*u^3*a^1*w^2) +
    ((-532915 / 8 : ℝ)*u^3*a^1*w^4 +
    ((87073 / 18 : ℝ)*u^3*a^1*w^6 +
    (67612475 / 2304 : ℝ)*u^3*a^2)))) +
    ((((4158645 / 256 : ℝ)*u^3*a^2*w^2 +
    (-3486245 / 576 : ℝ)*u^3*a^2*w^4) +
    ((-36286185 / 8192 : ℝ)*u^3*a^3 +
    ((31072265 / 9216 : ℝ)*u^3*a^3*w^2 +
    (6222931 / 196608 : ℝ)*u^3*a^4))) +
    (((-1522091 / 96 : ℝ)*u^4*a^1*w^1 +
    (3596315 / 192 : ℝ)*u^4*a^1*w^3) +
    ((-540239 / 108 : ℝ)*u^4*a^1*w^5 +
    ((11748245 / 1024 : ℝ)*u^4*a^2*w^1 +
    (265685 / 96 : ℝ)*u^4*a^2*w^3))))) +
    (((((-153360235 / 110592 : ℝ)*u^4*a^3*w^1 +
    (-197860985 / 4608 : ℝ)*u^5) +
    ((281955041 / 10368 : ℝ)*u^5*a^1 +
    (2469959 / 768 : ℝ)*u^5*a^1*w^2)) +
    (((1887137 / 1296 : ℝ)*u^5*a^1*w^4 +
    (-153996959 / 24576 : ℝ)*u^5*a^2) +
    ((542745 / 512 : ℝ)*u^5*a^2*w^2 +
    ((312020387 / 1327104 : ℝ)*u^5*a^3 +
    (39583103 / 13824 : ℝ)*u^6*a^1*w^1)))) +
    ((((10089037 / 15552 : ℝ)*u^6*a^1*w^3 +
    (-268276799 / 248832 : ℝ)*u^6*a^2*w^1) +
    ((12977965 / 1728 : ℝ)*u^7 +
    ((-550635815 / 165888 : ℝ)*u^7*a^1 +
    (-14025815 / 186624 : ℝ)*u^7*a^1*w^2))) +
    (((558655477 / 1990656 : ℝ)*u^7*a^2 +
    (-1031029751 / 4478976 : ℝ)*u^8*a^1*w^1) +
    ((-22547525 / 36864 : ℝ)*u^9 +
    ((19983493963 / 161243136 : ℝ)*u^9*a^1 +
    (56581525 / 2985984 : ℝ)*u^11)))))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar9_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 9) =
      (oddCompactSourceScalar9 u a w : ℂ) := by
  rw [oddCompactSourceJet9_eq]
  simp only [oddCompactSourceJet9, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar9
  push_cast
  ring

/-- Exact scalar normalized source derivative of order 10. -/
def oddCompactSourceScalar10 (u a w : ℝ) : ℝ :=
  (((((((70335015 / 256 : ℝ) +
    ((-1588796145 / 1024 : ℝ)*a^1 +
    (152504033 / 32 : ℝ)*a^1*w^2)) +
    ((-16979395 / 8 : ℝ)*a^1*w^4 +
    ((467871 / 2 : ℝ)*a^1*w^6 +
    (-7572 / 1 : ℝ)*a^1*w^8))) +
    (((64 / 1 : ℝ)*a^1*w^10 +
    ((-152504033 / 1024 : ℝ)*a^2 +
    (254690925 / 256 : ℝ)*a^2*w^2)) +
    ((-21054195 / 64 : ℝ)*a^2*w^4 +
    ((172263 / 8 : ℝ)*a^2*w^6 +
    (-306 / 1 : ℝ)*a^2*w^8)))) +
    ((((-865949145 / 8192 : ℝ)*a^3 +
    ((161415495 / 1024 : ℝ)*a^3*w^2 +
    (-5991345 / 256 : ℝ)*a^3*w^4)) +
    ((2373 / 4 : ℝ)*a^3*w^6 +
    ((397222479 / 65536 : ℝ)*a^4 +
    (-64621341 / 4096 : ℝ)*a^4*w^2))) +
    (((1766379 / 512 : ℝ)*a^4*w^4 +
    ((49594707 / 262144 : ℝ)*a^5 +
    (-4425849 / 16384 : ℝ)*a^5*w^2)) +
    ((1341999 / 524288 : ℝ)*a^6 +
    ((-152504033 / 32 : ℝ)*u^1*a^1*w^1 +
    (288649715 / 48 : ℝ)*u^1*a^1*w^3))))) +
    (((((-1403613 / 1 : ℝ)*u^1*a^1*w^5 +
    ((79506 / 1 : ℝ)*u^1*a^1*w^7 +
    (-3136 / 3 : ℝ)*u^1*a^1*w^9)) +
    ((-220732135 / 256 : ℝ)*u^1*a^2*w^1 +
    ((2339355 / 2 : ℝ)*u^1*a^2*w^3 +
    (-1289133 / 8 : ℝ)*u^1*a^2*w^5))) +
    (((3888 / 1 : ℝ)*u^1*a^2*w^7 +
    ((-339206475 / 1024 : ℝ)*u^1*a^3*w^1 +
    (31679355 / 256 : ℝ)*u^1*a^3*w^3)) +
    ((-92925 / 16 : ℝ)*u^1*a^3*w^5 +
    ((60044067 / 4096 : ℝ)*u^1*a^4*w^1 +
    (-965071 / 128 : ℝ)*u^1*a^4*w^3)))) +
    ((((4727697 / 16384 : ℝ)*u^1*a^5*w^1 +
    ((-529598715 / 512 : ℝ)*u^2 +
    (3812600825 / 2304 : ℝ)*u^2*a^1)) +
    ((-1613042525 / 384 : ℝ)*u^2*a^1*w^2 +
    ((21054195 / 8 : ℝ)*u^2*a^1*w^4 +
    (-3588497 / 12 : ℝ)*u^2*a^1*w^6))) +
    (((6616 / 1 : ℝ)*u^2*a^1*w^8 +
    ((-4092034195 / 12288 : ℝ)*u^2*a^2 +
    (-240953565 / 256 : ℝ)*u^2*a^2*w^2)) +
    (((50445295 / 128 : ℝ)*u^2*a^2*w^4 +
    (-73353 / 4 : ℝ)*u^2*a^2*w^6) +
    ((1235959225 / 8192 : ℝ)*u^2*a^3 +
    (-420047235 / 2048 : ℝ)*u^2*a^3*w^2)))))) +
    ((((((2620975 / 128 : ℝ)*u^2*a^3*w^4 +
    ((-395559387 / 131072 : ℝ)*u^2*a^4 +
    (10732979 / 2048 : ℝ)*u^2*a^4*w^2)) +
    ((-5447693 / 131072 : ℝ)*u^2*a^5 +
    ((3073270495 / 3456 : ℝ)*u^3*a^1*w^1 +
    (-233155715 / 144 : ℝ)*u^3*a^1*w^3))) +
    (((8708431 / 18 : ℝ)*u^3*a^1*w^5 +
    ((-61468 / 3 : ℝ)*u^3*a^1*w^7 +
    (-39769035 / 256 : ℝ)*u^3*a^2*w^1)) +
    ((-24082115 / 72 : ℝ)*u^3*a^2*w^3 +
    ((158025 / 4 : ℝ)*u^3*a^2*w^5 +
    (758427295 / 6144 : ℝ)*u^3*a^3*w^1)))) +
    ((((-37065455 / 1152 : ℝ)*u^3*a^3*w^3 +
    ((-20894671 / 18432 : ℝ)*u^3*a^4*w^1 +
    (5337641155 / 6912 : ℝ)*u^4)) +
    ((-109330324405 / 165888 : ℝ)*u^4*a^1 +
    ((35090325 / 256 : ℝ)*u^4*a^1*w^2 +
    (-84803245 / 288 : ℝ)*u^4*a^1*w^4))) +
    (((126903 / 4 : ℝ)*u^4*a^1*w^6 +
    ((18423980195 / 73728 : ℝ)*u^4*a^2 +
    (2956235 / 1024 : ℝ)*u^4*a^2*w^2)) +
    ((-42257635 / 1152 : ℝ)*u^4*a^2*w^4 +
    ((-7612929815 / 294912 : ℝ)*u^4*a^3 +
    (139379485 / 6144 : ℝ)*u^4*a^3*w^2))))) +
    (((((619517245 / 3538944 : ℝ)*u^4*a^4 +
    ((-63474499 / 768 : ℝ)*u^5*a^1*w^1 +
    (-597557 / 5184 : ℝ)*u^5*a^1*w^3)) +
    ((-1114547 / 54 : ℝ)*u^5*a^1*w^5 +
    ((2678826577 / 27648 : ℝ)*u^5*a^2*w^1 +
    (318479 / 54 : ℝ)*u^5*a^2*w^3))) +
    (((-370946317 / 55296 : ℝ)*u^5*a^3*w^1 +
    ((-6537067075 / 27648 : ℝ)*u^6 +
    (80221317617 / 497664 : ℝ)*u^6*a^1)) +
    ((2788836379 / 124416 : ℝ)*u^6*a^1*w^2 +
    ((-1177729 / 3888 : ℝ)*u^6*a^1*w^4 +
    (-131315146603 / 3981312 : ℝ)*u^6*a^2)))) +
    ((((418575269 / 41472 : ℝ)*u^6*a^2*w^2 +
    ((4208898365 / 3981312 : ℝ)*u^6*a^3 +
    (2663110891 / 124416 : ℝ)*u^7*a^1*w^1)) +
    ((96757127 / 23328 : ℝ)*u^7*a^1*w^3 +
    ((-642295043 / 124416 : ℝ)*u^7*a^2*w^1 +
    (3902823925 / 110592 : ℝ)*u^8))) +
    (((-558875224091 / 35831808 : ℝ)*u^8*a^1 +
    ((150487757 / 248832 : ℝ)*u^8*a^1*w^2 +
    (28270507225 / 23887872 : ℝ)*u^8*a^2)) +
    (((-21907831189 / 20155392 : ℝ)*u^9*a^1*w^1 +
    (-5100420325 / 1990656 : ℝ)*u^10) +
    ((240719686787 / 483729408 : ℝ)*u^10*a^1 +
    (1301375075 / 17915904 : ℝ)*u^12)))))))

/-- The normalized source jet is the real scalar polynomial under exact embedding. -/
theorem oddCompactSourceScalar10_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w)
      (modularThetaLyapunovNormalizedSourceJet 10) =
      (oddCompactSourceScalar10 u a w : ℂ) := by
  rw [oddCompactSourceJet10_eq]
  simp only [oddCompactSourceJet10, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, oddCompactState]
  unfold oddCompactSourceScalar10
  push_cast
  ring

end
end HTGeometry
