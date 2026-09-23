import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewConstantSquare
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewTiltDetection

/-!
# Tilt detection by the constant-mode kernel

With `v = s + 3/2` the constant-mode kernel of the two-rate horizon plateau is
`skewPlateauMu s 0 = v·P(v²)/(512·Q(v²))` with `Q(u) = (4u−4)(4u−1)` and an explicit polynomial `P`
of degree seven (`skewConstantKernel_eq`): it is odd under the rate swap `v ↦ −v`. For the reflected
pair `s = σ − 2 + it`, `w = −3 − conj s` one has `y := w + 3/2 = −conj v`, and the difference-quotient
numerator `v·P(v²)·Q(y²) − y·P(y²)·Q(v²)` is antisymmetric in `(v, y)`, hence equals
`(v − y)·Ĥ((v+y)², vy)` for an explicit polynomial `Ĥ` (`skewConstantKernel_polynomial_identity`,
a pure polynomial identity). At the reflected pair `v − y = 2σ − 1`, `(v+y)² = −4t²` and
`vy = −((σ−½)² + t²)` are real, so `2·Re(skewPlateauMu s 0)·|512·Q(v²)|² = (2σ−1)·skewConstantTiltCofactor σ t`
with `skewConstantTiltCofactor σ t = 512·Ĥ(−4t², −((σ−½)² + t²))` a real polynomial of leading term
`(720896 : ℝ)·t^(18 : ℕ)` (`skewConstantKernel_re_tilt`), positive on the strip for `t ≥ 92`
(`skewConstantTiltCofactor_pos`). Hence the real part of the constant-mode kernel vanishes exactly on the
critical line there (`skewConstantKernel_re_eq_zero_iff`): once the physical clock coefficient is
normalized by the regularized constant term of the angular square, its dominant term is a tilt detector
with an elementary sign-definite cofactor.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- Odd part of the constant-mode numerator: `N₀(s) = v·P(v²)`, `v = s + 3/2`. -/
noncomputable def skewConstantP (u : ℂ) : ℂ := (-74655 / 2048 : ℂ) + (58863 / 256 : ℂ) * u + (-19053 / 32 : ℂ) * u ^ (2 : ℕ) + (36367 / 32 : ℂ) * u ^ (3 : ℕ) + (-3151 / 8 : ℂ) * u ^ (4 : ℕ) + (-46 : ℂ) * u ^ (5 : ℕ) + (36 : ℂ) * u ^ (6 : ℕ) + (-8 : ℂ) * u ^ (7 : ℕ)

/-- `Q(u) = (4u − 4)(4u − 1)`: the denominator is `512·Q(v²)`. -/
noncomputable def skewConstantQ (u : ℂ) : ℂ := 4 + (-20) * u + 16 * u ^ (2 : ℕ)

/-- The symmetric cofactor in the variables `(v+y)²`, `vy`. -/
noncomputable def skewConstantHhat (a b : ℂ) : ℂ := (-74655 / 512 : ℂ) + (-844179 / 512 : ℂ) * b + (-968133 / 128 : ℂ) * b ^ (2 : ℕ) + (-322127 / 16 : ℂ) * b ^ (3 : ℕ) + (-270651 / 8 : ℂ) * b ^ (4 : ℕ) + (-25877 : ℂ) * b ^ (5 : ℕ) + (-5238 : ℂ) * b ^ (6 : ℕ) + (1488 : ℂ) * b ^ (7 : ℕ) + (736 : ℂ) * b ^ (8 : ℕ) + (128 : ℂ) * b ^ (9 : ℕ) + (58863 / 64 : ℂ) * a + (989199 / 128 : ℂ) * a * b + (313467 / 8 : ℂ) * a * b ^ (2 : ℕ) + (671545 / 8 : ℂ) * a * b ^ (3 : ℕ) + (125377 / 2 : ℂ) * a * b ^ (4 : ℕ) + (6682 : ℂ) * a * b ^ (5 : ℕ) + (-16112 : ℂ) * a * b ^ (6 : ℕ) + (-9120 : ℂ) * a * b ^ (7 : ℕ) + (-1920 : ℂ) * a * b ^ (8 : ℕ) + (-19053 / 8 : ℂ) * a ^ (2 : ℕ) + (-181835 / 8 : ℂ) * a ^ (2 : ℕ) * b + (-370895 / 8 : ℂ) * a ^ (2 : ℕ) * b ^ (2 : ℕ) + (-65895 / 2 : ℂ) * a ^ (2 : ℕ) * b ^ (3 : ℕ) + (17578 : ℂ) * a ^ (2 : ℕ) * b ^ (4 : ℕ) + (32912 : ℂ) * a ^ (2 : ℕ) * b ^ (5 : ℕ) + (19840 : ℂ) * a ^ (2 : ℕ) * b ^ (6 : ℕ) + (4480 : ℂ) * a ^ (2 : ℕ) * b ^ (7 : ℕ) + (36367 / 8 : ℂ) * a ^ (3 : ℕ) + (22057 / 2 : ℂ) * a ^ (3 : ℕ) * b + (5451 / 2 : ℂ) * a ^ (3 : ℕ) * b ^ (2 : ℕ) + (-18536 : ℂ) * a ^ (3 : ℕ) * b ^ (3 : ℕ) + (-27616 : ℂ) * a ^ (3 : ℕ) * b ^ (4 : ℕ) + (-17472 : ℂ) * a ^ (3 : ℕ) * b ^ (5 : ℕ) + (-3584 : ℂ) * a ^ (3 : ℕ) * b ^ (6 : ℕ) + (-3151 / 2 : ℂ) * a ^ (4 : ℕ) + (1656 : ℂ) * a ^ (4 : ℕ) * b + (7400 : ℂ) * a ^ (4 : ℕ) * b ^ (2 : ℕ) + (11760 : ℂ) * a ^ (4 : ℕ) * b ^ (3 : ℕ) + (7776 : ℂ) * a ^ (4 : ℕ) * b ^ (4 : ℕ) + (1152 : ℂ) * a ^ (4 : ℕ) * b ^ (5 : ℕ) + (-184 : ℂ) * a ^ (5 : ℕ) + (-1584 : ℂ) * a ^ (5 : ℕ) * b + (-2832 : ℂ) * a ^ (5 : ℕ) * b ^ (2 : ℕ) + (-1760 : ℂ) * a ^ (5 : ℕ) * b ^ (3 : ℕ) + (-128 : ℂ) * a ^ (5 : ℕ) * b ^ (4 : ℕ) + (144 : ℂ) * a ^ (6 : ℕ) + (416 : ℂ) * a ^ (6 : ℕ) * b + (160 : ℂ) * a ^ (6 : ℕ) * b ^ (2 : ℕ) + (-32 : ℂ) * a ^ (7 : ℕ)

theorem skewConstantKernel_eq (s : ℂ) (h1 : (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : (2 * s + 4) * (2 * s + 5) ≠ 0) :
    skewPlateauMu s 0 = (s + 3 / 2) * skewConstantP ((s + 3 / 2) ^ (2 : ℕ)) / (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) := by
  unfold skewPlateauMu skewPlateauMuNumerator skewConstantP skewConstantQ
  have h1' : (0 : ℂ) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by intro h; apply h1; linear_combination -h
  have h2' : (0 : ℂ) - (2 * s + 4) * (2 * s + 5) ≠ 0 := by intro h; apply h2; linear_combination -h
  have hA : (128 : ℂ) * (2 - 0) ^ (2 : ℕ) * (0 - (2 * s + 1) * (2 * s + 2)) * (0 - (2 * s + 4) * (2 * s + 5)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) h1') h2'
  have hB : (512 : ℂ) * (4 + (-20) * (s + 3 / 2) ^ (2 : ℕ) + 16 * ((s + 3 / 2) ^ (2 : ℕ)) ^ (2 : ℕ)) ≠ 0 := by
    have : (4 : ℂ) + (-20) * (s + 3 / 2) ^ (2 : ℕ) + 16 * ((s + 3 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) = ((2 * s + 1) * (2 * s + 2)) * ((2 * s + 4) * (2 * s + 5)) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  rw [div_eq_div_iff hA hB]
  ring

theorem skewConstantQ_ne_zero (s : ℂ) (h1 : (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : (2 * s + 4) * (2 * s + 5) ≠ 0) :
    512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ)) ≠ 0 := by
  unfold skewConstantQ
  have : (4 : ℂ) + (-20) * (s + 3 / 2) ^ (2 : ℕ) + 16 * ((s + 3 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) = ((2 * s + 1) * (2 * s + 2)) * ((2 * s + 4) * (2 * s + 5)) := by ring
  rw [this]; exact mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)

/-- The antisymmetric difference-quotient numerator factors through the symmetric cofactor. -/
theorem skewConstantKernel_polynomial_identity (v y : ℂ) :
    v * skewConstantP (v ^ (2 : ℕ)) * (512 * skewConstantQ (y ^ (2 : ℕ))) - (512 * skewConstantQ (v ^ (2 : ℕ))) * (y * skewConstantP (y ^ (2 : ℕ))) =
      (v - y) * (512 * skewConstantHhat ((v + y) ^ (2 : ℕ)) (v * y)) := by
  unfold skewConstantP skewConstantQ skewConstantHhat
  ring

theorem skewConstantKernel_sub (s w : ℂ) (h1 : (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : (2 * s + 4) * (2 * s + 5) ≠ 0)
    (g1 : (2 * w + 1) * (2 * w + 2) ≠ 0) (g2 : (2 * w + 4) * (2 * w + 5) ≠ 0) :
    skewPlateauMu s 0 - skewPlateauMu w 0 =
      (s - w) * (512 * skewConstantHhat ((s + 3 / 2 + (w + 3 / 2)) ^ (2 : ℕ)) ((s + 3 / 2) * (w + 3 / 2))) /
        ((512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) * (512 * skewConstantQ ((w + 3 / 2) ^ (2 : ℕ)))) := by
  have hs := skewConstantQ_ne_zero s h1 h2
  have hw := skewConstantQ_ne_zero w g1 g2
  rw [skewConstantKernel_eq s h1 h2, skewConstantKernel_eq w g1 g2, div_sub_div _ _ hs hw,
    skewConstantKernel_polynomial_identity]
  have : s - w = (s + 3 / 2) - (w + 3 / 2) := by ring
  rw [this]

theorem skewConstantKernel_reflect (s : ℂ) (h1 : (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : (2 * s + 4) * (2 * s + 5) ≠ 0) :
    skewPlateauMu (-3 - s) 0 = -skewPlateauMu s 0 := by
  have h1r : (2 * (-3 - s) + 1) * (2 * (-3 - s) + 2) ≠ 0 := by
    intro h; apply h2; linear_combination h
  have h2r : (2 * (-3 - s) + 4) * (2 * (-3 - s) + 5) ≠ 0 := by
    intro h; apply h1; linear_combination h
  rw [skewConstantKernel_eq _ h1r h2r, skewConstantKernel_eq s h1 h2]
  have e1 : (-3 - s + 3 / 2) = -(s + 3 / 2) := by ring
  rw [e1, neg_sq, neg_mul, neg_div]

theorem skewConstantKernel_conj (s : ℂ) (h1 : (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : (2 * s + 4) * (2 * s + 5) ≠ 0) :
    skewPlateauMu (starRingEnd ℂ s) 0 = starRingEnd ℂ (skewPlateauMu s 0) := by
  have h1' : (2 * starRingEnd ℂ s + 1) * (2 * starRingEnd ℂ s + 2) ≠ 0 := by
    intro h; apply h1
    have := congrArg (starRingEnd ℂ) h
    simp only [map_mul, map_add, map_ofNat, Complex.conj_conj, map_one, map_zero] at this
    exact this
  have h2' : (2 * starRingEnd ℂ s + 4) * (2 * starRingEnd ℂ s + 5) ≠ 0 := by
    intro h; apply h2
    have := congrArg (starRingEnd ℂ) h
    simp only [map_mul, map_add, map_ofNat, Complex.conj_conj, map_zero] at this
    exact this
  rw [skewConstantKernel_eq _ h1' h2', skewConstantKernel_eq s h1 h2]
  unfold skewConstantP skewConstantQ
  simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-- The sum of the reflected pair, shifted, squares to the real number `−4t²`. -/
theorem skewConstant_pair_sum_sq (σ t : ℝ) :
    (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 / 2 + ((-1 - (σ : ℂ) + (t : ℂ) * Complex.I) + 3 / 2)) ^ (2 : ℕ) = ((-4 * t ^ (2 : ℕ) : ℝ) : ℂ) := by
  push_cast
  linear_combination (4 * (t : ℂ) ^ (2 : ℕ)) * Complex.I_sq

/-- The product of the shifted reflected pair is the real number `−((σ−½)² + t²)`. -/
theorem skewConstant_pair_prod (σ t : ℝ) :
    (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 / 2) * ((-1 - (σ : ℂ) + (t : ℂ) * Complex.I) + 3 / 2) = ((-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ)) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((t : ℂ) ^ (2 : ℕ)) * Complex.I_sq

/-- The cofactor at the reflected pair, as a real polynomial: `512·Ĥ(−4t², −((σ−½)² + t²))`. -/
noncomputable def skewConstantTiltCofactor (σ t : ℝ) : ℝ := (-737280 : ℝ) * t ^ (2 : ℕ) + (7462912 : ℝ) * t ^ (4 : ℕ) + (-14545920 : ℝ) * t ^ (6 : ℕ) + (-71756800 : ℝ) * t ^ (8 : ℕ) + (-70728704 : ℝ) * t ^ (10 : ℕ) + (-25199616 : ℝ) * t ^ (12 : ℕ) + (-2465792 : ℝ) * t ^ (14 : ℕ) + (1736704 : ℝ) * t ^ (16 : ℕ) + (720896 : ℝ) * t ^ (18 : ℕ) + (1130496 : ℝ) * σ * t ^ (2 : ℕ) + (-61083648 : ℝ) * σ * t ^ (4 : ℕ) + (-101238784 : ℝ) * σ * t ^ (6 : ℕ) + (-21676032 : ℝ) * σ * t ^ (8 : ℕ) + (35690496 : ℝ) * σ * t ^ (10 : ℕ) + (48963584 : ℝ) * σ * t ^ (12 : ℕ) + (39780352 : ℝ) * σ * t ^ (14 : ℕ) + (7929856 : ℝ) * σ * t ^ (16 : ℕ) + (-737280 : ℝ) * σ ^ (2 : ℕ) + (4161536 : ℝ) * σ ^ (2 : ℕ) * t ^ (2 : ℕ) + (62948352 : ℝ) * σ ^ (2 : ℕ) * t ^ (4 : ℕ) + (234995712 : ℝ) * σ ^ (2 : ℕ) * t ^ (6 : ℕ) + (128517120 : ℝ) * σ ^ (2 : ℕ) * t ^ (8 : ℕ) + (93440000 : ℝ) * σ ^ (2 : ℕ) * t ^ (10 : ℕ) + (-7217152 : ℝ) * σ ^ (2 : ℕ) * t ^ (12 : ℕ) + (-48431104 : ℝ) * σ ^ (2 : ℕ) * t ^ (14 : ℕ) + (-7929856 : ℝ) * σ ^ (2 : ℕ) * t ^ (16 : ℕ) + (1130496 : ℝ) * σ ^ (3 : ℕ) + (-56254464 : ℝ) * σ ^ (3 : ℕ) * t ^ (2 : ℕ) + (-22198272 : ℝ) * σ ^ (3 : ℕ) * t ^ (4 : ℕ) + (-353280000 : ℝ) * σ ^ (3 : ℕ) * t ^ (6 : ℕ) + (-193095680 : ℝ) * σ ^ (3 : ℕ) * t ^ (8 : ℕ) + (-361349120 : ℝ) * σ ^ (3 : ℕ) * t ^ (10 : ℕ) + (-120979456 : ℝ) * σ ^ (3 : ℕ) * t ^ (12 : ℕ) + (17301504 : ℝ) * σ ^ (3 : ℕ) * t ^ (14 : ℕ) + (-3301376 : ℝ) * σ ^ (4 : ℕ) + (95437824 : ℝ) * σ ^ (4 : ℕ) * t ^ (2 : ℕ) + (155461632 : ℝ) * σ ^ (4 : ℕ) * t ^ (4 : ℕ) + (422914048 : ℝ) * σ ^ (4 : ℕ) * t ^ (6 : ℕ) + (5891072 : ℝ) * σ ^ (4 : ℕ) * t ^ (8 : ℕ) + (494624768 : ℝ) * σ ^ (4 : ℕ) * t ^ (10 : ℕ) + (154206208 : ℝ) * σ ^ (4 : ℕ) * t ^ (12 : ℕ) + (-8650752 : ℝ) * σ ^ (4 : ℕ) * t ^ (14 : ℕ) + (4829184 : ℝ) * σ ^ (5 : ℕ) + (28993536 : ℝ) * σ ^ (5 : ℕ) * t ^ (2 : ℕ) + (-414064640 : ℝ) * σ ^ (5 : ℕ) * t ^ (4 : ℕ) + (-363958272 : ℝ) * σ ^ (5 : ℕ) * t ^ (6 : ℕ) + (223633408 : ℝ) * σ ^ (5 : ℕ) * t ^ (8 : ℕ) + (-534183936 : ℝ) * σ ^ (5 : ℕ) * t ^ (10 : ℕ) + (-112459776 : ℝ) * σ ^ (5 : ℕ) * t ^ (12 : ℕ) + (17943552 : ℝ) * σ ^ (6 : ℕ) + (-122134528 : ℝ) * σ ^ (6 : ℕ) * t ^ (2 : ℕ) + (466126848 : ℝ) * σ ^ (6 : ℕ) * t ^ (4 : ℕ) + (138178560 : ℝ) * σ ^ (6 : ℕ) * t ^ (6 : ℕ) + (-281288704 : ℝ) * σ ^ (6 : ℕ) * t ^ (8 : ℕ) + (440467456 : ℝ) * σ ^ (6 : ℕ) * t ^ (10 : ℕ) + (37486592 : ℝ) * σ ^ (6 : ℕ) * t ^ (12 : ℕ) + (-50046976 : ℝ) * σ ^ (7 : ℕ) + (-54747136 : ℝ) * σ ^ (7 : ℕ) * t ^ (2 : ℕ) + (-218320896 : ℝ) * σ ^ (7 : ℕ) * t ^ (4 : ℕ) + (289505280 : ℝ) * σ ^ (7 : ℕ) * t ^ (6 : ℕ) + (207880192 : ℝ) * σ ^ (7 : ℕ) * t ^ (8 : ℕ) + (-224919552 : ℝ) * σ ^ (7 : ℕ) * t ^ (10 : ℕ) + (29156352 : ℝ) * σ ^ (8 : ℕ) + (199742464 : ℝ) * σ ^ (8 : ℕ) * t ^ (2 : ℕ) + (139428864 : ℝ) * σ ^ (8 : ℕ) * t ^ (4 : ℕ) + (-698867712 : ℝ) * σ ^ (8 : ℕ) * t ^ (6 : ℕ) + (-90308608 : ℝ) * σ ^ (8 : ℕ) * t ^ (8 : ℕ) + (56229888 : ℝ) * σ ^ (8 : ℕ) * t ^ (10 : ℕ) + (27713536 : ℝ) * σ ^ (9 : ℕ) + (-67536896 : ℝ) * σ ^ (9 : ℕ) * t ^ (2 : ℕ) + (-250486784 : ℝ) * σ ^ (9 : ℕ) * t ^ (4 : ℕ) + (801177600 : ℝ) * σ ^ (9 : ℕ) * t ^ (6 : ℕ) + (25559040 : ℝ) * σ ^ (9 : ℕ) * t ^ (8 : ℕ) + (-42716160 : ℝ) * σ ^ (10 : ℕ) + (-107657216 : ℝ) * σ ^ (10 : ℕ) * t ^ (2 : ℕ) + (135307264 : ℝ) * σ ^ (10 : ℕ) * t ^ (4 : ℕ) + (-543752192 : ℝ) * σ ^ (10 : ℕ) * t ^ (6 : ℕ) + (-5111808 : ℝ) * σ ^ (10 : ℕ) * t ^ (8 : ℕ) + (15611904 : ℝ) * σ ^ (11 : ℕ) + (90456064 : ℝ) * σ ^ (11 : ℕ) * t ^ (2 : ℕ) + (91881472 : ℝ) * σ ^ (11 : ℕ) * t ^ (4 : ℕ) + (209190912 : ℝ) * σ ^ (11 : ℕ) * t ^ (6 : ℕ) + (3841024 : ℝ) * σ ^ (12 : ℕ) + (51519488 : ℝ) * σ ^ (12 : ℕ) * t ^ (2 : ℕ) + (-130613248 : ℝ) * σ ^ (12 : ℕ) * t ^ (4 : ℕ) + (-34865152 : ℝ) * σ ^ (12 : ℕ) * t ^ (6 : ℕ) + (-3497984 : ℝ) * σ ^ (13 : ℕ) + (-124321792 : ℝ) * σ ^ (13 : ℕ) * t ^ (2 : ℕ) + (53215232 : ℝ) * σ ^ (13 : ℕ) * t ^ (4 : ℕ) + (-1990656 : ℝ) * σ ^ (14 : ℕ) + (84606976 : ℝ) * σ ^ (14 : ℕ) * t ^ (2 : ℕ) + (-7602176 : ℝ) * σ ^ (14 : ℕ) * t ^ (4 : ℕ) + (3670016 : ℝ) * σ ^ (15 : ℕ) + (-26738688 : ℝ) * σ ^ (15 : ℕ) * t ^ (2 : ℕ) + (-2129920 : ℝ) * σ ^ (16 : ℕ) + (3342336 : ℝ) * σ ^ (16 : ℕ) * t ^ (2 : ℕ) + (589824 : ℝ) * σ ^ (17 : ℕ) + (-65536 : ℝ) * σ ^ (18 : ℕ)

theorem skewConstantTiltCofactor_eq (σ t : ℝ) :
    skewConstantTiltCofactor σ t = 512 * ((-74655 / 512 : ℝ) + (-844179 / 512 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (-968133 / 128 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (-322127 / 16 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (-270651 / 8 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (-25877 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (5 : ℕ) + (-5238 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (6 : ℕ) + (1488 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (7 : ℕ) + (736 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (8 : ℕ) + (128 : ℝ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (9 : ℕ) + (58863 / 64 : ℝ) * (-4 * t ^ (2 : ℕ)) + (989199 / 128 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (313467 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (671545 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (125377 / 2 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (6682 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (5 : ℕ) + (-16112 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (6 : ℕ) + (-9120 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (7 : ℕ) + (-1920 : ℝ) * (-4 * t ^ (2 : ℕ)) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (8 : ℕ) + (-19053 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) + (-181835 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (-370895 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (-65895 / 2 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (17578 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (32912 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (5 : ℕ) + (19840 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (6 : ℕ) + (4480 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (7 : ℕ) + (36367 / 8 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) + (22057 / 2 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (5451 / 2 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (-18536 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (-27616 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (-17472 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (5 : ℕ) + (-3584 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (6 : ℕ) + (-3151 / 2 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) + (1656 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (7400 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (11760 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (7776 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (1152 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (5 : ℕ) + (-184 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (5 : ℕ) + (-1584 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (-2832 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (-1760 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (3 : ℕ) + (-128 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (4 : ℕ) + (144 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (6 : ℕ) + (416 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (6 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) + (160 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (6 : ℕ) * (-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) ^ (2 : ℕ) + (-32 : ℝ) * (-4 * t ^ (2 : ℕ)) ^ (7 : ℕ)) := by
  unfold skewConstantTiltCofactor
  ring

/-- The symmetric cofactor at the real arguments of the reflected pair is the real cofactor. -/
theorem skewConstantHhat_real (σ t : ℝ) :
    (512 : ℂ) * skewConstantHhat ((-4 * t ^ (2 : ℕ) : ℝ) : ℂ) ((-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ)) : ℝ) : ℂ) = (skewConstantTiltCofactor σ t : ℂ) := by
  rw [skewConstantTiltCofactor_eq]
  unfold skewConstantHhat
  push_cast
  ring

/-- The real part of the constant-mode kernel is the tilt times its cofactor. -/
theorem skewConstantKernel_re_tilt (σ t : ℝ) (ht : 1 ≤ t) :
    2 * (skewPlateauMu ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) 0).re *
        Complex.normSq (512 * skewConstantQ (((σ : ℂ) - 2 + (t : ℂ) * Complex.I + 3 / 2) ^ (2 : ℕ))) =
      (2 * σ - 1) * skewConstantTiltCofactor σ t := by
  set s : ℂ := (σ : ℂ) - 2 + (t : ℂ) * Complex.I with hsdef
  set w : ℂ := -1 - (σ : ℂ) + (t : ℂ) * Complex.I with hwdef
  have hne : ∀ c : ℝ, (2 * s + (c : ℂ)) ≠ 0 := by
    intro c h
    have := congrArg Complex.im h
    rw [hsdef] at this
    simp at this
    linarith
  have gne : ∀ c : ℝ, (2 * w + (c : ℂ)) ≠ 0 := by
    intro c h
    have := congrArg Complex.im h
    rw [hwdef] at this
    simp at this
    linarith
  have h1 : (2 * s + 1) * (2 * s + 2) ≠ 0 := mul_ne_zero (by simpa using hne 1) (by simpa using hne 2)
  have h2 : (2 * s + 4) * (2 * s + 5) ≠ 0 := mul_ne_zero (by simpa using hne 4) (by simpa using hne 5)
  have g1 : (2 * w + 1) * (2 * w + 2) ≠ 0 := mul_ne_zero (by simpa using gne 1) (by simpa using gne 2)
  have g2 : (2 * w + 4) * (2 * w + 5) ≠ 0 := mul_ne_zero (by simpa using gne 4) (by simpa using gne 5)
  have hconj : starRingEnd ℂ s = -3 - w := by
    apply Complex.ext <;> simp [hsdef, hwdef]
    ring
  have hodd : skewPlateauMu w 0 = -(starRingEnd ℂ (skewPlateauMu s 0)) := by
    have hc := skewConstantKernel_conj s h1 h2
    rw [hconj, skewConstantKernel_reflect w g1 g2] at hc
    rw [← hc]; ring
  have hsum : skewPlateauMu s 0 - skewPlateauMu w 0 = (2 * (skewPlateauMu s 0).re : ℂ) := by
    rw [hodd, sub_neg_eq_add, Complex.add_conj]; push_cast; ring
  have hsub := skewConstantKernel_sub s w h1 h2 g1 g2
  have hsw : s - w = ((2 * σ - 1 : ℝ) : ℂ) := by rw [hsdef, hwdef]; push_cast; ring
  have hA : (s + 3 / 2 + (w + 3 / 2)) ^ (2 : ℕ) = ((-4 * t ^ (2 : ℕ) : ℝ) : ℂ) := skewConstant_pair_sum_sq σ t
  have hB : (s + 3 / 2) * (w + 3 / 2) = ((-((σ - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ)) : ℝ) : ℂ) := skewConstant_pair_prod σ t
  have hcv : starRingEnd ℂ (s + 3 / 2) = -(w + 3 / 2) := by
    rw [map_add, hconj, map_div₀, map_ofNat, map_ofNat]; ring
  have hden : (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) * (512 * skewConstantQ ((w + 3 / 2) ^ (2 : ℕ))) =
      (Complex.normSq (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : starRingEnd ℂ (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) = 512 * skewConstantQ ((w + 3 / 2) ^ (2 : ℕ)) := by
      unfold skewConstantQ
      simp only [map_mul, map_add, map_pow, map_neg, map_ofNat, hcv]
      ring
    rw [this]; ring
  have hcof : (512 : ℂ) * skewConstantHhat ((s + 3 / 2 + (w + 3 / 2)) ^ (2 : ℕ)) ((s + 3 / 2) * (w + 3 / 2)) = (skewConstantTiltCofactor σ t : ℂ) := by
    rw [hA, hB]
    exact skewConstantHhat_real σ t
  rw [hsw, hden, hcof] at hsub
  have hns : (Complex.normSq (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr (skewConstantQ_ne_zero s h1 h2)).ne'
  have key : (2 * (skewPlateauMu s 0).re : ℂ) * (Complex.normSq (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) : ℂ) =
      ((2 * σ - 1 : ℝ) : ℂ) * (skewConstantTiltCofactor σ t : ℂ) := by
    rw [← hsum, hsub]; exact div_mul_cancel₀ _ hns
  have key' : (2 * (skewPlateauMu s 0).re * Complex.normSq (512 * skewConstantQ ((s + 3 / 2) ^ (2 : ℕ))) : ℝ) = (2 * σ - 1) * skewConstantTiltCofactor σ t := by
    exact_mod_cast key
  exact key'

theorem skewMonoTop_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) (a b : ℕ) (hb : b ≤ 16) :
    σ ^ a * t ^ b ≤ t ^ (16 : ℕ) := by
  calc σ ^ a * t ^ b ≤ 1 * t ^ (16 : ℕ) :=
        mul_le_mul (pow_le_one₀ h0 h1) (pow_le_pow_right₀ ht1 hb) (pow_nonneg (by linarith) b) zero_le_one
    _ = t ^ (16 : ℕ) := one_mul _

/-- Group 1 of the lower-order monomials of the cofactor. -/
noncomputable def skewConstantTiltPart1 (σ t : ℝ) : ℝ := (-737280 : ℝ) * (σ ^ (0 : ℕ) * t ^ (2 : ℕ)) + (-70728704 : ℝ) * (σ ^ (0 : ℕ) * t ^ (10 : ℕ)) + (1130496 : ℝ) * (σ ^ (1 : ℕ) * t ^ (2 : ℕ)) + (35690496 : ℝ) * (σ ^ (1 : ℕ) * t ^ (10 : ℕ)) + (-737280 : ℝ) * (σ ^ (2 : ℕ) * t ^ (0 : ℕ)) + (128517120 : ℝ) * (σ ^ (2 : ℕ) * t ^ (8 : ℕ)) + (-7929856 : ℝ) * (σ ^ (2 : ℕ) * t ^ (16 : ℕ)) + (-353280000 : ℝ) * (σ ^ (3 : ℕ) * t ^ (6 : ℕ)) + (17301504 : ℝ) * (σ ^ (3 : ℕ) * t ^ (14 : ℕ)) + (422914048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (6 : ℕ)) + (-8650752 : ℝ) * (σ ^ (4 : ℕ) * t ^ (14 : ℕ)) + (-363958272 : ℝ) * (σ ^ (5 : ℕ) * t ^ (6 : ℕ)) + (17943552 : ℝ) * (σ ^ (6 : ℕ) * t ^ (0 : ℕ)) + (-281288704 : ℝ) * (σ ^ (6 : ℕ) * t ^ (8 : ℕ)) + (-54747136 : ℝ) * (σ ^ (7 : ℕ) * t ^ (2 : ℕ)) + (-224919552 : ℝ) * (σ ^ (7 : ℕ) * t ^ (10 : ℕ)) + (-698867712 : ℝ) * (σ ^ (8 : ℕ) * t ^ (6 : ℕ)) + (-67536896 : ℝ) * (σ ^ (9 : ℕ) * t ^ (2 : ℕ)) + (-42716160 : ℝ) * (σ ^ (10 : ℕ) * t ^ (0 : ℕ)) + (-5111808 : ℝ) * (σ ^ (10 : ℕ) * t ^ (8 : ℕ)) + (209190912 : ℝ) * (σ ^ (11 : ℕ) * t ^ (6 : ℕ)) + (-34865152 : ℝ) * (σ ^ (12 : ℕ) * t ^ (6 : ℕ)) + (-1990656 : ℝ) * (σ ^ (14 : ℕ) * t ^ (0 : ℕ)) + (-26738688 : ℝ) * (σ ^ (15 : ℕ) * t ^ (2 : ℕ)) + (-65536 : ℝ) * (σ ^ (18 : ℕ) * t ^ (0 : ℕ))

theorem skewConstantTiltPart1_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-2244870144 : ℝ) * t ^ (16 : ℕ) ≤ skewConstantTiltPart1 σ t := by
  unfold skewConstantTiltPart1
  have hb_0_2 : (-737280 : ℝ) * t ^ (16 : ℕ) ≤ (-737280 : ℝ) * (σ ^ (0 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 2 (by norm_num)) (show (-737280 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_0_10 : (-70728704 : ℝ) * t ^ (16 : ℕ) ≤ (-70728704 : ℝ) * (σ ^ (0 : ℕ) * t ^ (10 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 10 (by norm_num)) (show (-70728704 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_2 : 0 ≤ (1130496 : ℝ) * (σ ^ (1 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (1130496 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 2)
  have hb_1_10 : 0 ≤ (35690496 : ℝ) * (σ ^ (1 : ℕ) * t ^ (10 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (35690496 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 10)
  have hb_2_0 : (-737280 : ℝ) * t ^ (16 : ℕ) ≤ (-737280 : ℝ) * (σ ^ (2 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 2 0 (by norm_num)) (show (-737280 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_2_8 : 0 ≤ (128517120 : ℝ) * (σ ^ (2 : ℕ) * t ^ (8 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (128517120 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 8)
  have hb_2_16 : (-7929856 : ℝ) * t ^ (16 : ℕ) ≤ (-7929856 : ℝ) * (σ ^ (2 : ℕ) * t ^ (16 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 2 16 (by norm_num)) (show (-7929856 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_6 : (-353280000 : ℝ) * t ^ (16 : ℕ) ≤ (-353280000 : ℝ) * (σ ^ (3 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 6 (by norm_num)) (show (-353280000 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_14 : 0 ≤ (17301504 : ℝ) * (σ ^ (3 : ℕ) * t ^ (14 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (17301504 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 14)
  have hb_4_6 : 0 ≤ (422914048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (422914048 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 6)
  have hb_4_14 : (-8650752 : ℝ) * t ^ (16 : ℕ) ≤ (-8650752 : ℝ) * (σ ^ (4 : ℕ) * t ^ (14 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 4 14 (by norm_num)) (show (-8650752 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_5_6 : (-363958272 : ℝ) * t ^ (16 : ℕ) ≤ (-363958272 : ℝ) * (σ ^ (5 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 5 6 (by norm_num)) (show (-363958272 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_6_0 : 0 ≤ (17943552 : ℝ) * (σ ^ (6 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (17943552 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 0)
  have hb_6_8 : (-281288704 : ℝ) * t ^ (16 : ℕ) ≤ (-281288704 : ℝ) * (σ ^ (6 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 6 8 (by norm_num)) (show (-281288704 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_7_2 : (-54747136 : ℝ) * t ^ (16 : ℕ) ≤ (-54747136 : ℝ) * (σ ^ (7 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 7 2 (by norm_num)) (show (-54747136 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_7_10 : (-224919552 : ℝ) * t ^ (16 : ℕ) ≤ (-224919552 : ℝ) * (σ ^ (7 : ℕ) * t ^ (10 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 7 10 (by norm_num)) (show (-224919552 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_8_6 : (-698867712 : ℝ) * t ^ (16 : ℕ) ≤ (-698867712 : ℝ) * (σ ^ (8 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 8 6 (by norm_num)) (show (-698867712 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_9_2 : (-67536896 : ℝ) * t ^ (16 : ℕ) ≤ (-67536896 : ℝ) * (σ ^ (9 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 9 2 (by norm_num)) (show (-67536896 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_10_0 : (-42716160 : ℝ) * t ^ (16 : ℕ) ≤ (-42716160 : ℝ) * (σ ^ (10 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 10 0 (by norm_num)) (show (-42716160 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_10_8 : (-5111808 : ℝ) * t ^ (16 : ℕ) ≤ (-5111808 : ℝ) * (σ ^ (10 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 10 8 (by norm_num)) (show (-5111808 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_11_6 : 0 ≤ (209190912 : ℝ) * (σ ^ (11 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (209190912 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 11 6)
  have hb_12_6 : (-34865152 : ℝ) * t ^ (16 : ℕ) ≤ (-34865152 : ℝ) * (σ ^ (12 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 12 6 (by norm_num)) (show (-34865152 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_14_0 : (-1990656 : ℝ) * t ^ (16 : ℕ) ≤ (-1990656 : ℝ) * (σ ^ (14 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 14 0 (by norm_num)) (show (-1990656 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_15_2 : (-26738688 : ℝ) * t ^ (16 : ℕ) ≤ (-26738688 : ℝ) * (σ ^ (15 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 15 2 (by norm_num)) (show (-26738688 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_18_0 : (-65536 : ℝ) * t ^ (16 : ℕ) ≤ (-65536 : ℝ) * (σ ^ (18 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 18 0 (by norm_num)) (show (-65536 : ℝ) ≤ (0 : ℝ) by norm_num)
  linarith

/-- Group 2 of the lower-order monomials of the cofactor. -/
noncomputable def skewConstantTiltPart2 (σ t : ℝ) : ℝ := (7462912 : ℝ) * (σ ^ (0 : ℕ) * t ^ (4 : ℕ)) + (-25199616 : ℝ) * (σ ^ (0 : ℕ) * t ^ (12 : ℕ)) + (-61083648 : ℝ) * (σ ^ (1 : ℕ) * t ^ (4 : ℕ)) + (48963584 : ℝ) * (σ ^ (1 : ℕ) * t ^ (12 : ℕ)) + (4161536 : ℝ) * (σ ^ (2 : ℕ) * t ^ (2 : ℕ)) + (93440000 : ℝ) * (σ ^ (2 : ℕ) * t ^ (10 : ℕ)) + (1130496 : ℝ) * (σ ^ (3 : ℕ) * t ^ (0 : ℕ)) + (-193095680 : ℝ) * (σ ^ (3 : ℕ) * t ^ (8 : ℕ)) + (-3301376 : ℝ) * (σ ^ (4 : ℕ) * t ^ (0 : ℕ)) + (5891072 : ℝ) * (σ ^ (4 : ℕ) * t ^ (8 : ℕ)) + (4829184 : ℝ) * (σ ^ (5 : ℕ) * t ^ (0 : ℕ)) + (223633408 : ℝ) * (σ ^ (5 : ℕ) * t ^ (8 : ℕ)) + (-122134528 : ℝ) * (σ ^ (6 : ℕ) * t ^ (2 : ℕ)) + (440467456 : ℝ) * (σ ^ (6 : ℕ) * t ^ (10 : ℕ)) + (-218320896 : ℝ) * (σ ^ (7 : ℕ) * t ^ (4 : ℕ)) + (29156352 : ℝ) * (σ ^ (8 : ℕ) * t ^ (0 : ℕ)) + (-90308608 : ℝ) * (σ ^ (8 : ℕ) * t ^ (8 : ℕ)) + (-250486784 : ℝ) * (σ ^ (9 : ℕ) * t ^ (4 : ℕ)) + (-107657216 : ℝ) * (σ ^ (10 : ℕ) * t ^ (2 : ℕ)) + (15611904 : ℝ) * (σ ^ (11 : ℕ) * t ^ (0 : ℕ)) + (3841024 : ℝ) * (σ ^ (12 : ℕ) * t ^ (0 : ℕ)) + (-3497984 : ℝ) * (σ ^ (13 : ℕ) * t ^ (0 : ℕ)) + (84606976 : ℝ) * (σ ^ (14 : ℕ) * t ^ (2 : ℕ)) + (-2129920 : ℝ) * (σ ^ (16 : ℕ) * t ^ (0 : ℕ))

theorem skewConstantTiltPart2_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-1077216256 : ℝ) * t ^ (16 : ℕ) ≤ skewConstantTiltPart2 σ t := by
  unfold skewConstantTiltPart2
  have hb_0_4 : 0 ≤ (7462912 : ℝ) * (σ ^ (0 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (7462912 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 4)
  have hb_0_12 : (-25199616 : ℝ) * t ^ (16 : ℕ) ≤ (-25199616 : ℝ) * (σ ^ (0 : ℕ) * t ^ (12 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 12 (by norm_num)) (show (-25199616 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_4 : (-61083648 : ℝ) * t ^ (16 : ℕ) ≤ (-61083648 : ℝ) * (σ ^ (1 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 1 4 (by norm_num)) (show (-61083648 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_12 : 0 ≤ (48963584 : ℝ) * (σ ^ (1 : ℕ) * t ^ (12 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (48963584 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 12)
  have hb_2_2 : 0 ≤ (4161536 : ℝ) * (σ ^ (2 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (4161536 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 2)
  have hb_2_10 : 0 ≤ (93440000 : ℝ) * (σ ^ (2 : ℕ) * t ^ (10 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (93440000 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 10)
  have hb_3_0 : 0 ≤ (1130496 : ℝ) * (σ ^ (3 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (1130496 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 0)
  have hb_3_8 : (-193095680 : ℝ) * t ^ (16 : ℕ) ≤ (-193095680 : ℝ) * (σ ^ (3 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 8 (by norm_num)) (show (-193095680 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_4_0 : (-3301376 : ℝ) * t ^ (16 : ℕ) ≤ (-3301376 : ℝ) * (σ ^ (4 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 4 0 (by norm_num)) (show (-3301376 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_4_8 : 0 ≤ (5891072 : ℝ) * (σ ^ (4 : ℕ) * t ^ (8 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (5891072 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 8)
  have hb_5_0 : 0 ≤ (4829184 : ℝ) * (σ ^ (5 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (4829184 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 0)
  have hb_5_8 : 0 ≤ (223633408 : ℝ) * (σ ^ (5 : ℕ) * t ^ (8 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (223633408 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 8)
  have hb_6_2 : (-122134528 : ℝ) * t ^ (16 : ℕ) ≤ (-122134528 : ℝ) * (σ ^ (6 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 6 2 (by norm_num)) (show (-122134528 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_6_10 : 0 ≤ (440467456 : ℝ) * (σ ^ (6 : ℕ) * t ^ (10 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (440467456 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 10)
  have hb_7_4 : (-218320896 : ℝ) * t ^ (16 : ℕ) ≤ (-218320896 : ℝ) * (σ ^ (7 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 7 4 (by norm_num)) (show (-218320896 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_8_0 : 0 ≤ (29156352 : ℝ) * (σ ^ (8 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (29156352 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 0)
  have hb_8_8 : (-90308608 : ℝ) * t ^ (16 : ℕ) ≤ (-90308608 : ℝ) * (σ ^ (8 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 8 8 (by norm_num)) (show (-90308608 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_9_4 : (-250486784 : ℝ) * t ^ (16 : ℕ) ≤ (-250486784 : ℝ) * (σ ^ (9 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 9 4 (by norm_num)) (show (-250486784 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_10_2 : (-107657216 : ℝ) * t ^ (16 : ℕ) ≤ (-107657216 : ℝ) * (σ ^ (10 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 10 2 (by norm_num)) (show (-107657216 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_11_0 : 0 ≤ (15611904 : ℝ) * (σ ^ (11 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (15611904 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 11 0)
  have hb_12_0 : 0 ≤ (3841024 : ℝ) * (σ ^ (12 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (3841024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 0)
  have hb_13_0 : (-3497984 : ℝ) * t ^ (16 : ℕ) ≤ (-3497984 : ℝ) * (σ ^ (13 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 13 0 (by norm_num)) (show (-3497984 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_14_2 : 0 ≤ (84606976 : ℝ) * (σ ^ (14 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (84606976 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 14 2)
  have hb_16_0 : (-2129920 : ℝ) * t ^ (16 : ℕ) ≤ (-2129920 : ℝ) * (σ ^ (16 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 16 0 (by norm_num)) (show (-2129920 : ℝ) ≤ (0 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the cofactor. -/
noncomputable def skewConstantTiltPart3 (σ t : ℝ) : ℝ := (-14545920 : ℝ) * (σ ^ (0 : ℕ) * t ^ (6 : ℕ)) + (-2465792 : ℝ) * (σ ^ (0 : ℕ) * t ^ (14 : ℕ)) + (-101238784 : ℝ) * (σ ^ (1 : ℕ) * t ^ (6 : ℕ)) + (39780352 : ℝ) * (σ ^ (1 : ℕ) * t ^ (14 : ℕ)) + (62948352 : ℝ) * (σ ^ (2 : ℕ) * t ^ (4 : ℕ)) + (-7217152 : ℝ) * (σ ^ (2 : ℕ) * t ^ (12 : ℕ)) + (-56254464 : ℝ) * (σ ^ (3 : ℕ) * t ^ (2 : ℕ)) + (-361349120 : ℝ) * (σ ^ (3 : ℕ) * t ^ (10 : ℕ)) + (95437824 : ℝ) * (σ ^ (4 : ℕ) * t ^ (2 : ℕ)) + (494624768 : ℝ) * (σ ^ (4 : ℕ) * t ^ (10 : ℕ)) + (28993536 : ℝ) * (σ ^ (5 : ℕ) * t ^ (2 : ℕ)) + (-534183936 : ℝ) * (σ ^ (5 : ℕ) * t ^ (10 : ℕ)) + (466126848 : ℝ) * (σ ^ (6 : ℕ) * t ^ (4 : ℕ)) + (37486592 : ℝ) * (σ ^ (6 : ℕ) * t ^ (12 : ℕ)) + (289505280 : ℝ) * (σ ^ (7 : ℕ) * t ^ (6 : ℕ)) + (199742464 : ℝ) * (σ ^ (8 : ℕ) * t ^ (2 : ℕ)) + (56229888 : ℝ) * (σ ^ (8 : ℕ) * t ^ (10 : ℕ)) + (801177600 : ℝ) * (σ ^ (9 : ℕ) * t ^ (6 : ℕ)) + (135307264 : ℝ) * (σ ^ (10 : ℕ) * t ^ (4 : ℕ)) + (90456064 : ℝ) * (σ ^ (11 : ℕ) * t ^ (2 : ℕ)) + (51519488 : ℝ) * (σ ^ (12 : ℕ) * t ^ (2 : ℕ)) + (-124321792 : ℝ) * (σ ^ (13 : ℕ) * t ^ (2 : ℕ)) + (-7602176 : ℝ) * (σ ^ (14 : ℕ) * t ^ (4 : ℕ)) + (3342336 : ℝ) * (σ ^ (16 : ℕ) * t ^ (2 : ℕ))

theorem skewConstantTiltPart3_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-1209179136 : ℝ) * t ^ (16 : ℕ) ≤ skewConstantTiltPart3 σ t := by
  unfold skewConstantTiltPart3
  have hb_0_6 : (-14545920 : ℝ) * t ^ (16 : ℕ) ≤ (-14545920 : ℝ) * (σ ^ (0 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 6 (by norm_num)) (show (-14545920 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_0_14 : (-2465792 : ℝ) * t ^ (16 : ℕ) ≤ (-2465792 : ℝ) * (σ ^ (0 : ℕ) * t ^ (14 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 14 (by norm_num)) (show (-2465792 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_6 : (-101238784 : ℝ) * t ^ (16 : ℕ) ≤ (-101238784 : ℝ) * (σ ^ (1 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 1 6 (by norm_num)) (show (-101238784 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_14 : 0 ≤ (39780352 : ℝ) * (σ ^ (1 : ℕ) * t ^ (14 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (39780352 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 14)
  have hb_2_4 : 0 ≤ (62948352 : ℝ) * (σ ^ (2 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (62948352 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 4)
  have hb_2_12 : (-7217152 : ℝ) * t ^ (16 : ℕ) ≤ (-7217152 : ℝ) * (σ ^ (2 : ℕ) * t ^ (12 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 2 12 (by norm_num)) (show (-7217152 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_2 : (-56254464 : ℝ) * t ^ (16 : ℕ) ≤ (-56254464 : ℝ) * (σ ^ (3 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 2 (by norm_num)) (show (-56254464 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_10 : (-361349120 : ℝ) * t ^ (16 : ℕ) ≤ (-361349120 : ℝ) * (σ ^ (3 : ℕ) * t ^ (10 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 10 (by norm_num)) (show (-361349120 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_4_2 : 0 ≤ (95437824 : ℝ) * (σ ^ (4 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (95437824 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 2)
  have hb_4_10 : 0 ≤ (494624768 : ℝ) * (σ ^ (4 : ℕ) * t ^ (10 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (494624768 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 10)
  have hb_5_2 : 0 ≤ (28993536 : ℝ) * (σ ^ (5 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (28993536 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 2)
  have hb_5_10 : (-534183936 : ℝ) * t ^ (16 : ℕ) ≤ (-534183936 : ℝ) * (σ ^ (5 : ℕ) * t ^ (10 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 5 10 (by norm_num)) (show (-534183936 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_6_4 : 0 ≤ (466126848 : ℝ) * (σ ^ (6 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (466126848 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 4)
  have hb_6_12 : 0 ≤ (37486592 : ℝ) * (σ ^ (6 : ℕ) * t ^ (12 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (37486592 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 12)
  have hb_7_6 : 0 ≤ (289505280 : ℝ) * (σ ^ (7 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (289505280 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 6)
  have hb_8_2 : 0 ≤ (199742464 : ℝ) * (σ ^ (8 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (199742464 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 2)
  have hb_8_10 : 0 ≤ (56229888 : ℝ) * (σ ^ (8 : ℕ) * t ^ (10 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (56229888 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 10)
  have hb_9_6 : 0 ≤ (801177600 : ℝ) * (σ ^ (9 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (801177600 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 6)
  have hb_10_4 : 0 ≤ (135307264 : ℝ) * (σ ^ (10 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (135307264 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 10 4)
  have hb_11_2 : 0 ≤ (90456064 : ℝ) * (σ ^ (11 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (90456064 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 11 2)
  have hb_12_2 : 0 ≤ (51519488 : ℝ) * (σ ^ (12 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (51519488 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 2)
  have hb_13_2 : (-124321792 : ℝ) * t ^ (16 : ℕ) ≤ (-124321792 : ℝ) * (σ ^ (13 : ℕ) * t ^ (2 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 13 2 (by norm_num)) (show (-124321792 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_14_4 : (-7602176 : ℝ) * t ^ (16 : ℕ) ≤ (-7602176 : ℝ) * (σ ^ (14 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 14 4 (by norm_num)) (show (-7602176 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_16_2 : 0 ≤ (3342336 : ℝ) * (σ ^ (16 : ℕ) * t ^ (2 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (3342336 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 16 2)
  linarith

/-- Group 4 of the lower-order monomials of the cofactor. -/
noncomputable def skewConstantTiltPart4 (σ t : ℝ) : ℝ := (-71756800 : ℝ) * (σ ^ (0 : ℕ) * t ^ (8 : ℕ)) + (1736704 : ℝ) * (σ ^ (0 : ℕ) * t ^ (16 : ℕ)) + (-21676032 : ℝ) * (σ ^ (1 : ℕ) * t ^ (8 : ℕ)) + (7929856 : ℝ) * (σ ^ (1 : ℕ) * t ^ (16 : ℕ)) + (234995712 : ℝ) * (σ ^ (2 : ℕ) * t ^ (6 : ℕ)) + (-48431104 : ℝ) * (σ ^ (2 : ℕ) * t ^ (14 : ℕ)) + (-22198272 : ℝ) * (σ ^ (3 : ℕ) * t ^ (4 : ℕ)) + (-120979456 : ℝ) * (σ ^ (3 : ℕ) * t ^ (12 : ℕ)) + (155461632 : ℝ) * (σ ^ (4 : ℕ) * t ^ (4 : ℕ)) + (154206208 : ℝ) * (σ ^ (4 : ℕ) * t ^ (12 : ℕ)) + (-414064640 : ℝ) * (σ ^ (5 : ℕ) * t ^ (4 : ℕ)) + (-112459776 : ℝ) * (σ ^ (5 : ℕ) * t ^ (12 : ℕ)) + (138178560 : ℝ) * (σ ^ (6 : ℕ) * t ^ (6 : ℕ)) + (-50046976 : ℝ) * (σ ^ (7 : ℕ) * t ^ (0 : ℕ)) + (207880192 : ℝ) * (σ ^ (7 : ℕ) * t ^ (8 : ℕ)) + (139428864 : ℝ) * (σ ^ (8 : ℕ) * t ^ (4 : ℕ)) + (27713536 : ℝ) * (σ ^ (9 : ℕ) * t ^ (0 : ℕ)) + (25559040 : ℝ) * (σ ^ (9 : ℕ) * t ^ (8 : ℕ)) + (-543752192 : ℝ) * (σ ^ (10 : ℕ) * t ^ (6 : ℕ)) + (91881472 : ℝ) * (σ ^ (11 : ℕ) * t ^ (4 : ℕ)) + (-130613248 : ℝ) * (σ ^ (12 : ℕ) * t ^ (4 : ℕ)) + (53215232 : ℝ) * (σ ^ (13 : ℕ) * t ^ (4 : ℕ)) + (3670016 : ℝ) * (σ ^ (15 : ℕ) * t ^ (0 : ℕ)) + (589824 : ℝ) * (σ ^ (17 : ℕ) * t ^ (0 : ℕ))

theorem skewConstantTiltPart4_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-1535978496 : ℝ) * t ^ (16 : ℕ) ≤ skewConstantTiltPart4 σ t := by
  unfold skewConstantTiltPart4
  have hb_0_8 : (-71756800 : ℝ) * t ^ (16 : ℕ) ≤ (-71756800 : ℝ) * (σ ^ (0 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 0 8 (by norm_num)) (show (-71756800 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_0_16 : 0 ≤ (1736704 : ℝ) * (σ ^ (0 : ℕ) * t ^ (16 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (1736704 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 16)
  have hb_1_8 : (-21676032 : ℝ) * t ^ (16 : ℕ) ≤ (-21676032 : ℝ) * (σ ^ (1 : ℕ) * t ^ (8 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 1 8 (by norm_num)) (show (-21676032 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_16 : 0 ≤ (7929856 : ℝ) * (σ ^ (1 : ℕ) * t ^ (16 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (7929856 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 16)
  have hb_2_6 : 0 ≤ (234995712 : ℝ) * (σ ^ (2 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (234995712 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 6)
  have hb_2_14 : (-48431104 : ℝ) * t ^ (16 : ℕ) ≤ (-48431104 : ℝ) * (σ ^ (2 : ℕ) * t ^ (14 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 2 14 (by norm_num)) (show (-48431104 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_4 : (-22198272 : ℝ) * t ^ (16 : ℕ) ≤ (-22198272 : ℝ) * (σ ^ (3 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 4 (by norm_num)) (show (-22198272 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_3_12 : (-120979456 : ℝ) * t ^ (16 : ℕ) ≤ (-120979456 : ℝ) * (σ ^ (3 : ℕ) * t ^ (12 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 3 12 (by norm_num)) (show (-120979456 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_4_4 : 0 ≤ (155461632 : ℝ) * (σ ^ (4 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (155461632 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 4)
  have hb_4_12 : 0 ≤ (154206208 : ℝ) * (σ ^ (4 : ℕ) * t ^ (12 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (154206208 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 12)
  have hb_5_4 : (-414064640 : ℝ) * t ^ (16 : ℕ) ≤ (-414064640 : ℝ) * (σ ^ (5 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 5 4 (by norm_num)) (show (-414064640 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_5_12 : (-112459776 : ℝ) * t ^ (16 : ℕ) ≤ (-112459776 : ℝ) * (σ ^ (5 : ℕ) * t ^ (12 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 5 12 (by norm_num)) (show (-112459776 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_6_6 : 0 ≤ (138178560 : ℝ) * (σ ^ (6 : ℕ) * t ^ (6 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (138178560 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 6)
  have hb_7_0 : (-50046976 : ℝ) * t ^ (16 : ℕ) ≤ (-50046976 : ℝ) * (σ ^ (7 : ℕ) * t ^ (0 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 7 0 (by norm_num)) (show (-50046976 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_7_8 : 0 ≤ (207880192 : ℝ) * (σ ^ (7 : ℕ) * t ^ (8 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (207880192 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 8)
  have hb_8_4 : 0 ≤ (139428864 : ℝ) * (σ ^ (8 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (139428864 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 4)
  have hb_9_0 : 0 ≤ (27713536 : ℝ) * (σ ^ (9 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (27713536 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 0)
  have hb_9_8 : 0 ≤ (25559040 : ℝ) * (σ ^ (9 : ℕ) * t ^ (8 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (25559040 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 8)
  have hb_10_6 : (-543752192 : ℝ) * t ^ (16 : ℕ) ≤ (-543752192 : ℝ) * (σ ^ (10 : ℕ) * t ^ (6 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 10 6 (by norm_num)) (show (-543752192 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_11_4 : 0 ≤ (91881472 : ℝ) * (σ ^ (11 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (91881472 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 11 4)
  have hb_12_4 : (-130613248 : ℝ) * t ^ (16 : ℕ) ≤ (-130613248 : ℝ) * (σ ^ (12 : ℕ) * t ^ (4 : ℕ)) :=
    mul_le_mul_of_nonpos_left (skewMonoTop_le σ t h0 h1 ht1 12 4 (by norm_num)) (show (-130613248 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_13_4 : 0 ≤ (53215232 : ℝ) * (σ ^ (13 : ℕ) * t ^ (4 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (53215232 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 13 4)
  have hb_15_0 : 0 ≤ (3670016 : ℝ) * (σ ^ (15 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (3670016 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 15 0)
  have hb_17_0 : 0 ≤ (589824 : ℝ) * (σ ^ (17 : ℕ) * t ^ (0 : ℕ)) :=
    mul_nonneg (show (0 : ℝ) ≤ (589824 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 17 0)
  linarith

theorem skewConstantTiltCofactor_split (σ t : ℝ) :
    skewConstantTiltCofactor σ t = ((720896 : ℝ)) * t ^ (18 : ℕ) + skewConstantTiltPart1 σ t + skewConstantTiltPart2 σ t + skewConstantTiltPart3 σ t + skewConstantTiltPart4 σ t := by
  unfold skewConstantTiltCofactor skewConstantTiltPart1 skewConstantTiltPart2 skewConstantTiltPart3 skewConstantTiltPart4
  ring

/-- On the strip and above height 92 the constant-mode cofactor is positive. -/
theorem skewConstantTiltCofactor_pos (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (92 : ℝ) ≤ t) : 0 < skewConstantTiltCofactor σ t := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [skewConstantTiltCofactor_split]
  have p1 := skewConstantTiltPart1_ge σ t h0 h1 ht1
  have p2 := skewConstantTiltPart2_ge σ t h0 h1 ht1
  have p3 := skewConstantTiltPart3_ge σ t h0 h1 ht1
  have p4 := skewConstantTiltPart4_ge σ t h0 h1 ht1
  have hbig : (6067244032 : ℝ) * t ^ (16 : ℕ) < ((720896 : ℝ)) * t ^ (18 : ℕ) := by
    have : t ^ (18 : ℕ) = t ^ (16 : ℕ) * t ^ (2 : ℕ) := by ring
    rw [this]
    have hp : 0 < t ^ (16 : ℕ) := pow_pos (by linarith) 16
    have hsq : (92 : ℝ) ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith
    nlinarith
  linarith

/-- Above height 92 the real part of the constant-mode kernel vanishes exactly on the critical line. -/
theorem skewConstantKernel_re_eq_zero_iff (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (92 : ℝ) ≤ t) :
    (skewPlateauMu ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) 0).re = 0 ↔ σ = 1 / 2 := by
  have key := skewConstantKernel_re_tilt σ t (by linarith)
  have hne : ∀ c : ℝ, (2 * ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + (c : ℂ)) ≠ 0 := by
    intro c h; have := congrArg Complex.im h; simp at this; linarith
  have hpos : 0 < Complex.normSq (512 * skewConstantQ (((σ : ℂ) - 2 + (t : ℂ) * Complex.I + 3 / 2) ^ (2 : ℕ))) := by
    apply Complex.normSq_pos.mpr
    exact skewConstantQ_ne_zero _ (mul_ne_zero (by simpa using hne 1) (by simpa using hne 2)) (mul_ne_zero (by simpa using hne 4) (by simpa using hne 5))
  have hcof := skewConstantTiltCofactor_pos σ t h0 h1 ht
  constructor
  · intro hre
    rw [hre] at key
    have : (2 * σ - 1) * skewConstantTiltCofactor σ t = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hcof.ne'
  · intro hσ
    subst hσ
    have : 2 * (skewPlateauMu (((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) 0).re * Complex.normSq (512 * skewConstantQ ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I + 3 / 2) ^ (2 : ℕ))) = 0 := by
      rw [key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'

end RHTower.D4BMScalarStream
