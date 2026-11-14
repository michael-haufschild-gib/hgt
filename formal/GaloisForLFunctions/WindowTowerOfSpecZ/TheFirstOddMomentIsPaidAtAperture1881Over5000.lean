import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A first-moment supersolution at aperture `1881/5000`

A degree-32 lower approximation to the logarithmic boundary potential retains
prime-two reflection. A piecewise polynomial supersolution bounds the position
source's inverse capacity by `389/1000`. Completing squares pays its full charge
`77/30`, leaving a mass floor `1/2000` in the polynomial comparison form.
-/

noncomputable section
open Real MeasureTheory Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def logarithmicPolynomial16 (x : ℝ) : ℝ :=
  x ^ 2 / 2 + x ^ 4 / 4 + x ^ 6 / 6 + x ^ 8 / 8 +
  x ^ 10 / 10 + x ^ 12 / 12 + x ^ 14 / 14 + x ^ 16 / 16 +
  x ^ 18 / 18 + x ^ 20 / 20 + x ^ 22 / 22 + x ^ 24 / 24 +
  x ^ 26 / 26 + x ^ 28 / 28 + x ^ 30 / 30 + x ^ 32 / 32

private def stripResidual (x : ℝ) : ℝ :=
  (31 / 80 + logarithmicPolynomial16 x) * (263 / 100 - 23 / 10 * x) +
    49 / 100 * (263 / 100 - 23 / 10 * (1843 / 1000 - x)) - x

/-- Homogenization under `x=(421/500+t)/(1+t)`; every monomial coefficient is nonnegative. -/
private def stripHomogeneous (t : ℝ) : ℝ :=
  (31 / 80 * (1 + t) ^ 32 +
    (421 / 500 + t) ^ 2 * (1 + t) ^ 30 / 2 +
    (421 / 500 + t) ^ 4 * (1 + t) ^ 28 / 4 +
    (421 / 500 + t) ^ 6 * (1 + t) ^ 26 / 6 +
    (421 / 500 + t) ^ 8 * (1 + t) ^ 24 / 8 +
    (421 / 500 + t) ^ 10 * (1 + t) ^ 22 / 10 +
    (421 / 500 + t) ^ 12 * (1 + t) ^ 20 / 12 +
    (421 / 500 + t) ^ 14 * (1 + t) ^ 18 / 14 +
    (421 / 500 + t) ^ 16 * (1 + t) ^ 16 / 16 +
    (421 / 500 + t) ^ 18 * (1 + t) ^ 14 / 18 +
    (421 / 500 + t) ^ 20 * (1 + t) ^ 12 / 20 +
    (421 / 500 + t) ^ 22 * (1 + t) ^ 10 / 22 +
    (421 / 500 + t) ^ 24 * (1 + t) ^ 8 / 24 +
    (421 / 500 + t) ^ 26 * (1 + t) ^ 6 / 26 +
    (421 / 500 + t) ^ 28 * (1 + t) ^ 4 / 28 +
    (421 / 500 + t) ^ 30 * (1 + t) ^ 2 / 30 +
    (421 / 500 + t) ^ 32 / 32) *
      (263 / 100 * (1 + t) - 23 / 10 * (421 / 500 + t)) +
    (49 / 100 * ((263 / 100 - 23 / 10 * (1843 / 1000)) * (1 + t) +
      23 / 10 * (421 / 500 + t)) - (421 / 500 + t)) * (1 + t) ^ 32

private theorem stripHomogeneous_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ stripHomogeneous t := by
  unfold stripHomogeneous
  ring_nf
  positivity

private theorem stripHomogeneous_identity {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 33 * stripResidual ((421 / 500 + t) / (1 + t)) =
      stripHomogeneous t := by
  unfold stripResidual logarithmicPolynomial16 stripHomogeneous
  generalize hq : 421 / 500 + t = q
  generalize hp : 1 + t = p
  have hp0 : p ≠ 0 := by rw [← hp]; linarith only [ht]
  field_simp [hp0]
  ring

private theorem stripResidual_nonneg {x : ℝ} (hx : 421 / 500 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ stripResidual x := by
  rcases eq_or_lt_of_le hx1 with rfl | hx1
  · norm_num [stripResidual, logarithmicPolynomial16]
  let t := (x - 421 / 500) / (1 - x)
  have ht : 0 ≤ t := div_nonneg (by linarith only [hx]) (by linarith only [hx1])
  have hd : 0 < 1 + t := by linarith only [ht]
  have he : x = (421 / 500 + t) / (1 + t) := by
    dsimp [t]
    field_simp
    ring
  have hp := stripHomogeneous_nonneg ht
  rw [← stripHomogeneous_identity ht, ← he] at hp
  exact nonneg_of_mul_nonneg_right hp (pow_pos hd 33)

private theorem supersolution_capacity_rational :
    (329 / 600 : ℝ) - (263 / 200) * (421 / 500) ^ 2 +
      (80 / 93 + 23 / 30) * (843 / 1000) ^ 3 -
      (89 / 150) * (421 / 500) ^ 5 + (11 / 70) * (843 / 1000) ^ 7 ≤
        389 / 1000 := by
  norm_num

private def outsideSource (x : ℝ) : ℝ :=
  x * (80 / 31 - 89 / 30 * x ^ 2 + 11 / 10 * x ^ 4)

private theorem outside_polynomial_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 3 / 4) :
    1 ≤ (31 / 80 + t / 2 + t ^ 2 / 4 + t ^ 3 / 6 + t ^ 4 / 8 +
        t ^ 5 / 10 + t ^ 6 / 12 + t ^ 7 / 14 + t ^ 8 / 16) *
      (80 / 31 - 89 / 30 * t + 11 / 10 * t ^ 2) := by
  let P : ℝ := 131 - 413 * t + 236 * t ^ 2 + 101 * t ^ 3 +
    69 * t ^ 4 + 55 * t ^ 5 + 45 * t ^ 6
  -- Higher powers lie above their tangents at `1/2`; the retained quadratic has minimum above one.
  have hP : 1 ≤ P := by
    have he : P - (183 / 64 - 329 / 8 * (t - 1 / 2) + 236 * (t - 1 / 2) ^ 2) =
        (t - 1 / 2) ^ 2 *
          (101 * (t + 1) + 69 * (t ^ 2 + t + 3 / 4) +
            55 * (t ^ 3 + t ^ 2 + 3 / 4 * t + 1 / 2) +
            45 * (t ^ 4 + t ^ 3 + 3 / 4 * t ^ 2 + t / 2 + 5 / 16)) := by
      dsimp [P]
      ring
    have hr : 0 ≤ P - (183 / 64 - 329 / 8 * (t - 1 / 2) +
        236 * (t - 1 / 2) ^ 2) := by
      rw [he]
      positivity
    nlinarith only [hr, sq_nonneg (t - 2217 / 3776)]
  let Q : ℝ := (5 / 31 - 89 / 420 + 11 / 120) - 359 / 3360 * t + 11 / 160 * t ^ 2
  have hQ : -(1 / 900 : ℝ) ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (t - 359 / 462)]
  have hr : 0 ≤
      (31 / 80 + t / 2 + t ^ 2 / 4 + t ^ 3 / 6 + t ^ 4 / 8 +
        t ^ 5 / 10 + t ^ 6 / 12 + t ^ 7 / 14 + t ^ 8 / 16) *
        (80 / 31 - 89 / 30 * t + 11 / 10 * t ^ 2) - 1 -
        t / 1000 * P - t ^ 8 * Q - t ^ 7 / 1200 := by
    dsimp [P, Q]
    ring_nf
    positivity
  have htail : 0 ≤ t ^ 8 * Q + t ^ 7 / 1200 := by
    have h1 := mul_nonneg (pow_nonneg ht 8) (show 0 ≤ Q + 1 / 900 by linarith only [hQ])
    have h2 := mul_nonneg (pow_nonneg ht 7) (show 0 ≤ 3 / 4 - t by linarith only [ht1])
    nlinarith only [h1, h2]
  have hmain : 0 ≤ t / 1000 * P := mul_nonneg (by positivity) (by linarith only [hP])
  linarith only [hr, htail, hmain]

private theorem outsideSource_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ outsideSource x := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1]
  have h : 0 ≤ 80 / 31 - 89 / 30 * x ^ 2 + 11 / 10 * x ^ 4 := by
    have hs := sq_nonneg (x ^ 2 - 1)
    nlinarith only [hx2, hs]
  exact mul_nonneg hx h

private theorem outside_source_supersolution {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 843 / 1000) :
    x ≤ (31 / 80 + logarithmicPolynomial16 x) * outsideSource x := by
  have hx2 : x ^ 2 ≤ 3 / 4 := by nlinarith only [hx, hx1]
  have h := mul_le_mul_of_nonneg_left (outside_polynomial_bound (sq_nonneg x) hx2) hx
  have hp : 0 ≤ 80 / 31 - 89 / 30 * x ^ 2 + 11 / 10 * (x ^ 2) ^ 2 := by
    have h1 : x ^ 2 ≤ 1 := by linarith only [hx2]
    nlinarith only [h1, sq_nonneg (x ^ 2 - 1)]
  have ht : 0 ≤ (x ^ 18 / 18 + x ^ 20 / 20 + x ^ 22 / 22 + x ^ 24 / 24 +
      x ^ 26 / 26 + x ^ 28 / 28 + x ^ 30 / 30 + x ^ 32 / 32) *
        x * (80 / 31 - 89 / 30 * x ^ 2 + 11 / 10 * (x ^ 2) ^ 2) := by
    exact mul_nonneg (mul_nonneg (by positivity) hx) hp
  unfold logarithmicPolynomial16 outsideSource
  nlinarith only [h, ht]

private theorem logarithmicPolynomial16_nonneg (x : ℝ) : 0 ≤ logarithmicPolynomial16 x := by
  unfold logarithmicPolynomial16
  positivity

private theorem logarithmicPolynomial16_le_log {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    logarithmicPolynomial16 x ≤ -Real.log (1 - x ^ 2) / 2 := by
  have hx2 : |x ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [hx, hx1]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hx2
  have hb := Summable.sum_le_tsum (Finset.range 16)
    (fun n _ => show 0 ≤ (x ^ 2) ^ (n + 1) / ((n : ℝ) + 1) by positivity) hs.summable
  rw [hs.tsum_eq] at hb
  norm_num [Finset.sum_range_succ] at hb
  unfold logarithmicPolynomial16
  nlinarith only [hb]

/-- Completing squares leaves adjugate-weighted supersolution defects, all nonnegative. -/
private theorem paired_young_of_supersolution {a b w p q g h : ℝ}
    (ha : 0 < a) (hd : 0 < a * b - w ^ 2)
    (hp : 0 ≤ b * p - w * q) (hq : 0 ≤ a * q - w * p)
    (hg : p ≤ a * g + w * h) (hh : q ≤ w * g + b * h) (u v t : ℝ) :
    2 * t * (p * u + q * v) ≤ a * u ^ 2 + 2 * w * u * v + b * v ^ 2 +
      t ^ 2 * (p * g + q * h) := by
  have h1 := mul_nonneg hp (sub_nonneg.mpr hg)
  have h2 := mul_nonneg hq (sub_nonneg.mpr hh)
  have he : a * (a * b - w ^ 2) *
      (a * u ^ 2 + 2 * w * u * v + b * v ^ 2 +
        t ^ 2 * (p * g + q * h) - 2 * t * (p * u + q * v)) =
      (a * b - w ^ 2) * (a * u + w * v - t * p) ^ 2 +
      ((a * b - w ^ 2) * v - t * (a * q - w * p)) ^ 2 +
      a * t ^ 2 * ((b * p - w * q) * (a * g + w * h - p) +
        (a * q - w * p) * (w * g + b * h - q)) := by ring
  have hn : 0 ≤ a * (a * b - w ^ 2) *
      (a * u ^ 2 + 2 * w * u * v + b * v ^ 2 +
        t ^ 2 * (p * g + q * h) - 2 * t * (p * u + q * v)) := by
    rw [he]
    exact add_nonneg (add_nonneg (mul_nonneg hd.le (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg ha.le (sq_nonneg t)) (add_nonneg h1 h2))
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn (mul_pos ha hd))

private theorem scalar_young_of_supersolution {a p g : ℝ}
    (ha : 0 < a) (hp : 0 ≤ p) (hg : p ≤ a * g) (u t : ℝ) :
    2 * t * p * u ≤ a * u ^ 2 + t ^ 2 * (p * g) := by
  have hn : 0 ≤ (a * u - t * p) ^ 2 + t ^ 2 * p * (a * g - p) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg t) hp) (sub_nonneg.mpr hg))
  have he : (a * u - t * p) ^ 2 + t ^ 2 * p * (a * g - p) =
      a * (a * u ^ 2 + t ^ 2 * (p * g) - 2 * t * p * u) := by ring
  rw [he] at hn
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn ha)

private def stripSource (x : ℝ) : ℝ := 263 / 100 - 23 / 10 * x

/-- Polynomial multiplication coefficient for the first-overlap odd comparison. -/
def firstOverlapOddPotential (x : ℝ) : ℝ := 31 / 80 + logarithmicPolynomial16 x

/-- The left endpoint of prime-two reflection after dilation by `1881/5000`. -/
def firstOverlapOddStripLeft : ℝ := Real.log 2 / (1881 / 5000) - 1

private def primeWeight : ℝ := Real.log 2 / Real.sqrt 2

private theorem stripLeft_bounds :
    (421 / 500 : ℝ) ≤ firstOverlapOddStripLeft ∧ firstOverlapOddStripLeft ≤ 843 / 1000 := by
  unfold firstOverlapOddStripLeft
  constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem primeWeight_bounds : (49 / 100 : ℝ) ≤ primeWeight ∧ primeWeight ≤ 4902 / 10000 := by
  have hl : (14142 / 10000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hu : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  unfold primeWeight
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hu, Real.log_two_gt_d9]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hl, Real.log_two_lt_d9]

private theorem potential_lower (x : ℝ) : 31 / 80 ≤ firstOverlapOddPotential x := by
  unfold firstOverlapOddPotential
  linarith only [logarithmicPolynomial16_nonneg x]

private theorem potential_strip_lower {x : ℝ} (hx : 421 / 500 ≤ x) :
    31 / 80 + 1 / 2 ≤ firstOverlapOddPotential x := by
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 421 / 500) hx 2
  have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 421 / 500) hx 4
  have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 421 / 500) hx 6
  have hn : 1 / 2 ≤ (421 / 500 : ℝ) ^ 2 / 2 + (421 / 500 : ℝ) ^ 4 / 4 +
      (421 / 500 : ℝ) ^ 6 / 6 := by norm_num
  have hr : 0 ≤ logarithmicPolynomial16 x - (x ^ 2 / 2 + x ^ 4 / 4 + x ^ 6 / 6) := by
    unfold logarithmicPolynomial16
    ring_nf
    positivity
  unfold firstOverlapOddPotential
  linarith only [h2, h4, h6, hn, hr]

private theorem reflect_in_strip {x : ℝ}
    (hx : x ∈ Icc firstOverlapOddStripLeft 1) :
    firstOverlapOddStripLeft + 1 - x ∈ Icc firstOverlapOddStripLeft 1 :=
  ⟨by linarith only [hx.2], by linarith only [hx.1]⟩

private theorem stripSource_nonneg {x : ℝ} (hx : x ≤ 1) : 0 ≤ stripSource x := by
  unfold stripSource
  linarith only [hx]

private theorem strip_source_supersolution {x : ℝ}
    (hx : x ∈ Icc firstOverlapOddStripLeft 1) :
    x ≤ firstOverlapOddPotential x * stripSource x +
      primeWeight * stripSource (firstOverlapOddStripLeft + 1 - x) := by
  have hl : 421 / 500 ≤ x := stripLeft_bounds.1.trans hx.1
  have hr := stripResidual_nonneg hl hx.2
  have hy := reflect_in_strip hx
  have hg := stripSource_nonneg hy.2
  have hsource : 263 / 100 - 23 / 10 * (1843 / 1000 - x) ≤
      stripSource (firstOverlapOddStripLeft + 1 - x) := by
    unfold stripSource
    linarith only [stripLeft_bounds.2]
  have hm1 := mul_le_mul_of_nonneg_right primeWeight_bounds.1 hg
  have hm2 := mul_le_mul_of_nonneg_left hsource (by norm_num : (0 : ℝ) ≤ 49 / 100)
  unfold firstOverlapOddPotential stripSource stripResidual at *
  linarith only [hr, hm1, hm2]

private theorem potential_pair_det {x y : ℝ} (hx : 421 / 500 ≤ x) (hy : 421 / 500 ≤ y) :
    0 < firstOverlapOddPotential x * firstOverlapOddPotential y - primeWeight ^ 2 := by
  have ha := potential_strip_lower hx
  have hb := potential_strip_lower hy
  have hw := primeWeight_bounds
  have hm := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 31 / 80 + 1 / 2)
    (by linarith only [ha])
  nlinarith only [hm, hw.1, hw.2]

private theorem position_adjugate_nonneg {x y : ℝ}
    (hx : x ∈ Icc (421 / 500 : ℝ) 1) (hy : y ∈ Icc (421 / 500 : ℝ) 1) :
    0 ≤ firstOverlapOddPotential y * x - primeWeight * y := by
  have ha := potential_strip_lower hy.1
  have hm := mul_le_mul ha hx.1 (by norm_num : (0 : ℝ) ≤ 421 / 500)
    (by linarith only [ha])
  have hw := mul_le_mul primeWeight_bounds.2 hy.2 (by linarith only [hy.1])
    (by norm_num : (0 : ℝ) ≤ 4902 / 10000)
  linarith only [hm, hw]

private theorem capacity_identity (b : ℝ) :
    (∫ x in (0 : ℝ)..b, x * outsideSource x) + (∫ x in b..1, x * stripSource x) =
      329 / 600 - 263 / 200 * b ^ 2 + (80 / 93 + 23 / 30) * b ^ 3 -
        89 / 150 * b ^ 5 + 11 / 70 * b ^ 7 := by
  have h1 : (fun x => x * outsideSource x) =
      fun x : ℝ => (80 / 31) * x ^ 2 - (89 / 30) * x ^ 4 + (11 / 10) * x ^ 6 := by
    funext x
    unfold outsideSource
    ring
  have h2 : (fun x => x * stripSource x) =
      fun x : ℝ => (263 / 100) * x - (23 / 10) * x ^ 2 := by
    funext x
    unfold stripSource
    ring
  rw [h1, h2]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  rw [intervalIntegral.integral_const_mul (f := fun x : ℝ => x), integral_id]
  norm_num
  ring

private theorem capacity_bound :
    (∫ x in (0 : ℝ)..firstOverlapOddStripLeft, x * outsideSource x) +
      (∫ x in firstOverlapOddStripLeft..1, x * stripSource x) ≤ 389 / 1000 := by
  have hb := stripLeft_bounds
  have hb0 : 0 ≤ firstOverlapOddStripLeft := by linarith only [hb.1]
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 421 / 500) hb.1 2
  have h3 := pow_le_pow_left₀ hb0 hb.2 3
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 421 / 500) hb.1 5
  have h7 := pow_le_pow_left₀ hb0 hb.2 7
  rw [capacity_identity]
  linarith only [h2, h3, h5, h7, supersolution_capacity_rational]

private def reflect (x : ℝ) : ℝ := firstOverlapOddStripLeft + 1 - x

/-- The factor `1/2` counts each reflected pair once. -/
private def blockIntegral (f g : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..firstOverlapOddStripLeft, f x) +
    (∫ x in firstOverlapOddStripLeft..1, g x) / 2

/-- Multiplication by the polynomial potential, with prime-two reflection retained. -/
def firstOverlapOddEnergy (G : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, firstOverlapOddPotential x * G x ^ 2) +
    primeWeight * ∫ x in firstOverlapOddStripLeft..1, G x * G (reflect x)

private def pairDensity (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  firstOverlapOddPotential x * G x ^ 2 +
    firstOverlapOddPotential (reflect x) * G (reflect x) ^ 2 +
    2 * primeWeight * (G x * G (reflect x))

@[fun_prop] private theorem continuous_potential : Continuous firstOverlapOddPotential := by
  unfold firstOverlapOddPotential logarithmicPolynomial16
  fun_prop

@[fun_prop] private theorem continuous_reflect : Continuous reflect := by
  unfold reflect
  fun_prop

@[fun_prop] private theorem continuous_outsideSource : Continuous outsideSource := by
  unfold outsideSource
  fun_prop

@[fun_prop] private theorem continuous_stripSource : Continuous stripSource := by
  unfold stripSource
  fun_prop

@[fun_prop] private theorem continuous_pairDensity {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous (pairDensity G) := by
  unfold pairDensity
  fun_prop

private theorem blockIntegral_add {f g h k : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    blockIntegral (fun x => f x + h x) (fun x => g x + k x) =
      blockIntegral f g + blockIntegral h k := by
  unfold blockIntegral
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _),
    intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  ring

private theorem blockIntegral_sub {f g h k : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    blockIntegral (fun x => f x - h x) (fun x => g x - k x) =
      blockIntegral f g - blockIntegral h k := by
  unfold blockIntegral
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  ring

private theorem blockIntegral_const_mul (c : ℝ) (f g : ℝ → ℝ) :
    blockIntegral (fun x => c * f x) (fun x => c * g x) = c * blockIntegral f g := by
  unfold blockIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

private theorem blockIntegral_nonneg {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) firstOverlapOddStripLeft, 0 ≤ f x)
    (hg : ∀ x ∈ Icc firstOverlapOddStripLeft 1, 0 ≤ g x) : 0 ≤ blockIntegral f g := by
  have hb := stripLeft_bounds
  unfold blockIntegral
  exact add_nonneg
    (intervalIntegral.integral_nonneg (by linarith only [hb.1]) hf)
    (div_nonneg (intervalIntegral.integral_nonneg (by linarith only [hb.2]) hg) (by norm_num))

private theorem reflection_integral (f : ℝ → ℝ) :
    (∫ x in firstOverlapOddStripLeft..1, f (reflect x)) =
      ∫ x in firstOverlapOddStripLeft..1, f x := by
  have h := intervalIntegral.integral_comp_sub_left f (firstOverlapOddStripLeft + 1)
    (a := firstOverlapOddStripLeft) (b := 1)
  simpa only [reflect, add_sub_cancel_right, add_sub_cancel_left] using h

private theorem blockIntegral_pair {f g : ℝ → ℝ} (hg : Continuous g) :
    blockIntegral f (fun x => g x + g (reflect x)) =
      (∫ x in (0 : ℝ)..firstOverlapOddStripLeft, f x) +
        ∫ x in firstOverlapOddStripLeft..1, g x := by
  unfold blockIntegral
  rw [intervalIntegral.integral_add (f := g) (g := fun x => g (reflect x)) (hg.intervalIntegrable _ _)
    ((hg.comp continuous_reflect).intervalIntegrable _ _), reflection_integral]
  ring

private theorem blockIntegral_diagonal {f : ℝ → ℝ} (hf : Continuous f) :
    blockIntegral f (fun x => f x + f (reflect x)) = ∫ x in (0 : ℝ)..1, f x := by
  rw [blockIntegral_pair hf]
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)

private theorem blockIntegral_energy {G : ℝ → ℝ} (hG : Continuous G) :
    blockIntegral (fun x => firstOverlapOddPotential x * G x ^ 2) (pairDensity G) =
      firstOverlapOddEnergy G := by
  have hi : Continuous (fun x => firstOverlapOddPotential x * G x ^ 2) := by fun_prop
  have hir : Continuous (fun x => firstOverlapOddPotential (reflect x) * G (reflect x) ^ 2) := by
    fun_prop
  have hic : Continuous (fun x => G x * G (reflect x)) := by fun_prop
  unfold blockIntegral pairDensity firstOverlapOddEnergy
  rw [intervalIntegral.integral_add ((hi.intervalIntegrable _ _).add
      (hir.intervalIntegrable _ _)) ((hic.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_add (hi.intervalIntegrable _ _) (hir.intervalIntegrable _ _),
    reflection_integral (fun x => firstOverlapOddPotential x * G x ^ 2),
    intervalIntegral.integral_const_mul]
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hi.intervalIntegrable 0 firstOverlapOddStripLeft) (hi.intervalIntegrable firstOverlapOddStripLeft 1)
  linarith only [ha]

private theorem pair_young {G : ℝ → ℝ} (x t : ℝ)
    (hx : x ∈ Icc firstOverlapOddStripLeft 1) :
    2 * t * (x * G x + reflect x * G (reflect x)) ≤ pairDensity G x +
      t ^ 2 * (x * stripSource x + reflect x * stripSource (reflect x)) := by
  have hy := reflect_in_strip hx
  have hx' : x ∈ Icc (421 / 500 : ℝ) 1 := ⟨stripLeft_bounds.1.trans hx.1, hx.2⟩
  have hy' : reflect x ∈ Icc (421 / 500 : ℝ) 1 := ⟨stripLeft_bounds.1.trans hy.1, hy.2⟩
  have hg := strip_source_supersolution hx
  have hh := strip_source_supersolution hy
  have hrr : firstOverlapOddStripLeft + 1 - (firstOverlapOddStripLeft + 1 - x) = x := by ring
  rw [hrr] at hh
  have h := paired_young_of_supersolution
    (by linarith only [potential_lower x] : 0 < firstOverlapOddPotential x)
    (potential_pair_det hx'.1 hy'.1) (position_adjugate_nonneg hx' hy')
    (position_adjugate_nonneg hy' hx') hg (by simpa only [add_comm, reflect] using hh)
    (G x) (G (reflect x)) t
  unfold pairDensity
  dsimp only [reflect] at h ⊢
  nlinarith only [h]

private theorem firstOverlap_young {G : ℝ → ℝ} (hG : Continuous G) (t : ℝ) :
    2 * t * (∫ x in (0 : ℝ)..1, x * G x) ≤ firstOverlapOddEnergy G + (389 / 1000) * t ^ 2 := by
  let fE := fun x => firstOverlapOddPotential x * G x ^ 2
  let fC := fun x => x * outsideSource x
  let gC := fun x => x * stripSource x + reflect x * stripSource (reflect x)
  let fM := fun x => x * G x
  let gM := fun x => x * G x + reflect x * G (reflect x)
  have hfE : Continuous fE := by dsimp [fE]; fun_prop
  have hfC : Continuous fC := by dsimp [fC]; fun_prop
  have hgC : Continuous gC := by dsimp [gC]; fun_prop
  have hfM : Continuous fM := by dsimp [fM]; fun_prop
  have hgM : Continuous gM := by dsimp [gM]; fun_prop
  have hn : 0 ≤ blockIntegral
      (fun x => (fE x + t ^ 2 * fC x) - (2 * t) * fM x)
      (fun x => (pairDensity G x + t ^ 2 * gC x) - (2 * t) * gM x) := by
    apply blockIntegral_nonneg
    · intro x hx
      have hs := outside_source_supersolution hx.1 (hx.2.trans stripLeft_bounds.2)
      have h := scalar_young_of_supersolution
        (by linarith only [potential_lower x] : 0 < firstOverlapOddPotential x)
        hx.1 hs (G x) t
      dsimp [fE, fC, fM]
      nlinarith only [h]
    · intro x hx
      exact sub_nonneg.mpr (pair_young x t hx)
  rw [blockIntegral_sub
    (f := fun x => fE x + t ^ 2 * fC x)
    (g := fun x => pairDensity G x + t ^ 2 * gC x)
    (h := fun x => (2 * t) * fM x) (k := fun x => (2 * t) * gM x)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
    blockIntegral_add (f := fE) (g := pairDensity G)
      (h := fun x => t ^ 2 * fC x) (k := fun x => t ^ 2 * gC x)
      hfE (continuous_pairDensity hG) (by fun_prop) (by fun_prop),
    blockIntegral_const_mul, blockIntegral_const_mul] at hn
  have he : blockIntegral fE (pairDensity G) = firstOverlapOddEnergy G := blockIntegral_energy hG
  have hm : blockIntegral fM gM = ∫ x in (0 : ℝ)..1, x * G x := blockIntegral_diagonal hfM
  have hc : blockIntegral fC gC ≤ 389 / 1000 := by
    rw [show gC = fun x => (x * stripSource x) + (reflect x * stripSource (reflect x)) by rfl,
      blockIntegral_pair (by fun_prop)]
    exact capacity_bound
  rw [he, hm] at hn
  have ht := mul_le_mul_of_nonneg_left hc (sq_nonneg t)
  nlinarith only [hn, ht]

private theorem firstOverlap_energy_floor {G : ℝ → ℝ} (hG : Continuous G) :
    (31 / 80 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤ firstOverlapOddEnergy G := by
  have hn : 0 ≤ blockIntegral
      (fun x => firstOverlapOddPotential x * G x ^ 2 - (31 / 80) * G x ^ 2)
      (fun x => pairDensity G x - (31 / 80) * (G x ^ 2 + G (reflect x) ^ 2)) := by
    apply blockIntegral_nonneg
    · intro x _
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right (potential_lower x) (sq_nonneg _))
    · intro x hx
      have hy := reflect_in_strip hx
      have hx' := potential_strip_lower (stripLeft_bounds.1.trans hx.1)
      have hy' := potential_strip_lower (stripLeft_bounds.1.trans hy.1)
      change 31 / 80 + 1 / 2 ≤ firstOverlapOddPotential (reflect x) at hy'
      have hw := primeWeight_bounds
      have h1 := mul_nonneg (show 0 ≤ firstOverlapOddPotential x - 31 / 80 - primeWeight by
        linarith only [hx', hw.2]) (sq_nonneg (G x))
      have h2 := mul_nonneg (show 0 ≤ firstOverlapOddPotential (reflect x) - 31 / 80 - primeWeight by
        linarith only [hy', hw.2]) (sq_nonneg (G (reflect x)))
      have h3 := mul_nonneg (show 0 ≤ primeWeight by linarith only [hw.1])
        (sq_nonneg (G x + G (reflect x)))
      unfold pairDensity
      nlinarith only [h1, h2, h3]
  rw [blockIntegral_sub (by fun_prop) (continuous_pairDensity hG) (by fun_prop) (by fun_prop),
    blockIntegral_energy hG, blockIntegral_const_mul,
    blockIntegral_diagonal (f := fun x => G x ^ 2) (hG.pow 2)] at hn
  exact sub_nonneg.mp hn

/-- The polynomial reflection form pays the full first odd charge and leaves a mass floor. -/
theorem firstOverlapOddEnergy_sub_first_moment {G : ℝ → ℝ} (hG : Continuous G) :
    (1 / 2000 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤ firstOverlapOddEnergy G -
      (77 / 30 : ℝ) * (∫ x in (0 : ℝ)..1, x * G x) ^ 2 := by
  have hy := firstOverlap_young hG ((1000 / 389) * (∫ x in (0 : ℝ)..1, x * G x))
  have hf := firstOverlap_energy_floor hG
  have hm : 0 ≤ ∫ x in (0 : ℝ)..1, G x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  nlinarith only [hy, hf, hm]

/-- The polynomial potential lies below its logarithmic counterpart. -/
theorem firstOverlapOddPotential_le_log {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    firstOverlapOddPotential x ≤ 31 / 80 - Real.log (1 - x ^ 2) / 2 := by
  unfold firstOverlapOddPotential
  linarith only [logarithmicPolynomial16_le_log hx hx1]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstOverlapOddEnergy_sub_first_moment
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstOverlapOddPotential_le_log
