import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict attenuation of the canonical scalar Julia defect

For the Gamma-sewn compression used by the arithmetic Julia lift, the square of the scalar
compression has the universal hyperbolic form

`cosh(y/2)^(2 : ℕ) / sqrt(cosh(2y))`.

After the substitution `t = tanh(y/2)`, this becomes

`1 / sqrt(1 + 6t^(2 : ℕ) + t^(4 : ℕ))`.

This file proves that the corresponding quadratically normalized Julia defect is strictly
decreasing with the logarithmic aperture `y`.  The proof is analytic and exact; it uses no
numerical computation.
-/

open Set

namespace HTGeometry

noncomputable section

/-- Quartic denominator of the Gamma-sewn Julia compression in the coordinate
`t = tanh(y/2)`. -/
def juliaDefectQuartic (t : ℝ) : ℝ :=
  1 + 6 * t ^ (2 : ℕ) + t ^ (4 : ℕ)

/-- Logarithmic velocity of the squared Julia defect in the `tanh` coordinate. -/
def juliaDefectVelocity (t : ℝ) : ℝ :=
  t * (1 - t ^ (2 : ℕ)) * (t ^ (2 : ℕ) + 3) / juliaDefectQuartic t

/-- Hyperbolic duplication identity behind the universal quartic normal form. -/
theorem juliaDefectQuartic_tanh_mul_cosh_four (a : ℝ) :
    juliaDefectQuartic (Real.tanh a) * Real.cosh a ^ (4 : ℕ) =
      Real.cosh (4 * a) := by
  have hc0 : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  rw [juliaDefectQuartic, Real.tanh_eq_sinh_div_cosh]
  field_simp [hc0]
  rw [show 4 * a = 2 * (2 * a) by ring,
    Real.cosh_two_mul, Real.cosh_two_mul, Real.sinh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq a]

/-- Exact equality between the quartic and hyperbolic compression-square coordinates. -/
theorem inv_sqrt_juliaDefectQuartic_tanh_eq_cosh_ratio (a : ℝ) :
    (Real.sqrt (juliaDefectQuartic (Real.tanh a)))⁻¹ =
      Real.cosh a ^ (2 : ℕ) / Real.sqrt (Real.cosh (4 * a)) := by
  have hp : 0 < juliaDefectQuartic (Real.tanh a) := by
    rw [juliaDefectQuartic]
    positivity
  have hc4 : 0 < Real.cosh (4 * a) := Real.cosh_pos _
  have hsP0 : Real.sqrt (juliaDefectQuartic (Real.tanh a)) ≠ 0 := by positivity
  have hsC0 : Real.sqrt (Real.cosh (4 * a)) ≠ 0 := by positivity
  have hsP : Real.sqrt (juliaDefectQuartic (Real.tanh a)) ^ (2 : ℕ) =
      juliaDefectQuartic (Real.tanh a) := Real.sq_sqrt hp.le
  have hsC : Real.sqrt (Real.cosh (4 * a)) ^ (2 : ℕ) = Real.cosh (4 * a) :=
    Real.sq_sqrt hc4.le
  have hprod :
      Real.sqrt (Real.cosh (4 * a)) =
        Real.cosh a ^ (2 : ℕ) *
          Real.sqrt (juliaDefectQuartic (Real.tanh a)) := by
    have hsq :
        (Real.cosh a ^ (2 : ℕ) *
            Real.sqrt (juliaDefectQuartic (Real.tanh a))) ^ (2 : ℕ) =
          Real.cosh (4 * a) := by
      rw [mul_pow, hsP]
      nlinarith [juliaDefectQuartic_tanh_mul_cosh_four a]
    have hleft := Real.sqrt_nonneg (Real.cosh (4 * a))
    have hright : 0 ≤ Real.cosh a ^ (2 : ℕ) *
        Real.sqrt (juliaDefectQuartic (Real.tanh a)) := by positivity
    nlinarith
  field_simp [hsP0, hsC0]
  simpa [mul_comm] using hprod

/-- The inverse hyperbolic tangent lies strictly below its rational tangent envelope. -/
theorem artanh_lt_div_one_sub_sq
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.artanh t < t / (1 - t ^ (2 : ℕ)) := by
  have htmem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have ha : 0 < Real.artanh t := Real.artanh_pos ⟨ht0, ht1⟩
  have hs : 2 * Real.artanh t < Real.sinh (2 * Real.artanh t) :=
    Real.self_lt_sinh_iff.mpr (by positivity)
  rw [Real.sinh_two_mul, Real.sinh_artanh htmem,
    Real.cosh_artanh htmem] at hs
  have hu : 0 < 1 - t ^ (2 : ℕ) := by nlinarith
  have hsqrt : Real.sqrt (1 - t ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - t ^ (2 : ℕ) :=
    Real.sq_sqrt hu.le
  have hsqrt0 : Real.sqrt (1 - t ^ (2 : ℕ)) ≠ 0 := by positivity
  rw [show 2 * (t / Real.sqrt (1 - t ^ (2 : ℕ))) *
      (1 / Real.sqrt (1 - t ^ (2 : ℕ))) = 2 * (t / (1 - t ^ (2 : ℕ))) by
    field_simp [hsqrt0]
    nlinarith] at hs
  linarith

lemma juliaDefectQuartic_gt_one {t : ℝ} (ht0 : 0 < t) :
    1 < juliaDefectQuartic t := by
  rw [juliaDefectQuartic]
  nlinarith [sq_pos_of_pos ht0, sq_nonneg (t ^ (2 : ℕ))]

lemma juliaDefectQuartic_pos {t : ℝ} (ht0 : 0 < t) :
    0 < juliaDefectQuartic t :=
  lt_trans zero_lt_one (juliaDefectQuartic_gt_one ht0)

/-- Polynomial residue which makes normalized Julia attenuation strict. -/
lemma sqrt_juliaDefectQuartic_sub_one_gt_rational
    {t : ℝ} (ht0 : 0 < t) :
    t ^ (2 : ℕ) * (t ^ (2 : ℕ) + 3) / juliaDefectQuartic t <
      Real.sqrt (juliaDefectQuartic t) - 1 := by
  let u := t ^ (2 : ℕ)
  let p := juliaDefectQuartic t
  let s := Real.sqrt p
  have hu : 0 < u := sq_pos_of_pos ht0
  have hp : 1 < p := juliaDefectQuartic_gt_one ht0
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hs0 : 0 ≤ s := Real.sqrt_nonneg p
  have hsSq : s ^ (2 : ℕ) = p := Real.sq_sqrt hp0.le
  have hs1 : 1 < s := by nlinarith
  have hsP : s < p := by
    nlinarith [mul_pos (by linarith : 0 < s) (sub_pos.mpr hs1)]
  have hpoly : 0 < 3 * p - (u + 3) := by
    dsimp only [p, u, juliaDefectQuartic]
    nlinarith [sq_pos_of_pos ht0, sq_nonneg (t ^ (2 : ℕ))]
  have hbig : (s + 1) * (u + 3) < p * (u + 6) := by
    have hu3 : 0 < u + 3 := by positivity
    calc
      (s + 1) * (u + 3) < (p + 1) * (u + 3) := by gcongr
      _ < p * (u + 6) := by nlinarith
  have hsplus : 0 < s + 1 := by positivity
  have hid : s - 1 = u * (u + 6) / (s + 1) := by
    have hpform : p - 1 = u * (u + 6) := by
      dsimp only [p, u, juliaDefectQuartic]
      ring
    rw [← hpform]
    field_simp [ne_of_gt hsplus]
    nlinarith
  change u * (u + 3) / p < s - 1
  rw [hid]
  rw [div_lt_div_iff₀ hp0 hsplus]
  nlinarith [mul_pos hu (sub_pos.mpr hbig)]

/-- Core strict elasticity inequality in the `tanh` coordinate. -/
theorem artanh_mul_juliaDefectVelocity_lt_sqrt_sub_one
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.artanh t * juliaDefectVelocity t <
      Real.sqrt (juliaDefectQuartic t) - 1 := by
  have hu : 0 < 1 - t ^ (2 : ℕ) := by nlinarith
  have hp : 0 < juliaDefectQuartic t := juliaDefectQuartic_pos ht0
  have hfac : 0 < t * (1 - t ^ (2 : ℕ)) * (t ^ (2 : ℕ) + 3) /
      juliaDefectQuartic t := by positivity
  have h := mul_lt_mul_of_pos_right (artanh_lt_div_one_sub_sq ht0 ht1) hfac
  have hsimp :
      (t / (1 - t ^ (2 : ℕ))) *
          (t * (1 - t ^ (2 : ℕ)) * (t ^ (2 : ℕ) + 3) / juliaDefectQuartic t) =
        t ^ (2 : ℕ) * (t ^ (2 : ℕ) + 3) / juliaDefectQuartic t := by
    field_simp
  rw [hsimp] at h
  exact h.trans (sqrt_juliaDefectQuartic_sub_one_gt_rational ht0)

/-- Squared defect of the universal Gamma-sewn Julia compression. -/
def juliaDefectSquareProfile (y : ℝ) : ℝ :=
  let t := Real.tanh (y / 2)
  1 - (Real.sqrt (juliaDefectQuartic t))⁻¹

/-- Quadratically normalized squared Julia defect. -/
def juliaDefectAttenuationProfile (y : ℝ) : ℝ :=
  (4 / 3 : ℝ) * juliaDefectSquareProfile y / y ^ (2 : ℕ)

lemma hasDerivAt_half (y : ℝ) :
    HasDerivAt (fun z : ℝ => z / 2) (1 / 2 : ℝ) y := by
  simpa using (hasDerivAt_id y).div_const 2

lemma hasDerivAt_tanhHalf (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.tanh (z / 2))
      ((1 / Real.cosh (y / 2) ^ (2 : ℕ)) * (1 / 2 : ℝ)) y := by
  have hfun : (fun z : ℝ => Real.tanh (z / 2)) =
      Real.tanh ∘ fun z : ℝ => z / 2 := by funext z; rfl
  rw [hfun]
  exact (hasDerivAt_tanh (y / 2)).comp y (hasDerivAt_half y)

lemma hasDerivAt_juliaDefectQuartic (t : ℝ) :
    HasDerivAt juliaDefectQuartic (12 * t + 4 * t ^ (3 : ℕ)) t := by
  have hfun : juliaDefectQuartic =
      fun z : ℝ => 1 + 6 * z ^ (2 : ℕ) + z ^ (4 : ℕ) := rfl
  rw [hfun]
  have hraw := ((hasDerivAt_const (x := t) (c := (1 : ℝ))).add
    (((hasDerivAt_id t).pow 2).const_mul 6)).add ((hasDerivAt_id t).pow 4)
  apply hraw.congr_deriv
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

lemma hasDerivAt_juliaDefectQuartic_tanhHalf (y : ℝ) :
    HasDerivAt (fun z : ℝ => juliaDefectQuartic (Real.tanh (z / 2)))
      ((12 * Real.tanh (y / 2) + 4 * Real.tanh (y / 2) ^ (3 : ℕ)) *
        ((1 / Real.cosh (y / 2) ^ (2 : ℕ)) * (1 / 2 : ℝ))) y := by
  have hfun :
      (fun z : ℝ => juliaDefectQuartic (Real.tanh (z / 2))) =
        juliaDefectQuartic ∘ fun z : ℝ => Real.tanh (z / 2) := by
    funext z
    rfl
  rw [hfun]
  exact (hasDerivAt_juliaDefectQuartic (Real.tanh (y / 2))).comp y
    (hasDerivAt_tanhHalf y)

lemma hasDerivAt_juliaDefectSquareProfile
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt juliaDefectSquareProfile
      ((Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))))⁻¹ *
        juliaDefectVelocity (Real.tanh (y / 2))) y := by
  let t := Real.tanh (y / 2)
  let p := juliaDefectQuartic t
  let s := Real.sqrt p
  have ht0 : 0 < t := by
    dsimp only [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hp : 0 < p := juliaDefectQuartic_pos ht0
  have hs0 : s ≠ 0 := by dsimp only [s]; positivity
  have hpDeriv := hasDerivAt_juliaDefectQuartic_tanhHalf y
  have hsDeriv := hpDeriv.sqrt hp.ne'
  have hinv := hsDeriv.inv hs0
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have hD := hone.sub hinv
  have hfun : juliaDefectSquareProfile = fun z : ℝ =>
      1 - (Real.sqrt (juliaDefectQuartic (Real.tanh (z / 2))))⁻¹ := by
    funext z
    rfl
  rw [hfun]
  apply hD.congr_deriv
  dsimp only [t, p, s, juliaDefectVelocity]
  have htan := one_sub_tanh_sq (y / 2)
  have hsSq :
      Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) ^ (2 : ℕ) =
        juliaDefectQuartic (Real.tanh (y / 2)) := Real.sq_sqrt hp.le
  have hsCube :
      Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) ^ (3 : ℕ) =
        Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) *
          juliaDefectQuartic (Real.tanh (y / 2)) := by
    calc
      Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) ^ (3 : ℕ) =
          Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) *
            Real.sqrt (juliaDefectQuartic (Real.tanh (y / 2))) ^ (2 : ℕ) := by ring
      _ = _ := by rw [hsSq]
  field_simp [hs0, hp.ne']
  rw [htan, hsCube]
  field_simp [(Real.cosh_pos (y / 2)).ne']
  ring

/-- Pointwise derivative of the attenuation profile is strictly negative. -/
theorem juliaDefectAttenuationProfile_deriv_neg
    {y : ℝ} (hy : 0 < y) :
    deriv juliaDefectAttenuationProfile y < 0 := by
  let t := Real.tanh (y / 2)
  let p := juliaDefectQuartic t
  let s := Real.sqrt p
  let D := juliaDefectSquareProfile y
  let D' := s⁻¹ * juliaDefectVelocity t
  have ht0 : 0 < t := by
    dsimp only [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have ht1 : t < 1 := Real.tanh_lt_one _
  have hp : 0 < p := juliaDefectQuartic_pos ht0
  have hs0 : 0 < s := by dsimp only [s]; positivity
  have hyartanh : y = 2 * Real.artanh t := by
    dsimp only [t]
    rw [Real.artanh_tanh]
    ring
  have hcore := artanh_mul_juliaDefectVelocity_lt_sqrt_sub_one ht0 ht1
  have hElastic : y * D' < 2 * D := by
    change y * (s⁻¹ * juliaDefectVelocity t) <
      2 * juliaDefectSquareProfile y
    have hDform : juliaDefectSquareProfile y = 1 - s⁻¹ := by rfl
    rw [hDform, hyartanh]
    have hmul := mul_lt_mul_of_pos_left hcore (by positivity : 0 < 2 * s⁻¹)
    have hleft :
        2 * Real.artanh t * (s⁻¹ * juliaDefectVelocity t) =
          (2 * s⁻¹) * (Real.artanh t * juliaDefectVelocity t) := by ring
    have hright : 2 * (1 - s⁻¹) = (2 * s⁻¹) * (s - 1) := by
      field_simp [ne_of_gt hs0]
    rw [hleft, hright]
    exact hmul
  have hD := hasDerivAt_juliaDefectSquareProfile hy
  have hR : HasDerivAt juliaDefectAttenuationProfile
      ((4 / 3 : ℝ) * (D' * y ^ (2 : ℕ) - D * (2 * y)) / (y ^ (2 : ℕ)) ^ (2 : ℕ)) y := by
    have hD' : HasDerivAt juliaDefectSquareProfile D' y := by
      simpa only [D', s, p, t] using hD
    have hden : HasDerivAt (fun z : ℝ => z ^ (2 : ℕ)) (2 * y) y := by
      have hfun : (fun z : ℝ => z ^ (2 : ℕ)) = id ^ (2 : ℕ) := rfl
      rw [hfun]
      have hraw := (hasDerivAt_id y).pow 2
      exact hraw.congr_deriv (by simp)
    have hquot := (hD'.const_mul (4 / 3 : ℝ)).div hden
      (pow_ne_zero 2 hy.ne')
    have hfun : juliaDefectAttenuationProfile =
        fun z : ℝ => (4 / 3 : ℝ) * juliaDefectSquareProfile z / z ^ (2 : ℕ) := rfl
    rw [hfun]
    apply hquot.congr_deriv
    dsimp only [D, D']
    ring
  rw [hR.deriv]
  have hy2 : 0 < y ^ (2 : ℕ) := sq_pos_of_pos hy
  have hnum : D' * y ^ (2 : ℕ) - D * (2 * y) < 0 := by
    nlinarith [mul_pos hy (sub_pos.mpr hElastic)]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by norm_num) hnum) (sq_pos_of_pos hy2)

/-- **Julia defect attenuation law.**  The quadratically normalized defect is strictly decreasing
on the positive logarithmic aperture. -/
theorem strictAntiOn_juliaDefectAttenuationProfile :
    StrictAntiOn juliaDefectAttenuationProfile (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro y hy
    exact (hasDerivAt_juliaDefectSquareProfile hy |>.differentiableAt.const_mul
      (4 / 3 : ℝ) |>.div
        (differentiableAt_id.pow 2) (pow_ne_zero 2 hy.ne')).continuousAt.continuousWithinAt
  · intro y hy
    exact juliaDefectAttenuationProfile_deriv_neg (by simpa using hy)

end

end HTGeometry
