import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection
import GaloisForLFunctions.RHTower.XiMassFaithfulTransfer

/-!
# Adaptive-aperture faithfulness wall for the Xi mass carrier

One possible escape from the Route N timelike/glancing obstruction is to let the mass aperture grow
with observation time.  A larger aperture supplies stronger source damping.  This file proves the
exact obstruction on the divisor side.

The conserved mass charge gives

`|Im beta_a| * Re beta_a = Re alpha * |Im alpha|`.

Consequently the boost exponent at time `u` is not controlled independently by the aperture:

`u * |Im beta_a| = (u / Re beta_a) * Re alpha * |Im alpha|`.

Thus the universal adaptive parameter is `u / Re beta_a`.  Since `Re beta_a >= a`, any aperture
schedule with `a(u) >= kappa * u` makes the boost exponent, and its exponential amplification,
eventually bounded for every fixed zero.  Linear-scale source damping therefore erases the very
off-line signal the mass carrier was introduced to detect.  Only the sublinear/glancing regime can
remain faithful.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Absolute form of mass-charge conservation.  No information is lost: displacement contraction
is exactly reciprocal to the raised spectral height. -/
theorem xiMassFamily_absIm_mul_height_eq_charge {a : ℝ} (ha : 1 / 2 ≤ a)
    (q : XiZeroCopy) :
    |((xiMassFamily ha).pt q).im| * ((xiMassFamily ha).pt q).re =
      (xiPoissonPoint q).re * |(xiPoissonPoint q).im| := by
  have hdisp := xiPoissonAbstract.csqrtIm_massArg_mul_csqrtRe ha q
  have hkey :
      ((xiMassFamily ha).pt q).im * ((xiMassFamily ha).pt q).re =
        (xiPoissonPoint q).re * (xiPoissonPoint q).im := by
    simpa only [xiMassFamily_pt_eq_mass_pt, xiPoissonAbstract_pt,
      HTGeometry.AbstractSpectralFamily.mass, HTGeometry.csqrt_im,
      HTGeometry.csqrt_re] using hdisp
  have hheight0 : 0 ≤ ((xiMassFamily ha).pt q).re :=
    (xiMassFamily ha).re_nonneg q
  have hR : 0 ≤ (xiPoissonPoint q).re :=
    (three_lt_xiPoissonPoint_re q).le.trans' (by norm_num)
  rw [← abs_of_nonneg hheight0, ← abs_mul, hkey, abs_mul, abs_of_nonneg hR]

/-- The aperture alone already gives the reciprocal displacement bound. -/
theorem xiMassFamily_aperture_mul_absIm_le_charge {a : ℝ} (ha : 1 / 2 ≤ a)
    (q : XiZeroCopy) :
    a * |((xiMassFamily ha).pt q).im| ≤
      (xiPoissonPoint q).re * |(xiPoissonPoint q).im| := by
  have hheight : a ≤ ((xiMassFamily ha).pt q).re := (xiMassFamily ha).base_le q
  calc
    a * |((xiMassFamily ha).pt q).im| =
        |((xiMassFamily ha).pt q).im| * a := by ring
    _ ≤ |((xiMassFamily ha).pt q).im| * ((xiMassFamily ha).pt q).re :=
      mul_le_mul_of_nonneg_left hheight (abs_nonneg _)
    _ = (xiPoissonPoint q).re * |(xiPoissonPoint q).im| :=
      xiMassFamily_absIm_mul_height_eq_charge ha q

/-- **C52 exact adaptive invariant.**  Time amplification and mass contraction couple through the
single dimensionless ratio `u / Re beta_a`. -/
theorem xiMassFamily_time_mul_absIm_eq_heightRatio_mul_charge {a u : ℝ}
    (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    u * |((xiMassFamily ha).pt q).im| =
      (u / ((xiMassFamily ha).pt q).re) *
        ((xiPoissonPoint q).re * |(xiPoissonPoint q).im|) := by
  have hheight : 0 < ((xiMassFamily ha).pt q).re := (xiMassFamily ha).re_pos q
  have hcharge := xiMassFamily_absIm_mul_height_eq_charge ha q
  calc
    u * |((xiMassFamily ha).pt q).im| =
        (u / ((xiMassFamily ha).pt q).re) *
          (|((xiMassFamily ha).pt q).im| * ((xiMassFamily ha).pt q).re) := by
      field_simp [ne_of_gt hheight]
    _ = (u / ((xiMassFamily ha).pt q).re) *
          ((xiPoissonPoint q).re * |(xiPoissonPoint q).im|) := by rw [hcharge]

/-- A linear lower bound on aperture imposes a time-independent bound on the boost exponent. -/
theorem xiMassFamily_linearAperture_boost_le {a u kappa : ℝ}
    (ha : 1 / 2 ≤ a) (hkappa : 0 < kappa) (hlinear : kappa * u ≤ a)
    (q : XiZeroCopy) :
    u * |((xiMassFamily ha).pt q).im| ≤
      ((xiPoissonPoint q).re * |(xiPoissonPoint q).im|) / kappa := by
  have haperture := xiMassFamily_aperture_mul_absIm_le_charge ha q
  have hmul :
      kappa * (u * |((xiMassFamily ha).pt q).im|) ≤
        (xiPoissonPoint q).re * |(xiPoissonPoint q).im| := by
    calc
      kappa * (u * |((xiMassFamily ha).pt q).im|) =
          (kappa * u) * |((xiMassFamily ha).pt q).im| := by ring
      _ ≤ a * |((xiMassFamily ha).pt q).im| :=
        mul_le_mul_of_nonneg_right hlinear (abs_nonneg _)
      _ ≤ (xiPoissonPoint q).re * |(xiPoissonPoint q).im| := haperture
  exact (le_div_iff₀ hkappa).2 (by simpa [mul_comm, mul_left_comm] using hmul)

/-- Exponential amplification is likewise uniformly capped at linear aperture scale. -/
theorem xiMassFamily_linearAperture_expBoost_le {a u kappa : ℝ}
    (ha : 1 / 2 ≤ a) (hkappa : 0 < kappa) (hlinear : kappa * u ≤ a)
    (q : XiZeroCopy) :
    Real.exp (u * |((xiMassFamily ha).pt q).im|) ≤
      Real.exp (((xiPoissonPoint q).re * |(xiPoissonPoint q).im|) / kappa) :=
  Real.exp_le_exp.mpr (xiMassFamily_linearAperture_boost_le ha hkappa hlinear q)

/-- **Linear adaptive-aperture no-go.**  Along every eventually linear aperture schedule, the boost
exponent of each fixed divisor point cannot tend to infinity. -/
theorem xiMassFamily_linearSchedule_boost_not_tendsto_atTop
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) {kappa : ℝ} (hkappa : 0 < kappa)
    (hlinear : ∀ᶠ n : ℕ in atTop, kappa * (n : ℝ) ≤ a n) (q : XiZeroCopy) :
    ¬ Tendsto
      (fun n : ℕ => (n : ℝ) * |((xiMassFamily (ha n)).pt q).im|)
      atTop atTop := by
  let B : ℝ := (xiPoissonPoint q).re * |(xiPoissonPoint q).im| / kappa
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * |((xiMassFamily (ha n)).pt q).im| ≤ B := by
    filter_upwards [hlinear] with n hn
    exact xiMassFamily_linearAperture_boost_le (ha n) hkappa hn q
  intro htend
  have hlower : ∀ᶠ n : ℕ in atTop,
      B + 1 ≤ (n : ℝ) * |((xiMassFamily (ha n)).pt q).im| :=
    htend (eventually_ge_atTop (B + 1))
  have hfalse : ∀ᶠ _ : ℕ in atTop, False := by
    filter_upwards [hbound, hlower] with n hnB hnL
    linarith
  exact (Filter.Eventually.exists hfalse).elim fun _ h => h

/-- The actual exponential off-line detector cannot diverge under an eventually linear aperture
schedule. -/
theorem xiMassFamily_linearSchedule_expBoost_not_tendsto_atTop
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) {kappa : ℝ} (hkappa : 0 < kappa)
    (hlinear : ∀ᶠ n : ℕ in atTop, kappa * (n : ℝ) ≤ a n) (q : XiZeroCopy) :
    ¬ Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * |((xiMassFamily (ha n)).pt q).im|))
      atTop atTop := by
  let B : ℝ := Real.exp
    ((xiPoissonPoint q).re * |(xiPoissonPoint q).im| / kappa)
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) * |((xiMassFamily (ha n)).pt q).im|) ≤ B := by
    filter_upwards [hlinear] with n hn
    exact xiMassFamily_linearAperture_expBoost_le (ha n) hkappa hn q
  intro htend
  have hlower : ∀ᶠ n : ℕ in atTop,
      B + 1 ≤ Real.exp ((n : ℝ) * |((xiMassFamily (ha n)).pt q).im|) :=
    htend (eventually_ge_atTop (B + 1))
  have hfalse : ∀ᶠ _ : ℕ in atTop, False := by
    filter_upwards [hbound, hlower] with n hnB hnL
    linarith
  exact (Filter.Eventually.exists hfalse).elim fun _ h => h

/-- Original mass charge is strictly positive at every off-line divisor copy. -/
theorem xiMassFamily_charge_pos_of_im_ne_zero {q : XiZeroCopy}
    (hq : (xiPoissonPoint q).im ≠ 0) :
    0 < (xiPoissonPoint q).re * |(xiPoissonPoint q).im| :=
  mul_pos (by linarith [three_lt_xiPoissonPoint_re q]) (abs_pos.mpr hq)

/-- At an off-line divisor copy, divergent boost is equivalent to divergence of the exact
time-to-raised-height ratio.  This is the converse half of C52's adaptive invariant. -/
theorem xiMassFamily_boost_tendsto_iff_heightRatio_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hq : (xiPoissonPoint q).im ≠ 0) :
    Tendsto
        (fun n : ℕ => (n : ℝ) * |((xiMassFamily (ha n)).pt q).im|)
        atTop atTop ↔
      Tendsto
        (fun n : ℕ => (n : ℝ) / ((xiMassFamily (ha n)).pt q).re)
        atTop atTop := by
  let C : ℝ := (xiPoissonPoint q).re * |(xiPoissonPoint q).im|
  have hC : 0 < C := xiMassFamily_charge_pos_of_im_ne_zero hq
  have heq : ∀ n : ℕ,
      (n : ℝ) * |((xiMassFamily (ha n)).pt q).im| =
        ((n : ℝ) / ((xiMassFamily (ha n)).pt q).re) * C := by
    intro n
    exact xiMassFamily_time_mul_absIm_eq_heightRatio_mul_charge (ha n) q
  constructor
  · intro hboost
    have hdiv := hboost.atTop_div_const hC
    exact hdiv.congr' (Eventually.of_forall fun n => by
      rw [heq n]
      field_simp [ne_of_gt hC])
  · intro hratio
    exact (hratio.atTop_mul_const hC).congr'
      (Eventually.of_forall fun n => (heq n).symm)

/-- **Necessary scale law for faithful adaptation.**  If one off-line boost remains detectable by
diverging along an aperture schedule, then `n / a(n)` must diverge.  In particular no linear or
superlinear schedule can be faithful. -/
theorem xiMassFamily_boost_tendsto_implies_apertureRatio_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hq : (xiPoissonPoint q).im ≠ 0)
    (hboost : Tendsto
      (fun n : ℕ => (n : ℝ) * |((xiMassFamily (ha n)).pt q).im|)
      atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop atTop := by
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) / ((xiMassFamily (ha n)).pt q).re)
      atTop atTop :=
    (xiMassFamily_boost_tendsto_iff_heightRatio_tendsto a ha q hq).mp hboost
  have hle : ∀ n : ℕ,
      (n : ℝ) / ((xiMassFamily (ha n)).pt q).re ≤ (n : ℝ) / a n := by
    intro n
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n)
      (by linarith [ha n]) ((xiMassFamily (ha n)).base_le q)
  rw [tendsto_atTop] at hratio ⊢
  intro b
  filter_upwards [hratio b] with n hn
  exact hn.trans (hle n)

end

end RHTower
