import GaloisForLFunctions.RHTower.Sieve.VinogradovLogDerivativeApproximation
import GaloisForLFunctions.RHTower.Sieve.VinogradovUpperHalfSaving

namespace RHTower.Sieve

noncomputable section

/-- Integer model of the Route-T logarithmic block geometry.  A height
base `B` gives Taylor centre scale `B^200` and bilinear half-length
`B^99`; hence the relative product deficit is exactly `B^-2`. -/
def routeTLogCentreExponent : ℕ := 200

def routeTLogHalfLengthExponent : ℕ := 99

/-- Uniform multiplier large enough to cover the 200th-power floor-root discretization:
if `B` is the largest even integer below `X^(1/200)`, then `X < (B+2)^200 ≤ 2^200 B^200`,
and every convolution centre is below `2^202 B^200`. -/
def routeTLogCentreMultiplier : ℕ := 2 ^ 202

theorem vinogradovUsefulCoordinate_degree_bounds
    {u : ℕ} (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    200 * u ≤ j.val + 1 ∧ j.val + 1 ≤ 240 * u := by
  exact hj

theorem vinogradovCoordinateSavingExponent_mul_le_degree
    {k : ℕ} (j : Fin k) :
    200 * vinogradovCoordinateSavingExponent j ≤ j.val + 1 := by
  unfold vinogradovCoordinateSavingExponent
  exact Nat.mul_div_le _ _

theorem vinogradovUsefulCoordinate_saving_five_le_six
    {u : ℕ} (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    5 * vinogradovCoordinateSavingExponent j ≤ 6 * u := by
  have he := vinogradovCoordinateSavingExponent_mul_le_degree j
  have hd := (vinogradovUsefulCoordinate_degree_bounds j hj).2
  omega

/-- Lower denominator-window exponent has enormous slack throughout the
Taylor-compatible band. -/
theorem routeTLog_lowerWindow_exponent_compatible
    {u : ℕ} (hu : 1 ≤ u)
    (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    198 * vinogradovCoordinateSavingExponent j + 2 ≤
      200 * ((j.val + 1) - 4 * u) := by
  have hd := vinogradovUsefulCoordinate_degree_bounds j hj
  have he := vinogradovCoordinateSavingExponent_mul_le_degree j
  omega

/-- Upper denominator transport remains compatible with the `B^-2`
Taylor-product deficit.  This is the inequality that fails for the old
degree range extending to `400u`. -/
theorem routeTLog_upperWindow_exponent_compatible
    {u : ℕ} (hu : 141 ≤ u)
    (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    200 * ((j.val + 1) - (4 * u - 4)) + 3 ≤
      198 * ((j.val + 1) - vinogradovCoordinateSavingExponent j) := by
  have hd := vinogradovUsefulCoordinate_degree_bounds j hj
  have he := vinogradovCoordinateSavingExponent_mul_le_degree j
  have he' := vinogradovUsefulCoordinate_saving_five_le_six j hj
  omega

/-- Exact reciprocal of a positive logarithmic Taylor magnitude. -/
theorem one_div_logTaylorMagnitude
    {k : ℕ} {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (j : Fin k) :
    1 / logTaylorMagnitude t x j =
      2 * Real.pi * (j.val + 1) * x ^ (j.val + 1) / t := by
  unfold logTaylorMagnitude
  field_simp

/-- Explicit base threshold absorbing every coefficient uniformly over
the Taylor-compatible degree band. -/
def routeTLogWindowThreshold (u : ℕ) : ℕ :=
  32 * (240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u)

theorem routeTLogWindowThreshold_ge_two {u B : ℕ}
    (hB : routeTLogWindowThreshold u ≤ B) : 2 ≤ B := by
  unfold routeTLogWindowThreshold at hB
  have hmultPos : 0 < routeTLogCentreMultiplier := by
    norm_num [routeTLogCentreMultiplier]
  have hfactorPos : 0 < (240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u) := by
    exact Nat.mul_pos (by omega) (pow_pos hmultPos _)
  have hfactor : 1 ≤ (240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u) := by
    omega
  calc
    2 ≤ 32 := by omega
    _ = 32 * 1 := by omega
    _ ≤ 32 * ((240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u)) :=
      Nat.mul_le_mul_left 32 hfactor
    _ = 32 * (240 * u + 1) * routeTLogCentreMultiplier ^ (240 * u) := by ring
    _ ≤ B := hB

private theorem cast_pow_pow (B a c : ℕ) :
    ((((B ^ a) ^ c : ℕ) : ℝ)) = (B : ℝ) ^ (a * c) := by
  push_cast
  rw [← pow_mul]

private theorem routeTLog_base_pow_add_half
    {B n : ℕ} (hB : 2 ≤ B) :
    (B : ℝ) ^ n + 1 / 2 ≤ (B : ℝ) ^ (n + 2) := by
  have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hn : (1 : ℝ) ≤ (B : ℝ) ^ n := one_le_pow₀ (by linarith)
  rw [pow_add, pow_two]
  nlinarith [sq_nonneg ((B : ℝ) - 2)]

/-- The lower reciprocal-size window follows from the upper edge of the
height shell and lower edge of the Taylor-centre block. -/
theorem routeTLog_lower_window_of_shell
    {u B : ℕ} {t x : ℝ} (hu : 1 ≤ u) (hB : 2 ≤ B)
    (ht : 0 < t)
    (htop : t ≤ ((((B ^ routeTLogCentreExponent) ^ (4 * u) : ℕ) : ℝ)))
    (hx : (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    ((((B ^ routeTLogHalfLengthExponent) ^
          (2 * vinogradovCoordinateSavingExponent j) : ℕ) : ℝ)) + 1 / 2 ≤
      1 / logTaylorMagnitude t x j := by
  let d := j.val + 1
  let e := vinogradovCoordinateSavingExponent j
  let A := 200 * (d - 4 * u)
  have hd : 200 * u ≤ d := (vinogradovUsefulCoordinate_degree_bounds j hj).1
  have hdu : 4 * u ≤ d := by omega
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ)) hx
  have hcentreTop :
      ((((B ^ routeTLogCentreExponent) ^ (4 * u) : ℕ) : ℝ)) =
        (B : ℝ) ^ (800 * u) := by
    simpa [routeTLogCentreExponent, mul_comm, mul_left_comm, mul_assoc] using
      cast_pow_pow B 200 (4 * u)
  have hxpow : (B : ℝ) ^ (200 * d) ≤ x ^ d := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        ((B ^ routeTLogCentreExponent : ℕ) : ℝ)) hx d
    calc
      (B : ℝ) ^ (200 * d) = ((B : ℝ) ^ 200) ^ d := by rw [pow_mul]
      _ = (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) ^ d := by
        simp [routeTLogCentreExponent]
      _ ≤ x ^ d := h
  have hAt : (B : ℝ) ^ A * t ≤ x ^ d := by
    calc
      (B : ℝ) ^ A * t ≤
          (B : ℝ) ^ A * (B : ℝ) ^ (800 * u) := by
        rw [← hcentreTop]
        exact mul_le_mul_of_nonneg_left htop (by positivity)
      _ = (B : ℝ) ^ (200 * d) := by
        rw [← pow_add]
        congr 1
        unfold A
        omega
      _ ≤ x ^ d := hxpow
  have hconstant : (1 : ℝ) ≤ 2 * Real.pi * d := by
    have hpi := Real.pi_pos
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.two_le_pi]
    nlinarith
  have hratio : (B : ℝ) ^ A ≤
      2 * Real.pi * d * x ^ d / t := by
    rw [le_div_iff₀ ht]
    calc
      (B : ℝ) ^ A * t ≤ x ^ d := hAt
      _ ≤ 2 * Real.pi * d * x ^ d := by
        exact le_mul_of_one_le_left (by positivity) hconstant
  have hexponent := routeTLog_lowerWindow_exponent_compatible hu j hj
  have hwindow :
      (B : ℝ) ^ (198 * e) + 1 / 2 ≤ (B : ℝ) ^ A := by
    calc
      _ ≤ (B : ℝ) ^ (198 * e + 2) := routeTLog_base_pow_add_half hB
      _ ≤ (B : ℝ) ^ A :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ B by omega))
          (by simpa [d, e, A] using hexponent)
  rw [one_div_logTaylorMagnitude ht hx0 j]
  have hfinal := hwindow.trans hratio
  dsimp [d, e] at hfinal ⊢
  rw [show (((B ^ routeTLogHalfLengthExponent) ^
      (2 * vinogradovCoordinateSavingExponent j) : ℕ) : ℝ) =
      (B : ℝ) ^ (198 * vinogradovCoordinateSavingExponent j) by
    rw [show routeTLogHalfLengthExponent = 99 by rfl,
      cast_pow_pow]
    congr 1
    omega]
  simpa [Nat.cast_add, Nat.cast_one] using hfinal

theorem routeTLog_coefficient_le_base_cube
    {u B : ℕ} (hB : routeTLogWindowThreshold u ≤ B)
    (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    4 * Real.pi * (j.val + 1) *
        (routeTLogCentreMultiplier : ℝ) ^ (j.val + 1) + 1 ≤
      (B : ℝ) ^ 3 := by
  let d := j.val + 1
  have hd : d ≤ 240 * u := (vinogradovUsefulCoordinate_degree_bounds j hj).2
  have hmult1 : 1 ≤ routeTLogCentreMultiplier := by
    norm_num [routeTLogCentreMultiplier]
  have hpowNat : routeTLogCentreMultiplier ^ d ≤
      routeTLogCentreMultiplier ^ (240 * u) :=
    pow_le_pow_right₀ hmult1 hd
  have hpow : (routeTLogCentreMultiplier : ℝ) ^ d ≤
      (routeTLogCentreMultiplier : ℝ) ^ (240 * u) := by
    exact_mod_cast hpowNat
  have hdReal : (d : ℝ) ≤ ((240 * u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show d ≤ 240 * u + 1 by omega)
  have hpi : 4 * Real.pi ≤ 16 := by
    nlinarith [Real.pi_le_four]
  have hleft :
      4 * Real.pi * (d : ℝ) * (routeTLogCentreMultiplier : ℝ) ^ d ≤
        16 * ((240 * u + 1 : ℕ) : ℝ) *
          (routeTLogCentreMultiplier : ℝ) ^ (240 * u) := by
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hu0 : (0 : ℝ) ≤ ((240 * u + 1 : ℕ) : ℝ) := by positivity
    have hmul : (d : ℝ) * (routeTLogCentreMultiplier : ℝ) ^ d ≤
        ((240 * u + 1 : ℕ) : ℝ) *
          (routeTLogCentreMultiplier : ℝ) ^ (240 * u) :=
      mul_le_mul hdReal hpow (by positivity) hu0
    calc
      _ ≤ 16 * ((d : ℝ) * (routeTLogCentreMultiplier : ℝ) ^ d) := by
        nlinarith [mul_nonneg hd0
          (by positivity : (0 : ℝ) ≤ (routeTLogCentreMultiplier : ℝ) ^ d)]
      _ ≤ 16 * (((240 * u + 1 : ℕ) : ℝ) *
          (routeTLogCentreMultiplier : ℝ) ^ (240 * u)) := by
        gcongr
      _ = _ := by ring
  have hfactorPos : (0 : ℝ) <
      ((240 * u + 1 : ℕ) : ℝ) *
        (routeTLogCentreMultiplier : ℝ) ^ (240 * u) := by positivity
  have hfactor : (1 : ℝ) ≤
      ((240 * u + 1 : ℕ) : ℝ) *
        (routeTLogCentreMultiplier : ℝ) ^ (240 * u) := by
    have h1 : (1 : ℝ) ≤ ((240 * u + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 240 * u + 1 by omega)
    have h2 : (1 : ℝ) ≤ (routeTLogCentreMultiplier : ℝ) ^ (240 * u) :=
      one_le_pow₀ (by exact_mod_cast hmult1)
    nlinarith
  have hthresholdReal :
      32 * ((240 * u + 1 : ℕ) : ℝ) *
        (routeTLogCentreMultiplier : ℝ) ^ (240 * u) ≤ B := by
    have hc : (routeTLogWindowThreshold u : ℝ) ≤ B := by exact_mod_cast hB
    simpa [routeTLogWindowThreshold, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_pow] using hc
  have hcoefficient :
      4 * Real.pi * (d : ℝ) * (routeTLogCentreMultiplier : ℝ) ^ d + 1 ≤
        (B : ℝ) := by
    calc
      _ ≤ 16 * ((240 * u + 1 : ℕ) : ℝ) *
          (routeTLogCentreMultiplier : ℝ) ^ (240 * u) + 1 := by
        linarith
      _ ≤ 32 * ((240 * u + 1 : ℕ) : ℝ) *
          (routeTLogCentreMultiplier : ℝ) ^ (240 * u) := by
        nlinarith
      _ ≤ B := hthresholdReal
  have hBtwo : 2 ≤ B := routeTLogWindowThreshold_ge_two hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hBcube : (B : ℝ) ≤ (B : ℝ) ^ 3 := by
    simpa using (pow_le_pow_right₀ hB1 (show 1 ≤ 3 by omega))
  simpa [d, Nat.cast_add, Nat.cast_one] using hcoefficient.trans hBcube

/-- The lower edge of the height shell and upper edge of the centre
block imply the upper reciprocal-size window. -/
theorem routeTLog_upper_window_of_shell
    {u B : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hB : routeTLogWindowThreshold u ≤ B)
    (ht : 0 < t)
    (hbottom : ((((B ^ routeTLogCentreExponent) ^ (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (hx0 : 0 < x)
    (hx : x ≤ routeTLogCentreMultiplier *
      (((B ^ routeTLogCentreExponent : ℕ) : ℝ)))
    (j : Fin (vinogradovRouteTOrder (4 * u)))
    (hj : vinogradovUsefulCoordinate u j) :
    2 / logTaylorMagnitude t x j + 1 ≤
      ((((B ^ routeTLogHalfLengthExponent) ^
        (2 * ((j.val + 1) - vinogradovCoordinateSavingExponent j)) : ℕ) : ℝ)) := by
  let d := j.val + 1
  let e := vinogradovCoordinateSavingExponent j
  let A := 200 * (d - (4 * u - 4))
  have hB2 : 2 ≤ B := routeTLogWindowThreshold_ge_two hB
  have hd : 200 * u ≤ d := (vinogradovUsefulCoordinate_degree_bounds j hj).1
  have hdu : 4 * u - 4 ≤ d := by omega
  have hbottomPow :
      ((((B ^ routeTLogCentreExponent) ^ (4 * u - 4) : ℕ) : ℝ)) =
        (B : ℝ) ^ (200 * (4 * u - 4)) := by
    simpa [routeTLogCentreExponent, mul_comm, mul_left_comm, mul_assoc] using
      cast_pow_pow B 200 (4 * u - 4)
  have hxpow : x ^ d ≤ (routeTLogCentreMultiplier : ℝ) ^ d *
      (B : ℝ) ^ (200 * d) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x) hx d
    calc
      x ^ d ≤ (routeTLogCentreMultiplier *
          (((B ^ routeTLogCentreExponent : ℕ) : ℝ))) ^ d := h
      _ = (routeTLogCentreMultiplier : ℝ) ^ d * (B : ℝ) ^ (200 * d) := by
        rw [mul_pow]
        congr 1
        simp [routeTLogCentreExponent, pow_mul]
  have hnum :
      4 * Real.pi * d * x ^ d ≤
        (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ (200 * d) := by
    calc
      _ ≤ 4 * Real.pi * d * ((routeTLogCentreMultiplier : ℝ) ^ d *
          (B : ℝ) ^ (200 * d)) := by
        gcongr
      _ = _ := by ring
  have hproduct :
      (B : ℝ) ^ A * (B : ℝ) ^ (200 * (4 * u - 4)) =
        (B : ℝ) ^ (200 * d) := by
    rw [← pow_add]
    congr 1
    unfold A
    omega
  have hnumShell :
      4 * Real.pi * d * x ^ d ≤
        (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ A * t := by
    calc
      _ ≤ (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ (200 * d) := hnum
      _ = (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          ((B : ℝ) ^ A * (B : ℝ) ^ (200 * (4 * u - 4))) := by rw [hproduct]
      _ ≤ (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ A * t := by
        rw [hbottomPow] at hbottom
        calc
          _ = ((4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
              (B : ℝ) ^ A) *
              (B : ℝ) ^ (200 * (4 * u - 4)) := by ring
          _ ≤ ((4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
              (B : ℝ) ^ A) * t :=
            mul_le_mul_of_nonneg_left hbottom (by positivity)
          _ = _ := by ring
  have hdiv :
      4 * Real.pi * d * x ^ d / t ≤
        (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ A := by
    rw [div_le_iff₀ ht]
    simpa [mul_assoc] using hnumShell
  have hcoefficient := routeTLog_coefficient_le_base_cube hB j hj
  have hA1 : (1 : ℝ) ≤ (B : ℝ) ^ A :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ B by omega))
  have habsorbed :
      (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ A + 1 ≤
        (B : ℝ) ^ (A + 3) := by
    have hcoeff' : 4 * Real.pi * (d : ℝ) *
        (routeTLogCentreMultiplier : ℝ) ^ d + 1 ≤
        (B : ℝ) ^ 3 := by
      simpa [d, Nat.cast_add, Nat.cast_one] using hcoefficient
    calc
      _ ≤ (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d + 1) *
          (B : ℝ) ^ A := by
        calc
          _ ≤ (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
              (B : ℝ) ^ A +
              (B : ℝ) ^ A := by
                simpa [add_comm] using add_le_add_left hA1
                  ((4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
                    (B : ℝ) ^ A)
          _ = _ := by ring
      _ ≤ (B : ℝ) ^ 3 * (B : ℝ) ^ A := by gcongr
      _ = (B : ℝ) ^ (A + 3) := by rw [pow_add]; ring
  have hexponent := routeTLog_upperWindow_exponent_compatible hu j hj
  have hpower : (B : ℝ) ^ (A + 3) ≤ (B : ℝ) ^ (198 * (d - e)) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ B by omega))
      (by simpa [A, d, e] using hexponent)
  have hreciprocal :
      2 / logTaylorMagnitude t x j = 4 * Real.pi * d * x ^ d / t := by
    rw [show 2 / logTaylorMagnitude t x j =
      2 * (1 / logTaylorMagnitude t x j) by ring,
      one_div_logTaylorMagnitude ht hx0 j]
    simp only [d, Nat.cast_add, Nat.cast_one]
    ring
  rw [hreciprocal]
  have hdivadd : 4 * Real.pi * d * x ^ d / t + 1 ≤
      (4 * Real.pi * d * (routeTLogCentreMultiplier : ℝ) ^ d) *
          (B : ℝ) ^ A + 1 :=
    by simpa [add_comm] using add_le_add_right hdiv 1
  have hfinal := hdivadd.trans (habsorbed.trans hpower)
  dsimp [d, e] at hfinal ⊢
  rw [show (((B ^ routeTLogHalfLengthExponent) ^
      (2 * ((j.val + 1) - vinogradovCoordinateSavingExponent j)) : ℕ) : ℝ) =
      (B : ℝ) ^ (198 * ((j.val + 1) - vinogradovCoordinateSavingExponent j)) by
    rw [show routeTLogHalfLengthExponent = 99 by rfl, cast_pow_pow]
    congr 1
    omega]
  exact hfinal

def routeTLogBaseThreshold (u : ℕ) : ℕ :=
  max (routeTLogWindowThreshold u)
    (max
      (160 * vinogradovRouteTMoment (4 * u) ^ 2 *
        vinogradovRouteTOrder (4 * u))
      (vinogradovRouteTMomentConstant u))

theorem routeTLogBaseThreshold_ge_two {u B : ℕ}
    (hB : routeTLogBaseThreshold u ≤ B) : 2 ≤ B := by
  apply routeTLogWindowThreshold_ge_two
  exact (le_max_left _ _).trans hB

/-- Complete rational-approximant producer directly from one Route-T
height shell and centre block.  No reciprocal-window assumptions remain. -/
theorem exists_routeT_logTaylor_approximants_of_shell
    {u B : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hB : routeTLogBaseThreshold u ≤ B)
    (ht : 0 < t)
    (hbottom : ((((B ^ routeTLogCentreExponent) ^ (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ ((((B ^ routeTLogCentreExponent) ^ (4 * u) : ℕ) : ℝ)))
    (hxlower : (((B ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      (((B ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ∃ a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ,
      (∀ j, vinogradovUsefulCoordinate u j → 0 < q j) ∧
      (∀ j, vinogradovUsefulCoordinate u j → Nat.Coprime (a j) (q j)) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        |logTaylorMagnitude t x j - (a j : ℝ) / (q j : ℝ)| ≤
          1 / (q j : ℝ) ^ 2) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        (B ^ routeTLogHalfLengthExponent) ^
          (2 * vinogradovCoordinateSavingExponent j) ≤ q j) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        q j * (B ^ routeTLogHalfLengthExponent) ^
            (2 * vinogradovCoordinateSavingExponent j) ≤
          ((B ^ routeTLogHalfLengthExponent) ^ (j.val + 1)) ^ 2) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
            (1 + Real.log ((q j : ℝ) + 1)) ≤
          ((B ^ routeTLogHalfLengthExponent : ℕ) : ℝ) ^
            vinogradovCoordinateSavingExponent j) := by
  have hBwindow : routeTLogWindowThreshold u ≤ B :=
    (le_max_left _ _).trans hB
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two hB
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) <
      ((B ^ routeTLogCentreExponent : ℕ) : ℝ)) hxlower
  have hmomentBase :
      160 * vinogradovRouteTMoment (4 * u) ^ 2 *
          vinogradovRouteTOrder (4 * u) ≤ B := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hB)
  have hBpow : B ≤ B ^ routeTLogHalfLengthExponent := by
    have hB1 : 1 ≤ B := by omega
    simpa [routeTLogHalfLengthExponent] using
      (pow_le_pow_right₀ hB1 (show 1 ≤ 99 by omega))
  have hmoment :
      160 * vinogradovRouteTMoment (4 * u) ^ 2 *
          vinogradovRouteTOrder (4 * u) ≤
        B ^ routeTLogHalfLengthExponent := hmomentBase.trans hBpow
  exact exists_routeT_logTaylor_approximants hu ht hx0 hmoment
    (fun j hj => routeTLog_lower_window_of_shell (by omega) hB2 ht htop
      hxlower j hj)
    (fun j hj => routeTLog_upper_window_of_shell hu hBwindow ht hbottom
      hx0 hxupper j hj)

def routeTLogHalfBlock (C : ℕ) : ℕ :=
  C * (2 * C) ^ 98

theorem two_mul_routeTLogHalfBlock (C : ℕ) :
    2 * routeTLogHalfBlock C = (2 * C) ^ routeTLogHalfLengthExponent := by
  unfold routeTLogHalfBlock routeTLogHalfLengthExponent
  rw [show 99 = 98 + 1 by omega, pow_succ]
  ring

/-- Source-shaped logarithmic bilinear block estimate.  All coefficients
of `f(n-lm)` for `f(x)=(t/2π)log x` have the same negative sign, so the
sign-reversed approximant theorem applies without signed numerators. -/
theorem norm_routeTLogUpperHalfBilinearSum_le_rpow_of_shell
    {u C : ℕ} {t x : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖vinogradovUpperHalfBilinearSum (routeTLogHalfBlock C)
        (fun j : Fin (vinogradovRouteTOrder (4 * u)) =>
          -logTaylorMagnitude t x j)‖ ≤
      ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u) := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa [B] using hC)
  have hBpow : B ≤ B ^ routeTLogHalfLengthExponent := by
    simpa [routeTLogHalfLengthExponent] using
      (pow_le_pow_right₀ (show 1 ≤ B by omega) (show 1 ≤ 99 by omega))
  have hCB : routeTLogBaseThreshold u ≤ B := by
    simpa only [B] using hC
  have hmomentBase : vinogradovRouteTMomentConstant u ≤ B := by
    exact (le_max_right
      (160 * vinogradovRouteTMoment (4 * u) ^ 2 *
        vinogradovRouteTOrder (4 * u))
      (vinogradovRouteTMomentConstant u)).trans
      ((le_max_right (routeTLogWindowThreshold u)
        (max
          (160 * vinogradovRouteTMoment (4 * u) ^ 2 *
            vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentConstant u))).trans hCB)
  have hmoment : vinogradovRouteTMomentConstant u ≤ 2 * Q := by
    rw [hP]
    exact hmomentBase.trans hBpow
  obtain ⟨a, q, hq, hcop, happrox, hRq, hqR, habsorb⟩ :=
    exists_routeT_logTaylor_approximants_of_shell hu hCB
      ht (by simpa only [B] using hbottom) (by simpa only [B] using htop)
      (by simpa only [B] using hxlower) (by simpa only [B] using hxupper)
  have hsaving := norm_vinogradovUpperHalfBilinearSum_le_rpow_of_negApprox
    hu hmoment
    (fun j : Fin (vinogradovRouteTOrder (4 * u)) =>
      -logTaylorMagnitude t x j)
    a q hq hcop (by
      intro j hj
      simpa using happrox j hj)
    (by
      intro j hj
      rw [hP]
      exact hRq j hj)
    (by
      intro j hj
      rw [hP]
      exact hqR j hj)
    (by
      intro j hj
      rw [hP]
      exact habsorb j hj)
  rw [hP] at hsaving
  simpa only [Q, B] using hsaving

def routeTLogTwistedTaylorCoefficient
    {k : ℕ} (t x β : ℝ) (j : Fin k) : ℝ :=
  -logTaylorMagnitude t x j + if j.val = 0 then β else 0

/-- Uniform linear-twist form needed by the MV24.10 receiver.  The
twist affects only degree one; every useful coordinate has degree at
least `200u`, so the Diophantine proof is unchanged. -/
theorem norm_routeTLogTwistedUpperHalfBilinearSum_le_rpow_of_shell
    {u C : ℕ} {t x β : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 4) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hxlower : ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ)) ≤ x)
    (hxupper : x ≤ routeTLogCentreMultiplier *
      ((((2 * C) ^ routeTLogCentreExponent : ℕ) : ℝ))) :
    ‖vinogradovUpperHalfBilinearSum (routeTLogHalfBlock C)
        (routeTLogTwistedTaylorCoefficient
          (k := vinogradovRouteTOrder (4 * u)) t x β)‖ ≤
      ((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u) := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa [B, Q] using two_mul_routeTLogHalfBlock C
  have hBpow : B ≤ B ^ routeTLogHalfLengthExponent := by
    simpa [routeTLogHalfLengthExponent] using
      (pow_le_pow_right₀
        (show 1 ≤ B by
          have := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
          omega)
        (show 1 ≤ 99 by omega))
  have hCB : routeTLogBaseThreshold u ≤ B := by simpa only [B] using hC
  have hmomentBase : vinogradovRouteTMomentConstant u ≤ B := by
    exact (le_max_right
      (160 * vinogradovRouteTMoment (4 * u) ^ 2 *
        vinogradovRouteTOrder (4 * u))
      (vinogradovRouteTMomentConstant u)).trans
      ((le_max_right (routeTLogWindowThreshold u)
        (max
          (160 * vinogradovRouteTMoment (4 * u) ^ 2 *
            vinogradovRouteTOrder (4 * u))
          (vinogradovRouteTMomentConstant u))).trans hCB)
  have hmoment : vinogradovRouteTMomentConstant u ≤ 2 * Q := by
    rw [hP]
    exact hmomentBase.trans hBpow
  obtain ⟨a, q, hq, hcop, happrox, hRq, hqR, habsorb⟩ :=
    exists_routeT_logTaylor_approximants_of_shell hu hCB ht
      (by simpa only [B] using hbottom) (by simpa only [B] using htop)
      (by simpa only [B] using hxlower) (by simpa only [B] using hxupper)
  have hsaving := norm_vinogradovUpperHalfBilinearSum_le_rpow_of_negApprox
    hu hmoment (routeTLogTwistedTaylorCoefficient
      (k := vinogradovRouteTOrder (4 * u)) t x β)
    a q hq hcop (by
      intro j hj
      have hj0 : j.val ≠ 0 := by
        unfold vinogradovUsefulCoordinate at hj
        omega
      simpa [routeTLogTwistedTaylorCoefficient, hj0] using happrox j hj)
    (by
      intro j hj
      rw [hP]
      exact hRq j hj)
    (by
      intro j hj
      rw [hP]
      exact hqR j hj)
    (by
      intro j hj
      rw [hP]
      exact habsorb j hj)
  rw [hP] at hsaving
  simpa only [Q, B] using hsaving

end

end RHTower.Sieve
