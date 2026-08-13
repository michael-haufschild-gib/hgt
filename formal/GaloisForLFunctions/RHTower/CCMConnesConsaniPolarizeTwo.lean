import GaloisForLFunctions.RHTower.CCMConnesConsaniW02Correction

/-!
# The literal CCM `polarize2` real Fourier table

This file formalizes Lemma `polarize2` of Connes--Consani (2021) from its
zero-extended centered real Fourier functions.  Every entry is an equality for
the source correlation integral, not a separately postulated matrix kernel.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- A positive integer Fourier index, matching the source table's `n>0`. -/
abbrev CCMPositiveFourierIndex := {n : ℕ // 0 < n}

/-- Paper basis vector `ξ₀`, extended by zero outside `[-L/2,L/2]`. -/
def ccmCenteredConstantMode (L : CCMPositiveAperture) (x : ℝ) : ℝ :=
  (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
    (fun _ => (Real.sqrt (L : ℝ))⁻¹) x

/-- `ξ₀` bundled with its exact centered support. -/
def ccmCenteredConstantWindow (L : CCMPositiveAperture) :
    CCMCenteredWindowFunction L where
  toFun := ccmCenteredConstantMode L
  zero_outside x hx := by
    simp [ccmCenteredConstantMode, Set.indicator_of_notMem hx]

/-- `ξₙ`, `n>0`, bundled with its exact centered support. -/
def ccmCenteredCosineWindow (L : CCMPositiveAperture) (n : ℕ) :
    CCMCenteredWindowFunction L where
  toFun := ccmCenteredCosineMode L n
  zero_outside x hx := by
    simp [ccmCenteredCosineMode, Set.indicator_of_notMem hx]

/-- `ξ₋ₙ`, `n>0`, bundled with its exact centered support. -/
def ccmCenteredNegativeSineWindow (L : CCMPositiveAperture) (n : ℕ) :
    CCMCenteredWindowFunction L where
  toFun := ccmCenteredNegativeSineMode L n
  zero_outside x hx := by
    simp [ccmCenteredNegativeSineMode, Set.indicator_of_notMem hx]

private theorem centered_overlap_memberships
    (L : CCMPositiveAperture) (t : CCMApertureLag L)
    {x : ℝ} (hx : x ∈ Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)) :
    x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) ∧
      x - (t : ℝ) ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
  constructor
  · constructor <;> linarith [hx.1, hx.2, t.property.1]
  · constructor <;> linarith [hx.1, hx.2, t.property.1]

private theorem inv_sqrt_mul_inv_sqrt (L : CCMPositiveAperture) :
    (Real.sqrt (L : ℝ))⁻¹ * (Real.sqrt (L : ℝ))⁻¹ = ((L : ℝ))⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt L.property.le]

private theorem sqrt_two_div_mul_inv_sqrt (L : CCMPositiveAperture) :
    Real.sqrt (2 / (L : ℝ)) * (Real.sqrt (L : ℝ))⁻¹ =
      Real.sqrt 2 / (L : ℝ) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 / Real.sqrt (L : ℝ) * (Real.sqrt (L : ℝ))⁻¹ =
        Real.sqrt 2 / (Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ = Real.sqrt 2 / (L : ℝ) := by
      rw [Real.mul_self_sqrt L.property.le]

private theorem intervalIntegral_cos_centeredMode_overlap
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x)) =
      -((-1 : ℝ) ^ (n : ℕ)) *
        Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
          ccmCenteredModeFrequency L (n : ℕ) := by
  have hkpos : 0 < ccmCenteredModeFrequency L (n : ℕ) := by
    rw [ccmCenteredModeFrequency]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr n.property))
      L.property
  have hden : (0 : ℝ) ^ 2 + ccmCenteredModeFrequency L (n : ℕ) ^ 2 ≠ 0 := by
    norm_num only [zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact pow_ne_zero _ hkpos.ne'
  rw [show (fun x : ℝ => Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x)) =
      fun x : ℝ => Real.exp (0 * x) *
        Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) by simp]
  rw [intervalIntegral_exp_mul_cos hden]
  simp only [ccmExpCosPrimitive, zero_mul, Real.exp_zero, zero_mul, zero_add,
    zero_pow (by norm_num : 2 ≠ 0), zero_add, one_mul]
  have hpos : ccmCenteredModeFrequency L (n : ℕ) * ((L : ℝ) / 2) =
      ((n : ℕ) : ℝ) * Real.pi := by
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hneg :
      ccmCenteredModeFrequency L (n : ℕ) *
          ((t : ℝ) - (L : ℝ) / 2) =
        ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ) -
          ((n : ℕ) : ℝ) * Real.pi := by
    calc
      ccmCenteredModeFrequency L (n : ℕ) *
          ((t : ℝ) - (L : ℝ) / 2) =
          ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ) -
            ccmCenteredModeFrequency L (n : ℕ) * ((L : ℝ) / 2) := by ring
      _ = _ := by rw [hpos]
  rw [hpos, hneg, Real.sin_nat_mul_pi, Real.sin_sub_nat_mul_pi]
  field_simp [ne_of_gt hkpos]
  ring

private theorem intervalIntegral_cos_affine
    {a b c d : ℝ} (hc : c ≠ 0) :
    (∫ x in a..b, Real.cos (c * x + d)) =
      (Real.sin (c * b + d) - Real.sin (c * a + d)) / c := by
  have hbase :
      (∫ x in a..b, Real.cos (c * x + d)) =
        Real.sin (c * b + d) / c - Real.sin (c * a + d) / c := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      have harg : HasDerivAt (fun y : ℝ => c * y + d) c x := by
        simpa using ((hasDerivAt_id x).const_mul c).add_const d
      convert! ((Real.hasDerivAt_sin (c * x + d)).comp x harg).div_const c using 1
      exact (mul_div_cancel_right₀ _ hc).symm
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos (c * x + d))).intervalIntegrable _ _
  rw [hbase]
  ring

private theorem intervalIntegral_cos_double_centeredMode_overlap
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.cos (2 * ccmCenteredModeFrequency L (n : ℕ) * x -
        ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) =
      -Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
        ccmCenteredModeFrequency L (n : ℕ) := by
  have hkpos : 0 < ccmCenteredModeFrequency L (n : ℕ) := by
    rw [ccmCenteredModeFrequency]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr n.property))
      L.property
  rw [show (fun x : ℝ =>
      Real.cos (2 * ccmCenteredModeFrequency L (n : ℕ) * x -
        ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) =
      fun x : ℝ => Real.cos
        ((2 * ccmCenteredModeFrequency L (n : ℕ)) * x +
          (-(ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)))) by
    funext x
    ring_nf]
  rw [intervalIntegral_cos_affine (mul_ne_zero (by norm_num) hkpos.ne')]
  have hperiod : ccmCenteredModeFrequency L (n : ℕ) * (L : ℝ) =
      ((n : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hupper :
      (2 * ccmCenteredModeFrequency L (n : ℕ)) * ((L : ℝ) / 2) +
          -(ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) =
        ((n : ℕ) : ℝ) * (2 * Real.pi) -
          ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ) := by
    rw [← hperiod]
    ring
  have hlower :
      (2 * ccmCenteredModeFrequency L (n : ℕ)) *
          ((t : ℝ) - (L : ℝ) / 2) +
          -(ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) =
        ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ) -
          ((n : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [← hperiod]
    ring
  rw [hupper, hlower, Real.sin_nat_mul_two_pi_sub,
    Real.sin_sub_nat_mul_two_pi]
  field_simp [hkpos.ne']
  ring

private theorem cosine_mul_cosine_eq (a b : ℝ) :
    Real.cos a * Real.cos b =
      (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private theorem sine_mul_sine_eq (a b : ℝ) :
    Real.sin a * Real.sin b =
      (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private theorem intervalIntegral_centeredCosineDiagonal
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) *
        Real.cos (ccmCenteredModeFrequency L (n : ℕ) * (x - (t : ℝ)))) =
      ((L : ℝ) - (t : ℝ)) / 2 *
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) -
        Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
          (2 * ccmCenteredModeFrequency L (n : ℕ)) := by
  let k := ccmCenteredModeFrequency L (n : ℕ)
  have hpoint :
      (fun x : ℝ => Real.cos (k * x) * Real.cos (k * (x - (t : ℝ)))) =
        fun x : ℝ =>
          (1 / 2 : ℝ) * Real.cos (k * (t : ℝ)) +
            (1 / 2 : ℝ) * Real.cos (2 * k * x - k * (t : ℝ)) := by
    funext x
    rw [cosine_mul_cosine_eq]
    rw [show k * x - k * (x - (t : ℝ)) = k * (t : ℝ) by ring,
      show k * x + k * (x - (t : ℝ)) = 2 * k * x - k * (t : ℝ) by ring]
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun _x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (k * (t : ℝ)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (2 * k * x - k * (t : ℝ)))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral_cos_double_centeredMode_overlap L n t]
  simp only [smul_eq_mul]
  dsimp [k]
  ring

private theorem intervalIntegral_centeredSineDiagonal
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.sin (-(ccmCenteredModeFrequency L (n : ℕ)) * x) *
        Real.sin (-(ccmCenteredModeFrequency L (n : ℕ)) * (x - (t : ℝ)))) =
      ((L : ℝ) - (t : ℝ)) / 2 *
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) +
        Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
          (2 * ccmCenteredModeFrequency L (n : ℕ)) := by
  let k := ccmCenteredModeFrequency L (n : ℕ)
  have hpoint :
      (fun x : ℝ => Real.sin (-k * x) * Real.sin (-k * (x - (t : ℝ)))) =
        fun x : ℝ =>
          (1 / 2 : ℝ) * Real.cos (k * (t : ℝ)) -
            (1 / 2 : ℝ) * Real.cos (2 * k * x - k * (t : ℝ)) := by
    funext x
    rw [sine_mul_sine_eq]
    rw [show -k * x - -k * (x - (t : ℝ)) = -(k * (t : ℝ)) by ring,
      show -k * x + -k * (x - (t : ℝ)) = -(2 * k * x - k * (t : ℝ)) by ring,
      Real.cos_neg, Real.cos_neg]
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun _x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (k * (t : ℝ)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos (2 * k * x - k * (t : ℝ)))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral_cos_double_centeredMode_overlap L n t]
  simp only [smul_eq_mul]
  dsimp [k]
  ring

private theorem centeredRealModeScale_sq
    (L : CCMPositiveAperture) (n : ℕ) :
    ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ))) ^ 2 = 2 / (L : ℝ) := by
  rw [mul_pow, ← pow_mul, Real.sq_sqrt]
  · norm_num
  · exact div_nonneg (by norm_num) L.property.le

private theorem centeredRealModeScale_mul
    (L : CCMPositiveAperture) (n m : ℕ) :
    ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ))) *
        ((-1 : ℝ) ^ m * Real.sqrt (2 / (L : ℝ))) =
      (-1 : ℝ) ^ (n + m) * (2 / (L : ℝ)) := by
  have hsqrt : Real.sqrt (2 / (L : ℝ)) * Real.sqrt (2 / (L : ℝ)) =
      2 / (L : ℝ) := Real.mul_self_sqrt (div_nonneg (by norm_num) L.property.le)
  rw [pow_add]
  calc
    ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ))) *
          ((-1 : ℝ) ^ m * Real.sqrt (2 / (L : ℝ))) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ m) *
          (Real.sqrt (2 / (L : ℝ)) * Real.sqrt (2 / (L : ℝ))) := by ring
    _ = _ := by rw [hsqrt]

private theorem centeredModeFrequency_ne
    (L : CCMPositiveAperture) {n m : CCMPositiveFourierIndex} (hnm : n ≠ m) :
    ccmCenteredModeFrequency L (n : ℕ) ≠ ccmCenteredModeFrequency L (m : ℕ) := by
  intro h
  apply hnm
  apply Subtype.ext
  rw [ccmCenteredModeFrequency, ccmCenteredModeFrequency] at h
  have hscale : 2 * Real.pi / (L : ℝ) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt L.property)
  apply Nat.cast_injective (R := ℝ)
  apply (mul_left_cancel₀ hscale)
  simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using h

private theorem intervalIntegral_centeredCosineOffDiagonal
    (L : CCMPositiveAperture) (n m : CCMPositiveFourierIndex) (hnm : n ≠ m)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) *
        Real.cos (ccmCenteredModeFrequency L (m : ℕ) * (x - (t : ℝ)))) =
      ((-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) / 2) *
        ((Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ)) -
              Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) /
            (ccmCenteredModeFrequency L (n : ℕ) -
              ccmCenteredModeFrequency L (m : ℕ)) -
          (Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ)) +
              Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) /
            (ccmCenteredModeFrequency L (n : ℕ) +
              ccmCenteredModeFrequency L (m : ℕ))) := by
  let kn := ccmCenteredModeFrequency L (n : ℕ)
  let km := ccmCenteredModeFrequency L (m : ℕ)
  have hdiff : kn - km ≠ 0 :=
    sub_ne_zero.mpr (centeredModeFrequency_ne L hnm)
  have hsum : kn + km ≠ 0 := by
    have hkn : 0 < kn := by
      dsimp [kn]
      rw [ccmCenteredModeFrequency]
      exact div_pos
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr n.property))
        L.property
    have hkm : 0 < km := by
      dsimp [km]
      rw [ccmCenteredModeFrequency]
      exact div_pos
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr m.property))
        L.property
    positivity
  have hpoint :
      (fun x : ℝ => Real.cos (kn * x) * Real.cos (km * (x - (t : ℝ)))) =
        fun x : ℝ =>
          (1 / 2 : ℝ) * Real.cos ((kn - km) * x + km * (t : ℝ)) +
            (1 / 2 : ℝ) * Real.cos ((kn + km) * x - km * (t : ℝ)) := by
    funext x
    rw [cosine_mul_cosine_eq]
    rw [show kn * x - km * (x - (t : ℝ)) =
        (kn - km) * x + km * (t : ℝ) by ring,
      show kn * x + km * (x - (t : ℝ)) =
        (kn + km) * x - km * (t : ℝ) by ring]
    ring
  have hknL : kn * ((L : ℝ) / 2) = ((n : ℕ) : ℝ) * Real.pi := by
    dsimp [kn]
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hkmL : km * ((L : ℝ) / 2) = ((m : ℕ) : ℝ) * Real.pi := by
    dsimp [km]
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hu1 :
      (kn - km) * ((L : ℝ) / 2) + km * (t : ℝ) =
        (km * (t : ℝ) - ((m : ℕ) : ℝ) * Real.pi) +
          ((n : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hl1 :
      (kn - km) * ((t : ℝ) - (L : ℝ) / 2) + km * (t : ℝ) =
        (kn * (t : ℝ) - ((n : ℕ) : ℝ) * Real.pi) +
          ((m : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hu2 :
      (kn + km) * ((L : ℝ) / 2) - km * (t : ℝ) =
        (((m : ℕ) : ℝ) * Real.pi - km * (t : ℝ)) +
          ((n : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hl2 :
      (kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ) =
        (kn * (t : ℝ) - ((n : ℕ) : ℝ) * Real.pi) -
          ((m : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hsecond :
      (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
        Real.cos ((kn + km) * x - km * (t : ℝ))) =
      (Real.sin ((kn + km) * ((L : ℝ) / 2) - km * (t : ℝ)) -
          Real.sin ((kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ))) /
        (kn + km) := by
    rw [show (fun x : ℝ => Real.cos ((kn + km) * x - km * (t : ℝ))) =
        fun x : ℝ => Real.cos ((kn + km) * x + (-(km * (t : ℝ)))) by
      funext x
      ring_nf]
    exact intervalIntegral_cos_affine hsum
  have hsu1 :
      Real.sin ((kn - km) * ((L : ℝ) / 2) + km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (km * (t : ℝ)) := by
    rw [hu1, Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hsl1 :
      Real.sin ((kn - km) * ((t : ℝ) - (L : ℝ) / 2) + km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (kn * (t : ℝ)) := by
    rw [hl1, Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hsu2 :
      Real.sin ((kn + km) * ((L : ℝ) / 2) - km * (t : ℝ)) =
        -((-1 : ℝ) ^ ((n : ℕ) + (m : ℕ))) * Real.sin (km * (t : ℝ)) := by
    rw [hu2, Real.sin_add_nat_mul_pi, Real.sin_nat_mul_pi_sub, pow_add]
    ring
  have hsl2 :
      Real.sin ((kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (kn * (t : ℝ)) := by
    rw [hl2, Real.sin_sub_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((kn - km) * x + km * (t : ℝ)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((kn + km) * x - km * (t : ℝ)))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral_cos_affine hdiff, hsecond,
    hsu1, hsl1, hsu2, hsl2]
  dsimp [kn, km]
  ring

private theorem intervalIntegral_centeredSineOffDiagonal
    (L : CCMPositiveAperture) (n m : CCMPositiveFourierIndex) (hnm : n ≠ m)
    (t : CCMApertureLag L) :
    (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
      Real.sin (-(ccmCenteredModeFrequency L (n : ℕ)) * x) *
        Real.sin (-(ccmCenteredModeFrequency L (m : ℕ)) * (x - (t : ℝ)))) =
      ((-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) / 2) *
        ((Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ)) -
              Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) /
            (ccmCenteredModeFrequency L (n : ℕ) -
              ccmCenteredModeFrequency L (m : ℕ)) +
          (Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ)) +
              Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ))) /
            (ccmCenteredModeFrequency L (n : ℕ) +
              ccmCenteredModeFrequency L (m : ℕ))) := by
  let kn := ccmCenteredModeFrequency L (n : ℕ)
  let km := ccmCenteredModeFrequency L (m : ℕ)
  have hdiff : kn - km ≠ 0 :=
    sub_ne_zero.mpr (centeredModeFrequency_ne L hnm)
  have hsum : kn + km ≠ 0 := by
    have hkn : 0 < kn := by
      dsimp [kn]
      rw [ccmCenteredModeFrequency]
      exact div_pos
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr n.property))
        L.property
    have hkm : 0 < km := by
      dsimp [km]
      rw [ccmCenteredModeFrequency]
      exact div_pos
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr m.property))
        L.property
    positivity
  have hpoint :
      (fun x : ℝ => Real.sin (-kn * x) * Real.sin (-km * (x - (t : ℝ)))) =
        fun x : ℝ =>
          (1 / 2 : ℝ) * Real.cos ((kn - km) * x + km * (t : ℝ)) -
            (1 / 2 : ℝ) * Real.cos ((kn + km) * x - km * (t : ℝ)) := by
    funext x
    rw [sine_mul_sine_eq]
    rw [show -kn * x - -km * (x - (t : ℝ)) =
        -((kn - km) * x + km * (t : ℝ)) by ring,
      show -kn * x + -km * (x - (t : ℝ)) =
        -((kn + km) * x - km * (t : ℝ)) by ring,
      Real.cos_neg, Real.cos_neg]
    ring
  have hknL : kn * ((L : ℝ) / 2) = ((n : ℕ) : ℝ) * Real.pi := by
    dsimp [kn]
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hkmL : km * ((L : ℝ) / 2) = ((m : ℕ) : ℝ) * Real.pi := by
    dsimp [km]
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hu1 :
      (kn - km) * ((L : ℝ) / 2) + km * (t : ℝ) =
        (km * (t : ℝ) - ((m : ℕ) : ℝ) * Real.pi) +
          ((n : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hl1 :
      (kn - km) * ((t : ℝ) - (L : ℝ) / 2) + km * (t : ℝ) =
        (kn * (t : ℝ) - ((n : ℕ) : ℝ) * Real.pi) +
          ((m : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hu2 :
      (kn + km) * ((L : ℝ) / 2) - km * (t : ℝ) =
        (((m : ℕ) : ℝ) * Real.pi - km * (t : ℝ)) +
          ((n : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hl2 :
      (kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ) =
        (kn * (t : ℝ) - ((n : ℕ) : ℝ) * Real.pi) -
          ((m : ℕ) : ℝ) * Real.pi := by rw [← hknL, ← hkmL]; ring
  have hsecond :
      (∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
        Real.cos ((kn + km) * x - km * (t : ℝ))) =
      (Real.sin ((kn + km) * ((L : ℝ) / 2) - km * (t : ℝ)) -
          Real.sin ((kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ))) /
        (kn + km) := by
    rw [show (fun x : ℝ => Real.cos ((kn + km) * x - km * (t : ℝ))) =
        fun x : ℝ => Real.cos ((kn + km) * x + (-(km * (t : ℝ)))) by
      funext x
      ring_nf]
    exact intervalIntegral_cos_affine hsum
  have hsu1 :
      Real.sin ((kn - km) * ((L : ℝ) / 2) + km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (km * (t : ℝ)) := by
    rw [hu1, Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hsl1 :
      Real.sin ((kn - km) * ((t : ℝ) - (L : ℝ) / 2) + km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (kn * (t : ℝ)) := by
    rw [hl1, Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hsu2 :
      Real.sin ((kn + km) * ((L : ℝ) / 2) - km * (t : ℝ)) =
        -((-1 : ℝ) ^ ((n : ℕ) + (m : ℕ))) * Real.sin (km * (t : ℝ)) := by
    rw [hu2, Real.sin_add_nat_mul_pi, Real.sin_nat_mul_pi_sub, pow_add]
    ring
  have hsl2 :
      Real.sin ((kn + km) * ((t : ℝ) - (L : ℝ) / 2) - km * (t : ℝ)) =
        (-1 : ℝ) ^ ((n : ℕ) + (m : ℕ)) * Real.sin (kn * (t : ℝ)) := by
    rw [hl2, Real.sin_sub_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((kn - km) * x + km * (t : ℝ)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((kn + km) * x - km * (t : ℝ)))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral_cos_affine hdiff, hsecond,
    hsu1, hsl1, hsu2, hsl2]
  dsimp [kn, km]
  ring

private theorem ccmCenteredConstantMode_neg
    (L : CCMPositiveAperture) (x : ℝ) :
    ccmCenteredConstantMode L (-x) = ccmCenteredConstantMode L x := by
  have hmem : -x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) ↔
      x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
  · rw [ccmCenteredConstantMode, ccmCenteredConstantMode,
      Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · rw [ccmCenteredConstantMode, ccmCenteredConstantMode,
      Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa [hmem] using hx)]

private theorem ccmRealCorrelation_neg_eq_self_of_even_even
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = g x)
    (t : ℝ) :
    ccmRealCorrelation f g (-t) = ccmRealCorrelation f g t := by
  rw [ccmRealCorrelation, ccmRealCorrelation]
  rw [show (fun x : ℝ => f x * g (x - -t)) =
      fun x : ℝ => f x * g (x + t) by funext x; ring_nf]
  calc
    (∫ x : ℝ, f x * g (x + t)) =
        ∫ x : ℝ, f (-x) * g (-x + t) := by
          symm
          exact integral_neg_eq_self (fun x : ℝ => f x * g (x + t)) volume
    _ = ∫ x : ℝ, f x * g (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hf, show -x + t = -(x - t) by ring, hg]

private theorem ccmRealCorrelation_neg_eq_self_of_odd_odd
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (hg : ∀ x, g (-x) = -g x)
    (t : ℝ) :
    ccmRealCorrelation f g (-t) = ccmRealCorrelation f g t := by
  rw [ccmRealCorrelation, ccmRealCorrelation]
  rw [show (fun x : ℝ => f x * g (x - -t)) =
      fun x : ℝ => f x * g (x + t) by funext x; ring_nf]
  calc
    (∫ x : ℝ, f x * g (x + t)) =
        ∫ x : ℝ, f (-x) * g (-x + t) := by
          symm
          exact integral_neg_eq_self (fun x : ℝ => f x * g (x + t)) volume
    _ = ∫ x : ℝ, f x * g (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hf, show -x + t = -(x - t) by ring, hg]
      ring

/-- `polarize2(iii)`, abstract even/even form: the correlation is even and the two
orientations agree. -/
theorem ccmRealCorrelation_swap_eq_of_even_even
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = g x)
    (t : ℝ) :
    ccmRealCorrelation f g t = ccmRealCorrelation g f t := by
  rw [← ccmRealCorrelation_neg f g t,
    ccmRealCorrelation_neg_eq_self_of_even_even f g hf hg t]

/-- `polarize2(iii)`, abstract odd/odd form: the correlation is even and the two
orientations agree. -/
theorem ccmRealCorrelation_swap_eq_of_odd_odd
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (hg : ∀ x, g (-x) = -g x)
    (t : ℝ) :
    ccmRealCorrelation f g t = ccmRealCorrelation g f t := by
  rw [← ccmRealCorrelation_neg f g t,
    ccmRealCorrelation_neg_eq_self_of_odd_odd f g hf hg t]

/-- `polarize2(iii)`, center entry: `ξ₀ * ξ₀*` is the normalized tent. -/
theorem ccmRealCorrelation_centeredConstantMode
    (L : CCMPositiveAperture) (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredConstantMode L) (ccmCenteredConstantMode L) (t : ℝ) =
      ((L : ℝ) - (t : ℝ)) / (L : ℝ) := by
  change ccmRealCorrelation (ccmCenteredConstantWindow L)
      (ccmCenteredConstantWindow L) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredConstantMode L x * ccmCenteredConstantMode L (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredConstantMode L x * ccmCenteredConstantMode L (x - (t : ℝ))) =
      ∫ _x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2), ((L : ℝ))⁻¹ by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredConstantMode, ccmCenteredConstantMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt,
      inv_sqrt_mul_inv_sqrt]]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal]
  · simp only [smul_eq_mul]
    field_simp [ne_of_gt L.property]
    ring
  · linarith [t.property.2]

/-- `polarize2(iii)`, constant/cosine entry of the published table. -/
theorem ccmRealCorrelation_centeredCosineMode_constant
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredCosineMode L (n : ℕ))
        (ccmCenteredConstantMode L) (t : ℝ) =
      -Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
        (Real.sqrt 2 * Real.pi * ((n : ℕ) : ℝ)) := by
  change ccmRealCorrelation (ccmCenteredCosineWindow L (n : ℕ))
      (ccmCenteredConstantWindow L) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredConstantMode L (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredConstantMode L (x - (t : ℝ))) =
      (-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ)) *
        (Real.sqrt (L : ℝ))⁻¹ *
          ∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
            Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) by
    rw [intervalIntegral.integral_of_le (by linarith [t.property.2]),
      ← integral_Icc_eq_integral_Ioc]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredCosineMode, ccmCenteredConstantMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt]
    ring]
  rw [intervalIntegral_cos_centeredMode_overlap L n t]
  rw [show (-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ)) *
      (Real.sqrt (L : ℝ))⁻¹ =
      (-1 : ℝ) ^ (n : ℕ) *
        (Real.sqrt (2 / (L : ℝ)) * (Real.sqrt (L : ℝ))⁻¹) by ring,
    sqrt_two_div_mul_inv_sqrt]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  rw [ccmCenteredModeFrequency]
  field_simp [ne_of_gt L.property, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2),
    Nat.cast_ne_zero.mpr (ne_of_gt n.property)]
  ring_nf at hsqrt2 ⊢
  rw [hsqrt2]
  rcases neg_one_pow_eq_or ℝ (n : ℕ) with hsign | hsign <;>
    rw [pow_mul, hsign] <;> norm_num <;> ring

/-- `polarize2(iii)`: the opposite constant/cosine entry agrees with the same table value. -/
theorem ccmRealCorrelation_centeredConstant_cosineMode
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredConstantMode L)
        (ccmCenteredCosineMode L (n : ℕ)) (t : ℝ) =
      -Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
        (Real.sqrt 2 * Real.pi * ((n : ℕ) : ℝ)) := by
  rw [← ccmRealCorrelation_neg (ccmCenteredCosineMode L (n : ℕ))
      (ccmCenteredConstantMode L) (t : ℝ),
    ccmRealCorrelation_neg_eq_self_of_even_even
      (ccmCenteredCosineMode L (n : ℕ)) (ccmCenteredConstantMode L)
      (ccmCenteredCosineMode_neg L (n : ℕ)) (ccmCenteredConstantMode_neg L)
      (t : ℝ),
    ccmRealCorrelation_centeredCosineMode_constant]

/-- `polarize2(ii)`, the missing `n=0,m<0` cell: constant/sine symmetrized
correlations vanish identically. -/
theorem ccmCenteredConstantSineCorrelation_add_swap_eq_zero
    (L : CCMPositiveAperture) (m : ℕ) (t : ℝ) :
    ccmRealCorrelation (ccmCenteredConstantMode L)
        (ccmCenteredNegativeSineMode L m) t +
      ccmRealCorrelation (ccmCenteredNegativeSineMode L m)
        (ccmCenteredConstantMode L) t = 0 :=
  ccmRealCorrelation_add_swap_eq_zero_of_even_odd _ _
    (ccmCenteredConstantMode_neg L) (ccmCenteredNegativeSineMode_neg L m) t

/-- `polarize2(iii)`, literal positive-positive swap equality. -/
theorem ccmRealCorrelation_centeredCosineModes_swap
    (L : CCMPositiveAperture) (n m : ℕ) (t : ℝ) :
    ccmRealCorrelation (ccmCenteredCosineMode L n)
        (ccmCenteredCosineMode L m) t =
      ccmRealCorrelation (ccmCenteredCosineMode L m)
        (ccmCenteredCosineMode L n) t :=
  ccmRealCorrelation_swap_eq_of_even_even _ _
    (ccmCenteredCosineMode_neg L n) (ccmCenteredCosineMode_neg L m) t

/-- `polarize2(iii)`, literal negative-negative swap equality. -/
theorem ccmRealCorrelation_centeredNegativeSineModes_swap
    (L : CCMPositiveAperture) (n m : ℕ) (t : ℝ) :
    ccmRealCorrelation (ccmCenteredNegativeSineMode L n)
        (ccmCenteredNegativeSineMode L m) t =
      ccmRealCorrelation (ccmCenteredNegativeSineMode L m)
        (ccmCenteredNegativeSineMode L n) t :=
  ccmRealCorrelation_swap_eq_of_odd_odd _ _
    (ccmCenteredNegativeSineMode_neg L n)
    (ccmCenteredNegativeSineMode_neg L m) t

/-- `polarize2(iii)`, literal zero/positive swap equality. -/
theorem ccmRealCorrelation_centeredConstant_cosineMode_swap
    (L : CCMPositiveAperture) (n : ℕ) (t : ℝ) :
    ccmRealCorrelation (ccmCenteredConstantMode L)
        (ccmCenteredCosineMode L n) t =
      ccmRealCorrelation (ccmCenteredCosineMode L n)
        (ccmCenteredConstantMode L) t :=
  ccmRealCorrelation_swap_eq_of_even_even _ _
    (ccmCenteredConstantMode_neg L) (ccmCenteredCosineMode_neg L n) t

/-- `polarize2(iii)`, positive diagonal entry of the published table. -/
theorem ccmRealCorrelation_centeredCosineMode_self
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredCosineMode L (n : ℕ))
        (ccmCenteredCosineMode L (n : ℕ)) (t : ℝ) =
      ((L : ℝ) - (t : ℝ)) / (L : ℝ) *
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) -
        Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
          (2 * Real.pi * ((n : ℕ) : ℝ)) := by
  change ccmRealCorrelation (ccmCenteredCosineWindow L (n : ℕ))
      (ccmCenteredCosineWindow L (n : ℕ)) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredCosineMode L (n : ℕ) (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredCosineMode L (n : ℕ) (x - (t : ℝ))) =
      (((-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ))) ^ 2) *
        ∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) *
            Real.cos
              (ccmCenteredModeFrequency L (n : ℕ) * (x - (t : ℝ))) by
    rw [intervalIntegral.integral_of_le (by linarith [t.property.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredCosineMode, ccmCenteredCosineMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt]
    ring]
  rw [centeredRealModeScale_sq,
    intervalIntegral_centeredCosineDiagonal L n t, ccmCenteredModeFrequency]
  field_simp [ne_of_gt L.property, Nat.cast_ne_zero.mpr (ne_of_gt n.property)]

/-- `polarize2(iii)`, negative diagonal entry of the published table. -/
theorem ccmRealCorrelation_centeredNegativeSineMode_self
    (L : CCMPositiveAperture) (n : CCMPositiveFourierIndex)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredNegativeSineMode L (n : ℕ))
        (ccmCenteredNegativeSineMode L (n : ℕ)) (t : ℝ) =
      Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) /
          (2 * Real.pi * ((n : ℕ) : ℝ)) +
        ((L : ℝ) - (t : ℝ)) / (L : ℝ) *
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) := by
  change ccmRealCorrelation (ccmCenteredNegativeSineWindow L (n : ℕ))
      (ccmCenteredNegativeSineWindow L (n : ℕ)) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredNegativeSineMode L (n : ℕ) x *
        ccmCenteredNegativeSineMode L (n : ℕ) (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredNegativeSineMode L (n : ℕ) x *
        ccmCenteredNegativeSineMode L (n : ℕ) (x - (t : ℝ))) =
      (((-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ))) ^ 2) *
        ∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
          Real.sin (-(ccmCenteredModeFrequency L (n : ℕ)) * x) *
            Real.sin
              (-(ccmCenteredModeFrequency L (n : ℕ)) * (x - (t : ℝ))) by
    rw [intervalIntegral.integral_of_le (by linarith [t.property.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredNegativeSineMode, ccmCenteredNegativeSineMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt]
    ring]
  rw [centeredRealModeScale_sq,
    intervalIntegral_centeredSineDiagonal L n t, ccmCenteredModeFrequency]
  field_simp [ne_of_gt L.property, Nat.cast_ne_zero.mpr (ne_of_gt n.property)]
  ring_nf

/-- `polarize2(iii)`, distinct positive-index entry of the published table. -/
theorem ccmRealCorrelation_centeredCosineModes_of_ne
    (L : CCMPositiveAperture) (n m : CCMPositiveFourierIndex) (hnm : n ≠ m)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredCosineMode L (n : ℕ))
        (ccmCenteredCosineMode L (m : ℕ)) (t : ℝ) =
      (((n : ℕ) : ℝ) *
            Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) -
          ((m : ℕ) : ℝ) *
            Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ))) /
        (Real.pi * (((m : ℕ) : ℝ) ^ 2 - ((n : ℕ) : ℝ) ^ 2)) := by
  change ccmRealCorrelation (ccmCenteredCosineWindow L (n : ℕ))
      (ccmCenteredCosineWindow L (m : ℕ)) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredCosineMode L (m : ℕ) (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredCosineMode L (n : ℕ) x *
        ccmCenteredCosineMode L (m : ℕ) (x - (t : ℝ))) =
      (((-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ))) *
          ((-1 : ℝ) ^ (m : ℕ) * Real.sqrt (2 / (L : ℝ)))) *
        ∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
          Real.cos (ccmCenteredModeFrequency L (n : ℕ) * x) *
            Real.cos
              (ccmCenteredModeFrequency L (m : ℕ) * (x - (t : ℝ))) by
    rw [intervalIntegral.integral_of_le (by linarith [t.property.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredCosineMode, ccmCenteredCosineMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt]
    ring]
  rw [centeredRealModeScale_mul,
    intervalIntegral_centeredCosineOffDiagonal L n m hnm t]
  have hnEven : (-1 : ℝ) ^ ((n : ℕ) * 2) = 1 := by
    rw [show (n : ℕ) * 2 = 2 * (n : ℕ) by ring, pow_mul]
    norm_num
  have hmEven : (-1 : ℝ) ^ ((m : ℕ) * 2) = 1 := by
    rw [show (m : ℕ) * 2 = 2 * (m : ℕ) by ring, pow_mul]
    norm_num
  have hnat : (n : ℕ) ≠ (m : ℕ) := fun h => hnm (Subtype.ext h)
  have hnmR : ((n : ℕ) : ℝ) ≠ ((m : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsumR : ((n : ℕ) : ℝ) + ((m : ℕ) : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos (Nat.cast_pos.mpr n.property) (Nat.cast_pos.mpr m.property))
  have hsquare : ((m : ℕ) : ℝ) ^ 2 - ((n : ℕ) : ℝ) ^ 2 ≠ 0 := by
    intro h
    have hnpos : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.property
    have hmpos : 0 < ((m : ℕ) : ℝ) := Nat.cast_pos.mpr m.property
    apply hnmR
    nlinarith
  simp only [ccmCenteredModeFrequency]
  field_simp [ne_of_gt L.property, Real.pi_ne_zero, hnmR, hsumR, hsquare]
  ring_nf
  rw [hnEven, hmEven]
  ring

/-- `polarize2(iii)`, distinct negative-index entry of the published table. -/
theorem ccmRealCorrelation_centeredNegativeSineModes_of_ne
    (L : CCMPositiveAperture) (n m : CCMPositiveFourierIndex) (hnm : n ≠ m)
    (t : CCMApertureLag L) :
    ccmRealCorrelation (ccmCenteredNegativeSineMode L (n : ℕ))
        (ccmCenteredNegativeSineMode L (m : ℕ)) (t : ℝ) =
      (((m : ℕ) : ℝ) *
            Real.sin (ccmCenteredModeFrequency L (n : ℕ) * (t : ℝ)) -
          ((n : ℕ) : ℝ) *
            Real.sin (ccmCenteredModeFrequency L (m : ℕ) * (t : ℝ))) /
        (Real.pi * (((m : ℕ) : ℝ) ^ 2 - ((n : ℕ) : ℝ) ^ 2)) := by
  change ccmRealCorrelation (ccmCenteredNegativeSineWindow L (n : ℕ))
      (ccmCenteredNegativeSineWindow L (m : ℕ)) (t : ℝ) = _
  rw [ccmRealCorrelation_centeredWindow_eq_integral L _ _ t]
  change (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredNegativeSineMode L (n : ℕ) x *
        ccmCenteredNegativeSineMode L (m : ℕ) (x - (t : ℝ))) = _
  rw [show (∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
      ccmCenteredNegativeSineMode L (n : ℕ) x *
        ccmCenteredNegativeSineMode L (m : ℕ) (x - (t : ℝ))) =
      (((-1 : ℝ) ^ (n : ℕ) * Real.sqrt (2 / (L : ℝ))) *
          ((-1 : ℝ) ^ (m : ℕ) * Real.sqrt (2 / (L : ℝ)))) *
        ∫ x in ((t : ℝ) - (L : ℝ) / 2)..((L : ℝ) / 2),
          Real.sin (-(ccmCenteredModeFrequency L (n : ℕ)) * x) *
            Real.sin
              (-(ccmCenteredModeFrequency L (m : ℕ)) * (x - (t : ℝ))) by
    rw [intervalIntegral.integral_of_le (by linarith [t.property.2]),
      ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨hx0, hxt⟩ := centered_overlap_memberships L t hx
    rw [ccmCenteredNegativeSineMode, ccmCenteredNegativeSineMode,
      Set.indicator_of_mem hx0, Set.indicator_of_mem hxt]
    ring]
  rw [centeredRealModeScale_mul,
    intervalIntegral_centeredSineOffDiagonal L n m hnm t]
  have hnEven : (-1 : ℝ) ^ ((n : ℕ) * 2) = 1 := by
    rw [show (n : ℕ) * 2 = 2 * (n : ℕ) by ring, pow_mul]
    norm_num
  have hmEven : (-1 : ℝ) ^ ((m : ℕ) * 2) = 1 := by
    rw [show (m : ℕ) * 2 = 2 * (m : ℕ) by ring, pow_mul]
    norm_num
  have hnat : (n : ℕ) ≠ (m : ℕ) := fun h => hnm (Subtype.ext h)
  have hnmR : ((n : ℕ) : ℝ) ≠ ((m : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsumR : ((n : ℕ) : ℝ) + ((m : ℕ) : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos (Nat.cast_pos.mpr n.property) (Nat.cast_pos.mpr m.property))
  have hsquare : ((m : ℕ) : ℝ) ^ 2 - ((n : ℕ) : ℝ) ^ 2 ≠ 0 := by
    intro h
    have hnpos : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.property
    have hmpos : 0 < ((m : ℕ) : ℝ) := Nat.cast_pos.mpr m.property
    apply hnmR
    nlinarith
  simp only [ccmCenteredModeFrequency]
  field_simp [ne_of_gt L.property, Real.pi_ne_zero, hnmR, hsumR, hsquare]
  ring_nf
  rw [hnEven, hmEven]
  ring

end RHTower
