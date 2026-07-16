import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayPolarization

/-!
# Arithmetic polar coordinates for a complete primitive theta ray

For positive primitive indices `a,b`, the coordinates

```text
x = r + log(u)/2 - log(a),
y = r + log(1-u)/2 - log(b)
```

invert the radial and angular coordinates already used by the primitive-ray density packet.  This
module proves the inverse identities and then sums the entire positive common scale `g`.  The
result is an exact pointwise bridge from the original pair of square-index density atoms to the
five-derivative radial packet, before any sign estimate or change-of-variables theorem.
-/

open Real

namespace RHTower

noncomputable section

def thetaCuspPrimitiveRayArithmeticPolarX (a : ℕ) (r u : ℝ) : ℝ :=
  r + Real.log u / 2 - Real.log (a : ℝ)

def thetaCuspPrimitiveRayArithmeticPolarY (b : ℕ) (r u : ℝ) : ℝ :=
  r + Real.log (1 - u) / 2 - Real.log (b : ℝ)

theorem thetaCuspPrimitiveRayArithmeticPolarX_scaled_sq
    {a : ℕ} (ha : 0 < a) (r : ℝ) {u : ℝ} (hu : 0 < u) :
    ((a : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarX a r u)) ^ 2 =
      u * Real.exp r ^ 2 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hexp : Real.exp (thetaCuspPrimitiveRayArithmeticPolarX a r u) =
      Real.exp r * Real.exp (Real.log u / 2) / (a : ℝ) := by
    unfold thetaCuspPrimitiveRayArithmeticPolarX
    rw [Real.exp_sub, Real.exp_add, Real.exp_log haR]
  have hhalf : Real.exp (Real.log u / 2) ^ 2 = u := by
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_log hu using 1
    ring
  rw [hexp]
  field_simp [haR.ne']
  rw [hhalf]

theorem thetaCuspPrimitiveRayArithmeticPolarY_scaled_sq
    {b : ℕ} (hb : 0 < b) (r : ℝ) {u : ℝ} (hu : u < 1) :
    ((b : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarY b r u)) ^ 2 =
      (1 - u) * Real.exp r ^ 2 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hsub : 0 < 1 - u := sub_pos.mpr hu
  have hexp : Real.exp (thetaCuspPrimitiveRayArithmeticPolarY b r u) =
      Real.exp r * Real.exp (Real.log (1 - u) / 2) / (b : ℝ) := by
    unfold thetaCuspPrimitiveRayArithmeticPolarY
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hbR]
  have hhalf : Real.exp (Real.log (1 - u) / 2) ^ 2 = 1 - u := by
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_log hsub using 1
    ring
  rw [hexp]
  field_simp [hbR.ne']
  rw [hhalf]

/-- The arithmetic inverse recovers the radial logarithmic coordinate exactly. -/
theorem thetaCuspPrimitiveRayRadialLog_arithmeticPolar
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspPrimitiveRayRadialLog a b
        (thetaCuspPrimitiveRayArithmeticPolarX a r u)
        (thetaCuspPrimitiveRayArithmeticPolarY b r u) = r := by
  unfold thetaCuspPrimitiveRayRadialLog
  rw [thetaCuspPrimitiveRayArithmeticPolarX_scaled_sq ha r hu0,
    thetaCuspPrimitiveRayArithmeticPolarY_scaled_sq hb r hu1]
  rw [show u * Real.exp r ^ 2 + (1 - u) * Real.exp r ^ 2 =
      Real.exp r ^ 2 by ring]
  rw [show Real.exp r ^ 2 = Real.exp (r + r) by
    rw [Real.exp_add, pow_two], Real.log_exp]
  ring

/-- The arithmetic inverse recovers the angular coordinate exactly. -/
theorem thetaCuspPrimitiveRayAngularWeight_arithmeticPolar
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspPrimitiveRayAngularWeight a b
        (thetaCuspPrimitiveRayArithmeticPolarX a r u)
        (thetaCuspPrimitiveRayArithmeticPolarY b r u) = u := by
  unfold thetaCuspPrimitiveRayAngularWeight
  rw [thetaCuspPrimitiveRayArithmeticPolarX_scaled_sq ha r hu0,
    thetaCuspPrimitiveRayArithmeticPolarY_scaled_sq hb r hu1]
  field_simp [Real.exp_ne_zero r]
  ring

/-- One positive common scale in arithmetic polar coordinates is exactly one atom of the radial
primitive packet. -/
theorem thetaCuspTailSecondDensityAtom_arithmeticPolar_eq_radial
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (g : ℕ) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspTailSecondDensityAtom (a * g)
        (thetaCuspPrimitiveRayArithmeticPolarX a r u) *
      thetaCuspTailSecondDensityAtom (b * g)
        (thetaCuspPrimitiveRayArithmeticPolarY b r u) =
      16 * Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) *
        thetaCuspPolynomialAtom
          (thetaCuspDensityPrimitiveRayPolynomial u) g r := by
  have h := thetaCuspTailSecondDensityAtom_primitiveRay_eq_radial
    ha hb g
      (thetaCuspPrimitiveRayArithmeticPolarX a r u)
      (thetaCuspPrimitiveRayArithmeticPolarY b r u)
  rw [thetaCuspPrimitiveRayRadialLog_arithmeticPolar ha hb r hu0 hu1,
    thetaCuspPrimitiveRayAngularWeight_arithmeticPolar ha hb r hu0 hu1] at h
  exact h

/-- **Complete common-scale arithmetic ray.**  Summing every positive common scale produces the
actual five-derivative primitive radial packet with no residual arithmetic series. -/
theorem tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_eq_radialPacket
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑' g : ℕ,
      thetaCuspTailSecondDensityAtom (a * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarX a r u) *
        thetaCuspTailSecondDensityAtom (b * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarY b r u)) =
      16 * Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) *
        thetaCuspPrimitiveRayRadialPacket u r := by
  calc
    _ = ∑' g : ℕ,
        16 * Real.exp
            ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
                thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) *
          thetaCuspPolynomialAtom
            (thetaCuspDensityPrimitiveRayPolynomial u) (g + 1) r := by
      apply tsum_congr
      intro g
      exact thetaCuspTailSecondDensityAtom_arithmeticPolar_eq_radial
        ha hb (g + 1) r hu0 hu1
    _ = 16 * Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) *
        (∑' g : ℕ,
          thetaCuspPolynomialAtom
            (thetaCuspDensityPrimitiveRayPolynomial u) (g + 1) r) := by
      rw [tsum_mul_left]
    _ = _ := by
      rw [tsum_thetaCuspPrimitiveRayPolynomialAtom_eq]

/-- Signed Jacobian determinant of the inverse map `(r,u) -> (x,y)`. -/
def thetaCuspPrimitiveRayArithmeticPolarSignedJacobian (u : ℝ) : ℝ :=
  -(1 / (2 * thetaCuspPrimitiveRayMoment u))

/-- The derivative matrix of the displayed inverse coordinates has the claimed signed
determinant. -/
theorem thetaCuspPrimitiveRayArithmeticPolarSignedJacobian_eq
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 * (-(1 / (2 * (1 - u)))) - (1 / (2 * u)) * 1 =
      thetaCuspPrimitiveRayArithmeticPolarSignedJacobian u := by
  have hu : u ≠ 0 := hu0.ne'
  have hsub : 1 - u ≠ 0 := (sub_pos.mpr hu1).ne'
  unfold thetaCuspPrimitiveRayArithmeticPolarSignedJacobian
    thetaCuspPrimitiveRayMoment
  field_simp [hu, hsub]
  ring

/-- Absolute Jacobian of the inverse map `(r,u) -> (x,y)` on the open angular interval. -/
def thetaCuspPrimitiveRayArithmeticPolarJacobian (u : ℝ) : ℝ :=
  1 / (2 * thetaCuspPrimitiveRayMoment u)

theorem abs_thetaCuspPrimitiveRayArithmeticPolarSignedJacobian
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    |thetaCuspPrimitiveRayArithmeticPolarSignedJacobian u| =
      thetaCuspPrimitiveRayArithmeticPolarJacobian u := by
  have hmoment : 0 < thetaCuspPrimitiveRayMoment u := by
    unfold thetaCuspPrimitiveRayMoment
    positivity
  unfold thetaCuspPrimitiveRayArithmeticPolarSignedJacobian
    thetaCuspPrimitiveRayArithmeticPolarJacobian
  rw [abs_neg, abs_of_pos]
  positivity

/-- The displayed Jacobian is positive on the active angular interval. -/
theorem thetaCuspPrimitiveRayArithmeticPolarJacobian_pos
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < thetaCuspPrimitiveRayArithmeticPolarJacobian u := by
  unfold thetaCuspPrimitiveRayArithmeticPolarJacobian
    thetaCuspPrimitiveRayMoment
  positivity

/-- **Exact arithmetic seam weight.**  Dividing the polar density prefactor by the angular
Jacobian moment produces precisely the singular beta weight used by the seam-preserving angular
bridge.  The remaining factor depends on the primitive indices only through their joint
logarithmic height; no density factor has been estimated separately. -/
theorem thetaCuspPrimitiveRayArithmeticPolarPrefactor_div_moment_eq
    (a b : ℕ) (r : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) /
        thetaCuspPrimitiveRayMoment u =
      Real.exp
          (r / 2 - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) := by
  have hsub : 0 < 1 - u := sub_pos.mpr hu1
  have hw : 0 < u * (1 - u) := mul_pos hu0 hsub
  have hinv : (u * (1 - u))⁻¹ =
      Real.exp (-(Real.log u + Real.log (1 - u))) := by
    calc
      (u * (1 - u))⁻¹ = (Real.exp (Real.log (u * (1 - u))))⁻¹ := by
        rw [Real.exp_log hw]
      _ = Real.exp (-Real.log (u * (1 - u))) := (Real.exp_neg _).symm
      _ = _ := by rw [Real.log_mul hu0.ne' hsub.ne']
  unfold thetaCuspPrimitiveRayArithmeticPolarX
    thetaCuspPrimitiveRayArithmeticPolarY thetaCuspPrimitiveRayMoment
  rw [Real.rpow_def_of_pos hw, Real.log_mul hu0.ne' hsub.ne']
  rw [div_eq_mul_inv, hinv, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Pointwise density times the exact polar Jacobian.  This is the integrand required by the later
global change-of-variables theorem. -/
theorem tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_mul_jacobian
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑' g : ℕ,
      thetaCuspTailSecondDensityAtom (a * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarX a r u) *
        thetaCuspTailSecondDensityAtom (b * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarY b r u)) *
        thetaCuspPrimitiveRayArithmeticPolarJacobian u =
      (8 * Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) /
            thetaCuspPrimitiveRayMoment u) *
        thetaCuspPrimitiveRayRadialPacket u r := by
  rw [tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_eq_radialPacket
    ha hb r hu0 hu1]
  unfold thetaCuspPrimitiveRayArithmeticPolarJacobian
  ring

/-- The complete arithmetic ray with its exact Jacobian is the seam weight times the full radial
packet.  This is the pointwise interface between the original square-index density product and
`integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_corePolarKernel`: the exponent `-3/4` is
forced by the density and the change of variables, rather than inserted as an auxiliary weight. -/
theorem tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_mul_jacobian_eq_seamWeight
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑' g : ℕ,
      thetaCuspTailSecondDensityAtom (a * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarX a r u) *
        thetaCuspTailSecondDensityAtom (b * (g + 1))
          (thetaCuspPrimitiveRayArithmeticPolarY b r u)) *
        thetaCuspPrimitiveRayArithmeticPolarJacobian u =
      8 * Real.exp
          (r / 2 - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
        thetaCuspPrimitiveRayRadialPacket u r := by
  rw [tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_mul_jacobian
    ha hb r hu0 hu1]
  calc
    (8 * Real.exp
          ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
              thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) /
        thetaCuspPrimitiveRayMoment u) *
        thetaCuspPrimitiveRayRadialPacket u r =
      8 *
        (Real.exp
            ((thetaCuspPrimitiveRayArithmeticPolarX a r u +
                thetaCuspPrimitiveRayArithmeticPolarY b r u - r) / 2) /
          thetaCuspPrimitiveRayMoment u) *
        thetaCuspPrimitiveRayRadialPacket u r := by ring
    _ = _ := by
      rw [thetaCuspPrimitiveRayArithmeticPolarPrefactor_div_moment_eq
        a b r hu0 hu1]
      ring

end

end RHTower
