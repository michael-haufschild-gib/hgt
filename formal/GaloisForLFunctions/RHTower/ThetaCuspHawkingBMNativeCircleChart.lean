import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential

/-! The original hyperbolic circle chart and its complete radial and angular derivatives. -/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def denominator (d theta : ℝ) : ℝ := Real.cosh d-Real.sinh d*Real.cos theta
def radialNumerator (d theta : ℝ) : ℝ := Real.sinh d-Real.cosh d*Real.cos theta
def offset (d theta : ℝ) : ℝ := Real.sinh d*Real.sin theta/denominator d theta
def height (d theta : ℝ) : ℝ := 1/denominator d theta

/-- Every original circle point remains in the upper half-plane. -/
theorem denominator_pos (d theta : ℝ) : 0 < denominator d theta := by
  have hc := Real.cosh_pos d
  have hid := Real.cosh_sq_sub_sinh_sq d
  have hab : |Real.sinh d| < Real.cosh d := by
    nlinarith [sq_abs (Real.sinh d)]
  have hm : Real.sinh d*Real.cos theta ≤ |Real.sinh d| := by
    calc
      Real.sinh d*Real.cos theta ≤ |Real.sinh d*Real.cos theta| := le_abs_self _
      _ = |Real.sinh d| * |Real.cos theta| := abs_mul _ _
      _ ≤ |Real.sinh d| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |Real.sinh d| := mul_one _
  dsimp [denominator]
  linarith

def circle (d theta : ℝ) (z : Point) : Point :=
  ![z 0+z 1*offset d theta,z 1*height d theta]

/-- Positivity of the original base height supplies positivity of every circle height. -/
theorem circle_pos (d theta : ℝ) (z : UpperHalfPlane) : 0 < circle d theta (coordinates z) 1 := by
  exact mul_pos z.im_pos (one_div_pos.mpr (denominator_pos d theta))

def offsetRadial (d theta : ℝ) : ℝ := Real.sin theta/(denominator d theta)^(2 : ℕ)
def heightRadial (d theta : ℝ) : ℝ := -radialNumerator d theta/(denominator d theta)^(2 : ℕ)
def offsetRadialSecond (d theta : ℝ) : ℝ :=
  -2*Real.sin theta*radialNumerator d theta/(denominator d theta)^(3 : ℕ)
def heightRadialSecond (d theta : ℝ) : ℝ :=
  2*(radialNumerator d theta)^(2 : ℕ)/(denominator d theta)^(3 : ℕ)-1/denominator d theta
def offsetAngular (d theta : ℝ) : ℝ :=
  -Real.sinh d*radialNumerator d theta/(denominator d theta)^(2 : ℕ)
def heightAngular (d theta : ℝ) : ℝ :=
  -Real.sinh d*Real.sin theta/(denominator d theta)^(2 : ℕ)
def offsetAngularSecond (d theta : ℝ) : ℝ :=
  -Real.sinh d*Real.cosh d*Real.sin theta/(denominator d theta)^(2 : ℕ)+
    2*(Real.sinh d)^(2 : ℕ)*radialNumerator d theta*Real.sin theta/(denominator d theta)^(3 : ℕ)
def heightAngularSecond (d theta : ℝ) : ℝ :=
  -Real.sinh d*Real.cos theta/(denominator d theta)^(2 : ℕ)+
    2*(Real.sinh d)^(2 : ℕ)*(Real.sin theta)^(2 : ℕ)/(denominator d theta)^(3 : ℕ)

private theorem denominator_radial (d theta : ℝ) :
    HasDerivAt (fun r => denominator r theta) (radialNumerator d theta) d :=
  (Real.hasDerivAt_cosh d).sub ((Real.hasDerivAt_sinh d).mul_const _)

private theorem numerator_radial (d theta : ℝ) :
    HasDerivAt (fun r => radialNumerator r theta) (denominator d theta) d :=
  (Real.hasDerivAt_sinh d).sub ((Real.hasDerivAt_cosh d).mul_const _)

private theorem denominator_angular (d theta : ℝ) :
    HasDerivAt (denominator d) (Real.sinh d*Real.sin theta) theta := by
  apply (((Real.hasDerivAt_cos theta).const_mul (Real.sinh d)).const_sub
    (Real.cosh d)).congr_deriv
  ring

private theorem numerator_angular (d theta : ℝ) :
    HasDerivAt (radialNumerator d) (Real.cosh d*Real.sin theta) theta := by
  apply (((Real.hasDerivAt_cos theta).const_mul (Real.cosh d)).const_sub
    (Real.sinh d)).congr_deriv
  ring

/-- Both radial derivatives of the actual horizontal offset. -/
theorem offset_radial_derivatives (d theta : ℝ) :
    HasDerivAt (fun r => offset r theta) (offsetRadial d theta) d ∧
    HasDerivAt (fun r => offsetRadial r theta) (offsetRadialSecond d theta) d := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · apply (((Real.hasDerivAt_sinh d).mul_const (Real.sin theta)).div
      (denominator_radial d theta) hn).congr_deriv
    dsimp [offsetRadial]
    field_simp [hn]
    dsimp [denominator,radialNumerator]
    linear_combination Real.sin theta*Real.cosh_sq_sub_sinh_sq d
  · apply ((hasDerivAt_const d (Real.sin theta)).div
      ((denominator_radial d theta).pow 2) (pow_ne_zero _ hn)).congr_deriv
    dsimp [offsetRadialSecond]
    field_simp [hn]
    ring

/-- Both radial derivatives of the actual height ratio. -/
theorem height_radial_derivatives (d theta : ℝ) :
    HasDerivAt (fun r => height r theta) (heightRadial d theta) d ∧
    HasDerivAt (fun r => heightRadial r theta) (heightRadialSecond d theta) d := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · apply ((hasDerivAt_const d (1:ℝ)).div (denominator_radial d theta) hn).congr_deriv
    dsimp [heightRadial]
    ring
  · apply ((numerator_radial d theta).neg.div
      ((denominator_radial d theta).pow 2) (pow_ne_zero _ hn)).congr_deriv
    dsimp [heightRadialSecond]
    field_simp [hn]
    ring

/-- Both angular derivatives of the actual horizontal offset. -/
theorem offset_angular_derivatives (d theta : ℝ) :
    HasDerivAt (offset d) (offsetAngular d theta) theta ∧
    HasDerivAt (offsetAngular d) (offsetAngularSecond d theta) theta := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · apply (((Real.hasDerivAt_sin theta).const_mul (Real.sinh d)).div
      (denominator_angular d theta) hn).congr_deriv
    dsimp [offsetAngular]
    field_simp [hn]
    dsimp [denominator,radialNumerator]
    linear_combination -(Real.sinh d)^(2 : ℕ)*Real.sin_sq_add_cos_sq theta
  · apply (((numerator_angular d theta).const_mul (-Real.sinh d)).div
      ((denominator_angular d theta).pow 2) (pow_ne_zero _ hn)).congr_deriv
    dsimp [offsetAngularSecond]
    field_simp [hn]
    ring

/-- Both angular derivatives of the actual height ratio. -/
theorem height_angular_derivatives (d theta : ℝ) :
    HasDerivAt (height d) (heightAngular d theta) theta ∧
    HasDerivAt (heightAngular d) (heightAngularSecond d theta) theta := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · apply ((hasDerivAt_const theta (1:ℝ)).div (denominator_angular d theta) hn).congr_deriv
    dsimp [heightAngular]
    ring
  · apply (((Real.hasDerivAt_sin theta).const_mul (-Real.sinh d)).div
      ((denominator_angular d theta).pow 2) (pow_ne_zero _ hn)).congr_deriv
    dsimp [heightAngularSecond]
    field_simp [hn]
    ring

private theorem circle_quadratic (d theta : ℝ) :
    (radialNumerator d theta)^(2 : ℕ)+(Real.sin theta)^(2 : ℕ)=(denominator d theta)^(2 : ℕ) := by
  dsimp [radialNumerator,denominator]
  linear_combination ((Real.cos theta)^(2 : ℕ)-1)*Real.cosh_sq_sub_sinh_sq d+
    Real.sin_sq_add_cos_sq theta

/-- The literal circle chart has hyperbolic polar area factor `sinh d`.
This is the local measure identity needed to turn a polar cap cutoff into an
unweighted angular integral after division by the chart height squared. -/
theorem polar_area_jacobian (d theta : ℝ) :
    offsetRadial d theta*heightAngular d theta-
      offsetAngular d theta*heightRadial d theta =
        -Real.sinh d*(height d theta)^(2 : ℕ) := by
  have hn := (denominator_pos d theta).ne'
  have he := circle_quadratic d theta
  dsimp [offsetRadial,heightAngular,offsetAngular,heightRadial,height]
  field_simp [hn]
  linear_combination -Real.sinh d*he

/-- The polar area identity is invariant under the literal positive base-height scaling. -/
theorem polar_area_jacobian_scaled (d theta y : ℝ) :
    (y*offsetRadial d theta)*(y*heightAngular d theta)-
      (y*offsetAngular d theta)*(y*heightRadial d theta) =
        -Real.sinh d*(y*height d theta)^(2 : ℕ) := by
  rw [show (y*offsetRadial d theta)*(y*heightAngular d theta)-
      (y*offsetAngular d theta)*(y*heightRadial d theta)=
        y^(2 : ℕ)*(offsetRadial d theta*heightAngular d theta-
          offsetAngular d theta*heightRadial d theta) by ring,
    polar_area_jacobian]
  ring

/-- The chart reconstructs the hyperbolic radial distance from its normalized point. -/
theorem polar_distance_cosh (d theta : ℝ) :
    (offset d theta ^ (2 : ℕ) + height d theta ^ (2 : ℕ) + 1) / (2 * height d theta) = Real.cosh d := by
  have hn := (denominator_pos d theta).ne'
  have hcore :
      (Real.sinh d * Real.sin theta) ^ (2 : ℕ) + 1 + (denominator d theta) ^ (2 : ℕ) =
        2 * Real.cosh d * denominator d theta := by
    dsimp [denominator]
    nlinarith [Real.cosh_sq_sub_sinh_sq d, Real.sin_sq_add_cos_sq theta]
  rw [offset, height]
  field_simp [hn]
  nlinarith [hcore]

/-- The normalized horizontal coordinate is the radial sine component. -/
theorem polar_normalized_sin (d theta : ℝ) :
    offset d theta / height d theta = Real.sinh d * Real.sin theta := by
  have hn := (denominator_pos d theta).ne'
  dsimp [offset, height]
  field_simp [hn]

/-- The normalized height defect is the radial cosine component. -/
theorem polar_normalized_cos (d theta : ℝ) :
    Real.cosh d - (height d theta)⁻¹ = Real.sinh d * Real.cos theta := by
  have hn := (denominator_pos d theta).ne'
  dsimp [height, denominator]
  field_simp [hn]
  ring

/-- The polar principal symbol is the original hyperbolic Laplacian, with no omitted mixed jet. -/
theorem polar_principal (d theta : ℝ) :
    (Real.sinh d)^(2 : ℕ)*(offsetRadial d theta)^(2 : ℕ)+(offsetAngular d theta)^(2 : ℕ)=
      (Real.sinh d)^(2 : ℕ)*(height d theta)^(2 : ℕ) ∧
    (Real.sinh d)^(2 : ℕ)*offsetRadial d theta*heightRadial d theta+
      offsetAngular d theta*heightAngular d theta=0 ∧
    (Real.sinh d)^(2 : ℕ)*(heightRadial d theta)^(2 : ℕ)+(heightAngular d theta)^(2 : ℕ)=
      (Real.sinh d)^(2 : ℕ)*(height d theta)^(2 : ℕ) := by
  have hn := (denominator_pos d theta).ne'
  have he := circle_quadratic d theta
  constructor
  · dsimp [offsetRadial,offsetAngular,height]
    field_simp [hn]
    linear_combination (Real.sinh d)^(2 : ℕ)*he
  constructor
  · dsimp [offsetRadial,heightRadial,offsetAngular,heightAngular]
    ring
  · dsimp [heightRadial,heightAngular,height]
    field_simp [hn]
    linear_combination (Real.sinh d)^(2 : ℕ)*he

/-- The polar first-order chain-rule contribution cancels exactly in both original coordinates. -/
theorem polar_connection (d theta : ℝ) :
    (Real.sinh d)^(2 : ℕ)*offsetRadialSecond d theta+
      Real.sinh d*Real.cosh d*offsetRadial d theta+offsetAngularSecond d theta=0 ∧
    (Real.sinh d)^(2 : ℕ)*heightRadialSecond d theta+
      Real.sinh d*Real.cosh d*heightRadial d theta+heightAngularSecond d theta=0 := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · dsimp [offsetRadialSecond,offsetRadial,offsetAngularSecond]
    ring
  · have he := circle_quadratic d theta
    have hc : Real.sinh d*denominator d theta-Real.cosh d*radialNumerator d theta-
        Real.cos theta=0 := by
      dsimp [denominator,radialNumerator]
      linear_combination Real.cos theta*Real.cosh_sq_sub_sinh_sq d
    dsimp [heightRadialSecond,heightRadial,heightAngularSecond]
    field_simp [hn]
    linear_combination 2*(Real.sinh d)^(2 : ℕ)*he+
      Real.sinh d*denominator d theta*hc

/-- Moving the base-point Laplacian through the circle map leaves an exact angular derivative. -/
theorem base_laplacian_coefficients (d theta : ℝ) :
    1+(offset d theta)^(2 : ℕ)-(height d theta)^(2 : ℕ) = -2*offsetAngular d theta ∧
    2*offset d theta*height d theta = -2*heightAngular d theta := by
  have hn := (denominator_pos d theta).ne'
  constructor
  · dsimp [offset,height,offsetAngular]
    field_simp [hn]
    dsimp [denominator,radialNumerator]
    linear_combination Real.cosh_sq_sub_sinh_sq d+
      (Real.sinh d)^(2 : ℕ)*Real.sin_sq_add_cos_sq theta
  · dsimp [offset,height,heightAngular]
    ring

end
end RHTower.D4BMNativeCircle
