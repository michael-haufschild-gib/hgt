import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic

/-!
# The traceless Hessian of a scalar on the hyperbolic plane is purely scalar-type

On the upper half-plane with the metric `y⁻²(dx² + dy²)` the Christoffel symbols are
`Γ^x_{xy} = Γ^x_{yx} = −1/y`, `Γ^y_{xx} = 1/y`, `Γ^y_{yy} = −1/y`. For a scalar `f` the Hessian is
`H_{ab} = ∂_a∂_b f − Γ^c_{ab}∂_c f`, the Laplacian `Δf = y²(f_xx + f_yy)`, and the traceless
Hessian `X_{ab} = H_{ab} − ½ g_{ab} Δf` has components
`X_xx = ½(f_xx − f_yy) − f_y/y = −X_yy`, `X_xy = f_xy + f_x/y`. Its covariant divergence
`D_b = g^{ac}∇_c X_{ab}` (with `g^{ac} = y² δ^{ac}`, `∇_c X_{ab} = ∂_c X_{ab} − Γ^d_{ca}X_{db} − Γ^d_{cb}X_{ad}`)
is exactly the gradient of `½Δf − f` (`tfHessian_divergence_x`, `tfHessian_divergence_y`), and its
curl `∂_x D_y − ∂_y D_x` vanishes identically in the jets of `f` (`tfHessian_divergence_curl`). In
the scalar/vector decomposition of symmetric tensors on the two-dimensional angular surface the
vector-type part is detected by the coexact part of the divergence, so a spin-two source of
traceless-Hessian form has no vector-type component: it can excite only the scalar sector.
-/

set_option autoImplicit false

namespace RHTower.D4BMScalarStream

/-- `X_xx` of the traceless Hessian, in terms of the jets of `f`. -/
noncomputable def tfHessXX (y fy fxx fyy : ℂ) : ℂ := (1 / 2) * (fxx - fyy) - fy / y

/-- `X_xy` of the traceless Hessian. -/
noncomputable def tfHessXY (y fx fxy : ℂ) : ℂ := fxy + fx / y

/-- The covariant divergence `D_x = y²(∇_x X_xx + ∇_y X_yx)`: the partial derivatives of the
components are written through the jets of `f`, and the Christoffel terms `−2Γ^y_xx X_yx` and
`−(Γ^y_yy + Γ^x_yx) X_yx` are `∓(2/y)X_xy`. -/
noncomputable def tfHessDivX (y fx fxy fxxx fxyy : ℂ) : ℂ :=
  y ^ (2 : ℕ) * (((1 / 2) * (fxxx - fxyy) - fxy / y - (2 / y) * tfHessXY y fx fxy) +
    ((fxyy + fxy / y - fx / y ^ (2 : ℕ)) + (2 / y) * tfHessXY y fx fxy))

/-- The covariant divergence `D_y = y²(∇_x X_xy + ∇_y X_yy)`, with the Christoffel terms
`−Γ^y_xx X_yy − Γ^x_xy X_xx = (2/y)X_xx` and `−2Γ^y_yy X_yy = −(2/y)X_xx`. -/
noncomputable def tfHessDivY (y fy fxx fyy fxxy fyyy : ℂ) : ℂ :=
  y ^ (2 : ℕ) * (((fxxy + fxx / y) + (2 / y) * tfHessXX y fy fxx fyy) +
    ((-((1 / 2) * (fxxy - fyyy) - fyy / y + fy / y ^ (2 : ℕ))) - (2 / y) * tfHessXX y fy fxx fyy))

/-- `D_x` is the `x`-derivative of `½Δf − f`, `Δf = y²(f_xx + f_yy)`. -/
theorem tfHessian_divergence_x (y fx fxy fxxx fxyy : ℂ) (hy : y ≠ 0) :
    tfHessDivX y fx fxy fxxx fxyy = (1 / 2) * y ^ (2 : ℕ) * (fxxx + fxyy) - fx := by
  unfold tfHessDivX tfHessXY
  field_simp
  ring

/-- `D_y` is the `y`-derivative of `½Δf − f`. -/
theorem tfHessian_divergence_y (y fy fxx fyy fxxy fyyy : ℂ) (hy : y ≠ 0) :
    tfHessDivY y fy fxx fyy fxxy fyyy = y * (fxx + fyy) + (1 / 2) * y ^ (2 : ℕ) * (fxxy + fyyy) - fy := by
  unfold tfHessDivY tfHessXX
  field_simp
  ring

/-- `∂_x D_y`, differentiating `tfHessian_divergence_y` in the jets of `f`. -/
noncomputable def tfHessDivY_dx (y fxy fxxx fxyy fxxxy fxyyy : ℂ) : ℂ := (-1 : ℂ) * fxy + (1 : ℂ) * fxyy * y ^ (1 : ℕ) + (1 / 2 : ℂ) * fxyyy * y ^ (2 : ℕ) + (1 : ℂ) * fxxx * y ^ (1 : ℕ) + (1 / 2 : ℂ) * fxxxy * y ^ (2 : ℕ)

/-- `∂_y D_x`, differentiating `tfHessian_divergence_x` in the jets of `f` (the explicit powers of `y`
are differentiated as well). -/
noncomputable def tfHessDivX_dy (y fxy fxxx fxyy fxxxy fxyyy : ℂ) : ℂ := (-1 : ℂ) * fxy + (1 : ℂ) * fxyy * y ^ (1 : ℕ) + (1 / 2 : ℂ) * fxyyy * y ^ (2 : ℕ) + (1 : ℂ) * fxxx * y ^ (1 : ℕ) + (1 / 2 : ℂ) * fxxxy * y ^ (2 : ℕ)

/-- The curl of the divergence of the traceless Hessian vanishes. -/
theorem tfHessian_divergence_curl (y fxy fxxx fxyy fxxxy fxyyy : ℂ) :
    tfHessDivY_dx y fxy fxxx fxyy fxxxy fxyyy - tfHessDivX_dy y fxy fxxx fxyy fxxxy fxyyy = 0 := by
  unfold tfHessDivY_dx tfHessDivX_dy
  ring

end RHTower.D4BMScalarStream
