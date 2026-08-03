import Mathlib

/-!
# Modified-Bessel order recurrence and intensity annihilator

This file isolates the exact algebraic difference-equation content of the order-variable
modified-Bessel argument.  No special-function facts enter: every solution of

`y (z + 1) = y (z - 1) + c * z * y z`

has a three-dimensional symmetric-square state, and the intensity
`y z * y (z - 2)` has an explicit order-three scalar annihilator with polynomial
coefficients and nonzero endpoints.  The later analytic module instantiates `c = 2 / s` for
`K_z(s)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- The affine second-order order-shift recurrence. -/
def AffineOrderShiftRecurrence (c : ℂ) (y : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, y (z + 1) = y (z - 1) + c * z * y z

/-- The reflected adjacent-order product used by the Bessel intensity. -/
def orderShiftIntensity (y : ℂ → ℂ) (z : ℂ) : ℂ :=
  y z * y (z - 2)

/-- Symmetric-square state `(y(z)^2, y(z)y(z-1), y(z-1)^2)`. -/
def orderShiftSymmetricState (y : ℂ → ℂ) (z : ℂ) : Fin 3 → ℂ :=
  ![y z ^ 2, y z * y (z - 1), y (z - 1) ^ 2]

/-- Recurrent coefficient of `y(z+2)` in front of `y z`. -/
def orderShiftAlpha (c z : ℂ) : ℂ :=
  1 + c ^ 2 * z * (z + 1)

/-- Recurrent coefficient of `y(z+3)` in front of `y z`. -/
def orderShiftA (c z : ℂ) : ℂ :=
  c * (z + 2) * orderShiftAlpha c z + c * z

/-- Recurrent coefficient of `y(z+3)` in front of `y(z-1)`. -/
def orderShiftR (c z : ℂ) : ℂ :=
  1 + c ^ 2 * (z + 2) * (z + 1)

/-- The four intensity shifts as linear forms on the symmetric-square state. -/
def orderShiftIntensityRow (c z : ℂ) : Fin 4 → Fin 3 → ℂ
  | 0 => ![1, -c * (z - 1), 0]
  | 1 => ![0, c * z, 1]
  | 2 => ![orderShiftAlpha c z, c * (z + 1), 0]
  | 3 => ![c * z * orderShiftA c z,
      orderShiftA c z + c * z * orderShiftR c z,
      orderShiftR c z]

/-- Matrix whose rows are three selected intensity forms. -/
def orderShiftIntensityMinor (c z : ℂ) (missing : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  match missing with
  | 0 => ![orderShiftIntensityRow c z 1,
      orderShiftIntensityRow c z 2,
      orderShiftIntensityRow c z 3]
  | 1 => ![orderShiftIntensityRow c z 0,
      orderShiftIntensityRow c z 2,
      orderShiftIntensityRow c z 3]
  | 2 => ![orderShiftIntensityRow c z 0,
      orderShiftIntensityRow c z 1,
      orderShiftIntensityRow c z 3]
  | 3 => ![orderShiftIntensityRow c z 0,
      orderShiftIntensityRow c z 1,
      orderShiftIntensityRow c z 2]

/-- Alternating maximal-minor coefficients of the scalar intensity annihilator. -/
def orderShiftIntensityCoeff (c z : ℂ) : Fin 4 → ℂ
  | 0 => (orderShiftIntensityMinor c z 0).det
  | 1 => -(orderShiftIntensityMinor c z 1).det
  | 2 => (orderShiftIntensityMinor c z 2).det
  | 3 => -(orderShiftIntensityMinor c z 3).det

theorem orderShiftIntensityCoeff_zero (c z : ℂ) :
    orderShiftIntensityCoeff c z 0 = orderShiftA c z := by
  simp [orderShiftIntensityCoeff, orderShiftIntensityMinor, orderShiftIntensityRow,
    orderShiftAlpha, orderShiftA, orderShiftR, Matrix.det_fin_three]
  ring

theorem orderShiftIntensityCoeff_three (c z : ℂ) :
    orderShiftIntensityCoeff c z 3 =
      c * ((z - 1) * orderShiftAlpha c z + (z + 1)) := by
  simp [orderShiftIntensityCoeff, orderShiftIntensityMinor, orderShiftIntensityRow,
    Matrix.det_fin_three]
  ring

/-- The first scalar-annihilator coefficient is not the zero function when `c ≠ 0`. -/
theorem orderShiftIntensityCoeff_zero_function_ne_zero {c : ℂ} (hc : c ≠ 0) :
    (fun z => orderShiftIntensityCoeff c z 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [Pi.zero_apply, orderShiftIntensityCoeff_zero] at h0
  simp [orderShiftA, orderShiftAlpha] at h0
  exact hc h0

/-- The last scalar-annihilator coefficient is not the zero function when `c ≠ 0`. -/
theorem orderShiftIntensityCoeff_three_function_ne_zero {c : ℂ} (hc : c ≠ 0) :
    (fun z => orderShiftIntensityCoeff c z 3) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [Pi.zero_apply, orderShiftIntensityCoeff_three] at h1
  norm_num [hc] at h1

/-- Each of the four shifted intensities is the advertised rational linear form on the
symmetric-square state. -/
theorem orderShiftIntensity_add_nat_eq_state
    {c : ℂ} {y : ℂ → ℂ} (hy : AffineOrderShiftRecurrence c y)
    (z : ℂ) (j : Fin 4) :
    orderShiftIntensity y (z + (j : ℕ)) =
      ∑ k : Fin 3, orderShiftIntensityRow c z j k * orderShiftSymmetricState y z k := by
  have hm := hy (z - 1)
  have h0 := hy z
  have h1 := hy (z + 1)
  have h2 := hy (z + 2)
  have hm0 : y z = y (z - 2) + c * (z - 1) * y (z - 1) := by
    convert hm using 1 <;> ring
  have hm' : y (z - 2) = y z - c * (z - 1) * y (z - 1) := by
    exact (eq_sub_iff_add_eq).2 hm0.symm
  have h0' : y (z + 1) = y (z - 1) + c * z * y z := h0
  have h1' : y (z + 2) = y z + c * (z + 1) * y (z + 1) := by
    convert h1 using 1 <;> ring
  have h2' : y (z + 3) = y (z + 1) + c * (z + 2) * y (z + 2) := by
    convert h2 using 1 <;> ring
  fin_cases j <;>
    simp [orderShiftIntensity, orderShiftIntensityRow, orderShiftSymmetricState,
      Fin.sum_univ_three]
  · rw [hm']
    ring
  · rw [h0']
    ring
  · rw [h1', h0']
    simp only [orderShiftAlpha]
    ring
  · rw [h2', h1', h0']
    rw [show z + 3 - 2 = z + 1 by ring, h0']
    simp only [orderShiftAlpha, orderShiftA, orderShiftR]
    ring

/-- Alternating maximal minors give a linear dependence among the four intensity rows. -/
theorem sum_orderShiftIntensityCoeff_mul_row_eq_zero (c z : ℂ) (k : Fin 3) :
    ∑ j : Fin 4, orderShiftIntensityCoeff c z j * orderShiftIntensityRow c z j k = 0 := by
  fin_cases k <;>
    simp [Fin.sum_univ_four, orderShiftIntensityCoeff, orderShiftIntensityMinor,
      orderShiftIntensityRow, orderShiftAlpha, orderShiftA, orderShiftR,
      Matrix.det_fin_three] <;>
    ring

/-- **Exact scalar annihilator for the intensity.**  The four consecutive shifts of
`y(z)y(z-2)` satisfy a polynomial/rational linear relation. -/
theorem orderShiftIntensity_scalar_annihilator
    {c : ℂ} {y : ℂ → ℂ} (hy : AffineOrderShiftRecurrence c y) (z : ℂ) :
    ∑ j : Fin 4,
      orderShiftIntensityCoeff c z j * orderShiftIntensity y (z + (j : ℕ)) = 0 := by
  simp_rw [orderShiftIntensity_add_nat_eq_state hy z]
  calc
    ∑ j : Fin 4, orderShiftIntensityCoeff c z j *
        ∑ k : Fin 3, orderShiftIntensityRow c z j k * orderShiftSymmetricState y z k =
        ∑ k : Fin 3, (∑ j : Fin 4,
          orderShiftIntensityCoeff c z j * orderShiftIntensityRow c z j k) *
            orderShiftSymmetricState y z k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by
      simp [sum_orderShiftIntensityCoeff_mul_row_eq_zero]

/-! Polynomial realization of the annihilator coefficients. -/

def orderShiftAlphaPoly (c : ℂ) : Polynomial ℂ :=
  1 + Polynomial.C (c ^ 2) * Polynomial.X * (Polynomial.X + 1)

def orderShiftAPoly (c : ℂ) : Polynomial ℂ :=
  Polynomial.C c * (Polynomial.X + 2) * orderShiftAlphaPoly c +
    Polynomial.C c * Polynomial.X

def orderShiftRPoly (c : ℂ) : Polynomial ℂ :=
  1 + Polynomial.C (c ^ 2) * (Polynomial.X + 2) * (Polynomial.X + 1)

def orderShiftIntensityRowPoly (c : ℂ) : Fin 4 → Fin 3 → Polynomial ℂ
  | 0 => ![1, -Polynomial.C c * (Polynomial.X - 1), 0]
  | 1 => ![0, Polynomial.C c * Polynomial.X, 1]
  | 2 => ![orderShiftAlphaPoly c, Polynomial.C c * (Polynomial.X + 1), 0]
  | 3 => ![Polynomial.C c * Polynomial.X * orderShiftAPoly c,
      orderShiftAPoly c + Polynomial.C c * Polynomial.X * orderShiftRPoly c,
      orderShiftRPoly c]

def orderShiftIntensityMinorPoly (c : ℂ) (missing : Fin 4) :
    Matrix (Fin 3) (Fin 3) (Polynomial ℂ) :=
  match missing with
  | 0 => ![orderShiftIntensityRowPoly c 1,
      orderShiftIntensityRowPoly c 2,
      orderShiftIntensityRowPoly c 3]
  | 1 => ![orderShiftIntensityRowPoly c 0,
      orderShiftIntensityRowPoly c 2,
      orderShiftIntensityRowPoly c 3]
  | 2 => ![orderShiftIntensityRowPoly c 0,
      orderShiftIntensityRowPoly c 1,
      orderShiftIntensityRowPoly c 3]
  | 3 => ![orderShiftIntensityRowPoly c 0,
      orderShiftIntensityRowPoly c 1,
      orderShiftIntensityRowPoly c 2]

/-- Polynomial coefficients whose evaluations are `orderShiftIntensityCoeff`. -/
def orderShiftIntensityCoeffPoly (c : ℂ) : Fin 4 → Polynomial ℂ
  | 0 => (orderShiftIntensityMinorPoly c 0).det
  | 1 => -(orderShiftIntensityMinorPoly c 1).det
  | 2 => (orderShiftIntensityMinorPoly c 2).det
  | 3 => -(orderShiftIntensityMinorPoly c 3).det

theorem eval_orderShiftIntensityCoeffPoly (c z : ℂ) (j : Fin 4) :
    (orderShiftIntensityCoeffPoly c j).eval z = orderShiftIntensityCoeff c z j := by
  fin_cases j <;>
    simp [orderShiftIntensityCoeffPoly, orderShiftIntensityMinorPoly,
      orderShiftIntensityRowPoly, orderShiftAlphaPoly, orderShiftAPoly, orderShiftRPoly,
      orderShiftIntensityCoeff, orderShiftIntensityMinor, orderShiftIntensityRow,
      orderShiftAlpha, orderShiftA, orderShiftR, Matrix.det_fin_three]

theorem orderShiftIntensityCoeffPoly_zero_ne_zero {c : ℂ} (hc : c ≠ 0) :
    orderShiftIntensityCoeffPoly c 0 ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  have h0' : (orderShiftIntensityCoeffPoly c 0).eval 0 = 0 := by simpa using h0
  rw [eval_orderShiftIntensityCoeffPoly,
    orderShiftIntensityCoeff_zero] at h0'
  simp [orderShiftA, orderShiftAlpha] at h0'
  exact hc h0'

theorem orderShiftIntensityCoeffPoly_three_ne_zero {c : ℂ} (hc : c ≠ 0) :
    orderShiftIntensityCoeffPoly c 3 ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  have h1' : (orderShiftIntensityCoeffPoly c 3).eval 1 = 0 := by simpa using h1
  rw [eval_orderShiftIntensityCoeffPoly,
    orderShiftIntensityCoeff_three] at h1'
  norm_num [hc] at h1'

end

end HTGeometry
end GaloisForLFunctions
