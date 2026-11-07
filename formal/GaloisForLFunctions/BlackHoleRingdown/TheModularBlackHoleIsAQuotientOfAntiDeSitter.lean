import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The modular black hole is a quotient of the Rindler wedge of AdS₄

AdS₄ is the quadric `⟨X, X⟩ = −1` in `ℝ^{3,2}`, `⟨X, X′⟩ = −X₀X₀′ + X₁X₁′ + X₂X₂′ + X₃X₃′ − X₄X₄′`.
The exterior `r > 1`, `y > 0` of the massless topological black hole
`−(r² − 1) dt² + dr²/(r² − 1) + r² (dx² + dy²)/y²` maps to it by

`Φ(t, r, x, y) = (r Y(x, y), √(r² − 1) cosh t, √(r² − 1) sinh t)`,

where `Y(x, y) = ((x² + y² + 1)/2y, (x² + y² − 1)/2y, x/y)` is the hyperboloid point of `x + iy`.

* **On the quadric** (`ambientForm_adsEmbedding`): `⟨Y, Y⟩₂,₁ = −1` and `cosh² − sinh² = 1`.
* **Isometric** (`hasDerivAt_adsEmbedding_*`, `ambientForm_partial`): the Gram matrix of the four
  coordinate derivatives of `Φ` is the black-hole metric.
* **A chart of the Rindler wedge** (`adsEmbedding_mem_wedge`, `adsEmbedding_injective`,
  `exists_adsEmbedding_eq`): `Φ` is a bijection from the exterior onto
  `{⟨X,X⟩ = −1, X₃ > |X₄|, X₀ > X₁}`.
* **Modular equivariance** (`hyperboloid_moebius`, `adsEmbedding_smul`). With
  `M = (1/y) [[x² + y², x], [x, 1]]`, `γ ∈ SL₂(ℝ)` acts by `M ↦ γ M γᵀ`, a linear map multiplying
  `det M = −⟨Y, Y⟩` by `det γ²`. So `Φ(t, r, γz) = Λ_γ Φ(t, r, z)` with `Λ_γ` in the isometry group
  of `ℝ^{3,2}`, acting on `(X₀, X₁, X₂)` and fixing `X₃, X₄`.

So the black hole with horizon `PSL₂(ℤ)\ℍ` is the quotient of the Rindler wedge of AdS₄ by the image
of `SL₂(ℤ)` in `SO(2,1) ⊂ SO(3,2)`: locally it is AdS₄, and its arithmetic lies in the group.
-/

set_option autoImplicit false

open Real
open scoped MatrixGroups

namespace GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-! ### The ambient space and the embedding -/

/-- The form of `ℝ^{3,2}`: `−X₀X₀′ + X₁X₁′ + X₂X₂′ + X₃X₃′ − X₄X₄′`. -/
def ambientForm (X X' : Fin 5 → ℝ) : ℝ :=
  -(X 0 * X' 0) + X 1 * X' 1 + X 2 * X' 2 + X 3 * X' 3 - X 4 * X' 4

/-- The hyperboloid point of `x + iy`. -/
def hyperboloid (x y : ℝ) : Fin 3 → ℝ :=
  ![(x ^ 2 + y ^ 2 + 1) / (2 * y), (x ^ 2 + y ^ 2 - 1) / (2 * y), x / y]

/-- The embedding of the black-hole exterior into `ℝ^{3,2}`. -/
def adsEmbedding (t r x y : ℝ) : Fin 5 → ℝ :=
  ![r * hyperboloid x y 0, r * hyperboloid x y 1, r * hyperboloid x y 2,
    √(r ^ 2 - 1) * cosh t, √(r ^ 2 - 1) * sinh t]

/-- The black-hole metric `diag(−(r² − 1), 1/(r² − 1), r²/y², r²/y²)` in `(t, r, x, y)`. -/
def blackHoleMetric (r y : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then ![-(r ^ 2 - 1), (r ^ 2 - 1)⁻¹, r ^ 2 / y ^ 2, r ^ 2 / y ^ 2] i else 0

theorem hyperboloid_lorentz {x y : ℝ} (hy : y ≠ 0) :
    -(hyperboloid x y 0) ^ 2 + (hyperboloid x y 1) ^ 2 + (hyperboloid x y 2) ^ 2 = -1 := by
  simp only [hyperboloid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

theorem sq_sqrt_sub_one {r : ℝ} (hr : 1 ≤ r) : √(r ^ 2 - 1) ^ 2 = r ^ 2 - 1 :=
  sq_sqrt (by nlinarith)

/-- **The exterior lies on AdS₄.** -/
theorem ambientForm_adsEmbedding (t : ℝ) {r : ℝ} (hr : 1 ≤ r) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (adsEmbedding t r x y) (adsEmbedding t r x y) = -1 := by
  have hY := hyperboloid_lorentz (x := x) hy
  have hs := sq_sqrt_sub_one hr
  have hc := cosh_sq_sub_sinh_sq t
  simp only [ambientForm, adsEmbedding, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination r ^ 2 * hY + (r ^ 2 - 1) * hc + (cosh t ^ 2 - sinh t ^ 2) * hs

/-! ### The coordinate derivatives -/

/-- `∂Φ/∂t`. -/
def partialT (t r : ℝ) : Fin 5 → ℝ := ![0, 0, 0, √(r ^ 2 - 1) * sinh t, √(r ^ 2 - 1) * cosh t]

/-- `∂Φ/∂r`. -/
def partialR (t r x y : ℝ) : Fin 5 → ℝ :=
  ![hyperboloid x y 0, hyperboloid x y 1, hyperboloid x y 2,
    r / √(r ^ 2 - 1) * cosh t, r / √(r ^ 2 - 1) * sinh t]

/-- `∂Φ/∂x`. -/
def partialX (r x y : ℝ) : Fin 5 → ℝ := ![r * (x / y), r * (x / y), r / y, 0, 0]

/-- `∂Φ/∂y`. -/
def partialY (r x y : ℝ) : Fin 5 → ℝ :=
  ![r * ((y ^ 2 - x ^ 2 - 1) / (2 * y ^ 2)), r * ((y ^ 2 - x ^ 2 + 1) / (2 * y ^ 2)),
    r * (-x / y ^ 2), 0, 0]

theorem hasDerivAt_adsEmbedding_t (t r x y : ℝ) :
    HasDerivAt (fun t => adsEmbedding t r x y) (partialT t r) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact (hasDerivAt_cosh t).const_mul _
  · exact (hasDerivAt_sinh t).const_mul _

theorem hasDerivAt_sqrt_sub_one {r : ℝ} (hr : 1 < r) :
    HasDerivAt (fun r : ℝ => √(r ^ 2 - 1)) (r / √(r ^ 2 - 1)) r := by
  have hpos : 0 < r ^ 2 - 1 := by nlinarith
  have h := ((hasDerivAt_pow 2 r).sub_const 1).sqrt hpos.ne'
  convert h using 1
  have hs : 0 < √(r ^ 2 - 1) := sqrt_pos.mpr hpos
  field_simp
  push_cast
  ring

theorem hasDerivAt_adsEmbedding_r (t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    HasDerivAt (fun r => adsEmbedding t r x y) (partialR t r x y) r := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hasDerivAt_mul_const _
  · exact hasDerivAt_mul_const _
  · exact hasDerivAt_mul_const _
  · exact (hasDerivAt_sqrt_sub_one hr).mul_const (cosh t)
  · exact (hasDerivAt_sqrt_sub_one hr).mul_const (sinh t)

/-- `d/dx` of `r (x² + c)/(2y)`. -/
theorem hasDerivAt_quadratic_x (r c x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun x : ℝ => r * ((x ^ 2 + c) / (2 * y))) (r * (x / y)) x := by
  have h := ((((hasDerivAt_pow 2 x).add_const c).div_const (2 * y))).const_mul r
  refine h.congr_deriv ?_
  field_simp
  push_cast
  ring

/-- `d/dy` of `r (x² + y² + c)/(2y)`. -/
theorem hasDerivAt_quadratic_y (r c x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => r * ((x ^ 2 + y ^ 2 + c) / (2 * y)))
      (r * ((y ^ 2 - x ^ 2 - c) / (2 * y ^ 2))) y := by
  have hnum : HasDerivAt (fun y : ℝ => x ^ 2 + y ^ 2 + c) (2 * y) y := by
    refine (((hasDerivAt_pow 2 y).const_add (x ^ 2)).add_const c).congr_deriv ?_
    push_cast
    ring
  have hden : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
    simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
  have h := (hnum.div hden (by positivity)).const_mul r
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_adsEmbedding_x (t r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun x => adsEmbedding t r x y) (partialX r x y) x := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine ((hasDerivAt_quadratic_x r (y ^ 2 + 1) x y hy).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · show r * ((x ^ 2 + y ^ 2 + 1) / (2 * y)) = r * ((x ^ 2 + (y ^ 2 + 1)) / (2 * y))
      ring
    · rfl
  · refine ((hasDerivAt_quadratic_x r (y ^ 2 - 1) x y hy).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · show r * ((x ^ 2 + y ^ 2 - 1) / (2 * y)) = r * ((x ^ 2 + (y ^ 2 - 1)) / (2 * y))
      ring
    · rfl
  · refine ((((hasDerivAt_id x).div_const y).const_mul r).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · show r * (x / y) = r * (id x / y)
      rfl
    · show r * (1 / y) = r / y
      ring
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

theorem hasDerivAt_adsEmbedding_y (t r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => adsEmbedding t r x y) (partialY r x y) y := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hasDerivAt_quadratic_y r 1 x hy
  · refine ((hasDerivAt_quadratic_y r (-1) x hy).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · show r * ((x ^ 2 + y ^ 2 - 1) / (2 * y)) = r * ((x ^ 2 + y ^ 2 + -1) / (2 * y))
      ring
    · show r * ((y ^ 2 - x ^ 2 - -1) / (2 * y ^ 2)) = r * ((y ^ 2 - x ^ 2 + 1) / (2 * y ^ 2))
      ring
  · refine ((((hasDerivAt_inv hy).const_mul x).const_mul r).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · show r * (x / y) = r * (x * y⁻¹)
      rw [div_eq_mul_inv]
    · show r * (x * -(y ^ 2)⁻¹) = r * (-x / y ^ 2)
      ring
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

/-! ### The Gram matrix -/

theorem ambientForm_comm (X X' : Fin 5 → ℝ) : ambientForm X X' = ambientForm X' X := by
  simp only [ambientForm]
  ring

theorem gram_tt (t : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ambientForm (partialT t r) (partialT t r) = -(r ^ 2 - 1) := by
  have hs := sq_sqrt_sub_one hr
  have hc := cosh_sq_sub_sinh_sq t
  simp [ambientForm, partialT]
  linear_combination (sinh t ^ 2 - cosh t ^ 2) * hs - (r ^ 2 - 1) * hc

theorem gram_tr (t r x y : ℝ) : ambientForm (partialT t r) (partialR t r x y) = 0 := by
  simp [ambientForm, partialT, partialR]
  ring

theorem gram_tx (t r x y : ℝ) : ambientForm (partialT t r) (partialX r x y) = 0 := by
  simp [ambientForm, partialT, partialX]

theorem gram_ty (t r x y : ℝ) : ambientForm (partialT t r) (partialY r x y) = 0 := by
  simp [ambientForm, partialT, partialY]

theorem gram_rr (t : ℝ) {r : ℝ} (hr : 1 < r) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialR t r x y) (partialR t r x y) = (r ^ 2 - 1)⁻¹ := by
  have hpos : 0 < r ^ 2 - 1 := by nlinarith
  have hs0 : √(r ^ 2 - 1) ≠ 0 := (sqrt_pos.mpr hpos).ne'
  have hs : √(r ^ 2 - 1) ^ 2 = r ^ 2 - 1 := sq_sqrt hpos.le
  have hc := cosh_sq_sub_sinh_sq t
  have hY := hyperboloid_lorentz (x := x) hy
  have hrad : (r / √(r ^ 2 - 1) * cosh t) * (r / √(r ^ 2 - 1) * cosh t) -
      (r / √(r ^ 2 - 1) * sinh t) * (r / √(r ^ 2 - 1) * sinh t) = r ^ 2 / (r ^ 2 - 1) := by
    rw [show (r / √(r ^ 2 - 1) * cosh t) * (r / √(r ^ 2 - 1) * cosh t) -
        (r / √(r ^ 2 - 1) * sinh t) * (r / √(r ^ 2 - 1) * sinh t) =
        r ^ 2 / √(r ^ 2 - 1) ^ 2 * (cosh t ^ 2 - sinh t ^ 2) by ring, hc, hs, mul_one]
  have hsplit : ambientForm (partialR t r x y) (partialR t r x y) =
      (-(hyperboloid x y 0) ^ 2 + (hyperboloid x y 1) ^ 2 + (hyperboloid x y 2) ^ 2) +
        ((r / √(r ^ 2 - 1) * cosh t) * (r / √(r ^ 2 - 1) * cosh t) -
          (r / √(r ^ 2 - 1) * sinh t) * (r / √(r ^ 2 - 1) * sinh t)) := by
    simp only [ambientForm, partialR]
    simp
    ring
  rw [hsplit, hY, hrad]
  field_simp
  ring

theorem gram_rx (t r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialR t r x y) (partialX r x y) = 0 := by
  simp [ambientForm, partialR, partialX, hyperboloid]
  field_simp
  ring

theorem gram_ry (t r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialR t r x y) (partialY r x y) = 0 := by
  simp [ambientForm, partialR, partialY, hyperboloid]
  field_simp
  ring

theorem gram_xx (r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialX r x y) (partialX r x y) = r ^ 2 / y ^ 2 := by
  simp [ambientForm, partialX]
  field_simp

theorem gram_xy (r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialX r x y) (partialY r x y) = 0 := by
  simp [ambientForm, partialX, partialY]
  field_simp
  ring

theorem gram_yy (r x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ambientForm (partialY r x y) (partialY r x y) = r ^ 2 / y ^ 2 := by
  simp [ambientForm, partialY]
  field_simp
  ring

/-- The coordinate derivatives in the order `(t, r, x, y)`. -/
def partialVec (t r x y : ℝ) : Fin 4 → Fin 5 → ℝ :=
  ![partialT t r, partialR t r x y, partialX r x y, partialY r x y]

/-- **The embedding is isometric.** The Gram matrix of the coordinate derivatives of `Φ` in
`ℝ^{3,2}` is the black-hole metric. -/
theorem ambientForm_partial (t : ℝ) {r : ℝ} (hr : 1 < r) (x : ℝ) {y : ℝ} (hy : y ≠ 0)
    (i j : Fin 4) :
    ambientForm (partialVec t r x y i) (partialVec t r x y j) = blackHoleMetric r y i j := by
  fin_cases i <;> fin_cases j <;>
    simp [partialVec, blackHoleMetric, gram_tt t hr.le, gram_tr, gram_tx, gram_ty,
      gram_rr t hr x hy, gram_rx t r x hy, gram_ry t r x hy, gram_xx r x hy, gram_xy r x hy,
      gram_yy r x hy, ambientForm_comm (partialR t r x y) (partialT t r),
      ambientForm_comm (partialX r x y) (partialT t r), ambientForm_comm (partialY r x y) (partialT t r),
      ambientForm_comm (partialX r x y) (partialR t r x y),
      ambientForm_comm (partialY r x y) (partialR t r x y),
      ambientForm_comm (partialY r x y) (partialX r x y)]

/-! ### A chart of the Rindler wedge -/

/-- `Φ` is injective on the exterior. -/
theorem adsEmbedding_injective {t r x y t' r' x' y' : ℝ} (hr : 1 < r) (hr' : 1 < r')
    (hy : 0 < y) (hy' : 0 < y')
    (h : adsEmbedding t r x y = adsEmbedding t' r' x' y') :
    t = t' ∧ r = r' ∧ x = x' ∧ y = y' := by
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [adsEmbedding, hyperboloid] at h0 h1 h2 h3 h4
  simp at h0 h1 h2 h3 h4
  have hp : 0 < r ^ 2 - 1 := by nlinarith
  have hp' : 0 < r' ^ 2 - 1 := by nlinarith
  have hs := sq_sqrt hp.le
  have hs' := sq_sqrt hp'.le
  have hc := cosh_sq_sub_sinh_sq t
  have hc' := cosh_sq_sub_sinh_sq t'
  -- `X₃² − X₄² = r² − 1` recovers `r`.
  have hrr : r ^ 2 - 1 = r' ^ 2 - 1 := by
    have e : (√(r ^ 2 - 1) * cosh t) ^ 2 - (√(r ^ 2 - 1) * sinh t) ^ 2 =
        (√(r' ^ 2 - 1) * cosh t') ^ 2 - (√(r' ^ 2 - 1) * sinh t') ^ 2 := by rw [h3, h4]
    linear_combination e - (cosh t ^ 2 - sinh t ^ 2) * hs + (cosh t' ^ 2 - sinh t' ^ 2) * hs'
      - (r ^ 2 - 1) * hc + (r' ^ 2 - 1) * hc'
  have hr_eq : r = r' := by nlinarith
  subst hr_eq
  have hs0 : 0 < √(r ^ 2 - 1) := sqrt_pos.mpr hp
  have hsinh : sinh t = sinh t' := mul_left_cancel₀ hs0.ne' h4
  have ht : t = t' := sinh_injective hsinh
  have hr0 : r ≠ 0 := by linarith
  -- `Y₀ − Y₁ = 1/y` and `Y₂ = x/y`.
  have hinv : 1 / y = 1 / y' := by
    have e0 := mul_left_cancel₀ hr0 h0
    have e1 := mul_left_cancel₀ hr0 h1
    have : (x ^ 2 + y ^ 2 + 1) / (2 * y) - (x ^ 2 + y ^ 2 - 1) / (2 * y) =
        (x' ^ 2 + y' ^ 2 + 1) / (2 * y') - (x' ^ 2 + y' ^ 2 - 1) / (2 * y') := by rw [e0, e1]
    field_simp at this ⊢
    linarith
  have hyy : y = y' := by
    field_simp at hinv
    linarith
  subst hyy
  have e2 := mul_left_cancel₀ hr0 h2
  have hxx : x = x' := by
    field_simp at e2
    exact e2
  exact ⟨ht, rfl, hxx, rfl⟩

/-- `Φ` maps the exterior into the Rindler wedge `X₃ > |X₄|`, `X₀ > X₁`. -/
theorem adsEmbedding_mem_wedge (t : ℝ) {r : ℝ} (hr : 1 < r) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    |adsEmbedding t r x y 4| < adsEmbedding t r x y 3 ∧
      adsEmbedding t r x y 1 < adsEmbedding t r x y 0 := by
  have hpos : 0 < r ^ 2 - 1 := by nlinarith
  have hs0 : 0 < √(r ^ 2 - 1) := sqrt_pos.mpr hpos
  have hc := cosh_sq_sub_sinh_sq t
  have hcpos := cosh_pos t
  have habs : |sinh t| < cosh t := by
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (sinh t), sq_nonneg (cosh t + sinh t),
      sq_nonneg (cosh t - sinh t)]
  refine ⟨?_, ?_⟩
  · simp only [adsEmbedding]
    simp only [Matrix.cons_val, abs_mul, abs_of_pos hs0]
    exact mul_lt_mul_of_pos_left habs hs0
  · simp [adsEmbedding, hyperboloid]
    have hr0 : 0 < r := by linarith
    apply mul_lt_mul_of_pos_left _ hr0
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith

/-- `Φ` maps the exterior onto the Rindler wedge `{⟨X,X⟩ = −1, X₃ > |X₄|, X₀ > X₁}`. -/
theorem exists_adsEmbedding_eq {X : Fin 5 → ℝ} (hX : ambientForm X X = -1)
    (h34 : |X 4| < X 3) (h01 : X 1 < X 0) :
    ∃ t r x y : ℝ, 1 < r ∧ 0 < y ∧ adsEmbedding t r x y = X := by
  have hw : 0 < X 3 ^ 2 - X 4 ^ 2 := by
    have h4 : X 4 ^ 2 < X 3 ^ 2 := by
      have := sq_lt_sq' (neg_lt_of_abs_lt h34) (lt_of_abs_lt h34)
      simpa using this
    linarith
  set ρ := √(X 3 ^ 2 - X 4 ^ 2) with hρ
  have hρ0 : 0 < ρ := sqrt_pos.mpr hw
  have hρ2 : ρ ^ 2 = X 3 ^ 2 - X 4 ^ 2 := sq_sqrt hw.le
  set r := √(1 + ρ ^ 2) with hrdef
  have hr2 : r ^ 2 = 1 + ρ ^ 2 := sq_sqrt (by positivity)
  have hr1 : 1 < r := by
    have hr0' : 0 ≤ r := sqrt_nonneg _
    nlinarith
  have hr0 : 0 < r := by linarith
  have hsq : √(r ^ 2 - 1) = ρ := by
    rw [hr2, add_sub_cancel_left, sqrt_sq hρ0.le]
  set t := arsinh (X 4 / ρ) with htdef
  have hsinh : ρ * sinh t = X 4 := by
    rw [htdef, sinh_arsinh]
    field_simp
  have hcosh : ρ * cosh t = X 3 := by
    have hc := cosh_sq_sub_sinh_sq t
    have hcpos : 0 < cosh t := cosh_pos t
    have hX3 : 0 < X 3 := lt_of_le_of_lt (abs_nonneg _) h34
    have e : (ρ * cosh t) ^ 2 = X 3 ^ 2 := by
      have : (ρ * cosh t) ^ 2 = ρ ^ 2 * (cosh t ^ 2 - sinh t ^ 2) + (ρ * sinh t) ^ 2 := by ring
      rw [this, hc, hsinh, hρ2]
      ring
    have hpos : 0 < ρ * cosh t := mul_pos hρ0 hcpos
    nlinarith [sq_nonneg (ρ * cosh t - X 3), sq_nonneg (ρ * cosh t + X 3)]
  -- The horizon point.
  have hq : -(X 0) ^ 2 + X 1 ^ 2 + X 2 ^ 2 = -r ^ 2 := by
    have := hX
    simp only [ambientForm] at this
    nlinarith
  set y := r / (X 0 - X 1) with hydef
  have hd : 0 < X 0 - X 1 := by linarith
  have hy0 : 0 < y := div_pos hr0 hd
  set x := X 2 * y / r with hxdef
  refine ⟨t, r, x, y, hr1, hy0, ?_⟩
  funext i
  fin_cases i
  · simp only [adsEmbedding, hyperboloid, hxdef, hydef]
    simp
    field_simp
    nlinarith [hq]
  · simp only [adsEmbedding, hyperboloid, hxdef, hydef]
    simp
    field_simp
    nlinarith [hq]
  · simp [adsEmbedding, hyperboloid, hxdef, hydef]
    field_simp
  · simp [adsEmbedding, hsq, hcosh]
  · simp [adsEmbedding, hsq, hsinh]

/-! ### Modular equivariance -/

/-- `γ = [[a, b], [c, d]]` acting on `Y` through `M ↦ γ M γᵀ`, `M = [[Y₀ + Y₁, Y₂], [Y₂, Y₀ − Y₁]]`. -/
def moebiusLorentz (a b c d : ℝ) (Y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((a ^ 2 * (Y 0 + Y 1) + 2 * a * b * Y 2 + b ^ 2 * (Y 0 - Y 1)) +
        (c ^ 2 * (Y 0 + Y 1) + 2 * c * d * Y 2 + d ^ 2 * (Y 0 - Y 1))) / 2,
    ((a ^ 2 * (Y 0 + Y 1) + 2 * a * b * Y 2 + b ^ 2 * (Y 0 - Y 1)) -
        (c ^ 2 * (Y 0 + Y 1) + 2 * c * d * Y 2 + d ^ 2 * (Y 0 - Y 1))) / 2,
    a * c * (Y 0 + Y 1) + (a * d + b * c) * Y 2 + b * d * (Y 0 - Y 1)]

/-- The transformation of `ℝ^{3,2}` induced by `γ`, fixing `X₃` and `X₄`. -/
def ambientLorentz (a b c d : ℝ) (X : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![moebiusLorentz a b c d ![X 0, X 1, X 2] 0, moebiusLorentz a b c d ![X 0, X 1, X 2] 1,
    moebiusLorentz a b c d ![X 0, X 1, X 2] 2, X 3, X 4]

/-- **`Λ_γ` is an isometry of `ℝ^{3,2}`** for `det γ = 1`. -/
theorem ambientForm_ambientLorentz {a b c d : ℝ} (h : a * d - b * c = 1) (X X' : Fin 5 → ℝ) :
    ambientForm (ambientLorentz a b c d X) (ambientLorentz a b c d X') = ambientForm X X' := by
  simp [ambientForm, ambientLorentz, moebiusLorentz]
  linear_combination (-(X 0 * X' 0) + X 1 * X' 1 + X 2 * X' 2) * (a * d - b * c + 1) * h

/-- **Equivariance of the hyperboloid point.** For `ad − bc = 1` and `w = (az + b)/(cz + d)`,
`Y(w) = Λ_γ Y(z)`, in coordinates `Re w = ((ax+b)(cx+d) + acy²)/D`, `Im w = y/D`,
`D = (cx + d)² + c²y²`. -/
theorem hyperboloid_moebius {a b c d : ℝ} (h : a * d - b * c = 1) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    hyperboloid (((a * x + b) * (c * x + d) + a * c * y ^ 2) / ((c * x + d) ^ 2 + (c * y) ^ 2))
        (y / ((c * x + d) ^ 2 + (c * y) ^ 2)) =
      moebiusLorentz a b c d (hyperboloid x y) := by
  have hD : (c * x + d) ^ 2 + (c * y) ^ 2 ≠ 0 := by
    intro h0
    have hc : c * y = 0 := by nlinarith [sq_nonneg (c * x + d), sq_nonneg (c * y)]
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hc with h1 | h1
      · exact h1
      · exact absurd h1 hy.ne'
    have hd0 : d = 0 := by subst hc0; nlinarith [sq_nonneg d]
    subst hc0
    subst hd0
    simp at h
  have hy0 : y ≠ 0 := hy.ne'
  set N := (a * x + b) * (c * x + d) + a * c * y ^ 2 with hN
  set D := (c * x + d) ^ 2 + (c * y) ^ 2 with hDdef
  have key : N ^ 2 + y ^ 2 = ((a * x + b) ^ 2 + (a * y) ^ 2) * D := by
    simp only [hN, hDdef]
    linear_combination (-(y ^ 2) * (a * d - b * c + 1)) * h
  funext i
  fin_cases i
  · show ((N / D) ^ 2 + (y / D) ^ 2 + 1) / (2 * (y / D)) = _
    have l : ((N / D) ^ 2 + (y / D) ^ 2 + 1) / (2 * (y / D)) =
        (((a * x + b) ^ 2 + (a * y) ^ 2) + D) / (2 * y) := by
      rw [show ((N / D) ^ 2 + (y / D) ^ 2 + 1) / (2 * (y / D)) =
        (N ^ 2 + y ^ 2 + D ^ 2) / (2 * y * D) by field_simp, key]
      field_simp
    rw [l, hDdef]
    simp [hyperboloid, moebiusLorentz]
    field_simp
    ring
  · show ((N / D) ^ 2 + (y / D) ^ 2 - 1) / (2 * (y / D)) = _
    have l : ((N / D) ^ 2 + (y / D) ^ 2 - 1) / (2 * (y / D)) =
        (((a * x + b) ^ 2 + (a * y) ^ 2) - D) / (2 * y) := by
      rw [show ((N / D) ^ 2 + (y / D) ^ 2 - 1) / (2 * (y / D)) =
        (N ^ 2 + y ^ 2 - D ^ 2) / (2 * y * D) by field_simp, key]
      field_simp
    rw [l, hDdef]
    simp [hyperboloid, moebiusLorentz]
    field_simp
    ring
  · show (N / D) / (y / D) = _
    simp [hyperboloid, moebiusLorentz, hN]
    field_simp
    ring

/-- **Modular equivariance of the embedding.** `Φ(t, r, γz) = Λ_γ Φ(t, r, z)` for `γ ∈ SL₂(ℤ)`. -/
theorem adsEmbedding_smul (t r : ℝ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    adsEmbedding t r (g • z).re (g • z).im =
      ambientLorentz (g 0 0) (g 0 1) (g 1 0) (g 1 1) (adsEmbedding t r z.re z.im) := by
  have hdet : ((g 0 0 : ℤ) : ℝ) * (g 1 1 : ℤ) - (g 0 1 : ℤ) * (g 1 0 : ℤ) = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hz := UpperHalfPlane.coe_specialLinearGroup_apply g z
  have hre : (g • z).re = (((g 0 0 : ℝ) * z.re + g 0 1) * ((g 1 0 : ℝ) * z.re + g 1 1) +
      (g 0 0 : ℝ) * (g 1 0 : ℝ) * z.im ^ 2) /
        (((g 1 0 : ℝ) * z.re + g 1 1) ^ 2 + ((g 1 0 : ℝ) * z.im) ^ 2) := by
    rw [UpperHalfPlane.re, hz, Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  have him : (g • z).im = z.im /
      (((g 1 0 : ℝ) * z.re + g 1 1) ^ 2 + ((g 1 0 : ℝ) * z.im) ^ 2) := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_apply]
    simp
    ring
  have hY := hyperboloid_moebius hdet z.re z.im_pos
  rw [hre, him]
  funext i
  fin_cases i
  · simp only [adsEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp only [adsEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp only [adsEmbedding, ambientLorentz]
    rw [hY]
    simp [moebiusLorentz]
    ring
  · simp [adsEmbedding, ambientLorentz]
  · simp [adsEmbedding, ambientLorentz]

end

end GaloisForLFunctions.BlackHoleRingdown
