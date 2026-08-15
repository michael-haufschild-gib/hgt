import GaloisForLFunctions.RHTower.CCMEulerRayLogDerivativeIndex

/-!
# The real Euler ray of the shifted-Xi Schur kernel

Restricting the generalized Schur kernel

```text
S_omega (z, w) = i (1 - Theta_omega z * conj (Theta_omega w))/(z - conj w)
```

to the vertical ray `z = i y`, `w = i x` turns the complex Cauchy denominator into the *real*
Cauchy denominator: `i/(i y - conj (i x)) = 1/(x + y)`.  So the ray kernel is exactly the real
Cauchy--Loewner kernel `L_omega (x, y) = (1 - f_omega x * f_omega y)/(x + y)`.

Scalar positivity of the Euler quotient is not enough: for two unequal values the matrix
`(1 - r_i r_j)` has determinant `-(r_1 - r_2)^2 < 0`.  Every factor of the explicit Euler formula
`(16)` for `f_omega` is nevertheless positive, which is what makes the ray a real, prime-side
object with no critical-strip evaluation.
-/

open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The ray restriction -/

/-- **Equation (13).**  On the vertical ray the complex Cauchy denominator becomes the real one. -/
theorem ray_cauchy_denominator {x y : ℝ} (hxy : x + y ≠ 0) :
    Complex.I / ((Complex.I * (y : ℂ)) - (starRingEnd ℂ) (Complex.I * (x : ℂ)))
      = ((1 / (x + y) : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (Complex.I * (x : ℂ)) = -(Complex.I * (x : ℂ)) := by
    simp [Complex.conj_I]
  rw [hconj, sub_neg_eq_add]
  have hfac : Complex.I * (y : ℂ) + Complex.I * (x : ℂ) = Complex.I * ((x + y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfac]
  have hxyC : ((x + y : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hxy
  push_cast
  field_simp

/-- **Equations (9) → (2).**  The Schur kernel restricted to the ray is the real Cauchy–Loewner
kernel of the positive Euler quotient. -/
theorem schur_ray_eq_loewner {f : ℝ → ℝ} {x y : ℝ} (hxy : x + y ≠ 0) :
    Complex.I * (1 - ((f y : ℝ) : ℂ) * (starRingEnd ℂ) ((f x : ℝ) : ℂ))
        / ((Complex.I * (y : ℂ)) - (starRingEnd ℂ) (Complex.I * (x : ℂ)))
      = (((1 - f x * f y) / (x + y) : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) ((f x : ℝ) : ℂ) = ((f x : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hconj]
  have hsplit : Complex.I * (1 - ((f y : ℝ) : ℂ) * ((f x : ℝ) : ℂ))
      / ((Complex.I * (y : ℂ)) - (starRingEnd ℂ) (Complex.I * (x : ℂ)))
      = (1 - ((f y : ℝ) : ℂ) * ((f x : ℝ) : ℂ))
        * (Complex.I / ((Complex.I * (y : ℂ)) - (starRingEnd ℂ) (Complex.I * (x : ℂ)))) := by
    ring
  rw [hsplit, ray_cauchy_denominator hxy]
  push_cast
  ring

/-! ## The Cauchy–Loewner kernel of a real quotient -/

/-- The real Cauchy–Loewner kernel `(2)`. -/
def loewnerKernel (f : ℝ → ℝ) (x y : ℝ) : ℝ := (1 - f x * f y) / (x + y)

theorem loewnerKernel_diagonal (f : ℝ → ℝ) (x : ℝ) :
    loewnerKernel f x x = (1 - f x ^ 2) / (2 * x) := by
  unfold loewnerKernel
  rw [show x + x = 2 * x from by ring, sq]

/-! ## Scalar positivity is insufficient -/

/-- The scalar contraction matrix of two values. -/
def contractionMatrix (r₁ r₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - r₁ * r₁, 1 - r₁ * r₂; 1 - r₂ * r₁, 1 - r₂ * r₂]

/-- **The two-value obstruction.**  `det (1 - r_i r_j) = -(r₁ - r₂)²`. -/
theorem det_contractionMatrix (r₁ r₂ : ℝ) :
    (contractionMatrix r₁ r₂).det = -((r₁ - r₂) ^ 2) := by
  rw [contractionMatrix, Matrix.det_fin_two_of]
  ring

/-- Hence for two distinct values the matrix `(1 - r_i r_j)` is not positive semidefinite, no
matter how small the values are: pointwise bounds `0 < r < 1` carry no kernel information. -/
theorem not_posSemidef_contractionMatrix {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂) :
    ¬ (contractionMatrix r₁ r₂).PosSemidef := by
  intro hpos
  have hdet := hpos.det_nonneg
  rw [det_contractionMatrix] at hdet
  have hpos' : 0 < (r₁ - r₂) ^ 2 := by
    have : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hne
    positivity
  linarith

/-! ## Positivity of the explicit Euler factors -/

/-- The archimedean prefactor of `(16)` is positive. -/
theorem eulerFactor_arch_pos {ω : ℝ} : 0 < Real.pi ^ ω := Real.rpow_pos_of_pos Real.pi_pos ω

/-- The polar prefactor of `(15)` is positive beyond the abscissa. -/
theorem eulerFactor_polar_pos {s : ℝ} (hs : 1 < s) : 0 < s * (s - 1) := by
  have h0 : 0 < s := by linarith
  have h1 : 0 < s - 1 := by linarith
  positivity

/-- The Gamma factor of `(15)` is positive beyond the abscissa. -/
theorem eulerFactor_gamma_pos {s : ℝ} (hs : 0 < s) : 0 < Real.Gamma (s / 2) :=
  Real.Gamma_pos_of_pos (by positivity)

/-- Each local Euler factor of `(16)` lies strictly between `0` and `1`. -/
theorem eulerFactor_local_mem {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    0 < 1 - (p : ℝ) ^ (-s) ∧ 1 - (p : ℝ) ^ (-s) < 1 := by
  have hp0 : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hp1 : (1 : ℝ) < p := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hlt : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg hp0.le, inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow_iff_of_pos hp0 |>.2 (Or.inl ⟨hp1, hs⟩)
  have hgt : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  exact ⟨by linarith, by linarith⟩

end GaloisForLFunctions.RHTower

end
