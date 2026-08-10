import GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation

/-!
# The Chern form of the finite squarefree determinant line is the Fisher metric

The dual Hermitian metric of the finite squarefree determinant line is `h_S(s) = Z_S(Re s)⁻¹`.  Its
logarithmic potential `-log h_S` depends only on `Re s`, so the plane Laplacian of the potential is
its second real derivative, which is exactly the Fisher curvature `V_S`.  Hence the Chern form

```text
-∂∂̄ log h_S = (1/4) Var_{S, Re s}(H_S) ds ∧ ds̄
```

carries the same coefficient as the projective Fisher metric: the determinant-line Chern metric and
the statistical metric are one geometry, not two.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The dual Hermitian metric `h_S(s) = Z_S(Re s)⁻¹` of the finite determinant line. -/
def finiteSquarefreeLineMetric (S : Finset Nat.Primes) (s : ℂ) : ℝ :=
  (finiteSquarefreePartition S s.re)⁻¹

theorem finiteSquarefreeLineMetric_pos (S : Finset Nat.Primes) (s : ℂ) :
    0 < finiteSquarefreeLineMetric S s :=
  inv_pos.mpr (finiteSquarefreePartition_pos S s.re)

/-- The logarithmic potential `-log h_S`, in the real coordinates of `s`. -/
def finiteSquarefreeLinePotential (S : Finset Nat.Primes) (x y : ℝ) : ℝ :=
  -Real.log (finiteSquarefreeLineMetric S ⟨x, y⟩)

theorem finiteSquarefreeLinePotential_eq (S : Finset Nat.Primes) (x y : ℝ) :
    finiteSquarefreeLinePotential S x y = Real.log (finiteSquarefreePartition S x) := by
  rw [finiteSquarefreeLinePotential, finiteSquarefreeLineMetric, Real.log_inv, neg_neg]

/-! ## The two coordinate directions -/

theorem hasDerivAt_finiteSquarefreeLinePotential_re (S : Finset Nat.Primes) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => finiteSquarefreeLinePotential S t y)
      (-finiteSquarefreeCurrent S x) x := by
  rw [show (fun t : ℝ => finiteSquarefreeLinePotential S t y) =
      fun t : ℝ => Real.log (finiteSquarefreePartition S t) from
    funext fun t => finiteSquarefreeLinePotential_eq S t y]
  exact hasDerivAt_log_finiteSquarefreePartition S x

theorem deriv_finiteSquarefreeLinePotential_re (S : Finset Nat.Primes) (y : ℝ) :
    (fun t : ℝ => deriv (fun u : ℝ => finiteSquarefreeLinePotential S u y) t) =
      fun t : ℝ => -finiteSquarefreeCurrent S t :=
  funext fun t => (hasDerivAt_finiteSquarefreeLinePotential_re S t y).deriv

/-- The second real derivative of the potential is the Fisher curvature. -/
theorem deriv_deriv_finiteSquarefreeLinePotential_re (S : Finset Nat.Primes) (x y : ℝ) :
    deriv (fun t : ℝ => deriv (fun u : ℝ => finiteSquarefreeLinePotential S u y) t) x =
      finiteSquarefreeCurvature S x := by
  rw [deriv_finiteSquarefreeLinePotential_re S y]
  simpa using ((hasDerivAt_finiteSquarefreeCurrent S x).neg).deriv

theorem finiteSquarefreeLinePotential_im_const (S : Finset Nat.Primes) (x : ℝ) :
    (fun v : ℝ => finiteSquarefreeLinePotential S x v) =
      fun _ : ℝ => Real.log (finiteSquarefreePartition S x) :=
  funext fun v => finiteSquarefreeLinePotential_eq S x v

/-- The potential is constant in the imaginary direction, so its second imaginary derivative
vanishes. -/
theorem deriv_deriv_finiteSquarefreeLinePotential_im (S : Finset Nat.Primes) (x y : ℝ) :
    deriv (fun t : ℝ => deriv (fun v : ℝ => finiteSquarefreeLinePotential S x v) t) y = 0 := by
  rw [finiteSquarefreeLinePotential_im_const S x]
  simp

/-! ## The Chern form -/

/-- The plane Laplacian of the logarithmic metric potential. -/
def finiteSquarefreeLineLaplacian (S : Finset Nat.Primes) (x y : ℝ) : ℝ :=
  deriv (fun t : ℝ => deriv (fun u : ℝ => finiteSquarefreeLinePotential S u y) t) x +
    deriv (fun t : ℝ => deriv (fun v : ℝ => finiteSquarefreeLinePotential S x v) t) y

theorem finiteSquarefreeLineLaplacian_eq (S : Finset Nat.Primes) (x y : ℝ) :
    finiteSquarefreeLineLaplacian S x y = finiteSquarefreeCurvature S x := by
  rw [finiteSquarefreeLineLaplacian, deriv_deriv_finiteSquarefreeLinePotential_re,
    deriv_deriv_finiteSquarefreeLinePotential_im, add_zero]

/-- The Chern form coefficient `-∂∂̄ log h_S = (1/4) Δ log Z_S`. -/
def finiteSquarefreeChernCoefficient (S : Finset Nat.Primes) (x y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * finiteSquarefreeLineLaplacian S x y

/-- **The determinant-line Chern metric is the Fisher metric.**  The Chern coefficient of the dual
determinant-line metric is one quarter of the Hamiltonian variance in the Born law. -/
theorem finiteSquarefreeChernCoefficient_eq_quarter_variance (S : Finset Nat.Primes) (x y : ℝ) :
    finiteSquarefreeChernCoefficient S x y =
      (1 / 4 : ℝ) * ∑ z : SquarefreeBitConfig S,
        finiteSquarefreeBornWeight S x z *
          (finiteSquarefreeHamiltonian S z - finiteSquarefreeCurrent S x) ^ 2 := by
  rw [finiteSquarefreeChernCoefficient, finiteSquarefreeLineLaplacian_eq,
    finiteSquarefreeCurvature_eq_variance]

/-- The Chern coefficient is exactly the projective Fisher metric `V_S/4`. -/
theorem finiteSquarefreeChernCoefficient_eq_projectiveMetric (S : Finset Nat.Primes) (x y : ℝ) :
    finiteSquarefreeChernCoefficient S x y = finiteSquarefreeCurvature S x / 4 := by
  rw [finiteSquarefreeChernCoefficient, finiteSquarefreeLineLaplacian_eq]
  ring

/-- **One geometry.**  The Chern form of the determinant-line metric and the calibrated horizontal
tangent energy are the same curvature up to the fixed calibration `16 (σ-1)²`. -/
theorem norm_finiteSquarefreeTangent_sq_eq_calibrated_chern (S : Finset Nat.Primes)
    (sigma y : ℝ) :
    ‖finiteSquarefreeTangent S sigma‖ ^ 2 =
      16 * (sigma - 1) ^ 2 * finiteSquarefreeChernCoefficient S sigma y := by
  rw [norm_finiteSquarefreeTangent_sq, finiteSquarefreeChernCoefficient,
    finiteSquarefreeLineLaplacian_eq]
  ring

end RHTower
