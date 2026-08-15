import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The radial flux of a moment tower

A moment tower obeying the first-order law `d/dy s_y(k) = -(k+1)·s_y(k+1)` turns every
first Hausdorff difference into a derivative: the primitive

`Φ_c(y) = ∑_{i,j} (c_i c_j / (i+j+1))·y^{i+j+1}·s_y(i+j)`

has derivative exactly the quadratic form of the first Hausdorff-difference matrix,

`Φ_c'(y) = ∑_{i,j} c_i c_j (y^{i+j} s_y(i+j) - y^{i+j+1} s_y(i+j+1))`.

Positivity of the first Hausdorff difference is therefore monotonicity of an explicit radial flux,
not an unrelated moment inequality.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The single-index radial primitive `y^{k+1}/(k+1)·s_y(k)`. -/
def radialFluxTerm (S : ℝ → ℕ → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  y ^ (k + 1) / ((k : ℝ) + 1) * S y k

/-- **The single-index flux law.**  Under the moment tower's first-order law, the derivative of the
radial primitive is the first Hausdorff difference. -/
theorem hasDerivAt_radialFluxTerm {S : ℝ → ℕ → ℝ} {y : ℝ} (k : ℕ)
    (hS : HasDerivAt (fun v : ℝ => S v k) (-((k : ℝ) + 1) * S y (k + 1)) y) :
    HasDerivAt (radialFluxTerm S k)
      (y ^ k * S y k - y ^ (k + 1) * S y (k + 1)) y := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun v : ℝ => v ^ (k + 1) / ((k : ℝ) + 1))
      (((k : ℝ) + 1) * y ^ k / ((k : ℝ) + 1)) y := by
    have h := hasDerivAt_pow (k + 1) y
    simpa using h.div_const ((k : ℝ) + 1)
  have hprod := hpow.mul hS
  refine hprod.congr_deriv ?_
  field_simp
  ring

/-- The radial primitive of a coefficient vector. -/
def radialFlux (S : ℝ → ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (y : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    c i * c j * radialFluxTerm S ((i : ℕ) + (j : ℕ)) y

/-- **The radial flux law.**  The derivative of the radial primitive is the quadratic form of the
first Hausdorff-difference matrix. -/
theorem hasDerivAt_radialFlux {S : ℝ → ℕ → ℝ} {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hS : ∀ k : ℕ, HasDerivAt (fun v : ℝ => S v k) (-((k : ℝ) + 1) * S y (k + 1)) y) :
    HasDerivAt (radialFlux S c)
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c i * c j *
        (y ^ ((i : ℕ) + (j : ℕ)) * S y ((i : ℕ) + (j : ℕ))
          - y ^ ((i : ℕ) + (j : ℕ) + 1) * S y ((i : ℕ) + (j : ℕ) + 1))) y := by
  have hfun : radialFlux S c
      = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          (fun v : ℝ => c i * c j * radialFluxTerm S ((i : ℕ) + (j : ℕ)) v) := by
    funext v
    simp only [radialFlux, Finset.sum_apply]
  rw [hfun]
  refine HasDerivAt.sum fun i _ => HasDerivAt.sum fun j _ => ?_
  exact (hasDerivAt_radialFluxTerm ((i : ℕ) + (j : ℕ)) (hS _)).const_mul (c i * c j)

end GaloisForLFunctions.HTGeometry

end
