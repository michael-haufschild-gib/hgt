import GaloisForLFunctions.HTGeometry.GaussTerminalSourceLogDerivative

/-!
# Apex-centered faithful Gauss source

De-resisted completed source leaves one unit atom at every admitted node.  Centering each atom at
the moving hard apex before aggregation gives residue `(y*x)^2 - 1`.  Its Cauchy transform has an
exact landing in the current admission logarithmic derivative, with degree and root-trace
counterterms forced by polynomial division.

Everything is finite-block algebra.  No representing measure, infinite extension, limiting
argument, or computation is used.
-/

open scoped BigOperators
open Polynomial Complex

namespace HTGeometry

/-- First trace of the current finite Gauss face. -/
noncomputable def gaussNodeTrace (s : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ gaussNodes s m, x

/-- Faithful unit-pole carrier centered at moving hard apex `1/y` before aggregation. -/
noncomputable def gaussApexCenteredUnitPoleTransformComplex
    (s : ℕ → ℝ) (m : ℕ) (y : ℝ) (z : ℂ) : ℂ :=
  ∑ x ∈ gaussNodes s m,
    (((y * x) ^ 2 - 1 : ℝ) : ℂ) / (z - (x : ℂ))

/-- **Exact apex-centered source landing.**  The signed faithful carrier is the admission
logarithmic derivative multiplied by its moving-apex quadratic, minus the intrinsic degree and
root-trace vacuum forced by polynomial division. -/
theorem gaussApexCenteredUnitPoleTransformComplex_eq_logDerivative
    {s : ℕ → ℝ} {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N)
    (y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    gaussApexCenteredUnitPoleTransformComplex s m y z =
      ((y : ℂ) ^ 2 * z ^ 2 - 1) *
          (Polynomial.aeval z (monicOrtho s (m + 1)).derivative /
            monicOrthoC s (m + 1) z) -
        (y : ℂ) ^ 2 *
          (((gaussNodes s m).card : ℂ) * z + (gaussNodeTrace s m : ℂ)) := by
  classical
  let nodes := gaussNodes s m
  have hpoint (x : ℝ) (hx : x ∈ nodes) :
      (((y * x) ^ 2 - 1 : ℝ) : ℂ) / (z - (x : ℂ)) =
        (((y : ℂ) ^ 2 * z ^ 2 - 1) / (z - (x : ℂ)) -
          (y : ℂ) ^ 2 * (z + (x : ℂ))) := by
    have hxz : z - (x : ℂ) ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
      exact hz him
    push_cast
    field_simp [hxz]
    ring
  rw [gaussApexCenteredUnitPoleTransformComplex,
    show gaussNodes s m = nodes by rfl]
  calc
    ∑ x ∈ nodes, (((y * x) ^ 2 - 1 : ℝ) : ℂ) / (z - (x : ℂ)) =
        ∑ x ∈ nodes,
          (((y : ℂ) ^ 2 * z ^ 2 - 1) / (z - (x : ℂ)) -
            (y : ℂ) ^ 2 * (z + (x : ℂ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x hx
    _ = ((y : ℂ) ^ 2 * z ^ 2 - 1) *
          gaussUnitPoleTransformComplex s m z -
        (y : ℂ) ^ 2 * (((nodes.card : ℂ) * z) + (gaussNodeTrace s m : ℂ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      rw [gaussUnitPoleTransformComplex,
        show gaussNodes s m = nodes by rfl, gaussNodeTrace,
        show gaussNodes s m = nodes by rfl]
      push_cast
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by
      rw [gaussUnitPoleTransformComplex_eq_logDerivative h hmN hz]

/-- Current degree form of the exact apex-centered landing. -/
theorem gaussApexCenteredUnitPoleTransformComplex_eq_degree_logDerivative
    {s : ℕ → ℝ} {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N)
    (y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    gaussApexCenteredUnitPoleTransformComplex s m y z =
      ((y : ℂ) ^ 2 * z ^ 2 - 1) *
          (Polynomial.aeval z (monicOrtho s (m + 1)).derivative /
            monicOrthoC s (m + 1) z) -
        (y : ℂ) ^ 2 *
          (((m + 1 : ℕ) : ℂ) * z + (gaussNodeTrace s m : ℂ)) := by
  rw [gaussApexCenteredUnitPoleTransformComplex_eq_logDerivative h hmN y hz,
    gaussNodes_card_below h m hmN]

/-- Pole residue of the centered faithful carrier has exactly the moving-apex sign. -/
theorem gaussApexCenteredResidue_pos_iff
    {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    0 < (y * x) ^ 2 - 1 ↔ 1 < y * x := by
  nlinarith [mul_pos hy hx]

end HTGeometry
