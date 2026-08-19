import Mathlib

/-!
# The imaginary-pole Bezoutian kernel is a Gram matrix

For a pole `a = i t` on the imaginary axis the paired resolvent block of the Bezoutian kernel
collapses to a rank-one Gram term:

`((w - a)⁻¹ + conj ((v - a)⁻¹)) / (w + conj v) = (w - a)⁻¹ · conj ((v - a)⁻¹)`.

The mechanism is that `(w - a) + conj (v - a) = w + conj v` exactly when `a` is purely imaginary,
so the divided sum of reciprocals cancels the denominator.  Summing over a finite divisor on the
imaginary axis therefore produces a manifest Gram matrix, and multiplying by `X(w) conj (X(v))` is a
congruence, so the whole Bezoutian is positive semidefinite.

This is the positivity engine for the value-fibre classifier: the only remaining analytic input is
the resolvent expansion of the logarithmic derivative over the divisor.
-/

open Matrix Finset
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- A right half-plane point is never an imaginary-axis pole. -/
theorem sub_imaginary_ne_zero {t : ℝ} {w : ℂ} (hw : 0 < w.re) :
    w - (t : ℝ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre
  linarith

theorem add_conj_ne_zero {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    w + (starRingEnd ℂ) v ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  linarith

/-- The two shifted factors of an imaginary-axis pole add up to the Bezoutian denominator. -/
theorem sub_imaginary_add_conj (t : ℝ) (w v : ℂ) :
    (w - (t : ℝ) * Complex.I) + (starRingEnd ℂ) (v - (t : ℝ) * Complex.I) =
      w + (starRingEnd ℂ) v := by
  rw [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_inv_sub_imaginary (t : ℝ) (v : ℂ) :
    (starRingEnd ℂ) ((v - (t : ℝ) * Complex.I)⁻¹) =
      ((starRingEnd ℂ) (v - (t : ℝ) * Complex.I))⁻¹ := map_inv₀ _ _

/-- **The rank-one collapse.**  One paired resolvent block of the Bezoutian kernel at an
imaginary-axis pole is a rank-one Gram term. -/
theorem bezoutian_imaginary_pole_rankOne (t : ℝ) {w v : ℂ}
    (hw : 0 < w.re) (hv : 0 < v.re) :
    ((w - (t : ℝ) * Complex.I)⁻¹ +
        (starRingEnd ℂ) ((v - (t : ℝ) * Complex.I)⁻¹)) / (w + (starRingEnd ℂ) v) =
      (w - (t : ℝ) * Complex.I)⁻¹ *
        (starRingEnd ℂ) ((v - (t : ℝ) * Complex.I)⁻¹) := by
  have hA : w - (t : ℝ) * Complex.I ≠ 0 := sub_imaginary_ne_zero hw
  have hB : (starRingEnd ℂ) (v - (t : ℝ) * Complex.I) ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr (sub_imaginary_ne_zero hv)
  have hsum := sub_imaginary_add_conj t w v
  have hden : w + (starRingEnd ℂ) v ≠ 0 := add_conj_ne_zero hw hv
  rw [conj_inv_sub_imaginary, ← hsum]
  rw [div_eq_iff (by rw [hsum]; exact hden)]
  field_simp
  ring

/-! ## The finite Gram form -/

/-- The Bezoutian kernel of a finite imaginary-axis divisor. -/
noncomputable def imaginaryBezoutianKernel {n : ℕ} (t : Fin n → ℝ) (w v : ℂ) : ℂ :=
  ∑ i, ((w - (t i : ℝ) * Complex.I)⁻¹ +
      (starRingEnd ℂ) ((v - (t i : ℝ) * Complex.I)⁻¹)) / (w + (starRingEnd ℂ) v)

/-- **The imaginary-pole Bezoutian kernel is a Gram matrix.** -/
theorem posSemidef_imaginaryBezoutian {n m : ℕ} (t : Fin n → ℝ) (w : Fin m → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    (Matrix.of fun j k => imaginaryBezoutianKernel t (w j) (w k)).PosSemidef := by
  classical
  set B : Matrix (Fin m) (Fin n) ℂ :=
    Matrix.of fun j i => (w j - (t i : ℝ) * Complex.I)⁻¹ with hB
  have hentry : (Matrix.of fun j k => imaginaryBezoutianKernel t (w j) (w k)) = B * Bᴴ := by
    ext j k
    rw [Matrix.mul_apply, Matrix.of_apply, imaginaryBezoutianKernel]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [bezoutian_imaginary_pole_rankOne (t i) (hw j) (hw k), hB]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  rw [hentry]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- **Congruence.**  Multiplying a positive semidefinite kernel by `d j · conj (d k)` preserves
positivity — this is the step that restores the factor `X(w) conj (X(v))`. -/
theorem posSemidef_congr_diagonal {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : M.PosSemidef) (d : Fin m → ℂ) :
    (Matrix.of fun j k => d j * M j k * (starRingEnd ℂ) (d k)).PosSemidef := by
  classical
  have hD : (Matrix.of fun j k => d j * M j k * (starRingEnd ℂ) (d k)) =
      (Matrix.diagonal d) * M * (Matrix.diagonal d)ᴴ := by
    ext j k
    rw [Matrix.of_apply, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    simp [RCLike.star_def]
  rw [hD]
  exact hM.mul_mul_conjTranspose_same _

end GaloisForLFunctions.HTGeometry
