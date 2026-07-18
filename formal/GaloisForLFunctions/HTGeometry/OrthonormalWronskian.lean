import GaloisForLFunctions.HTGeometry.OrthonormalMomentPolynomials
import GaloisForLFunctions.HTGeometry.SecondKindMomentPolynomials

/-!
# The orthonormal-normalized Wronskian

In the monic normalization the Wronskian `Qₙ₊₁ Rₙ - Qₙ Rₙ₊₁ = -hₙ / h₀` depends on `n`.  Rescaling
both families by their moment norms and weighting by the orthonormal off-diagonal recurrence
coefficient `aₙ = ‖Qₙ₊₁‖ / ‖Qₙ‖` removes that dependence entirely:

`aₙ (pₙ₊₁ rₙ - pₙ rₙ₊₁) = -1 / h₀`

*independently of `n`*.  This `n`-independent constant is the finite precursor of the determinant
identity `A D - B C = 1` of the Nevanlinna matrix: the classical normalization is recovered when the
moment sequence is normalized so that `h₀ = s₀ = 1`.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The second-kind family rescaled by the moment norms, matching `orthonormalPoly`. -/
noncomputable def secondKindNorm (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (monicOrthoNorm s n)⁻¹ • secondKind s n

/-- The orthonormal off-diagonal recurrence coefficient `aₙ = ‖Qₙ₊₁‖ / ‖Qₙ‖`. -/
noncomputable def recurOffSqrt (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  monicOrthoNorm s (n + 1) / monicOrthoNorm s n

theorem recurOffSqrt_pos (h : PositiveMomentForm s) (n : ℕ) : 0 < recurOffSqrt s n :=
  div_pos (monicOrthoNorm_pos h (n + 1)) (monicOrthoNorm_pos h n)

/-- **The normalized Wronskian is constant in `n`.** -/
theorem orthonormalWronskian_eq (h : PositiveMomentForm s) (n : ℕ) :
    Polynomial.C (recurOffSqrt s n) *
        (orthonormalPoly s (n + 1) * secondKindNorm s n -
          orthonormalPoly s n * secondKindNorm s (n + 1))
      = Polynomial.C (-(1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))) := by
  have hNn : monicOrthoNorm s n ≠ 0 := monicOrthoNorm_ne_zero h n
  have hNn1 : monicOrthoNorm s (n + 1) ≠ 0 := monicOrthoNorm_ne_zero h (n + 1)
  have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hw : monicOrtho s (n + 1) * secondKind s n - monicOrtho s n * secondKind s (n + 1)
      = Polynomial.C (-(momentInner s (monicOrtho s n) (monicOrtho s n) /
        momentInner s (monicOrtho s 0) (monicOrtho s 0))) := momentWronskian_eq h n
  have hgroup : Polynomial.C (recurOffSqrt s n) *
      (orthonormalPoly s (n + 1) * secondKindNorm s n -
        orthonormalPoly s n * secondKindNorm s (n + 1))
      = Polynomial.C (recurOffSqrt s n * (monicOrthoNorm s (n + 1))⁻¹ *
          (monicOrthoNorm s n)⁻¹) *
        (monicOrtho s (n + 1) * secondKind s n - monicOrtho s n * secondKind s (n + 1)) := by
    simp only [orthonormalPoly, secondKindNorm, Polynomial.smul_eq_C_mul, Polynomial.C_mul]
    ring
  rw [hgroup, hw, ← Polynomial.C_mul]
  congr 1
  rw [recurOffSqrt, ← monicOrthoNorm_sq h n]
  field_simp

/-- The normalized Wronskian never vanishes. -/
theorem orthonormalWronskian_ne_zero (h : PositiveMomentForm s) (n : ℕ) :
    Polynomial.C (recurOffSqrt s n) *
        (orthonormalPoly s (n + 1) * secondKindNorm s n -
          orthonormalPoly s n * secondKindNorm s (n + 1)) ≠ 0 := by
  rw [orthonormalWronskian_eq h n, Ne, Polynomial.C_eq_zero, neg_eq_zero, div_eq_zero_iff]
  rintro (hA | hB)
  · exact one_ne_zero hA
  · exact h.self_ne_zero (monicOrtho_ne_zero s 0) hB

/-- With a normalized moment sequence (`h₀ = 1`) the constant is exactly `-1`, the classical
determinant normalization of the Nevanlinna matrix. -/
theorem orthonormalWronskian_eq_neg_one (h : PositiveMomentForm s)
    (h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) = 1) (n : ℕ) :
    Polynomial.C (recurOffSqrt s n) *
        (orthonormalPoly s (n + 1) * secondKindNorm s n -
          orthonormalPoly s n * secondKindNorm s (n + 1))
      = -1 := by
  rw [orthonormalWronskian_eq h n, h0]
  simp

end HTGeometry
