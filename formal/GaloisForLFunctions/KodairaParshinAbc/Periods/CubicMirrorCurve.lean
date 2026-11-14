import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-!
# The cubic mirror pencil as a Weierstrass curve

The cubic mirror model in arXiv:2611.13126 has discriminant
`1728·27³ t³(1-27t)`. The exact factorization identifies the finite singular
parameters and the generic modular invariant. The generic elliptic
instance is proved from the polynomial discriminant, not assumed.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.CubicMirror

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The Weierstrass model after replacing `y` with `2y`. -/
def curve (t : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(27 - 648 * t) / 4
  a₆ := -(5832 * t ^ 2 - 972 * t + 27) / 4

theorem c₄ (t : K) : (curve t).c₄ = 324 * (1 - 24 * t) := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The discriminant has a triple factor at zero and a simple factor at `1/27`. -/
theorem discriminant (t : K) : (curve t).Δ = 1728 * 27 ^ 3 * t ^ 3 * (1 - 27 * t) := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Exact classification of all finite nonsingular parameters. -/
theorem isElliptic_iff (t : K) :
    (curve t).IsElliptic ↔ t ≠ 0 ∧ 1 - 27 * t ≠ 0 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, discriminant]
  simp only [mul_ne_zero_iff]
  norm_num

/-- No finite singular member has vanishing `c₄`. -/
theorem c₄_or_discriminant_ne_zero (t : K) : (curve t).c₄ ≠ 0 ∨ (curve t).Δ ≠ 0 := by
  rw [c₄, discriminant]
  by_cases h : 1 - 24 * t = 0
  · right
    have ht : t = 1 / 24 := by linear_combination -(1 / 24 : K) * h
    rw [ht]
    norm_num
  · left
    exact mul_ne_zero (by norm_num) h

/-- The pencil over the rational function field. -/
def genericCurve : WeierstrassCurve (RatFunc ℚ) :=
  curve (algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X)

instance genericCurve_isElliptic : genericCurve.IsElliptic := by
  apply (isElliptic_iff _).mpr
  refine ⟨RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero, ?_⟩
  have h : (1 - 27 * Polynomial.X : ℚ[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun p : ℚ[X] => p.coeff 0) he
    simp at hc
  convert RatFunc.algebraMap_ne_zero h using 1 <;> simp

/-- The generic modular invariant, without any assumed ellipticity input. -/
theorem genericCurve_j :
    genericCurve.j =
      (1 - 24 * algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X) ^ 3 /
        ((algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X) ^ 3 *
          (1 - 27 * algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X)) := by
  obtain ⟨hx, hs⟩ := (isElliptic_iff
    (algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X)).mp genericCurve_isElliptic
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  change ((curve _).Δ)⁻¹ * (curve _).c₄ ^ 3 = _
  rw [c₄, discriminant]
  field_simp
  ring

end GaloisForLFunctions.KodairaParshinAbc.CubicMirror

#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.c₄
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.discriminant
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.isElliptic_iff
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.c₄_or_discriminant_ne_zero
#print axioms GaloisForLFunctions.KodairaParshinAbc.CubicMirror.genericCurve_j
