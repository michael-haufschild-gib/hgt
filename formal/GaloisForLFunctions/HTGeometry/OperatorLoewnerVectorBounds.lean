import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Vector-wise consequences of Loewner bounds on `E →L[ℂ] E`

The C⋆-order on the bounded operators of a Hilbert space is the quadratic-form order: `0 ≤ T`
means `T = S⋆S`, hence `⟪T v, v⟫` is a squared norm.  This file records the vector-wise form of a
Loewner lower bound, `m ≤ T ⟹ m‖v‖² ≤ Re⟪T v, v⟫ ⟹ m²‖v‖² ≤ ‖T v‖²`, which is what the
two-sided Hilbert–Schmidt sandwich estimates consume.
-/

open scoped Ring InnerProductSpace
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- A nonnegative operator has nonnegative quadratic form. -/
theorem re_inner_nonneg_of_nonneg {T : E →L[ℂ] E} (hT : 0 ≤ T) (v : E) :
    0 ≤ RCLike.re (inner ℂ (T v) v) := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  rw [hS, show (star S * S) v = adjoint S (S v) from rfl, adjoint_inner_left,
    inner_self_eq_norm_sq]
  positivity

/-- A Loewner lower bound is a lower bound on the quadratic form. -/
theorem smul_one_le_re_inner {T : E →L[ℂ] E} {m : ℝ} (h : m • (1 : E →L[ℂ] E) ≤ T) (v : E) :
    m * ‖v‖ ^ 2 ≤ RCLike.re (inner ℂ (T v) v) := by
  have hnn := re_inner_nonneg_of_nonneg (sub_nonneg.mpr h) v
  have hval : ((T - m • (1 : E →L[ℂ] E)) v) = T v - ((m : ℂ)) • v := by
    simp [sub_apply, Complex.coe_smul]
  have hsm : RCLike.re (inner ℂ (((m : ℂ)) • v) v) = m * ‖v‖ ^ 2 := by
    rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    simp only [← RCLike.ofReal_pow]
    norm_num
    exact Or.inl (by rw [← Complex.ofReal_pow, Complex.ofReal_re])
  rw [hval, inner_sub_left, map_sub, hsm] at hnn
  linarith

/-- A Loewner lower bound gives a vector-wise lower bound on the norm. -/
theorem sq_mul_norm_sq_le_norm_apply_sq {T : E →L[ℂ] E} {m : ℝ} (hm : 0 ≤ m)
    (h : m • (1 : E →L[ℂ] E) ≤ T) (v : E) : (m * m) * ‖v‖ ^ 2 ≤ ‖T v‖ ^ 2 := by
  have h1 : m * ‖v‖ ^ 2 ≤ RCLike.re (inner ℂ (T v) v) := smul_one_le_re_inner h v
  have h2 : RCLike.re (inner ℂ (T v) v) ≤ ‖T v‖ * ‖v‖ := by
    calc RCLike.re (inner ℂ (T v) v) ≤ ‖(inner ℂ (T v) v : ℂ)‖ := RCLike.re_le_norm _
      _ ≤ ‖T v‖ * ‖v‖ := norm_inner_le_norm _ _
  have h3 : m * ‖v‖ ≤ ‖T v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
    · rw [← hv, mul_zero]; exact norm_nonneg _
    · have := h1.trans h2
      nlinarith [hv]
  nlinarith [norm_nonneg (T v), norm_nonneg v, h3, hm]

end GaloisForLFunctions.HTGeometry
