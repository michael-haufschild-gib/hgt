import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A positive function with nonnegative logarithmic curvature cannot die at a
finite right endpoint where it is continuous. -/
theorem pos_right_endpoint_of_logarithmic_curvature
    {f f₁ f₂ : ℝ → ℝ} {l b : ℝ} (hlb : l < b)
    (hc : ContinuousOn f (Icc l b))
    (hd : ∀ x ∈ Ioo l b, HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Ioo l b, HasDerivAt f₁ (f₂ x) x)
    (hp : ∀ x ∈ Ioo l b, 0 < f x)
    (hcurv : ∀ x ∈ Ioo l b, (f₁ x) ^ 2 ≤ f x * f₂ x) :
    0 < f b := by
  let u := (l + b) / 2
  have hu : u ∈ Ioo l b := by dsimp [u]; constructor <;> linarith
  have hr : ∀ x ∈ Ioo l b,
      HasDerivAt (fun y => f₁ y / f y)
        ((f₂ x * f x - f₁ x * f₁ x) / (f x) ^ 2) x :=
    fun x hx => (hd₁ x hx).div (hd x hx) (hp x hx).ne'
  have hm : MonotoneOn (fun y => f₁ y / f y) (Ioo l b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo l b)
    · exact fun x hx => (hr x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hr x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo l b := by simpa using hx
      exact div_nonneg (by nlinarith [hcurv x hx']) (sq_nonneg _)
  let C := f₁ u / f u
  have hder : ∀ x ∈ Ioo u b,
      HasDerivAt (fun y => f y * Real.exp (-C * y))
        ((f₁ x - C * f x) * Real.exp (-C * x)) x := by
    intro x hx
    have hx' : x ∈ Ioo l b := ⟨hu.1.trans hx.1, hx.2⟩
    convert (hd x hx').mul (((hasDerivAt_id x).const_mul (-C)).exp) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hmono : MonotoneOn (fun y => f y * Real.exp (-C * y)) (Icc u b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u b)
    · exact (hc.mono (Icc_subset_Icc hu.1.le le_rfl)).mul (by fun_prop)
    · intro x hx
      exact (hder x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo u b := by simpa using hx
      have hratio : C ≤ f₁ x / f x := hm hu ⟨hu.1.trans hx'.1, hx'.2⟩ hx'.1.le
      have hfx := hp x ⟨hu.1.trans hx'.1, hx'.2⟩
      have hbound : C * f x ≤ f₁ x := (le_div_iff₀ hfx).mp hratio
      exact mul_nonneg (sub_nonneg.mpr hbound) (Real.exp_pos _).le
  have hle := hmono (left_mem_Icc.mpr hu.2.le) (right_mem_Icc.mpr hu.2.le) hu.2.le
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp
    ((mul_pos (hp u hu) (Real.exp_pos _)).trans_le hle)

end GaloisForLFunctions.HTGeometry
