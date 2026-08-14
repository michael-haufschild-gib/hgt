import GaloisForLFunctions.HTGeometry.MellinReflectionKernel
import Mathlib.Analysis.MellinTransform

/-!
# The genus-`g` Barnes model factor

The reflection kernel of `1/(1+y)` on the critical strip is `integral_halfLine_reflection`.  The
model factor of a genus-`g` linear canonical product is `t^{g+1}/(1+t)`, whose Mellin transform is
therefore the same kernel translated by `g+1`.

Two facts about it are what a Mellin-Barnes expansion of a sum of rescaled model factors consumes:
the value of the transform, and its behaviour under rescaling of the argument, which is the step
turning the sum over the scales into a Dirichlet series.

* `GaloisForLFunctions.HTGeometry.barnesModel`;
* `GaloisForLFunctions.HTGeometry.mellin_barnesModel`;
* `GaloisForLFunctions.HTGeometry.mellin_barnesModel_scaled`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set

noncomputable section

/-- Complex powers of a positive real invert together with the base. -/
theorem ofReal_cpow_inv_eq {v : ℝ} (hv : 0 < v) (w : ℂ) :
    ((v⁻¹ : ℝ) : ℂ) ^ w = (((v : ℝ) : ℂ) ^ w)⁻¹ := by
  have hprod : ((v⁻¹ : ℝ) : ℂ) ^ w * (((v : ℝ) : ℂ) ^ w) = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg (le_of_lt (inv_pos.2 hv)) hv.le]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hv.ne', Complex.ofReal_one, Complex.one_cpow]
  have hne : (((v : ℝ) : ℂ) ^ w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hv.ne'))
  field_simp at hprod ⊢
  exact hprod

/-- The model factor of a genus-`g` linear canonical product. -/
def barnesModel (g : ℕ) (t : ℝ) : ℂ := ((t : ℝ) : ℂ) ^ (g + 1 : ℕ) / (1 + ((t : ℝ) : ℂ))

/-- **The shifted reflection kernel.**  The Mellin integral of the genus-`g` model factor is the
reflection kernel translated by `g+1`. -/
theorem integral_barnesKernel_shift {w : ℂ} (g : ℕ)
    (hw0 : 0 < (w + (g + 1 : ℕ)).re) (hw1 : (w + (g + 1 : ℕ)).re < 1) :
    (∫ t in Ioi (0 : ℝ),
        ((t : ℝ) : ℂ) ^ (w - 1) * (((t : ℝ) : ℂ) ^ (g + 1 : ℕ) / (1 + ((t : ℝ) : ℂ))))
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (w + (g + 1 : ℕ))) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ((t : ℝ) : ℂ) ^ (w - 1) * (((t : ℝ) : ℂ) ^ (g + 1 : ℕ) / (1 + ((t : ℝ) : ℂ)))
        = ((t : ℝ) : ℂ) ^ ((w + (g + 1 : ℕ)) - 1) / (1 + ((t : ℝ) : ℂ)) := by
    intro t ht
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    have hnat : ((t : ℝ) : ℂ) ^ (g + 1 : ℕ) = ((t : ℝ) : ℂ) ^ ((g + 1 : ℕ) : ℂ) :=
      (Complex.cpow_natCast _ _).symm
    rw [hnat, ← mul_div_assoc, ← Complex.cpow_add _ _ htne]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  exact integral_halfLine_reflection hw0 hw1

/-- **The Mellin transform of the model factor.** -/
theorem mellin_barnesModel {w : ℂ} (g : ℕ)
    (hw0 : 0 < (w + (g + 1 : ℕ)).re) (hw1 : (w + (g + 1 : ℕ)).re < 1) :
    mellin (barnesModel g) w = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (w + (g + 1 : ℕ))) := by
  rw [mellin]
  simp only [barnesModel, smul_eq_mul]
  exact integral_barnesKernel_shift g hw0 hw1

/-- **The scaling law of the model transform.**  Rescaling the argument by a positive number
multiplies the transform by that number to the power of the Mellin variable.  Applied at a scale
`n^σ` this is the step which turns the sum over `n` into a Dirichlet series. -/
theorem mellin_barnesModel_scaled (g : ℕ) (w : ℂ) {A : ℝ} (hA : 0 < A) :
    mellin (fun x : ℝ => barnesModel g (x / A)) w
      = ((A : ℝ) : ℂ) ^ w * mellin (barnesModel g) w := by
  have hAinv : (0 : ℝ) < A⁻¹ := inv_pos.2 hA
  have hfun : (fun x : ℝ => barnesModel g (x / A)) = fun x : ℝ => barnesModel g (x * A⁻¹) := by
    funext x
    rw [div_eq_mul_inv]
  rw [hfun, mellin_comp_mul_right (barnesModel g) w hAinv]
  rw [smul_eq_mul]
  congr 1
  rw [ofReal_cpow_inv_eq hA (-w), Complex.cpow_neg, inv_inv]

end

end GaloisForLFunctions.HTGeometry
