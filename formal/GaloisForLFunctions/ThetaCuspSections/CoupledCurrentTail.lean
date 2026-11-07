import GaloisForLFunctions.ThetaCuspSections.TheSharpCurrentTail
import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore
import GaloisForLFunctions.ThetaCuspSections.EvenCauchyBound

/-!
# The coupled analytic current tail

The product `Ξ(b-iz)Ξ(b+iz)` is even and bounded on a fixed aperture circle.
Subtracting its two Cauchy derivative formulas retains the aperture factor
before taking norms. This pays a factor of thirty-two in the complete tail.
-/

open Complex MeasureTheory Set Metric Filter
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower

/-- The two opposite aperture shifts retain a common decay envelope. -/
def coupledXiProduct (b : ℝ) (z : ℂ) : ℂ :=
  XiC ((b : ℂ) - z * I) * XiC ((b : ℂ) + z * I)

theorem coupledXiProduct_differentiable (b : ℝ) : Differentiable ℂ (coupledXiProduct b) :=
  (XiC_differentiable.comp (by fun_prop)).mul (XiC_differentiable.comp (by fun_prop))

theorem coupledXiProduct_even (b : ℝ) (z : ℂ) :
    coupledXiProduct b (-z) = coupledXiProduct b z := by
  simp only [coupledXiProduct, neg_mul, sub_neg_eq_add, add_neg_eq_sub, mul_comm]

/-- The complete coupled product has no loss from the common contour phase. -/
theorem norm_coupledXiProduct_le {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) (b : ℝ) :
    ‖coupledXiProduct b z‖ ≤ 1000000 * Real.exp (-(7 / 5 * |b|)) := by
  have hre : |z.re| ≤ 3 / 2 := (abs_re_le_norm z).trans hz
  have hm : (b : ℂ) - z * I = ((b + z.im : ℝ) : ℂ) + ((-z.re : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hp : (b : ℂ) + z * I = ((b - z.im : ℝ) : ℂ) + (z.re : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have h1 := norm_XiC_le_wide (b + z.im) (-z.re) (by rwa [abs_neg])
  have h2 := norm_XiC_le_wide (b - z.im) z.re hre
  have habs : 2 * |b| ≤ |b + z.im| + |b - z.im| := by
    have hh := abs_add_le (b + z.im) (b - z.im)
    rw [show b + z.im + (b - z.im) = 2 * b by ring, abs_mul] at hh
    norm_num at hh
    exact hh
  rw [coupledXiProduct, norm_mul, hm, hp]
  calc
    _ ≤ (1000 * Real.exp (-(7 / 10 * |b + z.im|))) *
        (1000 * Real.exp (-(7 / 10 * |b - z.im|))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1000000 * Real.exp (-(7 / 10 * (|b + z.im| + |b - z.im|))) := by
      rw [show -(7 / 10 * (|b + z.im| + |b - z.im|)) =
        -(7 / 10 * |b + z.im|) + -(7 / 10 * |b - z.im|) by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith only [habs]

theorem coupledXiProduct_real (a b : ℝ) :
    (coupledXiProduct b (a : ℂ)).re = normSq (XiC ((b : ℂ) - (a : ℂ) * I)) := by
  have he : (b : ℂ) + (a : ℂ) * I = (starRingEnd ℂ) ((b : ℂ) - (a : ℂ) * I) := by
    simp
  rw [coupledXiProduct, he, XiC_conj, Complex.mul_conj, Complex.ofReal_re]

theorem deriv_coupledXiProduct_re (a b : ℝ) :
    (deriv (coupledXiProduct b) (a : ℂ)).re = current a b := by
  have hh := ((coupledXiProduct_differentiable b (a : ℂ)).hasDerivAt).real_of_complex
  have he : (fun x : ℝ => (coupledXiProduct b (x : ℂ)).re) =
      (fun x : ℝ => normSq (XiC ((b : ℂ) - (x : ℂ) * I))) :=
    funext fun x => coupledXiProduct_real x b
  rw [he] at hh
  exact hh.unique (hasDerivAt_normSq_XiC a b)

/-- The complete current tail retains the aperture factor before taking norms. -/
theorem abs_current_le_coupled {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    |current a b| ≤ 1125000 * |a| * Real.exp (-(7 / 5 * |b|)) := by
  have hh := norm_deriv_even_le (coupledXiProduct_differentiable b)
    (coupledXiProduct_even b)
    (fun z hz => norm_coupledXiProduct_le
      (le_of_eq (by simpa only [mem_sphere, dist_zero_right] using hz)) b)
    (a := (a : ℂ)) (by simpa only [norm_real, Real.norm_eq_abs] using ha)
  rw [norm_real, Real.norm_eq_abs] at hh
  rw [← deriv_coupledXiProduct_re a b]
  exact (abs_re_le_norm _).trans (hh.trans_eq (by ring))

#print axioms abs_current_le_coupled

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
