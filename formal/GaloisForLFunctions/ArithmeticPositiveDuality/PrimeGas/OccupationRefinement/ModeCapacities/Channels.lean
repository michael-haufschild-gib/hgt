import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Probabilities
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.FiniteShells

/-! # Coherent associative refinement with independent capacity units at each prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open CoassociativeSplitting

def kernel (s : ℂ) (u v : ℕ → ℝ) : Kernel := fun a b =>
  Complex.exp (s*(Real.log (branch u v a.val b.val):ℂ))

theorem kernel_rescale (s : ℂ) (g u v : ℕ → ℝ) (hg : positive g) :
    kernel s (g*u) (g*v)=kernel s u v := by
  funext a b
  rw [kernel,kernel,branch_rescale g u v hg a b]

private theorem telescopes {u v w : ℕ → ℝ} (hu : positive u) (hv : positive v) (hw : positive w)
    (a b c : ℕ+) :
    branch (u+v) w (a*b).val c.val * branch u v a.val b.val =
    branch u (v+w) a.val (b*c).val * branch v w b.val c.val := by
  have hab := (profile_pos (positive_add hu hv) (a*b)).ne'
  have hbc := (profile_pos (positive_add hv hw) (b*c)).ne'
  simp only [PNat.mul_coe] at hab hbc ⊢
  simp only [branch,add_assoc,mul_assoc a.val b.val c.val]
  field_simp [hab,hbc]

theorem associative (s : ℂ) {u v w : ℕ → ℝ} (hu : positive u) (hv : positive v) (hw : positive w)
    (a b c : ℕ+) :
    kernel s (u+v) w (a*b) c * kernel s u v a b =
    kernel s u (v+w) a (b*c) * kernel s v w b c := by
  simp only [kernel,←Complex.exp_add,←mul_add,←Complex.ofReal_add]
  rw [←Real.log_mul (branch_pos (positive_add hu hv) hw (a*b) c).ne' (branch_pos hu hv a b).ne',
    ←Real.log_mul (branch_pos hu (positive_add hv hw) a (b*c)).ne' (branch_pos hv hw b c).ne',
    telescopes hu hv hw]

theorem kernel_norm (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (a b : ℕ+) :
    ‖kernel s u v a b‖^2=(branch u v a.val b.val)^(2*s.re) := by
  rw [kernel,Complex.norm_exp,sq,←Real.exp_add,Real.rpow_def_of_pos (branch_pos hu hv a b)]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  congr 1
  ring

#print axioms kernel_rescale
#print axioms associative
#print axioms kernel_norm

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
